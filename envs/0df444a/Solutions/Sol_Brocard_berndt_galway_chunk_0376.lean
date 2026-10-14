-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0376
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:29:47.681297+00:00
-- url     : https://prove2.me/submissions/9a5068f7-ba29-4d62-be93-d40bca021919

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 67446045 ≤ n < 67625901 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 67447295 1250 67446045 67446047
    0x1020c0a14011b14070c03050706020d020f0c15040b07061a06070b160e0a1806080d0509010c030c02090906101e1205150106050903010b040e100b060f0a0201060503010b100807 77
    0x3103160751381e0700038030381c414001c4e0008103c5504860700114070580082c000fa5141100281c200700c007950035442550440c2d8200000b03428040381d045040403044a1400d0140c04203108250b00d03000700d820541002c500400c80c4002c0003200e60085013a03455484001622201c45030411016114020b401010301c008840030880e43c04402040390f81410309820101d01c4080000c0101d201500b041d440a072492130240c54140c0f14103911b20540c005000a1000350410003160300002d002031050380525810011001c1a05e030603d0310401c1e5011040d81e0003080c226607801d040c00312964a0750305a600b0364a0004020000404c80640c504040f001c080302d1740e03180042d51178000381904907240442d0696641c05002c081c00000c41c041d0340444d0180070107450313030b07134841540605140c00c40e180710401e18081c5182c12440f0041c074000150350b0346400300c1c0e00008a80f91b1070440114505001341e620002049801207080800b041e0190402c8055650581c02001350384580020001d40d14012807030180881c01c00c03400f0405403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 67448545 1250 67447295 67447307
    0x30106170c0d0c02100b0d020a2706030302030a110d0935160b070206040e0709080106090c020610030b060112140403030b030c0301140114010c0501020c0a14011b 71
    0x716121561290800040c4080340055408000c0b09500507000040c94182d40001403142c54040c1c003050f07415583ca40c6040e0b0120710780e00707035a00803130545c443c0e1b4140f1004016040380c0a09201031050209000460303503850080e5984d00404408008a01f408180c40c912240009081d800a400c40e5142c4c45d0b19858441c1011000b42000c1840000302250000c0140340d50250030300310304420102000740001050031011118004a940150308105810810440540e4901c010388040e207030ba181e0074580c41e84440c0c60035107c202551740078031a90750074403400141c0340043d40d010b0002c0c809a80c00b62000355440c41c4812001030780701c1c00002c01d0704000001044440d403045110394140b1801542c0080c0e100d14500c00f001d868038044a08400180d1510f001e0340340b80c01c00b84a010441d0805600038080c04054804103068401c05014240420304490b00040c444c0c0e20070a401440c164004008655401103103208075200c1e0044c18040e20301c0c01d464040c035a10504148542880c16001c0c900320300030300681d007104590f4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 67449795 1250 67448545 67448551
    0x70807090b0c0a0c1d010b09030c060d14040b01060f0e030d0309020a09091101030c050a09051e040203010b09040b0a060801050f0402070501141605130308070c031203020a120203010617 81
    0x742e8800c03885803d001a80c0251804003415884003901e206030580b10402c400c510050b0001c1c01d00d48418464203940303490020700c1090850003183c0b419103810781a140384006002400340d0034040b000c1d100621041c44503401885058994503501c0060324145c10780d040d1084501d00c0441174041d8409022001c032140b0981c05050558070080040e0161995030081400b920102c203419511905e85e502d502506607010312422160040500f0690f0a00800c0b00d80a00516072a204280c041c0e902c65a034807120306401040c440c0c0d01000100700319100d584500c40811a9040403c01d203000e81e10b0008680c0f044d207071407040b680c1210300c0382c0e940c04016828001030082040038030345e0b52038000c3d07004e020001c00600d0138042d20117030701c400180515817490b14405000d00200c8400714101400810440003400700040d202500507650030603420b6542d400c0070f20341000240c4043c0c0c405401e44d921030b8403e1130681d41c560004c1a002c1d880340e56215a21803484005012488280f003410b0100d1015006011900c10845015034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 67451045 1250 67449795 67449817
    0x80702041d0303070216140906040507090b0c03040f06080f04080d060b19090e0907060e060706020406080403120c0503060915060c030405090c0702030d08040c050a03110108070807090b 81
    0x40e00d11038940042e2a54000b41c6020015800c082e0b02d080b00e04c2071900f044002800c201c20303070700c20b0f20001c0004a40313103401c0600014081c80e141c1000940c554001c0c040d030802401c1e0101d40a036140803110b801501ca402a0003139076441a0b00c030400082c07841c80340c4800380c041c040c10b00e00400c10b500c0380d5a4a8070198040c0c0d000b40d01c043c1c0c44100c00512948410040c01e443c800d800300784405c0380b40d100c100402c26103068104001341c0c3c050400780b01c1d14842c00a200416a103c07801c103503100b00e03c840b0000d401e5000d404001030015000042c04213011703501010045c021032180d160000b4100641e240300c02558441071001d0002a000d0000913100c0c94010030b4940c0000c407001021514074480300c04540258420703040744856510009040045050160000e68040020602c01c0e00340841c03a80000c1d19045464500300400c08080f0114051000c958215001008d000307000b060725942e6403501c403810108050b401e50100c0ca80310002112940103d80032031042000f80c0d0b803019440d091405402240e005100200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 67452295 1250 67451045 67451081
    0x10608070303200f060f0103030f020d0509040e01060e090a05100e0307060c050d060b1803010e0a02010e0105130f0302041415060c011d01060807080f070b0d090f06090203010507030908070204 84
    0x4c500e80c03400303005a41c0105120600700540d90706500300900300c4103451078140215801540c1c90323426250711009449400c481110046004481d0401941c058146900191170800c40c10081c803226000005d4401c22091040003652844004100c00318102e504083d03485c56190000c01c0b000d00050720603440511802c005007046401c000078074950780112031054211540c1900005940300031408000c100c0c2c2c1c032007407040b0024003018106a40035a04e51a400358000d041c0319070f460102d03c86a0154064907406061000750441301ca95502030013580b103001d07110580c000d600d8401c4001110800007207081c0305140035280840e1810204040c0700f1507034440c0c8c031040f6080d50386241c2842080003411400034181e404100104403903090114107414100242c0c8a00200d03070241303100480400f0302041c0300e021594482046601c0f03070100114980542a0000000d05000b0410360003000c225040d8401c044030350003a0001c0045d17940d0003005408403200400c01a01c1030314107121140041c0341c0703608041545079041910b6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 67453545 1250 67452295 67452313
    0xb1c0c05130e03030901090501060b160b0c0906070c050405070503130f06021c090209060307081011041701020a03060f050a03061a030d0c03020f070501050301030f020f060d0e01060807030320 84
    0x8a0070f5070400c1d14840880c1c1d440b102d2400600c2800d01990b0064071200b003046280428003030303103140d84d4040084000c2c8040c4c1c00d0f40008030000810304c140c41000070060411a1345a26a142c940d00400c01e5000303040c4100e06d443d010901041c41001601c2c442c4446600c1e20001c0041d17a2211005040030f0300381104c1c031580800c510300c8a90300400f0f588544e00d403180000f2640810900c104034100b800140a00d0081d0300040d010801b1501c0050f9116070428108400500c40a81c101d03c036030b052240350040e1302c5842908170039001d000b40560060001034400c1d40c1c200402038446080c00030071200b911401d54420a202400d00c00b041f000e0340503e20f00c14000c00f0200d400c4642001113410b09500d003648101052200203a10180360301803180f016a01c102c0c401a001680c10400003908fc0d00041c00090450380711038020500310349400c0424485850000c0c1110303102d80d40c90b03003400080e060070303603240301c15509000001401c4000050704000382ca0307240d00c551a69842e2900c0840207070b18840d800725814880c43c81c01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 67454795 1250 67453545 67453571
    0x70b0403020d020a05060408010b12010209010219030e04022704060303050405130905070e0f0a0902090415021c020301050406080102070f06090503070c060815010c0506010611030c030d0b1c0c0513 86
    0x10070060448e1000400c007145541c08100000c0f03581c43e20804940d0040100c5051a0707408500800e45244d003001c0d0800c0b1014900302200d2520000c0701c0603401c10300c00103010b8140b0400310002c0e5011500d001514200810070010b0005554051000902046045c0070500407450320100d07c1c0500810810000350500a40e15018170b08249580007001c0c000c0c519003482858080066003952000950f401400b040c000e41d4080380520030010000341103084002ca12141803009030301255010900d1050442e0809502114040298001c0c400c3d244214030b400c1001440d100107000751a03446d60042e4a0031001609900d0b42c4020b4040b954044600b070004206201c00a283d0310341507000760050707641d0300065241c54452011541c00750101c85051040504500e400240d0000301c0c1c138190781203072401d400008941031541c1c0c5103000d40d0715850114000800e1550340000e075580a106c105004642c0411252007182e4500103501710141c02401045031800d003800a428007018644c1c1c00c41c15203500040030300ca500702c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 67456045 1250 67454795 67454797
    0x1202070c0b04060905010c080405010e01050c0616080a0603030e240406030504030e1203090f190618090e030d02090a09020d0b0907090803070201030b0315071101050108070b0403020d020a0506 84
    0x14401c0004046000e200280e400350114002e49001e0800072920f4825481c0d202c0507001d5031040c0c60400459001c030000b03070b900c99021703101d00d49003040c125011400c01d990311404c0c0c001c1c500b500800103116000002c0c176001e07880c01540100c03070f0103481d61840b4215440c1440300080150901807002c3d1106130440d0b03404958000240010401603a0020b00c6042a1030000c20290b013000400744a0f1168000700d400700c06003c004c862102c4000c64080c42d0800d00e00d404148024000d0f4070411181d01e8440c800141c098010902c201981245119240c41e140c4864421003102e00c201802c030001e0380b060080b0b150226040d03008044020300100b511914a564182c0c80003664099000010b00130740f100c1600103103050005005800291034103080c01c040d810035120741d07901e010b400401307410561102c022070203a84007840510303030030141c1e04c500c45d90504d410000500305124010200c3d410b50b2a200c00040e04000124030780e02503981c6e900c6191300d45441d54080094180081105030707030180e5005000990740d44ca0720 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 67457295 1250 67456045 67456049
    0x1c0b060f070b01081908180a03050105010803090102010f0c021504050a0507060c1e03080a1a04180507090504050a0204021c0c0e100c020906090405030c0105040308010509160f1202070c 81
    0x840b10105605040304c0da4202250042e0801c1c2d101400750580e0001203d81c4243c42c0105000f90119001c81c0c00000002c501e4aa50b034809400c5528000000c07941090100080c82e8410302038000b4402da46400c0c09440403502c010080c4030041c2c001c11080207102038805a069082400707031085400c504500c2e210b007800d103012a0300c81e1011500c1d1032001d20402480708c0e2410078041c0d504511407101800c41d24050681c10004040900f03056075051221171641004480030101400980100243d4104400c4900c0e03681241b03005681c0e81c0710f402000140c00c0c13000e020b110f00c51944600940101e60080e82800044d40205010b8400c5082c900c0b410316604449115035504005c00340d458004400d61081402955047d038070007101007000c500c40d444003503101c01d025944c01a0301a541c100c2c01340e4907030801c9411405542000102942490244410305601520003030503140215030001039500c0344090300200000513207412000c1120010119907050040c500805900c8101401601c2c1c4030382a581c07070b07007036401030303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 67458545 1250 67457295 67457303
    0xa1b080a091a071109090f010e061b160605070516242a0203040509040b01050a05010e010f0305100519170604020a1206020d020d0504060e031c0b060f07 67
    0x44070200000c402c1e050640c03a640030b8240d581ca00e08a2651120b890840f0f0b0000c1e0305029542c8007011808040040114603400c40a91000f00300000100c60301c0760f180c800507507003110368100c013010040c18501c1c21000c03240e4140c4840c00f5040e1041d02659104060310005141c03109100061040e10b4030328059111040314a485032450300c0252103006104280d416408413050140c40c80d00107110303070242451818045101201200009441d01041c08034910720a540245400c48201010b00c010000c00e101410b040c0e4004448860185440750011140244045a11b90000e07102c003034202c10190007a40910b81010703219650b04006030325440450806072065441c02501042181e0030004c10307000403242d803181c507600f0024000d181020340008080300c095010304480c4201c0103c0c10000c002e00c84c0e0407500d0360750085070155111030f42210220000c00c030440741500c440d0b0030704800406000011040303070510100d0802c1c0903010120303581220010100c444c425500040c0c204907403101d49001401424416100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 67459795 1250 67458545 67458557
    0x209061801030e06061809030706150305010b060a09060509030a0605070509030c0a030f03050315090a061806230406081504030f0c0b010b09030c040606030b04060f08030a1b080a 78
    0x118200040c02c43d8404010107070305800c11028080e6036942d01340e0410b01ca900d16092196180c41c2e804e8914214490490300910003031030585644000811506c000040300c0c01a40208498402d080900c5154030480c0154400202500010f00c10b00d40900050400c00d100602160007485990b034412040700e40990301400450404030302204186010041e8103540c031003c0d0381e5801c109203555198500c040e81d1040041c140003010000410440705e0340c07402089008020020f408c0b60504040301d90040c9124080c00040c882c9100e40010305030480d0246000300d070141d0349424294054955201154000d00d0060b0358020340b25080080c40200030000042034483c040d41c0341040782401e140150030700e00d200003164180441c84074040c020130030180c0c1c001d04482003009110364801011000a04000f642c030101ca130302528080000c10403d07455480f41496a200703407070030171449451750189154610701d841284c12030b5104002c2c0b40d070303107510a4550203182500c45520b0300d00d22a9030342d40e4503101d811201d040c50028030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 67461045 1250 67459795 67459837
    0x503130801050a060b0708090108072d0f0203030f07030c02010b030a0c05030c10021002030a0e0f01060602010e01090203070312030b0d080307080604020a02030d1a030f033004030e0103020906 84
    0x80c3c648503d400a20b07072401d61501d8203159070760f044018028151101d05000b102d03800105c165008031405000b1076109245401158040100c10781112486240380000850246402004a000000b100d010715400b01e904042d5680c0c000d0101c02600010b07202400f10f54a0728040c06c00d50f2810006400550722608014190604000030b1510340700c0d89282e254450600103101070441034000c20500c40f0941809805a600e944040402c000351042040c401e66903c200c800c1003080c920b0650010043c0c505541c000c0c008140068a12404c0c1c5d080f0550107589508400c400700300151041030030f681281d9150401060562034007000804d000c081074020b0700da6100001c100400182d1000003a03a008104403811030410030b400300025503e00900d4804141070b40c0e03641075900e00c13a50340d0051808141009040703801029100c061340f52690010903a16010198007210407400140c00d4070498014030801c0f0034040d45560f1034400700e40301d5184240d020706240e800c02c4003a80a444a0700140f00c00302c11040d170b90082e01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 67462295 1250 67461045 67461061
    0x60605040504150303170a1b050c0706080601140c0c03010501030807030809030a080c0310090c0903020a0f24030b0a0e06100e1e010e030a1109090d0f0c050313080105 73
    0x90040d0503101c4074030720f1030700c05000080d0418844c160096140ca4580244e990b1005070000406c0c1101101841c2c02c0311042c000203046c0d21a00412200f4115419140d0a5990754401c0e6600d8900782c2d00d482c08130ba4010b8034400c00d60840d6010706840300e031510440351000c0303084000c1381c00c4800070703001a0b901c60b8001442c07100713064100c00740c40c0c0c03c0b461850003107242c0103166600500c0c001001d030925030b0b00c280020100e58202515482100901110101001404030481024141101c103200881c0038070307410760002944134004030341c1c10102c2c0d120401c0051100104850303010107480c141d01728401d01d65507103101034064450704e5500010300890315141900341070210402078919400c130484030030020b02002103820340e19a0724400c41d06c0300c100c1e280f03160343c240001c0c0180ea1582550b4101d5400d48605030340481444520496140c00d500196014070b910340310b008050740c44251034100580443c885280e803070150b5200e20701061100d03000c1d800740e0f03040014075001480210000e62103210f540e03445005121050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 67463545 1250 67462295 67462301
    0x907050a06050a021c0201021306030f2702060a090b1314060310050f0a0306090507060311030405030301030b131a01090c030204050102060f060d050a0c06020d080403080f04080c01060605040504 85
    0x2920755410540c0c01c10407580002555400005c10201440d111010901078141c002d405940c002d02c160014001d00e10b484a10041c01005803002c46c854241c2028a40a01a00340d0f0580000302115580b901e084900c0070303000d000c2e80d0307070141628004000707a12100003100d94480b8054441507100c01c0345400c50500c1c24045200180710318003c00c2c89500c1c06c1041c0710003901402400c1d400c030740c004c0e1148104442d0000028109030196400a0202824445030408100c0003140c0102a5585a1010800c1a80c0c00c605d10034640001c41e0b004100da402040103101040b29030f03d40540c0145250f4210300d48400e0341e03841c0130f0340401d09040051551070a01c01448a00754034090103a26107118541103041a01c0e1400003580e4040151a8400ea4003030038000c552941c80e650340c03101d00c039600041110200005840d15200d0709045100740401401183d8420804a00ca800f4040c043e94045c1d45044076038849503030f803070840d000180c400c4808200400001100a00a0184c400200280d446440e1118544000d00c810303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 67464795 1250 67463545 67463549
    0x606060e0609010309050c101112120a0f0204090905030901080609091b040e030406051c0605060a052802011e090503030117030c031c0b0409150f140907050a 69
    0x28420030000140040e240c000c20350700020001d18010821600600b041414000d1010030340c0d81100480f0307501c451454000040c1580342a10a0484a01c01212211619603015030a10020301038039074404034040380a5504901032807403c114005281a950303070081002c0b00e10340c0c2000c50b450b070400700351600250b8110f290103500c003506846180340351401d050b05507250581c0c42409400000c031412249003036200d550200b041100b904c1c0460340e469483e1000a0b005402078040c80360310081441084102c40158042e44045841c06880c032810529450f005450703907040b0b908485030048602a81035140114440350202d03800c0b843d000014504d071801e864100f01d403046d00030754840b14102040880000e030300008407411102030315034007014098500ca005040d44240092881e03e840041910302038283e91401d550040f0172240d43c00c000d801920814001511000071002c0d1100d5600c4007401840c07861900301e5000c42e4102400001c080b0391600111205900548100d4969440850144a6030074440c06c1400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 67466045 1250 67464795 67464797
    0xf01060e1e070f0309050715030225051c17010f08100207080412051203010602031306020a0f060c11060a020405010f09030c0b070305040801020c0c010201060b12130c0e04060207060606 81
    0xe400e1404000c050316099509409a0130103585010840600c2010b100f1403000e0403901c80070040948580d10004c010b504424515002c04500e413503505100300c0702c1c0d560000802e901034080c140b074454401d0b00b500400d22011000c000d0013500c0a2924a0504904040d07000c1e1519458541d08141030041003403608d200f10342c44014003881000b42d440411910390645044521b058220b200d42165482e00500700f00034050340c10320b860310200001c40d009401001034182c0d0448005420005903640d01d080341e407552640006414010b40309109004500c0310380080c41540c2d05814034400c142040314001d403402d00203c440d050025804542407215607440b91240d52442e68901c0c0143c481400c1d42c607001e0ba0350304240305a150742e41000400c4c404150040090b82d00070321441000319216400e11840c030341c8404034014418015480c0c1040851229018010b6a004c400c5040481549a031746000d01c0c107608402d000299a650084400064241082540c86206a11401001d601c91100c0d103410026a402d54202d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 67467295 1250 67466045 67466101
    0x70e041e0501050a06090512010b0616110105120411040e03120a05011d0f0a0b0a060201091407081015080609070e0f01150302160b100816080a12020f01060e 69
    0x405c43d4000c1074403060701e400f2100b103004c034400110414010072041c032000c1c0d0400400316134002103c00581e02280e0719802085404042051b40c00110303a20b00c101c000007030130118001d0103d00840d06091400c82d480001420025001404603216440c42c0c001030041010190207800b048400c0c501c0d8025940140280b44000049034007200030740019400050075502c9800018002400000058201c0716804401a0216003c0f80d201c1c2c400901820329a181174803c0803000008070100c1ea0009a028100c40990028040c081300b096005006000445a04400900d82440200f0010b006000b160300402c034800040c00018901001041a0fa600610411a0700220740042006c00d542a0696403d4021803030016903505003070b14030342d0681051000242006a114080001c000e01007402c45041d0b5610108480390800419445040483c09004540680e0072184002001440c0480c14400d0354621740140d0769011120401c8900b10b60440e40076500da4506030051100441c40041d0610852641d02102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 67468545 1250 67467295 67467299
    0xc0f0307050c01050d09060f091208060105031303120c050301170102040b030103060c0c1a09010f0905150402030f0f01091a07020604030e030307020a090e010506100801050603070e041e0501050a 85
    0x142d202c10150070800d05010f800251002e40d80b1a5602c481d10281c7d1000c3c00f000b848000c01102d030001c1481c039100f12200c0d00e0b0390f001c5480b101d018142003440343d0300581d107440c03959440182c070801c5c100b100202202440803840740141222241d0044030340810640d540d81e07441350b241c060004404451001e596019034810402072082000100031a81580d4002c04003040842207480100d03560049284064100758070a02d040c0301c20303000c03a12018045d5809000030b00c108480030242004583c0347d04001491680044e5107540c00d503142031005a0300a0006007516000d8101505803410070103943c2007100d40d130355034000b103100704503055011a40145243c5a40055480c02c4400655620f801400240602111103050030081d5020022039040550142c2040303401507403240038001601d040d849000140d400c0000060072410038412400381c101280d0ba450000364a40410302c0207030351002e8412001c0001d10078900103d030702c941c09910740c0f0300c1b40c0459a16001c0d4101d5240000c803071041c4c00151080a031100e003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 67469795 1250 67468545 67468553
    0x10f08070605130902070302010b0102210405040b0301020f030103050f060a110d0f020c030d02030f09030304020102060412230304030807030b01020705130603021503090f01020301180e0c030f030c0f0307 89
    0x512003614500c2c14030703a5940b002c403590f410010500b0740c0116030040c0000303400e004166040d0000c0c5002a020303002c980c4900300310b2280c1ca02582040300b6501d048242844204407514040e0480ca5034410042e00052500781d580e00f46c040d066109130800e403a268810000c45070012410840c00c0d0303119070500d904225800c11030041e00e840b48035240d007031240d02d0b403155001d82000005504071081c008103001100d50340e80ca51140c0304041d400445010102c2907a10700060078000000c03080b60b21450b816800f401c110381d00da907103114101d00446489030800c445103600282e03825000c80d44000242e6850030301d5850345020301d8000d094403401068030041505001035900b0590f000500c40c010340344102d032492448440d50340324400a0001d40d001070b41c4501610030300d48403006c540740190300595804081d2545076081140c4c5074241c2c0f2082c1300d02030801040d4000b0038062042c1d9440040e1101c8400b0646100c0075080c030000e840c040642c054443d06c1c3c3c00001e00303140104410058080a00c40002c003450404a25850b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 67471045 1250 67469795 67469803
    0x140a0b09150106031e023702030f0a090503030d0f0b0a14060901020a050d08100b04050108040b04050f0d05030a0c030915051015050405010305130b0c0f09090406090605010f08 77
    0x10941d001c1c035440d50798a45e42c0d0005a0140020394a078030740c0c11074680744800f1001040303400ca0329128561400e50f074080c2036500340c4214100d2803503549800940ca041500114a000b42e40183c0b55402040a203d50110381070f50184010f2450807503041000c02d000c100200f600e0100c4a100f002d5a1203651a0070003000102c4680c1480074030900c04403900743d151494480188d080604095004140e4010143ea51030308035004984a4010611510240c411980b41c4064941c00d2049025640c0801c0f281400034001072000d200e1264003030b204130217a5403000302e030965284c5000361203100e00d03000c520b010007007003208011032140d4001170f441450180045825074607032224446000c105222255150000100e1088480f803041c802407a004000810780010b0040042c82504a4090310b0b0009081501080c0000340f01009076168a4100c6c0e0700c59400c1d110050b1513401a400001c062210310303000c1c0075184142d0340307150300684228004c003c08902d0000a03d0180d0807504141c002986000c0074440c2807140080000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 67472295 1250 67471045 67471049
    0xc1e2209151e051506040f150c2f060c01091403130b0703020f0607080f0709050f010c021c03030905070909080304120201090c180609020a0c031407140a0b091501 71
    0x42000a242d40718004c076407504c003407960005900420005000186501d40946172012240418050103ca0380410801c54145450940240c0b0710071a4801a50302c9004640b018401c107030845a002c0000070744d080105d0500c0c1c003c040c0e40c101a940d1107001d00140180f00c100101040442c101551500003542c0301c900380c0a8040c044c007083c146020a864003014000c000c8004d6005142003151410300d03011070010300302441140d04040740100d1901145015001c2e59002d01942c000801c0902c100f03c00d00011104001c07900d005980c44411819030042e101d5044041000c0c1c140241d4001c40c888030f0505200e440e08034143c0c0200402071504107010045403200e0103481d00725900508a003542425040124050b229050020386144460800042c0301c0440c01c210b0120040c0f001e10138810706d60390b80040030490250b06078400c0400c0c0c5841203003000a200705001c0388144146c003c0c0e142040c085843d80001c440c0c100004840541c40501c40c07100f441003500e074140e804030b95107009020510301503210f070031305402c18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 67473545 1250 67472295 67472351
    0x6030c0d0305130b07080a02010b0618062b061706041a040f0203060a0e0c0406050a06210c0323010b07080d0e0f0102090a05030c1e220915 61
    0x401c0401e0031040c5603080c1e200a0034007084d01a01d42c045403d085500c1c0c1d2003800d8090156282c10f6074280d0f00d08190060712940b0000d2041071110986000c01c1c444181d00c8202c508091007203c0c00a005000d003025030004400f46030080015850f03040454548615000c04881c041561140c03041100040314601e41015807040880b0b40803554941d40b81c2640709c824403460003035040c000c07801009155405640f01c0190748010100315540881c8860500049550740c0c0107003070700003442903070074056a8080d1200051024524400103454070382030303006008481c12071107840000394891400750348510315602c481400c09660840c03600554900580040c03948101e500050080c84085075590040d07a05600ca40c003c00314641c255400c4010800c043c60013580302c2c80c1202c3c4659001c3c1d0740422682000101b03034800c0380c070140c840024041d4854036041805502c508070303039016555000c040912844542c0594800e154414042854051031616052610a150300242e0322480c20300100000e14003810560b40720818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 67474795 1250 67473545 67473547
    0x30903030a0b010c0503030406050a0f05090d08130506130204050f150f15070b0103140a0b0c03150303040b030702100513061a04020f09310b0109030f0501020306040506030c0d0305 79
    0x2901c0300682d8a8130601e1000303481808007204110510015420903482104400820880c030001080c02004407041510800d030183d0114802040450182031815000032030b001401540303013240ea568501e004400c513070340712180303001e845a0402c40c1030a00904d5044030001203400c11134980800940c41d20075008200501c918004801114503480b034658032805a442407050301d99420300707414512850b220038441180d030342c90f0700707a28104500408180c0c1408280d001d10190710315100c0030000001c90b0406406090034900c804250880703a030381000204010702c441070100c0c0d06ca15003580047d06190001002e60246807c140c104014554a2034030300c0c9902d94405000224542108407180d1030b94402414150058030009500d484000d05102902011408540c2c03078a456100000d024038801e0051501c82c03c030201c0703544003400c21406400507101c0c0101031400c03160142e0b070b0741c031100c0001c80169004d60746650700005010003801c00d4001d032540404141d00170441c1d00c2500001c0317104030f1040c410240030420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 67476045 1250 67474795 67474811
    0x60f040303110c0105060a0602010204180905010f022704050c0901121415090c070807020d0303090b070908010c0807091401020a02060a080603060f0606090108060112050a0606020d05030903030a 85
    0x101079407040c881000c058800d2a10350f03802d18001402080c00362a80c620402a00070000780144c0705008480030385040300304640e44c01841c40900c00213410016800c807090f5494035280b0310405603a00c05820a40b1012580361507114030211500c4000d040c0030803560285d42000104051041070308211000b8000a20307107021742030040c06202c001080700c1580d440c440c61000342030103003071007038820000040d480480d40c0507035940701c1c0e4100492a1149480c014007802d010300410016290440c0e0283c40311b0301070f05010423084007942e9280702c811400c03a03020010414400060104503000d06c01c810710700096043c0700d030140c2401c1c48050108074052003030120300001020350121030791080c42a044080c0c1d018200741c0d1102082007003c1d00b54102215043d0203071003a4000030340c0e2005500012400b0f0340014040c82d1400c8000ca0045480a500508650500c50a182c80f9403842c003140c444e55200c0c8210100001d44d4a0420f8002401e245070748120004201c02031040c0406182c0c003108a0750814030301000010095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 67477295 1250 67476045 67476047
    0xf0a0507020d02120607030f0e0c01050906040b071a07050702090c09010219060e0f19060506211609020a020601140f09090708010507050a0518120106080a1101020f060f0403 76
    0x3802c240d80250000b84d51207009469240019006010740030589044c0520060000040100c07012040003030440d501100343c216082d40031710000c010070000a48000d190944516403410f40d584070040465001c54980704c0c0c0c0c1280a11108610740240c2607150203032801d45150001411600c0c0030b400d030201c81d440040c0c2c40e006a8002c020035034942c125600d000840300c0341810030303c3c0200024803d0110714000c1082000c1c1100700400d0b03180f0001100c80d2032081e50002921100000e00b0300074001038020294000c0c2104e466803000650075101c4078080200342c0106842d10701040c503840e6510900205006100d0450001c4c0c001c100c09054880206044011a030b0300030005098040140702036400c44000024441641c4000c2100000d80b01c0140080c001034845460882d568442c00303020b40001602400340301103000c000319031103452030002816450b4020140346010708480140d07208030000c1c0d015010b50f4040000c8204c40c2c4400507000d0020b0403403070000844031a1140002004000b0205007903000034101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 67478545 1250 67477295 67477309
    0x6060315120109050c131401060c08040b190207140a0306050402040b04140106020c01020a03120b190603060f0b0306030a08030c0d02030403030c17041101030207061b02030304170f0a050702 83
    0x100000000c3c4400c107041c0c00c003640c45410140031385000d0414003210030f0401d01c660003541b403810800d9031006010382c40c00d2412140707540c0d424000c40f83e840e010080000d1039584480a000518000701c50a08040107403540686855000d0f80148200400e004066280359500c9403460203d9400000c0801c0c1e503515440001d000301003c0420303a03441841c1c802c01c44800110b02c11988d050324616000c40b140035000400581c2e90f1200b180300100000d110505010000206030040c03030364a80c01a040f0f801d004100d0301c1040032100c264000e03400181d5950300802a02180e180c1c080004c0440860181c03071802c2c92400709844400741c11003d8500728000011510318031852080340ca0400401104546074185840c00602800c11407a00000040700030074001401ca00c29000310780107990000101007684600750066000c2d400c0b1170b201761100d83d510301070040a039844050170740005016501943d503030b00c0d2a10b00380c0020002240101005907082c80019103030040d0508507284a040b0b800c100e40c480e41d03944001004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 67479795 1250 67478545 67478569
    0x80c2101060605091003060806060609010e0907021c090f060f05040b030408030105090106020d020a12090306050115110a05120f0c0d03140c070c0315020403170c0706050306060315 79
    0x4590300e0060300050a40d070040180410342000c498090241c00540c85c2201607544030700805240303811150105600f03140c807500800e0096010304100d1003001c070810000c3c0c2000400c881c1000580c00c000f0894000301d01080d00d400c00c032482403d041c04000d08144402000450314041c040520400c1d0241c010582e0003481654000c0c498059207a940e840c25180500981d0000e2003114002c815400001c500706001091540c000c49196004100704041c40c0c8070140b00c006000d00c0f04083c84502031010011070303214010039000c3d210340586500d03d5029824010580e0810b030351a54502d03084072103210005540456005079007445883e65a484004412112441c2d2040c40c400001620070440404861500750308045156200c8155143d115550403880702c3c213511403010f008081960310072003407001a80000c907881c130041f00b5207030060600d600c07039a6042420308080074684d0f0003080411200c90b50101008050090156450030904505100c1e020a0b00ba000c06007a130140f80480d4141031a01b034481c4035500704 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 67481045 1250 67479795 67479859
    0x4030e030f0109060605040903120515040c030b0306070c021302130f03050f161503050a020706020408150105010c0b0a050402190b0409060e04110d03030b150306100306080c 76
    0x1520780c586006a00800c208401103407014140440005d0f21b16184c821340c007080d0b4041e111041d85040c885c8126000300b41c01400d0007140200d1094a9105840302c1c800c03c4801d28a503140001d041403041c041501d0010010885000c01840c050703101c0068030740f0803040031001c11300f01c2c0258880412980003a44c098041e0003142c102058001c0c00014450005150510340700180c055803c2a0710145955600f03080f54044c40403814460032201d0310240c0710f41d200da0303032040841c0401428040b15036204400d0341d00ca68002643d95201803c10041e10b03000c0d1315820300500c8242041c0b8840c00c0c0030b030380b40c800360303140140000c00150340c0d8000541591144241e040c0051000c81201140d1a29000c45100707541142c0580c1c51640d04d1b0040210b100c444c0b806900c1d01440d044031180c10158800401c220541303020b210103d08140d100c2034454601e41311a02d04a61040103280d01c140c6915148061001040f1a120f200d41003504100e4100480c48000c80c07074104101c0300b941c280c03042c00c50401d11182c181c1c10407680d100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 67482295 1250 67481045 67481053
    0x30905060c07060b03071a07020a03020a0b040e01080d020615030307050a03090f14060d050613050a02090127060f020f030c06070215100b091516022d040504030e03 72
    0x84020650010b00340a485070404002000310702c000d26980324032034083c0550840007039045c0700b0110380c40c602030214a0b10080c0404841501c940c0880e0807045c150340105000c171008101840150011211280034112190040c00d00b20100c501c02035860202800f04085c00c81207100c07500310303600c0030b0080b41c130415001400c031807946185140051003200700d0322443c60905141040802c502c0081c100302040d01c1402030103107040100031480704004000143c92940e1261056209660038031043c0165840340303001c10001611521b280c40050080142c0b8804440142140203000c940c03201c1d032082d040252a200d16201041d441c40c400203030720f0600746042101d083d100201c3e20110a40d000242c6c14410001942559807508030b20f0041d000c5058165041e60803003c10400c14803e15441d43c001c2d086180e00100011100108080e440400754415a4021400074280550307609500703014040030400198004c0c085882da400241403140989107403803052040c2d4a50001ca41450b1203861044130b0340000500b51 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 67483545 1250 67482295 67482301
    0x515030a090618050f21120702010b0a03050307050c120318040b12061902030403051207091203260903091504030b0108030409060e06151303080d060306050f010b120703090506 77
    0x21790f9600620380080c1a0301c43d880300b240001031141c8401030325940380c00546040001d011007000032543c0c000d12180031596208114407040e075807208035000039806400a1682e440c82d504125081c1a52101c0f860b00544208885480d881c400108490001149059910b030002034400040c01030000001c81541c030000d180000301c2d0700c20001c14654051900c52080c80700c141c40ca20b80c42000d9010440b00500421414050345c120400c14208942d072007001c038940480c40540740c04001a1511924806400049194400724140f80e5941c26407024060700050781c00c0245401020300e40d0b01d200e4011201d0149400404800340090300c4025100a1940311a8044040da1500340031076494200c1c0c403441e0310140c18000001070044c0d442c0e5209008a00140215920300700b00c0421801e99800b049405094080e43d100000101d8903840107841180b0035640c02040040c6181004030548138040c1c65060702040c40d0300100320440c1100101c075100074101840d0b1109548040d0b0a40003801d01d5500641a8041c190030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 67484795 1250 67483545 67483553
    0x30c0903150b13050901020c061608010e04030e030d0807020c040e03030a09080c0703050d18060f110312100f0f1811070c03060504120206040b0c0d0b0a0b12010515030a090618 77
    0xd403082c040388c24101c5d50b141e590450104200310100701d0036004281c41400601058143e02e41c201d0f03005000c1d04016480825400102e8545843c0d40c0700140041d44a44c00d01030031359410300080745042805c44040c031000e0407413400c2680700c0c8030142c200d021071940c1c0d813944d01c104650041500c00b1401240142d44001b9544d040050b2500303424000040000c00855601d81101190342e1914261030180d5550241b1400184058a01d41100c1d80801181d200034881c1d05020784050119602c1604040c480000c261718040000050b21420f400c44504480c042c1010303c0358500b211214102003d8950002c18503030b402c2c0300360617103d120b41c3e44050072243e10000c001c400e100c8103822560007941b049100111090715068203c3c1c0351101510002d1062402d0801319140c1c0043d03201500d4030820701200041c00240c0d400c0001c42c104d00f00d034030081c44440c010420445842808801034014501a40c41304049442c1e510340c3d113424440104224050781e500c095204c00d2004507481602148600302030340d4140620b50070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 67486045 1250 67484795 67484797
    0x11404110f0309070501080f040b04030c060c030c02160b0f0306010e0307080a170405030303130804050307060c05070902160609080409020414030f1207060e0c1906030c0903150b1305090102 83
    0x20b1081c80a2164090000c0e0321b510403222544188155017225280c0d03115503480c0190154050b20980c200003003225410301103a003502c6601848901500c001aa0b1140c9c5800642041d640c4011404200d505680802c0142203000856801c105150078645d52642c41000507900200145d00031501481030560100c1d03080c2c030001302e2542d05400b8041130303010cd20400c09801e50612807070068603056081800030a0300c004410b000c0d4041c0c1d0307100c3c100e19400e040e02d90000c285004515400000050b89801810741880800d120090250168070b07401d5190052081c8202e07541c04072520014440c3d0383e6a4088402d00414030180c0d8040d00741e03c1d909540e11503880c1c08020300c1980d0014054828003403400e0041101c0400101da013101721401d0b01c41c0d8180070594640d000180048803084029000b070003110b20b2a6680d030b00c040300c00f010740410030300c0d00e85007080070050072560701d00c0004044c0500030702c051002c1444030004801954a25402041245880c4046154901e0092400c0c0100382003c003441203401041d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 67487295 1250 67486045 67486051
    0x7140304140604060c0303020313050303100614090907080907092a11190602040503030304080703022406040f0e01090c06020c0f090408090a120c03020901060503040506011404110f03 80
    0x20702150030030101e0081150340c0c0700d18401d40011443da14031500000707000740c02640d4010214000e046000340070740c072800c0c21544100d96102ca05c401040c0f050000760f4100006c1808140801c10150070200408082640000d0242c03681040c44064000507048500030850070002c1c0034500c806100e096074070030f40041c00d07405408006002080c801c014034400c034030034600102e14140070f000808050b80c0300f44102c10350040c10241521003e03000c01011809132002c03c019801140b0030858969180c680e414000d0618103a100044910746140011340c18085039001d0351340c2c00c000300b01c40004448080c02c05450091138040111410365003003070120020300200c42c000070101c4890780c080e80d8100100c54104803c08142d501c04075403218800700410086074507071014141003030000d0800a1803544490703c20f10040c80403581250f103c030a4200c10700440c1003c0d81d281c4d004200c142400e60a500701a40d50342e49400050051502c3c11404101c41e444682d07072604800414900c00c09495980c1a22902501c4141c3c422 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 67488545 1250 67487295 67487309
    0x21c0b0610020319030b0d0501020304080403030e0d081207031d070f06050c2d060a06051302040506030f06030c0a0b03010906060e06070303020d0207061404030f0f021b0607140304 79
    0x241c0280545070001c01190912a6580074540100d0306408080d0010301e80c08510a400c4000480c3d80800a20700340700031401140070700364040d151841d40c03400800c0700f5840f00c03510380152080c0301614000385000081d02c001001104905c40950368100c4100c0091025004041002d141c2c8020522609404915441951440c020400e8069203d000030740e203500c1040b04103502717540071184076803840c030f041c51401104581ca180c080b6456481c0102141c5807903030079a03030300008507070710b94041109152090900c00d0290841c081581810702d00000030b0203034000108801000300c44200050416641400001002c10006007150451510790780001c1003500240520144180340150101d01903005171108014468010056881c0c400a40c2e8214060b401421051345050303002d2054034000313555030180795200030505030000c0740d030300c0d250030014581410a010b0405202c004440442c4280d40070074a140894113030640440f0b280d13064404280a8850000701030b000c0e107a682180742c0340d0784020005100320703070030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 67489795 1250 67488545 67488559
    0x3050603010203011203110a080a09180513020d0c05060307170a09020a030201050f0c0307060c02011a130b0105041226120a0509030c0d0305091b060d0207021c0b06 72
    0x1824003498202d210a00032090519155103c07400040c0c82082d00010310003240058440c0300710316680e042c2c40c0c1e4000220f1800810080c0306d0610124615421480034102e22440c00d106074100022005517580040341c02a000da40781111402c180503140070004000c000150200350b582c6840c0c40020042c0d113019aa10100042c82804183c4ea5031590003040310041c1c0003840b80303840502e1a07006580c10b0b80002000032205078280700c8500c902d4000c0c00600f040324040c1c0c2022130703a61484a4002e003114003002c044c16489200500b288410b0303c0b118081e00380c4a0080000090b540b0300c0c0c00058071035000b290700807010156441c0603d0200650201c4803403000122610b4150201c0048a1011003401900c24143c04030170382400103400f9514540249400c6503240342901c0c0b501c144451083e0030004034600400c042602d400c10b104020f20f003003000d505071111a20030b603090990b05070002041072060304000d0740b0315070300450781c8800c2d5969851419034500b0032011403544203c407440c06034140c86d01103942c0c85c42022 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 67491045 1250 67489795 67489801
    0xc0f05130603020f04020703020712030203030423072105100b12151906121407060c0203030f0306010924030b01031a12070b07031107080d020604110f0409060c0305 72
    0x12040c00703880309495004014262500300201808001d4015480c281d046100312400010808907850726251414001d9000e1940e030b02d0941004507030307020543d460203140e0600a400400b01c2c80042011000c0c0c0d001c0143c02d6014220000010705a250245c401070302c18052100181e100c60856030050040d000c0543e0007440140f0419509a156168400c02c20410903c01001880b07034459042c1c98454007508450006c1d0b0039807601441c43d402540208200c4515004810b41007841301e0401c0001d00606262500d1440060f680c1c3c0441d469000300c1809240101010010a002c0d0703004d1400400606682e01c81800007844904000d042090134100c0304020030b14213070320301c0580d500c2409510500d600344a4001c080080e19000d020010803591031581d4140981c284c04a5064180700051030003500070703601c85041c0e88010341c0301410141c0d654090300c110380c00500341c0210260045042c0c6e900c5504500340b04500d154001c082040d07020b80d03559842d0f00902d003918640810001e43e01c1211051070302d079010400c1d96 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 67492295 1250 67491045 67491079
    0xd0804180207021207061d1f0302070b0603070f0509040809061603080f101403010e0313060201050603060106140a0c0c0e010e060d200d020402040f1509030809090a02070c0f05 77
    0xc1c08038000c1c1c0d4005a180c480c0d140342000d05c110011141c0350050703d1440c0c0d48d0925181d610620500208407400a07030000358000130320544031805900010200c000d807024519014135183c0f2021144104c5000e841c01c40000340600c092081510315244002c0c11850755440b4030b8501030700070f20034008124040751070003001c0303039601c0c8a45482520400c54800c60004003420281040d5050004000d103651542d00c4d0356540401240c140003601d003000c942282030840c942010700103403d562009260394025400b201c01000300c1940300b600062842e04c40080303030b5540c03040da8108403400c3e405110701406400c0c0518000909800d903c08641c1200c803483d8940311203890f008100f103106072021501a00c0d0310200c103810b61028a5040000b49400401840b07c0c00140b40c0741e0124040e07800a60017168207000c0c000041201e03151000fa29450710416145c5840b403681181d941c50f20034010010458003c1003607000003851946942c0c11203c0454011607142241c56444954412a410500400c0e01a20340000906a50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 67493545 1250 67492295 67492303
    0x60912040806060105070602090432041101051b0706090306110304050c010f0309061803020609121608040e0405160504060b031f030c0603060e1e04020d08041802070212 74
    0x368000001074031258448000444071600007a500787d071840c0d030800a002c6c20f0380e6684034860f2022030b01060850b052066400041d03074956502c0014008000c0c010802000880cbc40d180c1a01082090809544501d0710524031511f8129107902d440180c840c40c0004a810750f0080307003200440f4440e410031302c00b4421165002007036000c1640c00800300e50015541c08420741c002d5250015a0314140350000307140c1c480342c83d40307415a0403c02c811204854510040014154103108444c0e01c1012240102400c1c0e2082c0300c0f4041a2041c804d540100d191030710321100070000300000300c0d0020059a800a00729042904201e6180c20780d400c02510514030712880012241024003403c07048542c80d140141c03c50740d0351410060b0140031020100c003400507090300840020500308181c00030b800741c0d660000d1558101b0b5180c0300a42c0340500600021007103d0096402d400080d203656034032650584010388010380134a02400240910b40101c1d540c042101c80d10001d51000c0d5002d0541d80b0300840d2580c6040902030505522 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 67494795 1250 67493545 67493549
    0x1081605010914150c0a061b030c14090307030b0405010b09010f06020703060203130c030c06030c03020304170d09020301020408010b010206060414010e07111501090f0507020d0f050403020405010806091204 90
    0x14640368000140c0c801c0c0f401c0c0810313000b032000120502c2e260020300620700b400d00040f14022107009a5601a04024112100705003094802609040000e0440c1d941d02810305010410721001c03030100002d800541d514240b10035030055130301ca540384185007041d1900c01d010300a2500540e000e0400080001000c40a0b000a141102c1080d005044c0070740c1140c0380c201c06036100400c1c40c08820880600940010006247c14008601408610801c0d50a0000081c203a4880e84c940504250041c01400301295240280d80b218075010b401580c2d4413426414400c0140181d0348000c1d40c194404100020401819000213261b040309a0988025548840405c1b0440c1c1c022a0310402802484005101c48600a51100d402a00b43d04089181c4880c11440d80c0c9000d030054206039866110400411400800b4010108158a00a020302540c544201d000390b80f950b04030200ea0400a40c11141d00383c9034012400c450103540c01034000e11a40d1784a030070103a6681d0007030f21070381120f22a01c0c0035909040c06000943d02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 67496045 1250 67494795 67494809
    0x14150a140a09170a0306030213140f0c0a0c06140108010b18040b040f0201050f0c0309010e0d0f120c0c080a1106070c050f0112051302270429010816050109 68
    0xa0300c855040d11050f240c2c10618000c0c092503034075203000c00540d480c00c0b0084a100810100410489400a090410464003524405041c40184284108084920213a42100d40310340b0708140c40c40c2c058140407000d85400002400407505100010030401019040010344071030a480c115a00c411090000300d0301c079012207000d019000c1000104001610702244200400d005243c494101224800194040d40c4901c0c0004803c0d40002166120307540c104c40e100781d00400855061200c0d04203a201c07081042c0405c0001000b139845459460500d50040146d4601103030010300e8928020f440e401c3c29991119121010703a245070b8980305100580c64454101d840007980030100d005c0103032030201400f4481c080500d1460500c501c102c01c01c840c1002c68890540f1800c09040c031003405040034010701c03c0c3c11746031070000c00626403d04e010014076406000b1850304103501c4013003001d110b102000c14011900030591350302c4021045500001d081007001951f400820060801c00e0740040d0ba0f4001503444031924440c0035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 67497295 1250 67496045 67496063
    0x6050609060d0203070309051605011404060c03081f031a060409020303040b0d0f05090604210504060c05030906130f05030109020a03020103020304020f190602010e030301080a14150a140a09 83
    0x9102c8650013842d0003070b600341004907825801e5a280e42c180030080e000c02428480744003081001e580c0c800c2902c07048544110f605031503d07090101c000d04a000b031000203014421258049598042c0c8542804002e03420403190307003403698892411b00c18102003410700d1104801d045001c10510302d0144140e03507a1540c000e0045141900e01030381c0c0e00d09500034030580f1090903580c0a900038915424080c02e4800d06011014041c980b815241c018401448500802504019190f00d600507a400c40219000d0b20b07400d0614117522000d81c40c3c15407940c4a14056580c1000c000b058a848140d0008101c1050704c50800c00c1c0d84845440e40145030032208401b8001e58001c014180800143d4000c0d0700854120f80050060020346841902003520b1410080000c00281001102000580d40c28490780b825072100d007000e1881d42d4036044095a8a03404000c01031708200c080b0020070b00d159810407015180100780b000e502c0080c64580890f000a010b4448c0300c2aa11180300001181e444e0140301c2c070002e2a80c00902c2c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 67498545 1250 67497295 67497307
    0x612020f04030b0406110d0203061e010207091119080105090703090c03060b040b0a0e011805010f0509060102160603060501110d02070e150901030503030a06210615090c090302040605060906 83
    0x30843c40718040c00981c0c41659441b5034454103c0ca480c02001d501c800c1500c00350752070801d54284001d4900f0110307280b05500f02c0840d0380303c01c0c2c2e81c01b10301030003120990301010600c20000c1d0b10580451042c1440405022280e58415442940003061981254000c503140c070001d0b0b03102c0790142e00b9552480c400510000014605000244246e0310802c0c202001610018840c1ca110012079410042034100040050144004110807080481c40b803045200c0703d001403086515080083c44c4203202400b80360701c5410004000781c00c41e407007086080080958070100c109842e0340ea64000d0020041d50081d5400201c1544814400400008d18555003540d181d006000440c504441000c040c54041c11300aa08100159452403941d107480019000c0c5000d400515503e007001c9981d8411608141c3c8890204107400c0090048030164000304802180c01035404502004041ea03400c9088100b41c211400d0030745000031501000b076000f6100010749109403800c03c03071175840b03d040001c0b901030f4111031603220404000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 67499795 1250 67498545 67498553
    0x70803030c030703021803150105030c010c0f1707080412020108010f080d0810050d080301090e06101403010b100f0212030c070303020c1204060503090c093d0803040612020f0403 78
    0xb406c010076030007000b080f54070300e0000190404900050350b43c802503038100184190314040c064000000004d0074082045079459030b40e44c01419075000e018045c1c1e05854014281c5400001c01c603040d4030307408003156a41e55101c0c003509050503640b5000342c1c000b5200ea000440c8601400c2103120aa81495004002d0803ea207001112881e070020205491203200c0400014030340c0300c040800d0700c544d1103400c0440d120b60509041c4403c5601d6001e001c1c0e05540100280100c10b80458603103070035220160504200c003c0d000001c03a0140c1010924507400101c2e02005200300d90b400740340c01c40610301c00e90a0711700811241900608500054a460741441800c018140010303020368020150001300320113466441c004215440c1c183d4106501020120380001304020b0319440521051440820132a0100c03403904103d603d041a500d030306079500386c0c01d00c0480400403100c4d42002400b40242d0241d4052101240c8a50980d80c40780c000d84949800300d030169810001124550003074070035021300c084034281041d1031a16 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 67501045 1250 67499795 67499797
    0xa0503041b090501090b1f14070303140f04021309111201110301080105061306080604060e0a170a0f02151b0c06250215060402130b030405010905070803030c03070302 73
    0x182081c007401c055080000c100c1a1030203498000c0140440010304c603401c000a0100d1032010303035000c86c081e50f50301500d41800e941010000c440342c00e0140c01c40f030b218119881e06030010700c00103a24011a40518040003c4482042ca0300752046d84280c507610089013680442030213032046504003d1000203030700303625880360078a10380d04000540079400124000d42c0c01050485203502c01e811035040e0340d444404000c2039090003940d82d55071120400e81000010b140558580d150740e03001c0c00042c08240c903140441c100c40303820080103034070350f402100303803070b02208900402c2e1840d5022420050100d900200e1101c90740d4008143c40741038110400300b800155680c0c3ea404101c28102d050405403682c8140400796200c0020407034144510320a0542078541c405a400001d4000c2c1c0a11001c0119881020034504d1580051506078000c00c00341d50141c3c403000e00301000d251120f441e820480d40900c1c00f20801007403000540065001034051815a246640c0b50320280740c881c4000c94080403180f40401c0030480f1544664 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 67502295 1250 67501045 67501073
    0x10c1b0f0905040521121302010806090702030906070609080a0f0905120601181b0e1306150f0504090c080a05010b07081605010605060409020a0206070e0307050d110a0b070605010801020a050304 85
    0x7a80c4d6490640000c1c62400b0388203042d206034501f072000c0c0c0181d9085503004281344d038112404840f400a01c1c504600020f5803031003805d4120f0300030000030401204024040c0c0015001c00d500c46150f544031103010100a041d0320392142102d000441c210800a15410541c2125039059030846c05060281c0c02c01d401c0b2001001030030742c446461aaa07020030f121303501d240741c141d004400c442e95800c0d6101c091001080300d81c0791010f40090880f80351032000c000703103541c4a549040020351414008600e041c20030041e1024021580f2585040c0d040135a41c034806980411700c2d5100b001c001c002000341c1d0762224880c5009004951000b0200d203402c0100b04a92080320088043c000d119000104000b51144c000c20b0064000385e0020079801d030041209140b00d40c050190f2a0300c18540d1610241240d002d82c000703907a41d107241c41807d0095448004001c1031000c428950410740d0005000610400c1d03542100788140c0e40b00031001c0c0d4009292070008107000c101070080701c00342d04c40c540d507550a41d00c0d503444a4010302145 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 67503545 1250 67502295 67502353
    0x30a0311040302040203100311030327040e0601060905040f05040203280f0f0605061519050f0403051e1609020309030706050a06080c09011203050306010c1b0f09050405 74
    0x207100000060340d850005610070102c1003002c094440c503615007a44001440a100d502c20740041c0721103005d592489001141c0e4882d6008145416516240824024031103080c0b080c145000d8000045802c40e001400b0f0001c59200340c1c0c00704102503030742c800c1c40225801960700941c0760b04405440c007680407414010280010001034424030b01e41081d6101100d07407000d5a003c4514425408003001030104500c01c0e542d002e90182d904a546401c42c5149a00d507101e4400c0421640d801c00c0c2c410346500d480740064030306104003a000c15588544904080e80c6d240d0500d0302e800c4024102e00e0a403101d6600c00300722901c8070340045074480c0203281040400c8000e904020031400d100d100078840f40f00403900e40c0c010035005040c0f2a40015115040c850100d09220800e03003020b004072042401009641c46452110b2002c03070b05898050f440c1e80314000129140075403075001400740000d80d44e01c1d1a0a95210144004840d0310600507a0b039140d84000c070b0390550b2004c9034054042d4100e6501c0105200340071040340d04401c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 67504795 1250 67503545 67503547
    0x406180905010603090c1d0f10030b010b0405150f03010506250f051011090409030e120102031608040f15061805010312021516020a0206121512030a0311 67
    0x940451200700d5000340d100500090300e6a003580d051102d60151a0041e1441070302c902c25849100901c1820400045c01190400080c00006030300c00d0401d4040700095030b4481e03c2c001c241d59444c012600d45400c28005c20b8440d4803100300c42000300040108803243c2080f06805603003581e18110400003e5086480341004803118030248000d540800803042c4a0140b28036804000d800c21403c0240ca004410900b240c1d0542c913202950300240c03130642c00e448500008440104007041c036881d00300ca403e081d0a0041d0340190507a10940c40180341900518840c82000000d00030410040d071044440100030b582c06800103144200c1034004c17a0303001d040c149050800300d1021905d40c0e680c1d0382c03960880c10210507888980740e0711001841001442800c0c00700b0b40c889031000b40341400c0c1c0c0d00c2200c501c0706000741200c40b041041442a42e0703100d002340b000711009600141220f850b071001444000501c402180d00912130b04817610340b040149070a4418001c5008200e004504010921100381c00801d0507015071020800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 67506045 1250 67504795 67504799
    0x3010609020c030a030608010c0c02061c0504030f0f0e210c0901060c05010b040603081b07080313060e01020d0210020a0309020301060906030c090b0d020402091c0b1f0b040618 77
    0x1030350700003019540400c00046941d03a81e0010001d048400940110720140d040c0001c0d500510342c8460381c1d1101c1030301222100d81c4d480041000060183c034030424a140b06040c00d040106240e0015001620800c4940301c1405441440d001210354402d0200401d81c411405800e0104500107a8503e0742070b0040401104e5800d10388000040441d1801d03071000d80011110080d0404101080c014003407501016074007801014107555071014140205034804041d8502d480801d403204204000d0400142010f1003035139514070030100303044081d4640303000301c0010410010584286520000780c208811110f503024001c2981c4c04540080a540403540c050b04054940c403c181c00342c0e8080c0700d4440201203988000400524510b005092190998004000640350002003040b075152a54054402681103800507030b039800c0000029100780c148102c217614000215000710800c8110740340c0501864030003d034400d40c50f03c51141c1c04003544182c0100002d668043c00104507090080030081000407010400c4200a5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 67507295 1250 67506045 67506059
    0x30f0206090d080d0f02040b04032409030309060507021908090d02060c01050703051b0405010e15070b0105120d0512091509030405040b0a050907080612030a09030b0f0103020a14030106 81
    0x240401070030366003c140021200b0802007a0f22903961000405401507003000d28001100d03029024500c4060b04001140f4411060020200b010f00c2c1c034580c40850400031180c86040080050030300707080445050340b0300340200e21200d0002039801e500f0301d0b0300c0c00c000000d101c003903540307080c10b400032402103800600079000400140d480c000501460010503000203440c0c50b0104c1300130180e42021f00008d0480314a01c1e90503250885100032242a644203080003135a03070030182c0110b9030500301c08000a0a01001080040c00c2011000b20303603048520449000085420072003000e903d6046014803480402c400300681403542100c0d411003075000312000300b80c5040e01a003184082a01d00101ca108145070000036092015103000d00c030741c0c0142074080da07c2941c21401c10020a0b00000c002e0800e01c2802030140000324242c0d45e2202900b400c100100039203842e011246030181c10400305010841c2d03008500d1000801485040328058102c070b8000744000026458481030108011511a2a503055500d41101040e51 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 67508545 1250 67507295 67507309
    0x40b030f0d0810060c03050307080405100501090e0706031a0d06180b040309060503040b010e150a08030403020310050402030d050c0309060313030e040615050c03040504050a05190504030801030f020609 88
    0x848580d01c5810b100e02c0c0100c1154481c209580040c0c0511111813aa440030075404015654050700c40d0518403001d88541c100181707030024240030510014104000450b040c28980c02452403042e003a000c480c00c140c0c44400c15029180c0c00d020480e00358408504c804400d1034048684c22000c2d0140000148207c0f03160a0301c1100381041c43c1c00c1d22135501c0c80c41803008069009a61200401c0c56181003815400e142c0c6c0c1c0c00b8551041071050801408006010607d401196800700301614801000e42e17100958891803103440c1d8100307100c00d920a00503203000e4840d441c250b0084511480e4010b003d404c8150820030300351415002008500d16510040c421802603480e020002d5011ba078508031500b40c210a989401054030303030350300082d500407402c0400800c8909004000c0901c92003460034039948034091500e446103580110380c0010350003402d101c140140400c0344d030301242c0145002d000038010154840507090036190280c0740200003909030001007000c601000046101d10348028515840c0451700c02c001948 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 67509795 1250 67508545 67508563
    0x613020a030b030303010603090b010b191d10030f060911090d1a240103020a0f080606070605040c06200705090c0c0f0105070809071a09010c050d03020c010b010503040f02040b030f 79
    0x302e940c41c08240c062041c2b0a003034600402140c0348031032406000072040201074100c503c1e000240500c03006504089800d0300402548039901030315a0300c40d01b0200703200501038601c01c8020484c2505d001d001041c0d6210a0146101c04c120b01030f0b06900e030901030428040f5000e00b10034251010f17400745a070300b09090700461081d4001e95015400c0040b0031965007990350704002c504200350505204119a042841c0c000304000800360f11410711080765071744c9901103410780c0304240c001020a450401004104944107840301c003901c101359210071718480781401141e84010700010207401903020160410103460595180c40d0b121148110250801c5401c01026141407002620204265140e404001400e40e000580951141c0704000500e105490038200d040561a603008049000200040c448280c4e4001c590340210b080d440b03001c40e50303002d41114000f00250010368010019500b001d2001c170700741d8494002e0760f004982116401e0403454041d0708101c000c1c501ca080b4160580114004004151024006010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 67511045 1250 67509795 67509797
    0x10e030301080a05010506040603030c0f0c0902070501021b07030807060c02070314010905010c030b0d03032304120906032a021615080604060f0e0a0b0a03110102060f0613020a030b0303030106 84
    0x20260b010f03883d1440c2914801082c050203540b8110701040030035406000072050741e400428801c01902c0c60700b1b00385480006030300b00240c91400060008200a415801002d00914882d07030305200f8100505029120001440050488a41071081202181491384907200824850040b0346c542980c076a110700d009031004902210f80d95440d1000710500400303014404401d60320b460200f00310300b0100d00003459441d400300f000d0308066807802d4005005032040c1038007031408585449955145040c6c941488604002c140c03060024292040024142e40130740141c1c0251002400d0703103044000f140c2c1202250304080c0d640304003140f28003c01c07280340b000f02035030300d802a01646905801040400502900602c000b40c100c50055207403103010812030040b4009c40d02940d98000c0c00f8821034680340b800c4005016040e514a60100c000d00700082000500412400401401c1e02502c1030b81e42d400316251001101101c1258201040c2182106010322a5000300f00c0c0c0b98035401d000810704410404245950005d07000300d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 67512295 1250 67511045 67511053
    0x70813030b070c110a051f0e04020408160605070209013305090102010b06091f090312080114090708160203040e010b0a03060b070515130204140a2007080c010e03030108 74
    0x7800b8100741a08141c18060703502c0b0217140d242070042007421601106003030b06202d09149840c0e81612611444255000041040d92101e4903020304a480c3c403c042c1d10711080d01c1102e500028282d0150099401c440d4000740451220b80c0780100000c07035400c490081c5010280c82c81c009026803042e01134401e00d42702e40d0b03584183c1c8400882e0006030842d10300840c2648906024004101d0955903c03035425440a03103045113400b583c683e810705840d8006d8070b80006241d00a04652580c00603409130b0700c40c0c122100c05500c000e1315049413040c40391840080d0f403850001821100000d000501010b00300803140780510481346099a181110f01e9044c00030380001e2440000007411441a81d418007410000c2c104c0604414035000b016501d141e910862254010302d0200b11000140700300ca010046000c80a801800911503100b10311b1500349111012129910b41e603142000300c500355004007041c075050340550280c461500c0e00720f444031718181c1c200745194800c0c0d40d281c640c00580b801d41840694000c0405070020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 67513545 1250 67512295 67512317
    0x140f0f07030e0a0b09090a020a0e061b100908070b06060f0d050f0708010b12070e040f0b01030e0304060207050d060b10020a0302011a151e180f0d030203070813030b07 73
    0x301d2602d070690304c01c9800c40030901ca101304607503030703c04107503001100c1d000016601d10a50b201501c41c0214040d840354011004a0001e020090700d034031291400305400280da51990a501002e822188060070140102c2c409100c1c800029a03801125030f0800380c020b0013a400c02400151076446035000c140300c241c20b65201d4042c06010308003094580d800c13400500f000c590560600c0c2000150340070b00f403601e03c03403c401d440200b103450740112a01e894409024100380116a803011048010307111920b100790000e40307003201d180c2d4071480c08003da906403100d41d405008000c0c1740134200301e1010800b000c242c607081d540e030b51400f050f541c4c0d1004041e2a035100e81c0151003560b038581806801c65912030300f1341522030401c50313a003001a41c44845240025052400c4a919088441c68854400d0710480f4240d05800001441218013012a403148071110b20466551444540c9002844206a8041002809039005102c80c50019120b0000781800201078024100b51950700e45401d283da440a5504801044856120b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 67514795 1250 67513545 67513549
    0x7030c18110f0702010c1401050f01170f06060d0309080a03030e060a09020f010503091501080c1003150306020f0705031809090d170a0b040203191803140f0f07030e 72
    0x1207034410080030030030038200401c03070000c420380d0b2042040003410003207440c455a00b04442c2481c112100c14241000f00705038540003490b10f00c048000e008201802c4d02c6080071180701d560008162940c040e04d00301406c0c00d0b0b126441806500c00391100104c040c041ca07440c0125005000300305180409010382d40100741c8000031100242807203005072115200c14241482070340580c03120104040020028030780240d59079034810616050088802900107500170f6240009049580080e40024105007250b6284c03401514010030b40489200c001c2c4000c500c1440c400420210b40d242e4080c21030b408a00c2c80d1b5034a402c00710b586803070079a840010341c0c0c11001014160440300382804100564030800c03c80040c840d6020324a0701901490b100c502503007114180d174001030300c0c004d01a00510958280580299107c2c20f115041c42072480c020a8041e040a02c2c1112020030404038a400402d520380549600740552035480302800d0300d03440341c03224091b1001c0400002c410b1060107030040001030b000345d0b1050303010059201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 67516045 1250 67514795 67514801
    0x31e0f06020405091b0909150303030703050405100e060f04061506020105010e220b0703180302030c06090d1407080418020c010c0201020f0901030f0905061305060f0705070f0507030c18 81
    0x405d82c4d10344004000e81c0342d05404c901c02243e40300d450071240f40f0b029588020741c035070042c0d2030b00c05003e825000200520840680542019000b20712890684030030010b58041c540c00c40d8840c2410001c560f00c8000464511485025032982050080c60046001c1c100c10f248040c000d511a0302c0300e00181c0d542c0340100403111402000d1038028401c0e0460740c016a16200d03501032441801c500140c540300003900860b0700180079900c05044c107984040800100a19030501079100d0b00b04060900140c09071000080d000640400c0414141e00030f41c454070146684a00000e0301c58000c49022642140c0811010541c184980f42402103480700032405680e80c921008914252105003005005580c01030045103500c2c158081034a80c01c06081c6800258040c24444080c0500010b0001400f580030340810710480640352100380075a5030048003160110303141c2901100c07040300e007144c0e2200003031814800d80c0c2c000740d100c0b003420358002e01610407110519229204d44004c1e48850303101c0d00c141005c208000d480c4045d940 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 67517295 1250 67516045 67516051
    0x110a09020f0415021f020a200a061104081906020c01060b0306031b0f060906090d060b030f060f0103030c08091302040510170112050a080c03042d031e0f0602040509 72
    0x1101030102101400c1000c5d05a58144044001140d004104090f030341d80700f074490040700441010900c480403d01c40520b41c55004486003503510504080e54400040c00d60400c42d0115031040005000406065201c000c48002c501e000700d5131140c080010240b40d020034022300000d000005062a0b4034140901050300e441d540d4481120450380491040d000da81d503030f804112007800d043d200300e51b48403511000100c0c1e61080c4806180d00ca920741005c4418400d09a10228140205504a405207070210007a907560b000220b81d40e1b4240782880d001030001a1155007161490f604c54111a0b05020101d0001206181d003144000c04259021404001038981070b41c0c2c20031784580320304008442c04105032810b162000140280d40e0300c24014140b42c0100241000585146070300011025180c41c840b11202d500c82e4014403900d01002c00880c00d10b00690218004080e01e803144500441200b0320707555030056410356500c1031219010408968501141d43c02580c02013480c46440010303545e5003080200302c0c18074006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 67518545 1250 67517295 67517297
    0x170406201c030203060d05030f040306060f140415030515040506071b0609020102030c0a1104051015030e010605060a050c01060e0108070608060604030c150207080105060607110a09020f0415 83
    0x50500305650122141050715281c040d07140141ea242e40b0074010030920640094010718500c400584140c4461305900600305491003080c0502520b0364440c40f07400111400e02030381815402481440c0107600d000e0b840076000c1d607010a401d18505c0da071f80e142e080c02c02c25143c4450004840c1c002c104010848284805a03200140e400d040307401008201450540c050001e200411f00c9996007002000c0da8002c01c2941c40c3c1e5174041c41154040303900380c50424000040021640d002d20b04140c0810300140c1a12890b5090351440f82070380065180301d104c201c0181c0004024860103541c1d610b40400d280d100c42005000c2d440080d1982513a4095010b402c0c0d0031104694095120003074000018040104041500012200c6910700f00209848032800640a403285d6403009202d0240041c0018240200386010303000790b40c69400743c1c0d0b07100e942c07180340d142660300c211407060307114a0400c441e000144003100e2142c800000600010318a07a2940da8020032a401711035401840000070a0030051445262a44c0210103d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 67519795 1250 67518545 67518553
    0xd03050c010b1903030e0d0b010b0406020c04050c070206031b030c09090609040506010314011103280c091e080102030f04050d0c08040b0f07050715020c0f030303010501030917040620 80
    0x10303c0c0b584076607203420341c00000d08000004409040035a5101c0010b010b07650080704403034065030b4803245000d50790310a100744030250040d4030002c1c001c0d01c2c0601c0350368032550005d00601d103808403c0d802c101d000d6200034000b0105208400d1040d41c01c00b601000355200382500c0390000c2d5162000010031161000c0280028841c1000c4010480002d9000c1141c80c1165449915141000030b012450380c054280320599074061040030081100b0750240051840204414a43c0c0741e001e40745428070b100554001c001c0c1140419020390040003110108001e50340b12101040c41002c070203850f035129509990054031068064940e0320240801e225040c0060a081c4105061115101c0640ea80c0d10400c3e0140e403198001420000c214031880071f0000c802ca9071000c3d401401c1c0d8500c10f071070f03811000700b10075541c0060006208035041d220403406c000c2484072154800400542c02c5030718040046020b081002d0381101e00c0c042d0100c0b00c19a801c510400784c80500300f55210030960264100c181403980020300c45422181d44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 67521045 1250 67519795 67519819
    0x51507020607060507050403050105040803010611210c01020c012c070608240303031303110307230307020d0804060f2d020c030a0501061703070209070305150d03050c010b 75
    0x1d149022a503003580c1c408000b203129034444505a81500403a40064425421700007013004010040b401035041e9010398850708021a036015419580341500b9034440c07140c4101c01030b0750070f02c480c0700000b81a07a070035100d0001d441d0000b04a44103094034000010020385590003095000c4000220b0035246542c0254030080c460185810002400110050894500748c584a0300340c0300d2510503d0021255600c01504496607820220002200102c808074290700094414142200840001c0221021035402401014642c9190300c040085c14801c004840c2e100d10040100f03600507101d44003004141c0c1e000d0090a0349840c5009805412241f00391640c0c0208102008452681500c03003c170152545a5400946c1c604000040207a10f00800411050f6262090103102c0d01006415008182a40c00d40d024544050b40143d02650780c8cc060100000e40c00400c02e000148001d00c250b00240e031040c805281d0950495028003c14000030100c06e041c1e000610007c6c0d008c04414003409030351150b450a403508518030b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 67522295 1250 67521045 67521049
    0xd0c0c08030106050d0603060606020303040b010e010522020d060815090a0b1603060911070302010e030a020303071b15060509060a030803060120010c020a210915030e06040c05150702 80
    0x4401409110f00340f00000c00c010402810303a0b403200b0007450344003200304000d81d2a481d020350350382c004031011201200b4100010491030002d00c1c0c80360485d140500500c0807006150b0071741c0d00045d003880e81d0324207159092244440c11741090050000400000001e8180d01c03160164510340075074014040343d150751008500070006035003195031075070209503021004c480d02e06046044010307080c6a0700103069241000c0c840c0900600e810014508580301e600200446c0001c040b00607264045e65400a0141e0410b100054003140281e80401100c2d00b46003070314441d151159038034118100c5881144035001c1c1d460100380803504000355000d400c940c00b225041040b40c6107a4650805100007881c80d410004044001000070110300000490182120001d011400c54400c000b5503c1c1560b0a0544085001151180c070030007031800d02c101a020305584004001d810403000300b08440350942c0380410599280b02912801310203200c2d4500551044110f0608076142104000c0c0290640040203025241085144016 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 67523545 1250 67522295 67522297
    0x615170705030606040b0301021204060b040e01060e0f060d080304030c0b01050d110f031002030a05060907050a080121021207091d0a20120c040f021624020a03020d0c0c08 75
    0x28000b1500410806e454502181c003a0017008051a4800e10388401d03c0100a016001032044d04010f07541040301004d100915800d90701240b00f200d042c4044480031444698528016a90000019040741040c444681e03601d000742e401141c055001070540007000c000c02c000ca02440380180021115804840440e440c0d03030b510707817101343d04a070310640805e40c00c0c151039141400070000702501000704540301d28241d5003200143c08111031a07440382042c0d00018440c10700400596244a165075142d801c030ba030804401d000c0e0910000351100b0340c0030f0b19542d0580140c2c0d444160041d8684180c0103481e0542c030307201052041e12070030300c40303e10450031010300c9032000507000440d01030441c2c00049141c4181c0e4400c480c8005943e9000c95550020145c6000500c9144002442104205d0a81c0c0c1001b0b025000e0400104034080c1201a003441e06d0040c03000404210003d4151440540a42602400703a00281d115012a4800b00c1c20300c000c41c0d0080780c0c1038030a402610964010309800e062044900c056035a4140c3c1c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 67524795 1250 67523545 67523551
    0x10905060a120b0d0609020a090c050414040b04020315010e0303040b0f0d060b0c03070b070c020a090b010311030702070608100e06010c0c051801050405060409050d0e030a06151707050306 82
    0x1000b524040c02c0071901e80ca0740003042c4000000d00551100040340c10a5800b9102d110720a80c060344c0211000900040743e4802e00c0d0711040b656458905050414039500c0303600503d92034090380726459482c120700360b9a0340d200450150803c56101d980da50101d0300050444905100014401c0c0c20038841004210141c4046800181b072410f42c04e52344038200c1101d980149a650403c04085c9000706501800c40b50002c02000400e0040104c40001d03030758028116010018000029041140103038200001403050b0052150ba100505002c980442030030342801e040d40080b07560b0380050348480c17401c100f01504220401e42125402881003680c600b842d000914048010b071181d41080001c422010a004041c0f91000141800425141c01483c040c2601d418080c070078001c80707108078034040110718245414842c41c041207500c0400340580c4111450281d81405001720301d69054040c4014150019a040c4640ca6601d400300300d05034480d604041000f40003440155401000d40c2c4050380a2025590015440764 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 67526045 1250 67524795 67524797
    0x105071b060603081909081605060304030509090c0301060318020904030c030207030b04060501061416020f0a0902040e09010509062206020c01020c100f09021e0307030c090c020606010905060a 84
    0x20440030350701d420310040000e81d10180a451010034054220b44011501071340200709070762400e6000392112043c035210002c0c024411184001c0d04010071682c1840805035a0050080c1401800c2c90004000b18280003000c481d000d4402500000600200f42c0511410b045c90048240f840c2c0d8581c03951340864a0110080e1029007841584050501014801c000c458042c40e80030303c1690083c14680f40103400b401d070071700814022a80c804031320071070707600c0700807d0310300100f045a07031248803140640034085e200042c141d0064000385912000300c0c81400c1d80c001000141040e18403003269140040c1c00c242141c5c809002002d0981041040c01440c0312903072203201080f0340c05400501e0140007072a0440c000c1c0b1402058030429400401c000c1030860f0042400310010800003800c1c010b400009611208465811350000d6100103101c9120b090b01c003510784800700b42c0b04058215000c0b00c1e200d8503070040402c0325a024904203501c0b6018036000a5044c001113412083c00e00303261200a04000005031580180e070030001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 67527295 1250 67526045 67526087
    0x30204060c08030402120a03030605030606120d2304060206010503010c05121602011b021b24071416090b04020405010f0806040f1109041a060702060705011103010b0d050702010507 79
    0xd8159500d0b074200010584a42e4200c50487e121480c001e80600554403640c1d129000b56800100f145c108110000c4000010340003070901c1c040d00315019a880c034010030104143c92705142c3c2100b118018040280040c24244d0028a260742c908400c2600f502c00354000207003004020b01c86480d41c02c1c01c00288580204e41400f08084483c42c40d03404900414280d161440b0704030b1204051825103801240c0f152444070742c000c1c5200b9400340141070081c400752a14140c004807864040a100880b2048042c01413507104070345020b502024800302e1032514080c0d49030855102e16250080011410714803c101b800c1009441c20f50410346080c0c0081c01000088520205112426000414aa42e0350748546c02040c03098404100c0351850050b4803149400041c180e40c0158600401c450030850030413649010f9150080c00b040c5080040d5007400040d80240808403503940d00c03215100030600840d0055806419611450b6131203440c0d510909054900c083d001c0025a49010180020740e640962420f58101602c6821 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 67528545 1250 67527295 67527301
    0x110f0d0b090102070f060204030201020f120412020319030f080702160303030908090307091e200a02070e13020406050108090a02012f03070606050307141e0d05010e010c030204060c0803 81
    0x35003e0311078448003c01031414844c1e00000c00500341d000c0d100b42c0e4002c0c0e01b10b13400c00c0003000c1e110b80e40d000704a10b829a4881d09010030002038810303104500b40c9a1014066030100050a042d5103030040c0340280460110f60030352403091486500c180407540c03212a601c02003103285c05000700a8440c45207400041c00705500c5200c0304046c0042070086030382c98000030b0100c84000399a000313240001e000701400c80c8680e044466a0718005119406082e40255015040704900381c8003160240140d80b2048594065024480001615048084000b8882d1200c00e03403414441d09984100002c94007241c12441c1804800d43c04c0c0310100740c00291100100da070a090805001010b000c204c1010744044da000c14842103100840b590317030034010000c2c7c024180b1a4200f403003640e490754100750701d40626006181001d020075205103034a14054840607030101d000b410000407203c41e071011031000c1300d840300280c1da107a4440c070349140d01c40400d204442d9158014a030440c14141000c40043c41d000741480007038403002d004008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 67529795 1250 67528545 67528561
    0x10219170f01030b062b030810052b020d12261f0801020a0509180c0a0c020604030204240801021c020f0405030105100819120809010b0913110f0d0b 65
    0x44100000c85140002017400403049202e805583c0484040300000d10231000300b0345807100641c018054940041c07912500f0310701c00c0c031080e002a411501b20840078038038004a1025850b107074180c0c000c0318002c246581e0400aa030101400f18203511100740941c0030724030312207110100d0007484c00380c0100188030321100720310311441a85401600740d000410107500c00902c40d800301303422900401410506854280021458600b43d00e6025012103000c0201c807020400390050303600c40d055034462203200078423147c202916038020504844e0300d40c03840303440190b0023100d104003040d001d404c4000400014009600e440c10f400c90300910321042045001600390049070b010a1412450300380d40c0600405402000185440121103000074140d10541d26a4041c0000c03440007103401d07400d8403101d9904403505095920b030000003100e64a0001303040781d5155507070707040054181c0c0d900c48411740919500c5260254064250034600710b1001d4a424041c0315103010141d0207000e40300c264115a40c13581100680701c2c0d40d507070100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 67531045 1250 67529795 67529809
    0x40c0905030708010e010b0a0b090108041a0a0501170703050d0c0501060e0c071401020906030721110309191221050103150612150b03030c010219170f01030b06 70
    0xc21a8540515940418002415844194030881000090020041180605c00030780040d000301000850100300144055002d292481c2d0041e12500f02c0f17100e05001c095840b40e58078003e4403000708181e01d510041041e1003802c800016800e010b000500312040c9540e623001d607201d04c80000c04060115080000e024060290301c044004c20754a4030800c9185018603294409610060084481401003c66100746900c1407096400e594000303000380d0b01e1900c03080740a607907100c10031862143c88680b03201b4801403c0c0e07a41c0180764044081c282215124240011030700e0414450b5007a002e2803a0500e4040b41c04149081e02408428555042010080241604000c1d42d50200840740791850b0400300000200304218030310480100c1c095a0410400d0789911007030100c02d1707903500090404802d0100d15200c41000c0c1e070001d04000e0001382240d00e00103102129a0aa80040311410040710141c10342c403e9a58204010840e0000500281ca90034138011164200018040c003000d01581a0075001809a40f0390380 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 67532295 1250 67531045 67531049
    0x50106120209032a03031605070b12010e0a0902030d0c02150f030c0a051605060703061a0306011d0415080f060103080f0705120409050907061805010804110414040b0c18040c09 77
    0x14041d66a181d1f00760034201d4401030400400c0b80e00b0b00c034405000910301c101c01c098450b008204401507051740d10300104181402da001d0407200c04560380b6900100140d13410480340b555106980c50b0840c0c00c0c0150b0042060341f444665904461140030070242400203000307801c9a5202405808182e11680c030000c04071210300840070747c4515030160802d039005201c0c00003039483c454040c1d40d0b003d0101c3e40c1c450300440d40301c940c001c08003002c424091005c03e040b58014040007981440c5448001d00e0f4681e0040000c003135541030307031180d0032004500301c080c009600240420008082050000c00665145079a41009803003564000d040c00740c030115441c0308001d801c2c0545205415010842501e8640701c984002c01030100381c0e0b03550b1b064420248000b070864002c1000450510506d41c26404d0b0600d0b180041d00d0807000280304a0b0004041483c00300ca81d501e921416200801c00700d01d05520b444c0910f4910314003034002d0310232245500c083c05441907455403400d000c10115804c1d5004241c10b40c80c0281910804055 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 67533545 1250 67532295 67532299
    0x14040617220314041a03010e0a06050d0f031106070315051005070f0c030501020307030e0d02010e0d21111c0603080313080c010f1b090506030115020307080d050106120209032a 77
    0x2208070020030217a22400385042c2c414040d0b07404515111540b014080700c1e664410079800c010b175000c1e03000102e00c0b608035a848160003800c2624409140101c2a03060a80494035134000c40c0e40c5492075512400d004c1e000307030060402a24070140360711a8010150880c081c09200819040c923a100c01000c0000c000d14190045501000135910b0b07003045070024000c0c22889007000303800c0c03082504036001c291050043c01182c81c403040c040e0998440955044600b007603607960070b10008060801c828290f48842c07056509a0048900660f164a0314910202c44440c0d01194002070034104a02800455104000c803504000410f0240c0100140d510302081140154a000d40c101d501c1d108003008504a01d800070259217007a007a100c984607083c2c0200380c032185054000c0541040092006000c21546a803141c42450340c14012a8140b0801c0e0741c0d4100264000783e000c031645c9884d140100103094106140000304040e4103401e50502d108200070030b54950040130b40c16000d6810319550f00440e08469944c00a401d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 67534795 1250 67533545 67533569
    0x290408070b0703171905060906130c05090a080309040c020601080303070c0201110118060b0111030f030604091403070c05040207050a0224040e060a0501030506010207151404061722031404 82
    0x45501700c0b2144214420300c600030b03410b00c00000d8842c5000541c540c450080140070b8110700340540d8400f40204094a06401400410044549140d40e071b12010310040003400002e5640300402d10500c030907030b0009035062080d0360081005104907540401500e030701c540c80386040030100145000403a0804c582e03443c1d00c42e5a500c0d0486411600c0650540300d038940c4c2c0a00300c203100a01c1c42e070300116103a140d4040a4203a0390400d00c40c0d034442007101e070011a0400c40050002c988034416031503048501c28081d008580a5000241801c20014907860b1400207001c101c40031410841c95880311030712052041002482074200007030103584a41d804200c5980480d20386200c545030781d191407105201c00020380381d0500c140000d00002810b5031107802182d100d403006a025207040c5240a05c501b41882039103100105100e12640e00c1e41110310782c0006000180070075038411b12800c5485000705003510303010303200101c15500291101094000908101c0b49541d040c502401001c01088200c0d4003802180c1100340c6d9840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 67536045 1250 67534795 67534801
    0x2100c020607090b03070f030e0109020319050c0a180c020f0609030a020f0105010605120403020c0907030501030b06090408041404020702030a0311060a09120f02010b0406290408070b070317 83
    0x350000d5007a100301926166040c0864a07074408000340c1c04216810030025012083c500901031294000d085541e20741c0c0000319801c4401ea0000f41014003d401d000c41522001300b140302407010070010f400c9040c01c2907803500300450074841d2040da0030486041140c1515140c2c00f800e444c45100b007010502c16000001a24041c0c10164021030b1030354000382c1c0d481c2c0140b06000c903240016806102d02ca040300d01070b4403428603107120341e01c0050f10901d00800a0f02940143c000080c440e4581c20b8165108084c1d55500141c158110f20f801c00b034032240a029140550400420030000810308401c4038141c46500c426021407403009800203010707100c1c5181c02501400303901c0401d0100343d00300e20380c14602148034040d240c071070740da043d001002c4a07000e25010f040f0190401d001c00382d0300d00a80385a40ca0307220510005c02e111903464003107419604650b02c481d8640d042e22502c2028401c900010380703003050035240b44502d040d2500401e41d0b900c142034000e440c0002c40008000007094020030700d080000300da186003aa402c0c0703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 67537295 1250 67536045 67536047
    0xf06130f0504140c0724090312050702010c0f20030c0d08011e09050a061d040201020705030a0b0a0c0203070b09030901090512060a0f0b0307080a02040e01270302100c 73
    0x211080c07141d00e0185082103d20070312400c024280d18842c002d000d10322802c14000c1c0c0c0382d00c1c45212400700041e500b11001384031001d40d4240fa010b01005540243c48034081c0c05880c0c0d05410482c0d400804007400c5900d00944c804c00e0039880901141228503602e00501000e128004051140004020301c80503448005200350785500c000c103040e918000261245110781e0ba8810103440e000380b15a00800c2c02c070a40c05402d012804080d440560055200b850014030b041e290b040d90380c49580202e004003c0017048100f00411903a0400150000e440280c1c042c2140c00c006a684c0404640040c290002d2603071181d91003094240f080090310345c4103402015648460414800040d180e40c0304c0d2002c40c0c00203400041c04105030908203510b500b0f494465001340344954820350b0340e80041640d03081798000e42ea160322072082c2d03e940403c580000b41442c10080c01e0301203001c1c810001100c5200d40c00d860f540e410215681460b4118000317940c4001c803030040700074400d086072408078203060845107409180741ca044e0f8032000007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 67538545 1250 67537295 67537319
    0x30d021b01060807120303020c100504050307020406050406050a0509090a06020a110c0114040e06120d03020c0105060901080741010e040e030d11040e0411130b010804020f0613 77
    0x28038803100030404191070784981900d41041e40901442d81107031184620001c0d229900420f103100210703081c0c4141f0500c4402c1401551825903042d01c00340c0c00031a56106518091080c0070081c00c0403102004641d141901058170034042c0d02c6240e1045031101c000400c142c000f4001d08000340c0c0c0c002002c6545a0300b502c1e01034444511807200c240c01740300d400401416540604044103600c000b0090a5040901e0314502c6809840024440c0386c1290b104d040701800d900c020022008040c0413038034096241d08403080350390308640c0d00030502403080880c40c1c010001c405000c505102a500442c50300919000c83e50712200040d80742540141c600c10b204402c500c404180a42d0b21000d0b81070983e0b6200f0310315102420441500e000290214a6800070000c40c0b603d0b07040f99014050100104c60351a00302076490a0842d00000c049a00395140c0400603012511072405548a90114a0300041001444507070741c0000c00c601c2009000a000d8946801c041d0724a5585400351244040c040d10788602c81070711216020741c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 67539795 1250 67538545 67538587
    0xc04030b0c0909150d0b010f08191101030504080417010f051f060810090203040606091b020d0302030c09060309070501030b01030c0c110a0807060810050105040303021905030d02 78
    0x811081140801c540021020454899210007800107001ea1100c14000c103201204407403141d4800c0006440c00c0c00904103100303080c02481c4100d07000c00201c3ca00f9030000d04005da45101c3c9841c0a0310800300400261885003010100b02080c42c000035a50780c0c0c1e2404403014421034011003400409500189041d4030150000b600382c03a0303110010310947c5c0783d01e600070014400c0e400b50024841d9110f00180f20280c805c0c290a980050210520002c440e581c0d00d030716040b0381c420340c0c054480c552550800c1c04003104030300903100300303041ea05000c92303c446000030003c0d101d00005c610740d8101500080440c12112042003038880e514402006d4a90b030741032807400e480d0b80c0c00e01442810301090411807540c65540c024031a04201c003c064481084030720855650507103030203003030845660085010740c0208003200c003040080050f0481e038030b4250850428500651009525030320a03030420404000508c0020307404900020300d5812141e4800c2d21540c0b6242103411406501d4010000c2031000c1a00c100b112415022420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 67541045 1250 67539795 67539803
    0x801020406090e010501120b01020718022503080109020901030b041e0507030203060d0b0402120304030b090c03030301030305040e04110301021c0e0304030803010501110c10050406030e0705010e10020a0203060c0403 94
    0x141595031800d282081e4a005d00c1050b010503030300120f11010940c1900242c2c81c42c181441070340c0c012600c032001c4080e1107010090283c0030a501042c20f404180c080044901d5812803401004428592035400920844050041c0400350b5000b04001c00d50364041e42104800150050092001101d81440c006840303ca80d558101c590b4180000310b0b107018001c0c800c890182c0302c064099802d03151107480e0300043c005c0281003240c01000300d00030030710f00400510250011310b204910850043c10300039103591810b84241680e6100760400c200410000350013504403800c4031010400140d15031703214180110559000350300907405500018810104140031240c0c800707100c03040c6008011078615150140ea8074040e501004107030a200308014001e0b5801803803226100c070012030480d500300d0195404280d40d20745900d05503000c9503010400303001ca1038060003100140680b1074000c0000500c0d1500003081c140c880f20006029174040c0d03141c52140ba10070704c900203079507401034111416814440304804150744071388000c0c4c17 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 67542295 1250 67541045 67541057
    0x110a060c0510051302103b010306030312021c0509070f0e0906040b071107030302063102060310030804090603020906010f020d0f02072102190305030d1a040c0e090106020115091d06010801020406 85
    0x1510560003403103a54107070383ccc2680d200400026040100002984520400c540640152502c464070480740d002c1d09105000420103418481d1420b00903500603a899002034483d21021390030002c1189000403400d9000b50008144a074503112100155107a14500d07c00003980c0c0145c080100500d84c00140160086219081da4041291702245030442100d4400d07540d25444401d0002030054074110004d1504680c180100c082c1542ea0303030383c50140680c000d6000e416540e0304c85408000b07614021300c149a0010003801d1840481c4083c00000b5111010810074509000c0800b901482251003004094050901e02c0c224134030030b499002c5221100308a01004a128811005041d1000110050031000300d941c803000641c1000785552400000c0e102d00189103481a008180d032071043e5465000d40c07074074005203494400e44c00899005104046a05801c20425a0f042c4800740c400f07010700a1a5100b01e45113a240005c046402c2203603240908d1034001c0c4003940d031203007100102d10440194010400c640440c0c0320b007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 67543545 1250 67542295 67542407
    0x140f090606030d080c031b0c0106050108130f12021f0515030106030812070203090603070f12020408070603020c01020c0715020105250c110a060c051005130210 70
    0x43e516424414071800140b071400c041a0308001d80c101441e089040d036154550000a0415203244035088400c0c800f6103a9101c0720300708600d58101e00c0180c0c0091580b480c0c64208030f11911210011500c2103001080000d010f8405103183c0c0c4240a0b00b5016461030022003150192188034401900c02620002c0041a0b00090800313640740504c0307440c003182c0d445201c0f03d082c10720004c130a19030020001c10040030350104101c0744030f050380ea801c021403213114035848040c0360701c2d21020014002101c1e1182500344500c100014001180002003850840d207003490301603030722010441000c0c064005c40c0500e038501d1050150118503003000d400c00388a01092580200416503902c41e5200072032032284100b01c4a2000305100c0045244079440e250f64190107010440030358001071001c60403482450f481540010090f81c8031404008091003c0c83e07090340b4800050050f4100011000d81c1c00c100018000e01c02c092098442c955a8001d0103404079414452150017240c0080300c40b40000c4002e004e8114201120310b40300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 67544795 1250 67543545 67543549
    0x2031009050a140106141303030305070f090e06061308010f020712050301030c030311031c0209040e0307020f010e0d080307030b0a080a032304180902010f02060408030a0c03140f090606 81
    0x600e900f00c2942104408164608001621740005011855107005020011a0b110401a101802c001c5100756800520b074079041c3c40c000c01c1e0080b08060141003080c0001e003004803002d510203141c0c00144c201c903010b0f9180080c0d600d661081d201c9900c094103079400d001c2c0c442c1c031105203940507101ea14052000c02441100d600000c807104d202c240001130112440b54000e101082c8030705108240207500c10f0840e4541100903088081000003000040f001b1034002480d5015800d141c0680b0488100c544c2c0150300740400780d80019000c01140041c0303410400d0704c4000e546699100d06110038401d030880c0b54940e070303400c00d440e000b4081c12103d0310300350060300d800c000012013000010300c004000707403d80c3d81d518a1114007240f90107440541050300001850030300c404140e80110100b00751115202c200001030811440c4009030081111809035400c6d90010402c1101241544045940c401003425000410b1044c50310150000c1140e2180b0408840084042004800c0c80c0012140200c5581003141c04503603c1000b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 67546045 1250 67544795 67544801
    0x408220e040b07050c070323100c0e04021e09010e100302040603150303020a0f030e0a0e06121507030e01020f040303030e06091c0c230601030311030906070305160602031009050a 78
    0x20b0800c0c4186c1c401c0c1010008102008804c003425070441150301062514a282c1c1860840d1914040020aa07110341462403607411441039060200156400c1d03040c5a029208000c03c0380e1b03495941000541e000400324041c1c1c0c403401017110080c400816040c0c2980790b400700200250400e025040c0460700c4d1124003071244e08065048400c8903815801003420816940c2c95201004640307c0407801c3c001c00f061a039640380c1c0c2c4c42c4641c00c05000007044000365442d0150030811000303010406895540c020031070710203010031141d4a4039400703091400c02069130492038050600a1045101d910303403c102c0803402108155164002450489090302224081d8541030f5078070380c9460b0030400302107288680c072902c014011301403103881c0c41603800349642c507010445444000180001080a454142c1c02160050003015045068100b55a51003801035003020000404160b8034840c54401405210010a07003900003001c800318a48210b0b4459010b644a007852128101d80407014000c1e005071606250004461001a00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 67547295 1250 67546045 67546057
    0x90705060708040b1b0102181503011212090f090605040b010f091406090411070c1707170c1207080d02060f0c090111031804050105010f080408220e040b0705 69
    0x8008600d4140f41903000c000030350000305000380345c3c0342807039030f5080c441028070207800034420000b4010f50390126103007000350641d140003c40c2c01a020910040c0300312000da1049500b801d03400a00000c2c2c40031603200c03d0310b090709140d02c90008a4000b080214004096822001c2201c00945092004403c0440113540280c507180c80c2c5000104400400c00c00c00482c100500358918000d00024034106c400340226099410a900b00c0b01d07041c000007000c40c10801d074081c01600400c66400c580754040601d60310540c42d0411761080003910368290008001c2184148080550100020102003c0c03002400c4c844e5101e500900c54111907008846018808500100c0d0ba584140352043c000300707440da203031300712440641c01903461a4100701401c03041d50120f0504100a00c07000110b2041c41d08900310807002c03c010b98405070051410004403c0c0401c07102600081d0050b085613002050580300c003a4000d034002000c00d02441c440c00c41c1c181c1d08000881ca0308881c58a070060740501d642f201541e48100c41613610388289 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 67548545 1250 67547295 67547303
    0x1090609140102191d060409020702012a03140c0f160915030f03020a05060a0203010e060126150307031406010902032203020106030204050f10060806060d11210907050607 75
    0x78040403c8207210300c4100c2c1d00705e01161140d42d40d80c01c0540c040f4030107421680009150960000b010b0042d50b0700f1039105030740411200780450b01c0e0050280911021444424003c0900c0300f05501c60301050b240809440d000150b40e01111a0511044d038180c0e619103640c040c81e20071540d074200100c1c02292a00a51003a85140004c1c0d2858618550307610b442000c001c6029001c42c0160340c10040011000d100e40342c040d07401c52001588030b5060241030b209151028001c82c0c180590b40040480581c11201e61644020403050301104950300c60344107417094800341c0b0442e0303454040e010300842044010380002079403188440894089a80b01c098190807032109a0300704001030900d0450070500302101010f0f40285110744000302c0c9a030764075404a0141d0b207040e1200715001d581881009640110300380014024095403404100c14100000801e540e4810315415504854640280004400c4043d00b02c440816842029407294000201d21330000340b0280d540b488280030f001000039032440d00e0802e640300d440d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 67549795 1250 67548545 67548577
    0xd1217091506120303240108060d0602030907050a17010b030606030a0f17040311010305060d0c0b09040219020703031107030206030a02250803011a1c020f0c01090609140102 76
    0x510801000041d900610480d4000301c42e14050030810814070155002d014110800c40e00c1440c458498440c1e9424098654100f010b80c000300b04e010390f1429001003405070480001681d030380702c81054901b0003180d5001150400e140b01400250340c080c20f003800405e580764800030040402d42008258403864180c40c02d40d4940d00088404010804029010304041d11820001101c500010141080750700140c0c026141174070074000e048403a5805008040e48481d04175208034420845507200400c4201c80c7c0110700020001144c400f032103860f15030403030b00c41e0000385806521840301010001c1d0356038000d010440024260346401305410a0016600d4207580d40100140d08554502170710000940283c0100c518030b02040c96804403510b44182503981e00c500400e0000c0e078945c10118200c010220410b000415030302d0810400341c224031031082d00e800600d5210000b6a49664030000d000442c0030f159800d10565180916800c1041000d6120014041c4268102100140400b009034200d000c1c403542a5004c0c1d003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 67551045 1250 67549795 67549813
    0x702030d0b040e0a240903090303170622090c03081b07080a0303020304170c0105070306050a05010c0f020f1302180402160303090309090c12060506090a09050c090d121709 75
    0xe000303070300505e1080c50b402030980101c4088200000f40c40e403e103401d80102c0e12810051051645c01003c0e40000110310107001d52070305250011a24480c2d05030074158035010304504504594007203030031140081e504242980410354503424214415803002c01d810304010000d01038030b101c00d203011a00c40101c44a550160400010341d4400340d0296000800c12140109079a200c1503100b402c15000c1c124502c0c5170800000d183c42c1003500641241c0942d00414440e0405110030400740c1e910a401e400d955910002c1d5090400091011820204440075016405110002044980d41c600e42c0030341003d0480d1046c4145540c06801408220b00c542003407a04410341114600c4e02084c001d81008a03868801c0c075108110f0355640c8821401c0350106102800041c40c00c410703040c110819400703010f021b0035040322118034002c081000111840c0e11445070007003481e181e42c009100004c40c50f040c0e44060344007500700c0820074440e250400c03100c0f01242c0d010001c100300da101c015003001c4910449100340520001080760f01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 67552295 1250 67551045 67551053
    0x6020312100e090d030506030601050d020d081213060606030c0503040803130b0702070303021506030601150e1008010323060711011104090b180c03010b0a030e060702030d0b040e0a 79
    0x204000c00791034215034250000101902c440c01d072148109008401340400040001c401000d0324806402988a54411b80046c0182d030340f542404c0c4500e96046a100310000c455141810b000c7c090010381ca425107080d0703030801607000314000c941c034046481603c0800c40180c070350106400310340141c5000341c0041c1080c000907000904080c02190405d00030400e00c25007115940e40c40c0380c1850111800340c01600242020800c01d41c04020080310103071105540801403419002080d42c40301c0510445038480001404020b50305e0082d4907020844001600b003100c4d0748590200078110410030b11086400b000206210b205000f84600c0461401022a0141440d9210035408031904e44520403040d00d06c0d540c5610002017841440700900061005a0003ca0307168410300420481c1c446c80009400c8070401c20080203882d0158008603410340d0300c0500b2894841d0040b00703084005026020080003d489040284074030742e40c000002d0f140348540e503042400b12102040c28001680d03664642e203001540700c3e01040c0006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 67553545 1250 67552295 67552327
    0x61107090c021009141005010b160212030408010615020606010c02040510120b0f07020303190c05041707050901080304050114160b070e0301050f040b1303020304090f0b120106060203 80
    0x1941c1510450300514204100441202e00600c01201c1c1a04896000040e0300011710046902c0880d8040030401c643c500400031001c0e01c11800000c1182098140034000c40d51b445803c07444064000040300d461390f46607601c1034000c02e481e01503104c1d98140c21309405616072001400c0e82c403034041a560442c440c035a650a0002811001c3e221080d081e850310b0001c40c0344449101c400d40000e01900300071070103080039130f090b00041c20301618040c11034200301308021040c21a01c8458040b000882d0700003d09102011003140e00c0c0c0642c1c0c00080b407441034541008003e040000f00b01059032411502d0380105d9980300c02c519564440c2c0c0c0302c0c950202d21150103100c001e4405801a09809110240b100c081d0080c9566980d49808101c03501400316500503d04805401c00f4402c5960001400112012a041c02e8640f400b100c0001011840c0c2c00700641404030401d4424020340300205409a428002240250001c10150041d62111801035688000e090000c003c1402081d0440f01140c0145242c0540d001080d242 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 67554795 1250 67553545 67553561
    0x2007031710080c120c100203120609040c030809041103040303090201030c050a140d0612030f020601050108190207020d05160608060402030106051923031801090b071b0f0804050a06110709 82
    0x13041c0500c12120803580c6a0012802c0400310075409980da0b215101ea5100700341c2406807100d801258000704000008014006260549411041c0c050f2070f000c5031400034010344540c0145820321080171052104040c0c2540080c50170038800d0300c0c1845401c13800740c0c00f00d071140281036425002071035403d002c550702d10720314000f030000e80c0c14900042111910380e030040e04c045d03054000890009040c0c2d00000b400d650f0501025026100902c3c0c101034609100071302d0500a040400e1600f22142d00042d440f0443d515074100c50007540c0d1120517110341e003d00c10045013038080144620004229482d001500c075140034422207060f64030680b11030f424503007500c040042d410510040b00e018016002000000d4050315003401011560b9464266075030326003681d00c0504051030500380c101c0c9a04002017200010030003210180d202c081842e2811011b0701142040980d54a0702030082d0007203a6007200e803802c1c002024010019918151240401244c0d41c06007211100d4150464221a030404c0310240000d031180c1d001000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 67556045 1250 67554795 67554829
    0x50f030a021f0e060a210507020703060c170408030a0f0b0a09050603100e010501060e01110a0201050d0f060e0402030d0804050604030e0612070801031704030203030d2007031710080c 80
    0x910b41c1c690f100462004d510503035500b07010400481d1480c02283e0f00881103004d00d1144038080c0700c5070802c241c020b0b5403929a800b005190f65269050703503001c2840b541c000206d1400b058005807450409041c01c410f03a038400d03584004614100381e100c020710704081c020018403803806441d1045503460025200014003002d42942c1e0325003d1030a402c0c1c07070510705018442040c1c0007038000040303a5140c080c0161559900700c80340c1d07040c01000720009103a4100403030000c5e0880d8083c00c0843c0d0f0392000d83c145000a00c03805030f800e01241c0c549079010920600e220300030780c032545c0f0030340403141c4152804030300b958034000803203005055901c21800100041e10500d07031114010000b9118500b4840c40c2150743c40c458508941a0340000d9103c8010002d021528941000302070364010b110b03251a0079900070070388038403680c4261900c1d15158132080340a000511002d40341c40d00113280c0e01c1e84854051a00038041315061b0003050252450740d0100b604004801c000f102100e40000c02001030303880721028403000700001034800c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 67557295 1250 67556045 67556057
    0xc0d0c05040e03090d06020c010612080307080c040906080a1b0509041101020c0a1d0c0f040e0907030203070e07030608030405061b0708120a270314030d0f06050f030a021f 75
    0x41425285e8640c008285442a2030160b1910140c980090840c3c2d0554028030815a03101c0c8044081070034003045a40150b89854091029960440e8510442c401c1c0e5020112680c03a01c14006030301c080118015124510900b994902e060040e48404584110341c01b03280c0e44403404d00080b07400214084481808608180140c4924460020025500051a074005402490584e1400340102c680384081c2c0d5010b200a14064100f540010321401540103030b0182c02c2c240361058000c45e034000000c10040c0000d550050803074003415100c001650130400c0c00d4442102107400c044020454003804401c0d1419503c000e00010f00381510100640107400da0403040c2d0115029401c4003180c5214203001c03141008003002c00c402c4d82c3c0d9140e80b10040ca41c0c40c911203800040300c00400442d1084843c4040b200860b5042004a002000840c0c000e905501c104d020071448503240c840e0103481d2228940000e021100e0844420070030582410a0688401004400030350058030303401010421240a0100c1c3e061003400e00d0f1078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 67558545 1250 67557295 67557307
    0xf030906090b0105130c2703080a050c060106031e0b01050c070303110c0613050904080d060f06090501020105070210050a0e01060b030411120d21021b0c0d0c05040e03 73
    0x340121158810203481071804080140420b040425516405000500c3c00b00300f4400c00b0380c002030594030256200418440c150110383c180c207801d907a42d40007540d0030150701581c541600001500035405078660b0f12907030142200008101d40a4424821700760040c20302c0041400c503e0408000510403031080070b05108003801030090b011010081d12000d5440b0707448d841c912543c1c0c40c80c1c007468260459041c1c1d20992080045a800207104078102003164400c0c0c41c2c1c1c1c0c100351664580301c51580112004501000e250a00000e200c442061022040f182181c840072400b0380c546004a083e81c0c8210344c80d00c01740e8030000ba206400c0d46e45a01c526442200e64100080000404166909640080d80212403c0c203002c401d020501064059940040004449080c1360303000c1100c010b071726400415030403014041e03440540000d00354440902e2000c401d00c9281103582724a041d0044640b008042d00e24a454403607041c40c402d0b1810320748d113a280c0c00da4000403140a024644005c00001c0c000d824500100e0780800e01103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 67559795 1250 67558545 67558553
    0x1202070807030c110f0d14010902060c0105011503111819080304030b0c0301030f080d14010e090f0f0a0813030609030c12020a0f03030b030708060a24030c060f0309 72
    0x140000c2842569030424840c01c1341421040d012064011394450401005450401d81d1500350884045038004a2403c022811400712801841702d428042e4204400046031402481c0660000b03041c1c92064080c5a0854041c15084045a10304428030180709810030500c03241c1d0100302150b40030014000e100c2075013105040707942800210180c5c01201d460380082400c0c8200b2208090311980020031241c2e15007558595182c0020725252281e02a088a000203045035620499801503003410700c55100191255940341c0a46440c204c04071403c0c1c40306d00450421802c990404a1282128a0020001c005498140d150311450354002ca1032420030080364000040025914007a9170400b070300984075004503d8060a2200034000c1d10034440c021034000e02c12076000118803080050340b403505858000740e224804000b203481d050031754201103124400d540810003600d040e5000100308060001200d450801d40851460f01444130f8000100100440342003889414881c1c03030840101d00c11450080749101d03807515 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 67561045 1250 67559795 67559797
    0x40f0f020a080d0210020a02070e0705070602070c060206070e1e120106080d02150613090206070c030b0907060309050705190e10360507030b031501030201080c04080a0312020708 78
    0x2201042c83c0d00b14401401c4a2a01440508030391011707448150b21b0004e040000070b46075440760062400103248100400c000c28480c006072031295910540c115507a4510307080c08001d03540346109200051180d000010034982c459581d801d081503000e41850964121000e540306604090005ca0b901318405030744075021823800340a003100401541c0082c0c8110030104a009042050000c409410744282005000c0c0b10b80381c09485507032410070160002403030517a07440010340038860000040c01c0e2651074130b00171081c404c1e008042400380030040100c60840740e40743d10a405543da054405011504012410080c0b810218403140300e07040b05c1414504500e4941c1ca00c89441e80c01503509180805030003000340001d014000000400d020110b604100031502d1050029580c500744601c0307181c0c1c0762a240031a0805000e50010502100c3c01000d5910700030030191080d00160b000d02c01680000c0300300000c1070328a508102124150f54a0f100600400d25407a2801d4400c0d52030f0b4000140c410750b00700803040106a03a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 67562295 1250 67561045 67561049
    0x10e01021308151506030714031f080a02090105060c01061208030601120b0d02132009130c1403150a0308030f01091b030b03010b060309150109020702010503040f0f020a 74
    0x181c00d0090a90411040624040c1201c03030322007081201e00305005040c400840020790503a41111a1556582c5100c82101e0760820395540d024204004002c1c8044241100304c500138880308a00c2c00e0b05034980d50400301d5500d0005400203508125004010300c8107052050080400001103000421038540e034101000e01c0441c0c24505846004010040c010707107680c031820a0214041e200303401c0c05039045107400110090000310000f07106c0e006104c0d0015003a221034116514440c801c400e08101940c040410401c190b0001c0c2485101e0351000d1000020100755204100e08180741c0d075600014000d01d044065119030001e000c0102c0d4080501c2d1840341581c031608500080d51003015407640320300701400070709524401a0050203045080c41c0322150100310b10f4018040c020700324036001c1002452000403d00400c2591811074010b0390001c2000a5400c0c00290806101020b0b613606101ea0303070300e18155080f409203130310090000d170081000c1004100c0081640860034010135800b2140328080c2c0c000317958980740e5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 67563545 1250 67562295 67562317
    0x5060708030411030d02030a030c080601080609041a190e0d090303081b18100801360501140102060a06030b180309120708010e0304080d0327030c120e0a0501030509010e0102 76
    0x2500101c0d0b09c2d45406241e0710090340e030600d211517081c4240041c15540001740002c1c000c00c072950006042c0700c0740d00d140060340003041646440ca4200010780d500c100c101040d0842245043c6400d82110000000b00c281d06c1d0a4070780ea500c4030140c02d59800311411388000c1d001d034100d0480f00d16001c1060f4000c20040c424440307000350b02201d00c00002c09200e000128080c0c40c1d01403241d9440104140c40700e0400c410300710b62250462a5100c1c0b0001d02504161070a2410200d005140500208030b00524458029004400360211001c0c0d984841e52042030340c40702c0c0401000900c0304808501750300707005c451110b1040881c4040d20b04282c1e001001c1400c2003030b400d56846155120302e4041085081c28415014000f05540155142c641006c100550340c2c0d10840920341010740d5803e0100c03080521802da1503809503406d0071000e640b0003d04005003001c0c2c844400380e8080296000910660b4003555408690900c00340c042c0078502e1800c401900240401010b11100395210054103200001c20b20040c0011416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 67564795 1250 67563545 67563547
    0x90f150c010b01030608030703020c01050a020109050708100e03190c0303020c0102030709050a0605040305030f090f030a060207030806040e190302010b1c11030c0612040c030c0306020a02120405060708030411030d0203 95
    0x1c2c080004080e61120b0340b101409400400c90f060129601140346a00c20f04282403240d44d4508010b0100d00410040d03c02070158004c00701c2c041075456000c104c070280b82c04004428800008804600b5851f44107030103207018082e65811503042c0c01401041d80304c114500a08005003002034140480382643d200300c4042000405d40c0006000c103140000b1540c002c0c080c54a03100341050309603580c66580c3e20a000f02002400004100318800c2e81d01d00c500b070070b1107240181c1940d080304c90b14502400a50840e160860210380c00f03800040c01d45c240b5105101d000c0c0c2e54140200305201c6200c6010a201940701400d50031552150b000b01035540340d205100c1881c2c480c0c6d007010f94214890b420003450091507607070800d2003a048079400485694424064a04800d03181841c02c0032034903135140906200c1040c1d84001c03c2c00d40760000001c140001540581503075249502541c03c3e410b142c2e91420a83c1c803450148540c0b20741e0511006000c80d128502542d4400e21030300c60300d65444540400240b03002e42801c424001640 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 67566045 1250 67564795 67564811
    0x100e041401060807121e02030402030a1a150904020901050d03030615090501180608010b16021c02180402060415030b0409060e070b07080a031e1d070e0c090f150c01 72
    0x140c040c0108031744001c400b104220021400441c80302c2021003203200c0c40f5680c1c0100204048d5a0b0034003140c0d0300d0907840001e0310400b45d1343c0200416110300844564481845080503082281003503055640704035030080403130210f603080004110702600040026010560748070001303d0980000a040d400c00c0343d40307843d0840014134120004000d078440c0600d0400c090404141040303e580c102044c40d040d5840c6200d1070382c07a4002248006231074001c81c1c0c0b000c0e51294581c460b0b001ea417907110b4241d080d454000d48111084030b5035407694461030300307082e04c2c0290015000c0104104004090703d00c0d0414409614000c59000020310000c2d00741d40140d40203031580780d07a0f0b07100d40e9000042040694000e007034031402075051280a8854070018058210340d0000d1584816002141c0015100c0e100d43c140214403007040441030903100081549108098a03810384589040401d82600b9001c61382c0c030400410100c10f140002007001e00817a809a140c485412000841461403040914809171000c0c60b461000043c0d004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 67567295 1250 67566045 67566047
    0x30c05010b090106200111092b08030a1a01020d2010050124050a0e010323010807081f0c0207080706050c010c0306060c02010e3c0f100e041401060807 66
    0x4060144a031117268541010051500c0400302a16070004d0b08a543d0952080c1428645c0d40d602d0890349c0d4200e40050200642c4100004d0801940c05100708010030003503415200c40e00c0e003000925044250150f40b041901001d858071030b050700c0d00b29072240710115000c15440802685005103004000038510344900c014041c0607a01034809800c14040740d1110607802d0031510251061190100072010000401c001070707900c2e4040c1d0801342da240e00d6040403c01c11000b410550440352030a0089100c6800368610008090900150a00400c602081e02071040842d4680c1d580041130706111010542c01038420016407400240030312002000d003910b5a503030300c000c4140c8040c00c44080f0322840007031525105081c44980d500003c0410f007258203003070000c64075888a0010340313011a0000205094804094086145180b20354561f02c00c615030b0002141c03503616a003c1007010019403180c3d5402181031080303105158414110a803041c1009480024030010520020242460980003200400c0a20007400051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 67568545 1250 67567295 67567337
    0xf020f040603020603040b040501201201050405360102160605010e0c0301090b040e010c0201090c05090903070305071703010303030e0d090b040b0901020c10020a0209010e0601020a030c05010b090106 87
    0x254048904001880c1554000b414030700020744007405024800000a08020b4250700c001c0c1e10f1290f0400b41001c1e0400f00d400c240666201c0a022072491850500002d41030402e400340034044c2c0c2c41c03035004082c401c985600d0120a0f078985100c40c02c140c8080840003162640a100030702c8070894201d86900c08040c030741043d0382a43d8040c1c0c800704110b225081008585a4000c05481c1034641d08000410401784000020f400740660070b00c0b0b00903a521f0151000c008a40550040d504140700d00c100d0a40c0990321004c0211000342101c3c000120b0300104811380009101c2c0c03004011151203030b40d600d20750300303e156035544158100360000c0b40800c0c0d6458100f00c605801300011f04c800d1a0528180322118104444005240114440c00c0d07400903003c03a40143c1c6078000d020300b0010b150042c12008111180c400000c1d42c5003004d1509a02804103c4008600800c80c81e80392480b414060300200341d0b1070402c0c1d5007290f94121150080c0c40035543d480030801595500d0294a0082202c1e94865800c0904c40444940d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 67569795 1250 67568545 67568569
    0x72604080613020d030305060d05060c0406020c01020c060403170403150906060504050610111009110a121e020406030204020a02060604050a020c21040f0806150a0b1210120f02 77
    0x6081e200b00c020001651452100240c9035131501c1c0216041d00c070728020646503007060000415900404080080003418000904104d9079030754202c0b119140c0310401a80c40e039641e082034603001001080248042901022040c41140541000703a151030346d2a114615070311001c0030002083c50302c3d840352409104043c018000030b00b408a40c10011801c0c5800062000c4034114a0700c000d014801c205412284000c1c040d00302003160880381800708000a02d09040008405241144107007400800401c0c00e07030310411190a51940000680104084038080b0344a0201c498000c0f82c0c03140c0c503900c010005860317500140141000b560000c0c042401c2c600104826104001c00c82200c8034414840f4880c1b4400004440c0c5000300802c0203034641e2500030132120290b10035030300b280c00782c02403001000503168400501c02d445110441030740400700102000304465003034203100301404e90702c090080f030021a0300c410401d50056003802c205038200b642c0d035105035a20341440b203095810754980020103080d420916240f82c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 67571045 1250 67569795 67569811
    0xb030601060e011d01142d0304080a050d0f0906020c010c050c070506070f020a120507150807030209040e0d020307030305010902040f0e040804080a140f0105060105030604020726040806 81
    0x468050b100300003070200c1c120720355454031802200700e003a000380d0007203c1c00701c6208203030591203594480350700702c6450308030b0803454001c5c080599007000000c002c00401a607024036802800103140c210928801c940e00e030407110010640d16170b6003400350701500c0703284203941901303114000c0076840355040316545084038000c040d680140202009542c209000105800301600c41c00c0b103106407200440d0600100f1004240e40094202c80d001c9404240684101a81d800c0c451196086a040700c0d221303001084440c0c0750903115400715545001003511140a50050011388102a20000740c1001089410b45440480b400140c0503800005a410501d0352501030f80b80504003280d825450702c1d02e8507801002102181c411640707101407441c0480c041004907400c135002803180601704c41c6081c409041500e0b2800035121a82101d202da06203511902d4010b0084921840b0141c44550941d0317503410a100107540320440485284e1104000740d18078964030040b06940400505081e44c68030306000886262000181110b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 67572295 1250 67571045 67571057
    0x2010504050d141b0a050d020a03020303040b0603030c0106090507140f0306010f0c050f010617010504020a0312020a080f070c1a0a14040510110c181303020304080d02010b03060106 79
    0x2101080000a150b06800200d01c0c143c00c0034050b0661601e1640541040d003160074020703a0b41491500c20026840c40201d0040041d9002001f09a0059a4500d1300001c02000350300107100203404142c100503110750120000d801c0d6031404405144290864865400081507969110700344100c69501081d0003c8800c10702d40301c545002c4c1c0b2680171a0707881c00300030b0070941004180901c1070a00c07880b4a9503001d0350340c1d1020444d241c1000080340d43c0e0103408903000b24840047c989080c04100d890501480c1d01858014001d20030880c00d5884441d24111a001c01c0000c0d4840c90402d60001245000142520000414100d8441045150581010140380d20804071110040350003003808800408a4111180c45c4c14a1054041107032121040c0b805260b2056078404103150b04061083e030000e1a0180700078207042030700e0343d08030034400300002c8000c69004c12094010203000078a00c0408840c0d5050301c2030082c0110f03420140d41c0c2031a2458024003121443c0140d444900154090804125103400360206e82001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 67573545 1250 67572295 67572301
    0x5070207030b010e090319080f24010e120706020a020306070f0801151403010603020310090203220204020d060b040e01240513030506280b0108040b0403090e010306050103030f020105 80
    0x284103400043c010710300b00400b11000714421403803c00451f810840c0d002181724019400c0e802c0604454000c65600c3d49200801001503101401102c100c140b191b21058403030720480240004540c81c4501200041d04490400700728910301c1802c100080040080b07900403c001240e42c4141424042d01400d00c10510801c0540144480c2e002090309064071440b01911214900c0c051049481030280b000d54035545000000110341d484e4941c0041d03104980315041d01071056602d9400108900c070407100080540780c203105121140245203d100d4500d0b000800150030003200c6100541103960590290300108030010b010402d80410a8840c0c0c010006115450055003081105201c09000500b2010800800003201d69003029100200c4000d942c001084600502d081403248000d4a07400702080d02c8040280d50100a1a0705030103640e5803400f041e594944a42c4079542d8441c030205003e00200c1c14003e540b60082040150703040d0780390080d8010744000c240d41d451803c0181c02c1c2d400c0c88083c003007164181820 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 67574795 1250 67573545 67573553
    0x20d0603031e091208040b03041202010e0d0203030c091302120403200a08030402031c0305060307050604030c0506031305060405100501050418080a02070b1803010e0607140a050705060403030603060507020703 91
    0x603c034116040544c0c20040c0c10350754600b0703003a070744100d4024142509011050000303104c2000c00c040c4205141d60001c004141c0c02034403841d501c1c2c903540b02d901e0042e0310820006000342c11040140030b00400c06881400b00300d40c03501d491016a00032541c409848600c4408001c1419400310171242c541e001007030f056544500c1190f20307030b88a45a011000d440c01900001050843d20204000081e04c5860143c0343c461101e103c100502500b0150340c5140700e81302e4020f0200d5241b9100c801c403011650700c00d102403d410b10f00014841c40350002001425103030054410503022403414044c0301d10807441013020b880b01e200c8207070340902155410782040340240d103000703000008000c8070f440b045ca2150b08003003003985070b60829a08a2504030240c20400c10180c2c041f40511111080f00d100100d40c14044001f481090f00803058a41c0d076490454014002840b02242c208902000030b005200940581c0b41c030b2490800982c580301c0c6031810030f56049002a03920341c800c00502189216003030300310a0b0351014201d85840c6480d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 67576045 1250 67574795 67574807
    0x6030c07060515040504030201060f0f21050307050607080a1508030304020904060b03120409060905060105070602090d1a0f090f03070b091509030301170106050a0308030a060306020d0603031e 84
    0x20300100a6039a601c085541c1e140c0c142020b20ba440f0f00100103002a240c1481c1c02030292030030348207245c07046070400710216900d031403001c10000f138411445125000307031203c16030245190340c010030035540c50000300a0840415004d120301c912405068440801c141880d4070000c1c120368005410162044e200d400500062101108882c1c0244d0100c1d080c01c0b1700d44071030402c44024050071003556171500c20721140840f08c40c3c0c818041c204944040d58200f0a072543e540b84442515801c80318140000c01c1000800300180c46540034100c80b546c003a00004213545280e40c5c40c925000440451062860b1030700c00c0101070141d420178240c1c00b0f03111002038441c90b455843c02a9690042041c010503184942001444a003400c0003044441c0200c00d858080c2400c4c41000e2a07203e901c28010307a90036a110718454440c480d014000c083c21284054219180c903031660b16012103580015200c101040d80301d10340000821901c0c00a400c1c0154a1440040c0c954a503180181030707003881c074401a0040030703000740740148550802 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 67577295 1250 67576045 67576057
    0x504110405010c020a0918030e09060307050d1b090209030f070501080a020c0a0b01090e0d020706080a0c050d0f021305010306030206040b09031515120a02030607200a050d030b06030c 80
    0x700b40143e001e03200e8130000b00c0310300721604004045032800d807581100401c81079202d540b403802915030001e801101403e101140e2002c0303031076941592003c0b01c03c1005003081041820401c0c000c0e04020700c54000c40d10803c010050030b5001e8034180e0b40101d0041e00070b2805100030f030070482c840c0780100542403a000c00030301310300c0b0002e2203042d22590119000000707080038029074602d150b001140e10625a1541548801030400d000070742001d01c00c1201101a0a000103181d070241d50494580ca0810360340d60140c200685941c501060411006002c90f8038115032038001c0c9010000f902d0000350b04d400c1c019100340c00d0b6210981c0802d0406003041010000b41c0c5500d400c49082d80c10750445607075120385190100780b6001010b00e100728824104010884480114030345184280811140f51454491807110a9612041d10101951540004000c1035505008000c8480044481e40c40200c4030403009407018141841d56000703446681185c0c1001d60403e5044c49841400c0200700e0f8414114281280c520b01c0324090f00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 67578545 1250 67577295 67577297
    0x7050711010e19080109060b180c13030b07020705041b050d0c0207030803010b03040606060504050112150b0a03061502070303140309150a20090d031809020a0810050411040501 77
    0x31a082c10015218014000400c94000d491510030700c0c0c3e502c403c207000784038000e025110b06143c41e04180c03a5140040c54a1a00c0d040c0000c200c03d152606458908603500c202c110340315030501d0340340000020300340702c06851046007590080c0090f41d1418050105641381c02d290304400c40310040d8190a0381d074000d81035440200701440001000c41024506a1a140d0319400141001c84c0100001070403811400084d40320b030740f1400091251507502c54041d201b030f004030300840780400ca06201c03610340642c2c41c1c0c0c1b000b03100041084141510b6a910034080c221540300c04014000243c546200b405a0a000b200800c886004d91004000c09890341c1c41c0148404802c0001154103580000400c100840801c010540450f402542e00070b030341010b14030340000740514042201682044088080344d04034940a4480e4881c0203005840403a16541c2c0c2113400180e1020b40000c0c049201c440410102824405009240361584400c403180c00c0c1516004000c04650703010038403890078485c4056031040f982c01a1802c442c42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 67579795 1250 67578545 67578557
    0x606040e0d090612061d070e0118090b2e11060912180907050d0507020615060a0311130320031e0f0d02060a0b0405040c030b0705071e03080705071101 66
    0x44c2800a01c043c1c51168406507106102140c1c13001419664071100d0300a4100c0d88039100350074801c50042d00c0783d40c000d4500d50124150000d0802403003c1c00d0300b1400d240a40200000810f0a50400f8010722821030808401e01034882c0c0c60610101e90000c1c0a00040d000740c4000b003005180c0742e16107607540e110307403031500b0088800071510101d03100014a00300c24002c8010014551032421500c010800d42190511217000e9040030003103940203001150311405101c0c44042445266040c909210140e0b0014200c54109541e52030b9420300700c84c0400140c440b807036002c8101c500c1c030351550030403252880300880c1241100c140008405203585e0001400c0303400250301400c880c103e181c03648151f820a004a4407402d814000d150351201025030200b9850b1040c2c03200c0c101080840c1e0301c002170008450044900424442c0211020310124480342141030380307c0401d01c1c10762320b081d5013079441218140300f400380e060803030f407001c8800000c058000032146d134003007514506a82000c0d152303183e03405500d21072009c41d814402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 67581045 1250 67579795 67579817
    0x801020708070318080706020a0c0902030708040602090f03191101050f090d060603120309050106060e060708031003080f04080c0d050606090907080706050c01050703020c06070e0d0b090606040e0d0906 88
    0x10012600c90003428840c00b1b5540c4603a8950020b91600c5205504031030040b4119070215111030f071072080da800b4550380c0c0d40d80c42c00e59645580b000000e60015100315841a019048084599810400b80d00d01d2103480d80324040d006014603112a411541840d2241840414001c1c08000e800b04410fa40104000312243e00c1d0000450034468000c0c2840d81014144120704045244100d4040d0090480c241c481c200800002d0703035404089a014207592201039211038100100c401207004c0341c0146400444845041d501c2942d00d5842c8131071a448103019200305034010904003e0a80e09120409540406030740251034480b40355203c5454460003014203101d030012101041d2507407410010790380600121030495446a40b00c0300c001d07042d900b0151352810b40798207007000214818864000d40340e001105400a1513141c036411415a0403805180c2140d03041088d050452010400904c1a140140301c0d560151106061007800c4c001036070405d21885030242c5c0b21403402a03c00745c1c040c41c64000c0340c032140b8002c00c07598 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 67582295 1250 67581045 67581077
    0x50a08030d0f0f090302010902101409061e070302070e06060a09211506050a1e1a09040906020307020d03050103020303180102250501080f0403090510051c02031008010207080703 78
    0x40c114028600e50345049454020146c055204c142400c3c02140e40841240f1032000851f8a140554100d60a0346024441e040c03260078110058280840350840840c1c0b15450b20601d0212030b00310440036001644442e4040145101090b000f40d000142500c000303150170701e42d120103842c8040c070f17100d048981c1854004040c4014044007010050300d6101c44450440c0c0c1000340f50b580540454015030327106201901000400e10124904001d099099a903803a03007007444e101502c4121600110781c1c1f006290304100381c81280c0d40f1881403541c0503105010040e145e0a081d90003e182001c40400c0c5014107203400014405658000299040c12150910044a61502c500102c4c10f02658088a422120243d440d200d50009200860310a41d171003039951100a54a80b25190460007003514003801052201105005c2400c00380b0f400b07949100c5e07900308145400c0c460500c42c80c000700d0b0382254030742440d4003000b881a49400c03c12500c00901146002358141482074a40122505c140d500007424890745030355204e145 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 67583545 1250 67582295 67582301
    0xb0a021005012d12030503040203070f06170a0c020703120c020402280206071218050607020601080c03010c0503161403010e040605071d01270605040807050a08030d0f 73
    0x1940e09209102550b940c0809011000307010300e030080c1c44144515440040400c07040600b0442d000a641c4807903070b03062518180e6040d8000b034400d9825019841000c5030311032020707480c0c800a046a44d6441d8103050301c2050007d03c0302c0054296a005400c0079420f0312640d43c002a02000d41e904000000401c003010002a2000210040e009401c030340085642031004403443d203007400740800c900d100380c408408180b003203840d913a0840d030300070108a09182d0400714440c40c0d03004100b00110390340203d44888035900d0b120b1600742c0803241200141d0115005002490040c0118200d01d1019030081c00030b040721400241c81c90000800740842c140d00314110075036007442040d24050300032203c80015030300d584510106545440898040c1c031018101000f2407a40c9209050b0072007201d41d03000030400c45901c1c0c0001112803075500c01200014651581d10030814000c1e01a80000511060b202c05558038030780110340342070071100c3c0d201a01c5580c480c941040240b401004070750403490208000034004100403040801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 67584795 1250 67583545 67583563
    0xc0b06150c0106030525030803180106090f1b090605070303020f040317030f0601080114010503250e01021903050a080a09060c0903030e040b010e011b050a050303010e07030509070b0a02 81
    0x140c1d03083c0507000044c0000815a82400016031484503040c0c10500300d040c13510105407000030b003e151b0401c0000e868058049800c4500c1001c1000801e100341d85066541c16140b0450240700401e9444a40d0550300c0e281403c0c2480340d030083d040c1164654503140015040e030182d000081d084c581c00040120007054038000311030141d6440401c0702900442c214803078900303400c103c9440300307511144404104650b02031910241224800000d404082031800011030b40c64002511104041c0c00503010150a2000884102003150460b0b031040b400400480009140c1000e051740900d81c40e55000c0c0c40000b0907800030403071b0f00365141410210195101d04018000410200201500300e0f8506920791103c01c0d03100710140100c074003a688426004240c4410881150205000c5070302244150517004a9540101000c201c0708400107080b00740042c513601d440f42040080790040700e507600b0020040c0305e110503e08801d60040c40c903140c2080301e4642240084e640e14814025500c05180c04250040114401c0140e020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 67586045 1250 67584795 67584817
    0x1020c1c05070f06020d0201060b04050f01020109060e010b030d0e0907030c0519030209040e19060b060403050f100e0a05060112080c160320030c04020711030a0812070c0b0615 77
    0x140c0b1a514000451240050b0149000601400d08017484c514030500900d015505009105841d00b0b01e41410058000c0e243c120032410b554844a420011500c14481c410483c1e00b068000718200b44650101030802c0b1950a0b02e40a1100e02c07100004c154a0303072443c0d69407207815801c0028907503c000d50103032001e026011001040f50100782c01e05850325496005445928000d443c14041200725800c12034444028a0880c9441c45081b02c0325008070f65213404c03e041c41741c00a451030b45030985949404e8200a200b068034056540507445035900004548601c1c0356080c200e0004d000442420303503d1f5522400d06110b0300003414007100d1100140b2100c00200c4404071004c1c0c084462000c0c40d84500c991069003480251400d0110040c9801c401d60490310b0341070004002805040c9010388001080000c1d00302c2002039480715107040a108403624204144680540101d04141e00d0303403201d40b07024200d600000d11a604200e001c10a46000414041001d03402401c1266494a42068407201428034081c205145c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 67587295 1250 67586045 67586053
    0x20f030403020307020a0b030103080703080a060503030703020601080d0507020a14040f1a01020607020d090e0a0f02070503180a061704032f12040e130303060305031c05070e01020c1c05 81
    0x109038000000702081361082d2a039250301651900c4428150000b48409402d10108100a4000034444c402c10f940c010040b80b000100300c0e484001203403035900a00c10450140c0d01000c01441071140c10070071306141d030701d44c2d2800c5850f0404907400300d00079020902ca080310036810024400780580c0d842d0018584101109420440610702e2446200920a040c0740b2034054041c14010501c0c00c1c0c0702250003c0f13038800c19100ca4404d00c3c500304005078040c00081042d201c030366503401000d01356106800203041283c000c3e8021500c4624510703c00311440e030051002031142d0322041c010401c150708035007004c0c2004210070f005c80d0030355a24107090380d583c0c4040e4801440189500414011102e8400c512050021b02c1801c45a008544040ca640ca030310440c025404681109000141407074042d2413550381c030346d100b898045119a030f2952194955000003124032201d60524110b8103c0d2003552040c2980140545051002543c031400080e4443e14255071041c084d10301d541003501c0c079510505101c0c4c1511b510500325 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 67588545 1250 67587295 67587301
    0x50d2007020108061e0d1407140a0803040302010c02041814030406020f030c0a0f03170c09040c05090f011b1a04020f030f070506130e070309050c01020d0507080c01020f03 75
    0x1201984400401c07804183c20300c01082131030030319111000240c640d02515010206003c0e04001d40780c0403c00c2c00b118000801e4256249500042c402c40005080040c0403d00d07400785c1c141004079030301d40b5070084600d80c0e006010801c0540c0e44404488412a0181c81c00204013a401c041c3d224441040a0003520707001c2104c203000509a8000300900c200c135035a48c2a074158401030203519803039100d000e108619582c400204200031420701e180d40c2d0400d41c400d05104410707503c01e200301c4041940c101c0d00c0d0514540041484a16800d203400746e1000240145400c030328000710f04001801d20b18404203aa410400c02c5440c01118031990018150701da41c104907031003030030258a200c804441b44112000c80c0290095400603107603050000f90340214025038000342074aa410300c81445902c2d0030911181d0303458550312000140c00c8a082d001a409650560340120b481205810550b00e442214602641194030940d0a45c410130f138004140c03040c0f00e41c84814583d0b50f00d0070400482c0a0b0040008109100f007001040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 67589795 1250 67588545 67588601
    0xc04081b01080109150b0d0b03060109151a0d09080408030c01061403060402061801090e0103030c12020610031b0506031f15080a020717030117010614010e01050d 71
    0x125a00e80c4000340c0c0c81002d580e807549044015182088482c10944440040a005a00300a03001d8881c0340c00c21600000c49a2128000900d42002a48190216541c1c0c020344466145214030706d070040d200286000e60200c2d41d84005040522410300e40c0c2001c1c581e40e060540c100020481120010800c0700226a1a56550310707000c0c5c003c013038a100381e1002c56040208020b582c2404502c091040f5001808141440c40021203d00103261090079035040204504010a0008003c550a80614020341e40d181d00f403e8686041004c1140186040c401e5501c11410410540b0300110090207499101220056841130405c0601c440c4040340c01069104501100300304280540c51f088403c10040134031142c522a0741c1c4c040c1d484035402d6070210400000d5110b000112011000c0d0000e1484911503031041c07001c04003440c1000c00e140c000b170b00100c14000900e5a481c40e5440709000781c401402c105a44034480c500360744c0000e0248054508141d0500001080208004601d0341c801c2079042c0c2d803034100c08000310907051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 67591045 1250 67589795 67589833
    0x306100c0602030a0b0916020c150f0414040b09010515090301020d0501060201020a020717151806010305010c0207060206010e0f040c0902071209090902090f0907230f060a080f0c0408 80
    0x41240180c06c0c20300000c011460703050b030040c00c5403825005441200300702810700080102c0c802030b41d0007664040000781000c00e0144014070061039002001140d101c010340c00c1100340e8480714021071141c1c440e140140015564000f42d065045d0300c01d5035517550340600d5404207029000d0b5256000c1c00c207180c075000140d000e40640041900c100264250790b00107440d498903001050040c294852207920110680b03d5040d0788050854112511080c030381001c440782d0304582c0c5800b009030401c48003a5101d54100c481c1c01e404000100c05807400d8005000b1139810084a41e02500b00241f951100001c4030010400340300c0c0410040001d040599002c1d0740ea18101d0604081d0102010b010380e0000d0100135001480780348501c074a8982070350003800003155807501440081d07820006002048180500340c03000a00e002a40e079144c110326149883c2d4400d04418404012940c82c000a2141c022003040194000c1c65902c03005040d071000d02c0390014880da8480c50300e4441280030715005144284503060341d001c4550f00070301c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 67592295 1250 67591045 67591061
    0x6010f0501020705060406050f0d0e0307050a1403040305100f020717030105090a0b011b060e0304060801090509030705060708280504150c05090f03010b0402070b09060108030f0306100c0602030a 85
    0x203001c807a103544e50366051140d40c0c0302d5842010000f4006004c1990b00400d200020b0980005083e004581b00c481c03085460b00350b611258003201c2503800151200208107010094034100e80d40e100242d414036142da22480c0d112004913120301e1429642d0711b282003a103207081d41170746c1c18140c201000c8140d0701d00c0d900542200e98020b02846101d0a07100e00014a000d0040c000c48400c003c040c4e441c00c24401e1003004220001c0c0c0381c00001c44a440d240c1809841d540401c0020b40014261692119403552401c00e614040301e03006000c20855800401907a404200001043c940007403152038602250394070440c0c40101c80100301c82c8200c8403040d81041c060102015084107018034003e050f1800c5151a801c0e003802211150080100411403d1200f2803442c5892060720500b09005400401c40000c2d0700001401c9905c025011a2118900814007c1004003003081902514062008600c0d01030326134545002400024802441250f03480203c200c010b02c00ca201030840b0350721460035510323420300078081d1f40941028 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 67593545 1250 67592295 67592297
    0x609020a08010e0a02040321021e010603030e04050c03060105070c080d030f0507020c0907031518090b0702010b0603010302060f0702040509070501030c260702071809060501290903010e06010f0501 86
    0x2600441c1c4181d04c507108030b50440707900042c9902228090030714075043d8003298120b1400e60098540c90b151007500e0203940d80b800d5500c42c0000a0300342c110718001d017140c1e01801e0340c20301a614100410072011007041c00c8a400980909005403101001d00c1d04805a00d416002040507006450701c11800c0e54258010010f40c4482c844c081c402d5984d0700d04101d0b13171200e0300c241e029803204480c40842c454501030b5020b4489604407580303040340c0e2a107031281140c0c0085120804081c2e643e490b03150714140700702c000f203c507007110751440240040b0003400c0008800340810301000c0c2c03144a000036080700301c240d1907044802c03641d8082d0082c0028079004a620f5200c490610031a40468200303080d00c130f045445400d48022240e8486d281040d02c4030741e41c410245050700104000305503c2000ca010814018501c03051100403400d40000c116610f0304d14001d001d07600107900c442c0945010740042c01502441106040040340114460ba48444503200040d0240407088003025041c00b414001044903c0d81800c40340945000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 67594795 1250 67593545 67593569
    0x60207030311010903090509130b18060906090303060f01030605090406090501150825030b0a020c070e060d0b040201200303090606060c0712020f100206060103060501050c07050607060609020a0801 86
    0x107140c110b5007a150007840050001c1c59814040c0031030301e0007180440e000004160241c074086182c0d9100401e00d041640e1080444a003900000c0b6600010010960322000c010080c0400c2e003443d1801139607a0201030002441405055407900c01648a0b40c0420000d1030000d1400d207040c106424400f00a104401003510154204000b10a030305142120f840704440d81d420003404000a0402e490312011043c17035042d61022407214000011075040840307980541321036480140d0390043c601c0d041d442c0c0701603070b445011340c100c0c1002040b4280e5117540c80d4003012034002c0c440881507621440102c070103442c0c03001c28450003403098030005030000340000994490030f42d0408445c09604d450082211900540c00c03583c2140c3d010742400e110360a03001480d10f1403c2e1029120304221000000000c0f10b083c010b030130030700045c0e11120801200790b901d8000e40c0c00410b020f08219141a038032810050f120085405014010000028130108100b925881038004004030902191205514a40240070b18400c3c80b4003003010345 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 67596045 1250 67594795 67594817
    0x715090c050907050706050405010905070e07030510030c030308151003020a0e0f09010b070f080f0c150708151309030309020109170d1b0f03031e020408070509060310060602070303 79
    0xe28001c064040c10030303500e030641024a17685c1c0740d40152a0081040f1615501c9140040c00100704101000c041d00051004021034604444020f040783c100130114100035501040070000300d40300c00c1c02c2c4402d0326010310340540340d65103840080c02d01d40d2071001100d40154803204609150f55041c1c0c080d054405040c0e49130b100d0841510704000c241c4420040d0954090200001008046904030041078428882e0304141410b0600da110664603401007549214003039000540c422494100b48040c3c660156111a403001d90f0030b09081c018000700d0000c042d40201c031881c100c3c8520030f64401148001c10324090100340b1a2080a01d0300401900315009d00b02d0204120550215a91070030344002021824040004d00e54025210f50403140c4a0051544109000224000c0c50108081119040c4640c0c066140450421054110042101d0100c0324205140b0700c180010b0101e0300001c200002140c07030844a20859844e9100080d04081e003080391128460b10300f110001c0d0b01500130640c8000c881c0a911426101d072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 67597295 1250 67596045 67596049
    0x110a09020c0705060703140403030c1e050a0803071112070b070801080c0f010c06050f0106080105060705031b0708061812070809010f0e040c02010e0c0103020c07060c05030715090c05 80
    0x4001c0509804032500008018422800d00001400420703009142030580414146111030306035000380c1040d0b0004100845003800c1c056003009401c0648000004c401d440c00da582c803101d840b82c0400100410f40180080403505403840790001c6052090713100141e50703c0d28064041110103921030003040326034505100007d40464000c8940504a40c0c50744080e24421020324100040340010494250501084c10841800b2035900d00c180d510514520000400550402078040c0505d10140d0005100f80020060240000e90110669030340900c00c8000300d80004c515001241401340036001207416124810400000035221111143e103410300da01501c0b54030350b05480301039082c410344a0213807001c04e081001c103285501c2450941300d048810324225900089460015058840549003500181e440b210602c0014100f40300f51305801030b00f401c045150000c1c141c11141c4841f1184114002e1140300d41d41803040c040207008440481b6400030800b0f4005520743d0f4400c0040c61a0b540585058100d250045064 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 67598545 1250 67597295 67597297
    0x801141e090a06020c03250c050f1e130c08041e0201090e061f090810051308030c130e0717010e010512070801180b10030803010b0f0c0a110a0902 64
    0x668041d00180581c9601501c0300d10295001d03112003c4c003403000300302030b000c0400c440d01411a60000181c5041c811481800c1c600c1d00685141c000c43d103c0c48406c030813100c1036a11501d99903049000820502c12421a400000301c030b6640c540c604085582c100101c82050a6001c66510311680c070804002c80a50160102c5103100d006038000240030031203d0100348802c1006100e8140c0c0078400410500c0c080c034600086100d110440860040407490312041032000182c1400021030b1313062100010040361400511030146442d413608090301095001001c1404400150122040900d144c0103007080590f86002d54640060129410710005240c01c10999080e0300751042c2c14101c8081c04003114081c0d003043c2c01c0041d480080004080742d407241d103000140c11082801001608411a07039041e001803610b0800c0c58030810000c0401c4912260f2031020301c00101220107a03815100d1061405407512024100144548650314a65042d48a000740400401103041d0b44245030a900380c480d030010540e60f16000b016 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 67599795 1250 67598545 67598551
    0x31403030c0a0309050a020a090608010b0319020919061d090604050c0907050904090c08060c160b0601050f0c1b04060f14041d1015030b0a05100801141e 67
    0x151403003040441e8110b0301c00d4204c0380a0710700131800e449080e40035500151240b0302580c4034401680e112807007041841001c0c42584c14004048d4054a40840d10300c0007810914103140c2c00910400c241000b04416018528102a1450281400f0011345883d4003440c1a418480706100c100c10807450001a401e04012031005c0c05181c3c4407005101601d051070800000c250010809420003506000e09800e40d80c56000e00203406019000c0007016506144e0124103141005048901d80c1804101020a0410403004045081e40000d0018031030388070040101c515104010701d4060484004c50300028080e404180c02124402455110301507401102c240421b45d50707944900c00b0310030302a002c20400c60048102099112000420004644c1c1045060315110b1242c10a40c403191390110318008605281e0b03118030b40c16488600a070070203d91541e0340e03440d140d002c001c3c90804074641b12004142c03d401c108900902428083d4000e000c4c4030b48071b54402108690840e126110744c0805040c240c8104a17490100e40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 67601045 1250 67599795 67599811
    0x31418030c150d0902010e03150402040c0203031b0a230a030b241c05160908060c09130e01020c0102070317010506030721110406081008061302062203140303 69
    0x2040a402d0f0249800405403014281d060152502400415640500c46450030480900d0b41d008036003454018442140c2c44c1c00803035019035204000b80700c40c004458030703000050815100381aa507001204d8088482a9468845c082c010100e180c2e000d00c0414044050f2404590b03640d020010600304800b040140c05500c04009281120780032150341c000d14010041490610031540d98104900480300180ac0300c1d0308440c003001c250458000c12070455444180000108901070061540d814425090001c40c401c3c114030512901150605610500d0160030003a601c2c0c00c6c4100841d141c0c13010b8070105000c0c1d8404071089001401c25604500c0c42c100d10410305042c3c0f50301400aa05503541d07000241e9407201c14411080404004110b1400f50441c40d008080c41444881d84141e1180c3c50040c0184c259400500180745081c100d010910084500048240d8800400030b2091540700e42c5001148040c0324200e04207103528000c0f074211100c0d00046c14000b0440c1d204100b020f121008907a407182d26400282c40181c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 67602295 1250 67601045 67601047
    0x190b1308150124171003020306160f0822050f0106120b04080a050c030d1b030b010804112d1008010b07061d01020705010b030105010f03050c0607031418030c15 70
    0x300801c0e948550f540e02d850b00d500303100b851a54201908039a01070210340c08940b80240d0340007070086041c2404407a07000000100d524451020142016008200d070070440c4040204500000d120b04400196020b0342510102a003441074078113041a030340b207001c1482e02013000d40c2070020005000340c490098424494000743c11460700d1325a135544445035070080a10301e04100c000d2058130b4401105000500603c0c1c013502000503c0d60041d43d07401016141426281c042c1454200350301251790308a8541c5070b1156011344920011000280002c2a04402600b0400303448a10341810011200100c881c0e1a0880d08554250348624114400c403111007003405410702101007401780800080e00e42d00503d00c00004601c0300513480c200c0c11115400c9070850001501d45a4486170820323480c1c2001e00c07400d8098460340f00d4641d50541140c4070150380f00421351509009940c0080d031b1805141c443c00908032000041140647c0c0c40b000710340001c1407a034034810f40520a008050800c20540740207404540305d040b84103822 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 67603545 1250 67602295 67602329
    0x60f0e0c090406080d0f020c0f061602010203130603050108070e16050906090607080304110f06041703040509040f0302010e0c0d150b0603011811040b0702190b13081501 74
    0xe0a06074000030009a0015203400001c201100e042c40307000c0e44c030041595a0078241400381c1c40245814408032150380625100c0326000300a856603011911000f01105c0315807003142e11840100d00d148030b154550110001984030100310343d0782c1500118100c95000084a50b195120040f190b1018820b461072000c030003e40844071000350240c0301400305450002c181e181002078100c0401c81682c040c1c03074200d030315a400200704020070000034110301c00c00f001035655420307103c50709000c9505482240900100c04403d441c0000018004000304e40103800c010b03046515a0800d85040565041e10040c22005542468401c03403900000154030752410900a0803216a0b0525403521071083c1c200001195440e91544d4940c00d903610b500d002140204207089001d1504810107147d103080700c0030b8000b10b105030b40c01007200b000b0143c0e01c0402c0e500025011145500c4003c6440c01e900c2d50820a9444030044510110307800c4000000540068200c13a140808d0301e41e0040002103100d030504007401450710000741c030010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 67604795 1250 67603545 67603561
    0x10212040b040c05040515040c03060b090d021f0804140d0e0d050a120801140103050105060a0818070803070320070603110c030309030d06050105031317040b0c010f060f0e 75
    0xc00c1e4100f8010120b0340c00e519215404142502e104841800c6999a12105000c40c0d0402c1c4c426003040320013900d0704010003420005002054411948285c0c030078a40008a28199038406014100964a9801c180c0d421501000050441c1e0821502603d18400d401117005044c080407424407841d404646c1c0e4804030055460030000701c4000c00c00d09464500c2002e901c100080c000249102586609442e0410301c2d615000c1801c043c04224a84ca50400d030420004000f6034950909840b40303103641303041c440059596940c3d50001898402c0c030881711485421ba0004a00101100500596000b542e0ba4140c0c03d86501216000d41d050aa003031085601030305040007003d10070780c0640b04590203260400d24151814040c50314507007099813108015000001c1e0813031800954403652006120030300f051400c500e024803100c1985c905006025203001c9003004ca202555500318122000350124000094484a41141660003804000d80c1554414605400418030181c0e598801089034484105034850b981c1d0001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 67606045 1250 67604795 67604813
    0x151d010b0d0e0d080907120510052203120b0418030806061e0c0607021204090c02150a0209030f0624030c03070303080907090b01050f090f040e01020d050901021204 72
    0x10400406070b58460080c1480c40003480356022049190f6941c00b8542070a44405081078016030056115408459800000400c0402c080d0106610300300c0000d035aa6030005d01c1ca0b9000e80c82c0202080d00081c041c880d60805800c440903168080c19074508201c0e265503c0280310880d01c400050803070341202c0070000f00c0002d1103521015031001000e080c42c0d003040c48000c6140e141e6040703483c0049039484042041c503030100301000400d03402001403000302400361206691344001d21490140801e225110000026114020040e000c50b0014100c0b401d0040d1410a0042c402500000d004502c03e01844104011154000440034000e80b40d206c41510f05006441d502c2265040c0310b041c3c0c5800d8020844540200e41d002d004c0d0300003c1d4000c0e02c510943d032500000f045c0c01c1805640003c0401890446207000d00d99009040d11100c0009007821030341c038080f030700c00500000c261207070099200c1d080031014a900d18041d000303403102400110b0305100ca03032a001805400c2c1c0c0100340c209034426200d08002004545100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 67607295 1250 67606045 67606057
    0xc110d02010e040f020403050c180106112802030c040c05040920040303030c0f080c030420040f02041509050f040b1305070302071103030915030702100906151d010b 72
    0x10600b1609400c4410200c0c050300c0070100465006070780400d003041800310a0211600d043e00460342c0d00d40c0b107000c004003803c900d0818014a01007120f00c100e071030321554042007080010701180403000e80a600048000f52201e4490b40102d0003405464048407a5007803500030002c030a540c6881e030608090038040944014034040c0031100520000744030350140c1508405c002d201540c000d90700480c0903160b6180181040c2505d00b8a2010005244108200b21203094152034200b035021364000c4240000d040054100e58110080a0780540f8102c1d411002c2d1645a0040040703804031801c021603000b50400a58080501d403190a41002c518601c01c0c05a14256004548002c8018104008403908072400b00441e14105c038000c0c04a42c1c001042424010038444921580f24110b0080d49030540306070214110b01c80080d40812312032404030108500500920451548441c000c80c1007040300a10b04107103000d48032282c14240607110030b120104581e90b00d2018021f8070301d0440340e1003400340d04e040d00301981c41d8400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 67608545 1250 67607295 67607297
    0x120309030f030e15090606090906040309120c090516110304061202070c1e030c1406121b0f0409060801020403030507030809010b0a120c050103021801030b13050702060a0b010c110d0201 81
    0x907090110f43e4035510000f03600694074174006048034980b810074800e510001030048111a0b010804000000340e10000920030398400044003504101c40d40340070340c2c2c001e60300d0308824585c900782010030002c404000c02001c2a0280c07170341c1c0c10900352003094406480c1c1c4074600072280014402581c651b0043c0d56030b00105074141c03242d0781e004100c1e0750f110220884010b501641c56815602210300300184484200d031072002e00480f0400d4518a1100c03800204203224844a86004030b1800e80000d02001034200219500e0510041ca20780c0c0d03c081c8461207050b94814069005664605540801d2084c414400d0b1002e0303d5041e10703418500400c0380c0301581c0c1c03281700a00c0c50030159241d0901009640715062202c000700100d4419210b400e040340703080f401003001e6420441c1010700c11b01080689082ca03102805881a082c04c0000c2c05d50544808122580e0401c00c0322620642024244039580750f002401782e2044494100800803000101d004444a483c0804007074201da550020ba06000d203003103010800e8803481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 67609795 1250 67608545 67608553
    0x60304020303211b090f09040c030203100c110a0807030c08040906060905040b040510090b040209040518060c0702030a030e0402130e0702070e0103051c02030708031003120309030f030e 81
    0x1030320310a00d40c00090b0b4040c8030043e403c400d1105050401d1005144000380e0000c00e81000a4800420311695500e00c9443c030411411022905014151039544c0c041e40e00903080e105914151507401010b0020544040000b070305280080c0c10510005c02c0c1d04208907440f11070b00d80342541a0320300311001540804251801d08003040005a0401d1a1081c20010981601d03202c041a280804000c120381e14030802038096400c0108114058441d52901415104a194001200148400031400034002d45201f2034000c1d02e808140012070138003100d46c0c0b400f0000082254525503e800c501c05960040b080020b4055000150b05030000340120265000c440010f840107040c8100344184885441c41a44180c00503100e81b03081c003c4440e03041c0000d030054030301d52040740300704c0d45076643d0a40d84030402a12481a113017080c807241c0c000d034030a00488031420703003220040e80c0724245a64144811891484100c0f18004444040c08049009001b415200780c0c1589410300707242c0154005038050514001c403102c40c0d0103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 67611045 1250 67609795 67609807
    0x10210060806040605150a030210050408010203040605060909030f07020603070c050303100e010602030c03040e07030603020a0f060e01030507020d0e0a090908030105040501050d0534031101031109010e060304020303 94
    0x580d00c1400014000d12004081500340390401104682028205c0d8040d80c28500340e00c80d15480311a08071741100c1c0d05442c0c00b01100c1c52140c0840b00fa0046410028440d400002031000f03001c4141c00444c003890088400d48460b031608407686503213104c1c01071b0401c6039107014820400503113824809554020140d0800300c1c030070f41d540e58810b0b0a40d071045070b00c586003040d15241880004007031101240540400c1c0021494403a985140d07030f40c0c0b40660302c118800020110005000188640c02220007941d010f44404400c1d0341702c5035410802c03210350158000041d6490070801082d07110780103542c040c1c50746401815460020040468241880105031900a5159000060b4154042c8103031200d0718000e000064480d4100030421040e10350603800301c0c1c8186c41d0102d600b4041600800d14603404c40c401d9103501c40c001044415020300d41c1c0707010303810074002c464203a00009101584090108010b4240c0c0c081081e005142a04a070fa0f02404100c940029100842403400d81401002035401600040c2140d0a001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 67612295 1250 67611045 67611073
    0x1b011205100e0f0f1807030209100b07030f11010908040e041106160605060d020315130c030308090114090613050102070605090a020901060c031b02010507140105150d051b0102 77
    0x81c01c01c3c0c0d41100d184190324204140072042c0310049411100e1445d1003210301c119a0a4241d0b11107560001a2140c00001c000c83e80094035409400003c0c403c5002c060f0300d42c811410081d00c0600516a8540880e03c104101d44840c903041c451440e50036400b01282e41840e0408100e02a207034402413080b540000c002207540d0242e07a03076401030305141014400707030a0050705a01c0c110701903c0010301198000e07502c08000c0801a5808200e249044110f5104450f5507a180f0403070f0700c5981072150300645401c950900100c141a0312a031104d11844404000f40310000c01c070100c0701d0515000321648400c40e08a04003088035151360390346825045020350009400c14030a03403940340403a41e099485020079440100901c08509241800600604040c10b1074450800d450318082c3c507040c3c4c0d490b00207070702c61045160740702168055030940b1680c941002010304a2903000b03e0316802031906a030165210346050520b0407040c40d0151406444c640e1120260003480340e15444640e1000c001c0303801505500859000d11120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 67613545 1250 67612295 67612319
    0x2010f11030907060903052808070804030629060c07170c12030310090c1106040302010c020f01090c0306050411132009011d04020d0f0209031b01120510 67
    0x300e2400110790789040402a0714940079003039201009001044004001141012030320a80c4d5059607c100c048400b010300c4c0c00c00002020701c42c020403102c0040f41150900c0350072009401070324850041040380700c000a08005500144620009000d55482c0b84801c09042580281c0f050714000c1c1e00300d6040585884909405444480030401d0031341c440c1a04112502d811000c201000c0003c80107103155041115825040d1201409215036407601e85a100310000d02c6038a100b0956100705003aa03010703082030b00c1c000b40a448414050070051045014902d02c0341c0040c0300301002c1a0f4080e0350808451b18556a900103000010020380d47c4070104600c85000b43c80d1040ca486003202c0040c400500d2008152580000701608425845401424071041da12039810075104580d4034642c82d080381014031040c0004000c1d108000c980361210b42000b0007800d08100c03c2d0058030740c3c95800c50503030b80720545411000c08034011001410740040c01c0c1d2440100c060001e68000f642014100f08084605074480301c0e04840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 67614795 1250 67613545 67613561
    0x110c0304181107020d06021e0a020109030f0207060203040e0a0e0d050705070b03010b09010c2a05090c0f160c0b03130311010b090604020d0b150301050102120421020102010f 76
    0x452121160380785907410345031240821103000b652440341403442580128250742e0350044011b01d8070340c3c00102c003c8121150411201501d40c110403403643d41e54200402030107440d500000710b000c6032985004031034180c0040360020542c0d209074011410540340c12400302c24600007501c0c000e5999a10a040240b1241c140312800c050003036911050b0303540085e442c001e0f10785442941b26440c5520207000601c10300c1e90b500304880d1440c100740f070200c81941d62070818841609110301c0324004190100701c0b641041046000310000c0307071800c45184025075500700c10748480b8030445401e07460583c0300f003188407c102429002403810a006a081203030451315654030311120352055078010004200350901d10100340d803015041d058800d40e80c0c028849400b01001141803980044c007a03910507034020407072800422040e40003144000c0001c11070760290000701c1581d1803a600a0003554018001c50800d4844052500b00b150101c0717998008104107500001d100304000080c681c8220304654070707031400300c140d040c2e10b004400c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 67616045 1250 67614795 67614809
    0xe03030408041e0303020304060c110414060a0605090631090510080a0f03050901030e10090308070206010e130f080c0c030c330702150d0506040605030a020103110c0304 74
    0x1640ba420245850078261410101402200800e0014000658003200790340485495050901c589600d502d0444c1c8501c3c440e0301c0494015141500c000d49042036030f00c40c00e0154405540306401c103611024100c440744100065560014010020030000c1d00c03a03428051240704404200e00d410081441000c5100e0351641d000203066500d50003404001d00002d40c441c0010a540c0005008422032540c0320800100e004401070184400440c1000550f40a0b8104a00c1c0400500039a144826001c1c1420002c1003070f100103900040c07040000440190000900d00d040e00c590254049031559440303556003189441100032280d481c0709103507000000d150000580034004100002d0902c0c0c5400c0c00a0600d0024003e80c80380c0700c0c050700c03e0484114101c2088a0230308840070441d9250207420300c00f91140ca40700c0d00302c0083d00114020083d503115001903010b814020800501400941c032000d0801c0156101d501607940d142d00700c580c40c1e000643c02517100c1d0329030240a1458500727061500384c1d0141560441d0344180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 67617295 1250 67616045 67616047
    0x6070806010201060f0302010c030311040f08150601080405060406020f07020901030b07080f01061b06150308030a0e12030604020306030705120a02090c03010605091e040507031a03010e0607030f0e03030408 90
    0x40419a028040d0313002030411016005600b915680000340504000c54014060680d245031020f00c0c26040000c0302c02904040c8584940d40fa90750340000d0f80d5122001180e50742003e26408941c0c0c0d503100d2422180036030340003002040c0342c0c1c07a41d45a410081d0b000b45206503130850104405030050f107406403118005c50003000504c4891070443e90113081103100030480c04e501e14402c001480a00d03044040c0701070080c45004143c0700e600e03042c60103400030704540c3e280060080d0843c0000041295000055100781e42980301402414050003e2954500c0e0751109180903080510000341c050810398003555104000900f1514144d90300c40114010800c104150507094100c51220030942c2000d5104a811054111031286076600d401c5009000b8040d044103c0e115410b546484041d04442c49009508004001d104010a06025001400514405d610a01d00c6c105c44940e840b40c92130180319804160944a0141c034460b9103002c0224001d10041900d10041e40e42d0b040081d10742c54042000d0351081b84181026 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 67618545 1250 67617295 67617301
    0x9080a032a030b030309060408010b01111b0402090103141617101a0d05070c0606050306040b0c0c01290405060a12080a11100b0f150301031202030408060708 69
    0x506680004400d124a554940209880e0101c010328a031145891841d00088108203580040e00b10310421461581c89032003c81c0104143c1c1c81036101d80350044090329507443c0c002002500f251140d2801c0c07120305500c0c0c10805403000d6403d00b6001485d010714145000030303559803102c0440c254880701392007011b0604447d6141d1581181c1154014030300311034141842c00c070b0b8504614032191511141c0030381c0c400340403001e010709104194041a1050001d901409202130719200308020710f003200d200d80645449003030140006050902044d41c901a9402c034803d15115030701c0300340300c800540c0412000c1d41290341e01c540214440403038140f800054201f0a03140507003000e901d8100000e50704042d0007603110b103120b901c0c20402c200d100000415134030742c016646030312404030100c00e0f1400c2c1101030031114540075680280180e07030504d07031001c06846812a0360050020320070f001d000c40003800c0030348411082d40400061010458000e00d47c14850f940e48102d900d0b19860700f00460805100395403c5020458250034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 67619795 1250 67618545 67618547
    0xa021606030b1516050303150f1e0904020307080f010212060405070804030c03030609052703040602190203190f0c0801051b0a090302030d020708010e07140907030207020409080a 78
    0x151500826541c541800024030040019141030f44140c08092208000620800c14030007155440103880c0d0013005070794a925100360b03a0742d021807042e42d200740704884004011005240180e84150720307070105110380c0f03244641c96040c406440b0010340203907030500c030310345002601000400000e40c8800b00080050f0700c2e845401ca0080c01c20001a01e8544a2420882004022540301e0741055200b60149802441c2c404981800c2c0c00604030b6800c0444401e050078104900d040c07418030120304229043d5400e00c09604503214080c2c0302d0003a401103034010303008288801040e815035680d0f054054002402c1e42d2101080c08929140f450038090b08075501080b6204183c01c3c00402d0071254001c241b07050090101d0b00d4030310070300d1043c100c101d034000808401c04600040300c85d10403060f0300040c503400340441c0d5080800c000007070350341d486920842d41c0541c20301e10200c0031204013060400841e22030b020403444a0a2034020003a1010004003c54205a03003030004c180980d4a0340240b036840c0c1e0042107c130b1780c0c40302940f034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 67621045 1250 67619795 67619833
    0x9080105011502030a050a0507061b11280611040801060312050702030c09090c03010e011d010615140d020d0207030816081b0408011a2b110d080a02 65
    0xc00790409000782d10039000300319000f104640e0115401d14115a55010800b815541740c09000c0001d403102c0c2c603220404603280c0c07032246000704c0c14401781c5580400c7c604180e2010380d50503c442c0790004001c100304109215201701903100544a20804000c614500c0440b8400c6c020780241d440700d86140c1d16480100140b24190490519030755044c504a8600b01039500400d03038400081110324050900b0342c0001d000fa0406014111090000a009116110030840c07980d0180c403115201c407460030452084035208a030140b00b040d00319001d818030b00c032000300f80d0b0b50256100708076982c100c01050030400c586030480c45907200400180c580e509006072540d106050080c010000201800e041604526500007070f40e420007080c0d40d21148050640c0c58004000304c1c00ca90305d0140d648101059800c0c040d131001c1c08014051006030148050300c0c00d820782205040211351081203445a510381850503d00746010400c280c81004819201a104554074441980c901c0002d90161101c640103800400701c10707083c403c13459 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 67622295 1250 67621045 67621049
    0xa110d150c0e10020c100908031206130b0108060d0206070512030739020f10051c020307121a06070b09070906051005070203150930370908010501 64
    0x50f030100c071607003c4900d0180d500c80c0d104004500c21007010041748541c41c46441c4c52400341a03c0002c3d681c95040d000700018030071030b050700d0140c0f04881e12804207440e02c040307108880c40f80b40145e44040701900e401003400103204039141d059070020710802c201000303d2010030061040400014407a036a03480c080c00000d10441c07910000d042c103542c15a0b220284600301d031000300108050004950b007801040e10001d0b140c0c804004006802c129a2000c80c00040e41040207054509001d40e4440071112001030580100d11048a0900204035040c03542c0b84200d1071544540c0896604107200390b081194100002c2013030304590402c4691001600800c010741506100c0741004110382e000512015080000042100480311210010000d011072410290741e020000301482e6540700382850858184006070545820921141840c917240940c1960f10480c008201c4241c8101c2ca2a041c904080e032946402c91a46c40d1001c0340c40c242c640c10303180300310b80e42110840d4090403945900c075007118900d0030010078256003050f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 67623545 1250 67622295 67622299
    0xb010503011a030a060f060201022203050a1e08040b0304050d09030803010b0c16031a0f0403050d0203180f240105031c020a0606030b07080f06030a110d150c0e 70
    0xa000400980700c0c003100c41c0c8100c0c12103000369a225071303841880800403c07071503102205000c031501d000209140c043d8000c020340304007040d454507040440002c1c007000b02c641e0301c0020100e511126090300400d203c085c0030000740c0c2c00080c0003049000181c03518001900103400c14610f2400000c02d1108004003002043c1d07070302059041370000c0a246444101b82400144174802c81c1441c0001d81c10a4103105204109280040070020074240d40c590401e42561b80d80c1c00442c51800d86000c010035209121001e090744141d0345555040d1401c0300c82d2048a0207034101820381d00914944443c3c075800d00c00c00707000081011508500030183d0748143d00b40c02e009807011918160f0320104c031000602941d240459400c47c0f082c0303180344203501c4c4100c0800c103d251001902d000391031249480c3d000310030400c11040c02c3c0e0250310035035290000c41d11001d60404c40b1200a0319041d905031f200000240001d440c00341600c400c3c140051191180456a4407a8006840c0708107500d56400d0307865028412154124105070300002d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 67624795 1250 67623545 67623547
    0x141c17070804030509010306050d0f0501060b0c1207150911240f180603040501090309060f0c060b04020f0c0109021806010503150d06020427020f22081903030b0105 72
    0xd210141103924060009010003100140503525a4040e40192000b008090081a8131030790a00302007014505240088904e9402d1030000209c56096000303840082e4200c901502c808540920180d01a41c4945001c552503c14210b82612410303240c45a600418000e00643c2c0c403401c000810000c14000d40c880201c144012140702600c0090190140c0714407a0000c80710680d00c49031030556504080c1404401c50b48401d002080008110041d0000d000081c465240c5038803a40d10b550055903d0410503500000040703119201d4408242290480106030720050300041c60585107081d50821a4443c0d80c0100041e91100801003c5040079028551441840c002e101094142400020500d10024010700074402000c0d076810fa0543d640d0105841442c1d01082c1190349a80e200842d07840541c1242070034401001804680050340d07842d000701c0e003007001240351507450f2800d6180c0c41c0e46100402e4500701c1d400d80c0038090214001c41308001d0414150410551820700c201c01e49801025100e400f8491410000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 67625901 1106 67624795 67624801
    0x30409020310090e0f010b040b011e030e0706050903070f03020f0907020102040819020405070206010602030415050d060e0f010b040503100f18140f011a010c141c17 72
    0x5001d4009224a90b141f00030402100c02d42d080203404541c0c1e0306580b425848000c19195181c9100f400c0009441541641461400032160003101c04640300244406192608002140082c10f41580f5081503030309560101d005049986481e9000b004c00401280c0b00328000c0d01074501030300c100e108035503401c0c04191900710000000d12081c3d00540c03030310001c100818030210b007d41c144c40d4540c0086241c00e14040c544115818203070785200401005200100940e5114011800108070043ca2442c1c9070a10044003005100180e01110740344004200c108042e4402264030320700300c0030000c40041c0504441c0c0c01000640a100c6142d40000200200b1400704450b0344801580c000d0488101c4003403100400e140c40c03c0703510b941c01312241501414004140780d8424031014000e00d2141300040094400e1100d4540782155854070b10381464481154414281e40c410a9000b00001958001140303007 = true := by decide +kernel

theorem cover : BRFrame.Cov 67446045 67625901 := by
  have h0 := BRFrame.cov_init 67446045
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67446045 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 67446045 ≤ n) (h2 : n < 67625901) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
