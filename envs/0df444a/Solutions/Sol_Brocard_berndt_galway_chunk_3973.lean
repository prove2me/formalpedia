-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3973
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:12:26.385805+00:00
-- url     : https://prove2.me/submissions/c97f6c86-f1ac-4083-b920-1916b54398b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 714388489 ≤ n < 714568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 714389739 1250 714388489 714388511
    0x10303020f0309032104030f05060f2401030c120f09050705030d021509011e230c1602130905030a090807120f0f02040c05090f06091c0611030f0703 65
    0x201e1203040c82042e810341160802c410601c09524110005e00d9507058214201070312903841000d0704034544002d444a5015504024a0b0b03c0310b030a4481c0d0061140c0f050401100c2142547c1c000c3d0500b00c0d4505040c9501c841c041c0c0401842241810858000c940f0103100341c0d16100381e08001014034440544c0d25000700344d030214182c100082d0aa1078860140e0040080941c40d43e070301d00d481c03440649001d12954a9080311205642c0c010441400284c0750b03400000c9a040d01c0000310403041004aa0044021840007007000039201031050300c0f1004056499020700740c40c0d07031000640307801407800140200c501e484980014403000001030301c011072468a80e125941c1c0c4402e0b800381d8a0321305200d8035200030610801d43c8000ba880413034003007406110300040c811020b240c1d400901945c01c05108480007502c085188859850980c0880344400d1069034201e20308405400414082c0c404c103a00c4504182036002e00d08100420380d400460b03050a518021502c0f070a0082210111480c190381d6200001d0400c986118 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 714390989 1250 714389739 714389743
    0x15041e0b0906061605032107120902090105040f0e060406050402010f02030310030f141506040c1e080402031507030c170f070f120207060204080d09030f111f0206010303020f 76
    0x10045034020142420100c00085200f61100c80d980120380c02e000511403000e5070868130391f44030300c4080301510326106407a0100005213807041081c0c40c1c02503107040180520168460341c0c0014151002502d01042c0004c42800b00300182c050181c5803091441060308010600030264883c0740124404d98500c5241c0303000c114101e035280426244449841180e5608000050100304402071a5203d502602c650a07085c19440b070400000484030b20728071400f0000c00196151034802e82c00303d10007608150031388690500c412844800b003011943c0a1003a000d000c80d065560030049040940b04110b110b4201d4a041107000340900100c1e032501005c504080c49481050540c100d01c18410519078502800d25600d80004440ca015020f45500600000d580c020b6240b4485000031b1036001e004800242c5e4651401d1509858074400905120800421000a00001c0d901400959075203400141c88550140da001c002040380d1341210f95103121240b02190b00303000c1600443d000781200e0090f025126220519840f1035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 714392239 1250 714390989 714390991
    0x1051503010b0d110c01051005181902191701090218010f09050a03050c0a0b0405090106031e0c080f010f060e01120b060f0301080c0a05060406030515041e0b09 70
    0x89280248014000c1800b4072015000c41c0d5942c1d00c0c00305031059500100030541d0f000c9400c4007880c0e5100e90070010348076040100b490091009455800b10180061001a001c080150a03c80c4201d2400d0100c08200c2803a01520090301d490810910000243c01001d80380d00d1302400d00c004440c9030000000f56920340f900c03e445c5400c8a00d01001c81c10707602c00b40119464040780803408240504100d001c1207988440c600100070798400c000500b240920303034040003030701900c950142903080d40402061000341c84000805046a20b2400c010558030241400040032007403640c0d20f8031105141c944444456548000343e00c0c0150402c02c154012039890704d03060034500100d40105c001082014031802c0c20741d442002c5980010002300c00000700c40030848002021a40075500241940324003000500002c4010701442005031412251840903924140100380240103912618045c165680d00280c85003801164018018034000c0c07040040f40840500c0e562041c45c030300c4040140d0703481c06141c0070a44c24011421 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 714393489 1250 714392239 714392269
    0x20d080106021b09190c0c02030c030f070b030910021801030c0e0604050609040216030206192a02030c0109030221071a04020307032913020a06050c0a020607080901080105 75
    0xd0383c15007070b80006018000c02c001d094002c015114031000203948040388101c41c6c0c1c600c01c0f07980309032a542c07217401014070b00030252008911a4100082185d420341000410704121940359903101e8481d0b0300c12660604220240c400b068085000090041d614039103ca00d0003160b05007620200b2010706194011105600c00207081c1e81c1004040009000314507002010700a8020014805442c01d817240b486110904001c000c100d001d64054014800c424581c10a4003032544aa407500300910122242105442c04030780e2a100c014948481c4001240e5109200300c41c1c544001400900c032107181403400954441c1034004107034402c0c40101d02d5070323500045071040700c2880340c2080461403212038504e403014485201a1080340d1520603420000009166850704003081d801d01261140d0108a540c0300c003005c0131004020351035110440c4c072960300681d510603400055582e146055900c941c01c4200c40703440e00e01c00010182d40300c000890700004100c040700c0280103001c8280d9840301980d0341c0360180038517502c203c0c0704 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 714394739 1250 714393489 714393523
    0xc070b13140a0c47040803090a080328050403050616091403031b070f030f0b0703050108150402031603050f0c0109081507030209120a05060c180108090c03030406020d08010602 77
    0x1031000400300c1c44404810812080e00c0d10311500004c02c400d0300c41c1e0380b082c0e020721060780011424010034a04080303608000c0111401641c81d00c030b8034880384462111809200701004050610039400544a1403d031000345a220302210703214100b010b8001030050342d200c3e00c00e00054061300082122134a04008450000000c0c00a6040c9480329086c12902078803510b02e49c0c0380c1d00c11180009a402d100c819008000c501402645510003500d04001c01750b42c100503d920249401c00004102c03e10002070000304805101407501010b4132036100103800c5c002c81410a05607210440804024001c02054951514260b0001ca501d41d5800354015600c1c1c0030765100e0505940c010769090320501d00381d0703038090740c0c01882440c00529203000100000d5130300490803c04051076200305e22080070000100400794011010400301402c0c40c00300880c4441001030980d1444c1001074000100e8500c80c0d0400400e20581c00080a603510ba584617007000f56542d40c4200174070000340f06500000b4a050022460b850038882440d0307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 714395989 1250 714394739 714394799
    0xf0d0f050313120804050f060103020105070605040213060b1c060b09090414010606051b062202030a05010207060b09010b03010806073615080c070b13140a0c 69
    0x4000e4a00c1e400041030b5410014240a0200000e42c840034003140010154071000c4480c03c06003491850701400c4140c0c40d8003a030101c4c00500150780c11806407800254480004a201c0d5140c0c03021601801aa0304410400b07801c020020940ba803105000e428449440700000c1c1c600304080780c00f44181c40041c8140101c1007003c00c81018241440e924142d8000c1c000d2554040800c0e52100346803c558043c0d000f800014401b00c1c01c1c01c4650030314106400c4c140b031407800a00050504000300088001c08003030005107841a0310f036850864809215804c0e1040e00301008540f903100c0350400e14081c24001900900c1221048000f1800c180804c0940f81a5214180107206940c0c8132074060b01c0301c0100044e180700340c6158071000700c02d408034041d10030030008003c2c02e1410792a141404042903a1010608007040c040740d80100440100c05c0001c0d52200c0350028400041034036a141000d00044841001601c0340003094150008000e000540c0c1d521a4465880d80d019240c0d030303880c800d0700d1903c1c09a2055900740203003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 714397239 1250 714395989 714396017
    0x1090b0103033b040e1e0c0907050c101508151b030106050d2a030606080106020c13111e0a091d04060903020708070905011a0c030a050a03020405060c0105090f0d 71
    0x94413004812240c20201e50006c11940e031482c1074210030803440141980078105510150034041d0300355401444900b019814000300c1114a511240003807410b100150b0340c0c1d004094401c2a41d441e2000904c200c03416601e44c00a00049410450f004580f00c05e54400101c0b812200c08860300112070481310a81d82d0a4188004c2031260750180c218502c01200310704024640c0700400c0c2034094040d0440b0001d46000450034540f10300076004441c1640440103541002c420700c501c50b26203124041c0440c0010318005242500e4000c0640382e4001d0010003680b4000481045216516050080950b20141d80b0b580034280e5450400c7c0741483e442e02c4171202820f8031000810005816600007505079840303401a00d404c16100c401e0107103030200700d900621074641c60700010000d007164802a26003408400e000240390101071420700340c2d2449084149420080001000701c4814480d034180c4000d420014000f545e1120a5580710740648025100c00c03440d4010310402c4032598400091000c410581500d880c1c0c3e40c1c06040f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 714398489 1250 714397239 714397241
    0x70501141c020f0a050304060b0306060d02040e16060210060801230601090302060d091a04080a111912080601030b10031e0c081b030106080c070501090b0103033b04 72
    0x1507688214580d8003808518441d0b19082e0140012404941d42d10380c030307843e003820319100340d8080d440d138a40280c02000500880d92910680c805010341c041d1000700306015020342e0f0514001c00e0000403041b401000c01c0c0440c242d80e012a22401d034880d05a018010151503140c01802c85030205501204007024145c0c0e091101030011007e503005905041c004e001e02e41ea900841c1203036014203070f00901c242d510701c240000c00c0495080500900326a4600f01010f1616a44403c0c0c1441003151203818040440888800090100700c510740e40300c0e503641034016140e0145003203126429000d03414004990340000242140d4030921038000103110003011b005114594160a800805400c2208419100351600900c802e030301e00d0040214841f4959581e094070b2803c600060384014508000040c581010001041800e604c0107055030481c2640c41c010f60344244c5454202d004140509005280c0d4052000000c181504030544007103441c411140003210310700340c0c4001640b101d06009044916000c104a604140c00c11b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 714399739 1250 714398489 714398527
    0x706110a0b0411040e010e060f090a0c03030c14031c020f04120f0210080c0301052b0507170309030a0f0204020702030a06051f0623040b0c01050907050114 68
    0x81015500c00000c1a00e0700303510310340c08503010f482a40c28082400c0150810f4482d02404010110081080003c01c40320300d515480301410b6950507444010100d440e80c01c041c004847c0da5503101440300104c564918000d804014030590582c1d640c1c0181c0c445c040d0104000c0102d900e0322440801540c001900003060304001c0d040007044c4c9080300c20a010100f540c05141d00d554143d640914180b00c001d090f0b910400480c015481544000c00400809209100c000c6c1010303030741581d4088502d4100c03c001200d090300c2514a008400306600440d00c2c09809020b4040792040944440c3c1009000c0b0004081ea050799920444100a4143d44070480420100d10300c40c42000c44240300802c05403030a8101c0c0c0000f8034010400742c3c1a5002950340702800480d800d01a00b80d15000920001d20030a9481d00702d02415444400e00440740012070950307100c1c40e0083c0481100d001e081034484183d00c40c5c40904c0d50f035008040c00c881e0510a840341e414086881e40c06001c5810015001d1000d861800300300d40307211040550 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 714400989 1250 714399739 714399767
    0x2041415041802090a1e11090a0b1204063b070803190806060c011104080c0109180203130605011e082b12050c0a0e0d05030d110c010c0203031015020706 67
    0x1b8103032075114a40420b41c02400030301c4800810030354640342400100411003025a1102c170703840404204070001d140c002c01c0f205600507000440040d1000000b456000503080c404d00007603c001c07403500c030821480c12001039207807802851022650f200d42c850190980d2441045003a58801d2001140c1c0807100d0701c03a401c010752041c000707404d860501410240050175100810000d8103140030106007846580c070200075000d806071092a00384e1145c1d02d0f2182103960001d0f1340e41e481c18980e07000400030b03021904d80c41d0740721149640900304104035a520040307880c10390002022071402202e1000c0002e10131500140d040e8040c140c280d017085107500c903411400c200340d400c46001c80902c0214144e140b80c0c001948a81c0d8400e0501c4014542d54110580c0000c04900f41002080e1184686103560800301740000140d41004202c60000942c01d4079465415020380912150301550350b0910700c40c0242c032075000c070145015101c01000026030603202d481800e9007254041001005034805203003080000c0c8590a541d0740d9103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 714402239 1250 714400989 714401021
    0x90518120d110c0d0809030a0c0209070323010f14060405210d1d031f020318061006031404051504020d050303070c1101110a0b0402041415041802090a 66
    0x1007000c28080040c1d0300070f4000c0c0e900316041aa2076104042d0003141965000940d00050341c40c1580c2c401002e030541800030000303401000504001000d40340a58007042c442c0b0081d030b100e9000d5802003a1500300c054424021030700845078002001070010050390b02103108c618018661401c09041c8014042e80c0c980ca00c40c1d0580034804009180c0460900780100303141102c83e5070301c078007900c28068440c075900c84014a080340240c0c0001d0801b40c88a0080c0e80c01d14110141140150380c9480b082c01c20709109c130517030407201400d009440c1484000c0300400264400c6601ea600c052100e45205844190b11900807a4040c1039038122a292201c4820302088140c0c2c054401805050350080a0f2155417560304101c1d000c0c0042005a0703c0d400034800c1c0030001072200c070401d2030409004450b140301a40c031141d00304001031005a040d03000c0380841d680c3d50008403030f1001c9401904d9080c41d150003901407c10000c48018001c42c901462061200c2296083c40555900a450f10800391503c01030070b402403c005204041003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 714403489 1250 714402239 714402251
    0xb0a09051509071101051605071112070e0f0f1308071505010801090201020c03370b10170106030b070c060b090903040602010f02121602070503030310090518120d 71
    0x20360b56158024080c89041c1d40f41d0001580e004040ca08480003d05444882640790340c0f0403100540c80340c112181d680e03001c2d490301504400c4601042003101404542030b4140900000850104c20020f40700d4401c0d54007401500c2c3d15110020f01c0c810303070301041e1040d004800e264031008011072103240c0100030701ca11644220b0f5045284864400071100d0a0b008014280d4444442c00705640e0b0400c94031248000460140038012080c00240b844466401c088954068029151008030a50030002948035a0418080300703e03840c007501a454064030b00c1c01030f40011020040c01008241052003007105581d440041c0f5102c0d1385802105403840d40c4940e01c11204240c4038248522161111003106014149420013191150b04050001e030a54607003041280380d130343c410301030240007014170b070407207508030780141040c00c41c00e1540c000403814200160030180d01444000b0500000b2065828005c08440d42c00c01c0800c9540c40c0c5115451a15118000d485070320b600c4403c0005080c40d1460091002c2c19800f0400100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 714404739 1250 714403489 714403531
    0x501090522060311010305150a0510020f030f03071e05250c030501020a020f03180d0302031201060903062706020d2703032d021c0e0a030f030b0a0905 66
    0x2d407181604112030156650f0642291544c150242035080b403002e0311104004010134010444104080c440c0078414449140c51382550350003171005d0218a0320260940c2e175a04554041c1404542c800c0e1503800000369a00c50340e503422000000c0d003048408650b0ba44c60300d000e185407905500e0144201d421028015800c0103100001c8405510a000314450000985c540110440103420320099074440c00f0190000c00c040e04420b19804d004640071034044036418520242070804914501400a0300c40c040303407504002007421a0007820b50317400c40f446420140402e048200740d20f41c21016040070304d2800c000c106001000101c55070080d0610102c80480001c20304000d640314400211522947d0803a4840e420840b0141981030089110703035480301c0c429005004000c80e050b1364107440d40004c031420315401b05503040801d00b08011840c05507000d01092154103a02c10020b0307110030001b541240031401441461074468064040c90140a02c000c2c1080c03605032400ea064805403d004080010401ca50341c11502 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 714405989 1250 714404739 714404741
    0x70b0f071209051e04050c090307170a1a04171206041a060703030501170a05030301143007090c1b05010e030310080111030c030604020c0f03041503150501090522 71
    0x1e40000e051500c4280640d9130400e000403910054084091004104500b071a581c4002407800116890905842d92031b1143c01071150421001d10802000451040302c01701490b10514803207400f441c019509900c203402c8072140d51300148140c101c4552400c3c200c0b80000d495160590101c0300780741504001c801556122000286150f1020100f100405c0c0e5a0b4014080c103e4000900481844500300800c9600640d07281c05640c3d0005118000940c0e50102100e41d141d22070100c030303a50028580401c0340f55801038064a090100300082001020301ca90240006c00030301c103009501601d00f0503150484499000390100d5006010328105640c0c56480b034004404942c0200000d600c10594403041c081a90b00304450b540c01c0d1641c500c440c0a002800b0f20500000400b03000032203400039411100140d03124926466141030034010011103185020200b0b0010348080101040760500f0081d175002c000034258026510000e02c80e901401e80002c0c100542444075040481002c0301c0090040b6044841c880b050b00c0c618 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 714407239 1250 714405989 714406009
    0x3111005010b0a0e0a030201171008030d060518060108130f1b0512030307080105012a03020f010b010309260c030309010606090e25030914030903070b0f07120905 71
    0x16200381e200040310000340c0d84c0052118802101100c4035030341c0c1d5242d600020050b600b00116030104c10b600101041c5407807041440d000c001c00041003a04e40b2000301c03c0c0004000c003294071906d03000c1d0088000781040e1700c1611648501c1400140c42d12090b0b912800e020600c102c501c0c20302121038400340f0142d04046201c42403070880c91141001300d00c0600341080d05101c0a545201074a0b08158000c0c02482041508243d038a0706503070081c642003002c0c200351112034180502030186c9200000300d46220005159021826010350440d500080c44500c07031580044085030b0140c0805800d5070401900c51041401d80d0101c0d2010030710360010300f82004011004142141c0c01565800c030103a550318000c0004642041d500d0000740344070503503103041e45401d1640745041c401c042c0c1c0c484504484200160b138842e00a070320000103250070082607288016480d5240b903480d40603003910340c40381c403850100086440141c011512029120b8020342c1c100086940d6664240000009150a000a000c00403a040e11600000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 714408489 1250 714407239 714407249
    0x10b0a03060606170c0a030b0a09090303060303080105060901020606060c15130b24011419030506041b2a240b0307050303040b071509052113030311100501 68
    0x880d00d2030210301504c034000c01d94012402941c1c2c003040141e400c02c0307041a1003080310141004241c5040341c60005010f41625005081450716001511060503407540c000c0080c0c1e031090320f0341101c0b642c0ba5420804540900c086080c01648a100040e00c9414050080e05c0c92401020032610206404044c5100c18070081341c0e4000c5200c10381410006202e401b0400b6a042020340c5c2400007481c0250170309a41007980719081034180201c3c2802c2c5907940d0320b038004035241941140c6008012622114005001d0001500e40d03512590814003002444c2c180d20002c0d00e50704d04192180e060505213913800c1003040c043c00b040d5660040c8400300020110b0b21256020b050700b07800000c004443c00c002d10242c2d04880c000003240c0c6c00b0b6030081405204a80307001048500340d404082d0004d495508900d8a44e0712500c100d0403c0100a0800e000c03e401c2180024249224128090380000401c40034803814049020300140f91054034078110040010a0003150f50742c108000440990303441c0503400c410365091710400c1e0f0207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 714409739 1250 714408489 714408491
    0x7030804061802100503100803131d09062d0106051b06060f0d1103011113140d0f020303120c0414030c0603011521290a17010b0a0306 59
    0x80204009092090040d0048080e94103096078040f50049190384001c103000206000300000400c10b650b000c050020000c00e108801c59a5900002203190781a40c0c0350310a146114001240782490001b507802d1540c49680a50001d200303540c2c1d0032801025180300b8607401da10f04a600c00c000002102e00310300030f0f070103021203494050b0b4030705a4030003683d9981140c1a101c007580d0890024040c05550b194100304185904913560704a280a0f810041c2039a40325031001c4d82d141d03281488446e02d112141000c0c1502c00304528081c8480c2c0d80d02c03507840344009054225503a00000440d0040c1c0010040c105209881d0700107802c4a040c4150f5100c0c9030b680705802e4811161524002c9404c000e40300c0030301652904100c090b400341c00e07403291000200c4c80c03600040c080c688800080003449903006209090400b5020402241d0780c900380300c10840800100320280780541030f07180302003821540440380300c2c90315071001000d410701d040030345816200c484943c90498068080c0d52900302c41d112031395400603264091806014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 714410989 1250 714409739 714409741
    0x2030a090b060f0f040b03190b010e1b041206090206070f0204050618190b03100c0f0c030512040302070b040b090a080a050a1101050405060309010509160f1a0708070308 74
    0x4040c8010703030004000501c18280070014580a80f01c03912030701180001582c0c00f1440e4210400024140b0451400c0e12002e00c1401003a802482203c009242c100e4800303614a10702612002c6242030b540c0105015010300001c2040200b20780100d41030204003d0307016113400180140290b001a01a51018100b41c4900c0c0d003241c4018290320b058410a60400360480d10342c0140030b6070000080b0040e5004104103200a5040d400010440310341e00a0310420300010241e030794858480115000030400350005c580000c01258078003c0c4a0b0007848420300f101e8050b01e4880c20064150038241420308014400c5045002e070f1640019601d503103c0140014080e4500e43d40d440d5103003030041c8144981d0030b40c03040c003050740070558080200388081504c1c2c08640d0001011600240d02c00f0060300c03240b0072a4407660700f110380081004403415040d804240607500c1c1000707403030742402c0c0710f040c40c04014200c0c018880c250b02003200400c01118011076030340c00424a214800c1c00d00d03c0d04c0d20341c00401d401140d416404038102340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 714412239 1250 714410989 714410993
    0x10e0601090338130201030e031603051c0b0d02100905040f0b01021204050d020d14061003020102010e070308030a02181e0a0915030609050a1407060e010302041406030606070602030a09 81
    0x40b495042007983d2680500a1600d408001302138101d40c24081d05041d918030f10b0340c01d030007014402c84080003041c80a12029083d1f40c5001840c0c0e904c0001c2c002d01d1841002d03804916882c490042960f844002001c5852031803144d000c0100f0300d02c1030000c40c002d2044a81001540340c540c1d000310600400b0003900042d040d09500006400c1c880f40e5541c2018403842004180420307a9180600000660181c80d1020780110621349214074070b1821020400324412901001002020036400000303491007039000f88540c9260b01d800d20f0380e680242c080100002014000154036031900d9001c0c00310301c000718500110007042c41008c00c5101100c035900d00c092040c0c032900c0305601d0070003201000040090150400031299018100740d90341c1d50500000f03203525258109142071013420002e03400040c0d0807040038012000d10501c011780d68a9544078200c00310303040e0074800700658002d100b59411641031341800084047e0040030800f070381e48010002030b403007601884502c0101e06244099845000f103000d0000c4c00078018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 714413489 1250 714412239 714412313
    0x71806051b0303090d0c152a020102120a0507030b1507030e090412030f090b100f06050c06011502032b0f0b031c0e04180b07050909010e06010903 64
    0x103441200c0060b441002031000500000500041c200010710300b50700a02c1d12840c000f04076131805034100520600f418650030506407510740f50300c41800d060049001000a100c0143d00340c0c054140179541c28110400040c2400880e0303000a54001755a180000703a202c40e003c0010398110034245030710f00f4078601007200e10415802811500841c4000c841002e203a151554a4078040c1925075802010140c0303c50046641c0c156a4201142403644840050030618081c80d81c010144001d204111180c0c0c1040d0740052058011000c40e40c103440311001902d0182e0034901e1039804941400d0b505000c5101c10808058042c0d10071100c01e003a80921149114007288020b049402d07a00088504e40da214a8600c0155540d0380c0002d0700c55100d80244040c07032180d80502d20580e0070030040004103400c9800c02e02150644001500018025441070120350f11039102e00c80101d425015454010b60000c00752001840094030207000d9980c0298140352001c034103602e85d074400c1c28021281100c900b080b010b80c01d0b140b01380c01d54 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 714414739 1250 714413489 714413527
    0xc0e120f0a150f1506032007120201050615040b09031c08090606011704030e0f04020c010609140115080c072013090c06120b0307081516120507180605 66
    0x9107010700c00c041214059401548283c81503c046c0340d910b0944c07000c00d000f1044240c00203510741c204503880d0300c42806c1825210489003420001540b803c4c0000d841d41c0b038822105141001101006400c06040200983d00c03070303110942c60361745440b42d09031801c100030b20414180c689004542d030350846400c00711095403a0a40c0600b031107043c80401c50000c82c13809110607466620542614041a580c0c202c030000c1513400080d211441c0e005400010b5000854074150810400c540c04a10308102c8800f44c010009408102800355190070502808900d07229071289544582000300448194034108490b80d07118081200071165910740d10540611940703501d003d003031900b0001d0f138240c02404007480039628603a6020036406000207010b11000502984030f01548100000d1030080c04407600191186c501350740e0350303100e40150f004038407a83c0c0c00100c1107100030031590f0311129207443d446002120303001950090b00c00100480700300040943c1c0c03440340c02540e49001c0010300f455181c0e1541d0b000c89070300300d01c00600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 714415989 1250 714414739 714414761
    0xc0203040b041d070224060d0210020d0f1b0b060a09090b190c020d0807050c010e06091c0e0105030a1415030c030d0801141f09080705040c0e120f0a15 66
    0x7003154090700040142c42d1881e49010300e06d03a80d00c0c03207030380b610000358404402d1000690804180780040c21042e03000070342c41e0b50364000798950103268640740608031a100303180b100c01c049420b2401906400600c0e0484a41c0c5c210100902c001c0c501d0340c94091940032540014825102810300c0018002994072032600c83c2c0c00c803286810240440444400061364400811802d40c0402804000003101e08e072048040d140480c81090080c0460200703500c015965600030364022695003d55900400010008058071991803207940300c0640c2078082c00019644ca800080401d00016110000403420900d619000d0b841003460103804400310f42c180062600e0401c100780200e009030b006c840071050a072b401500c603604440450620b01550030301040800c1484404964040c803801d440030301181c5a681214810302603440c20000c072060144d07031700304110640c2c03002405c810118004040300d20503805c021041c4511b00141d90201d480c41200ea0322628a8444c0c028000d50305503200c0507a080b0681c0072409500e1440d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 714417239 1250 714415989 714415993
    0x41b0501090b0313111507021801030203070b0a03021605030a030c230d0b0d1a130308060f0a050a06050406090b0702181504093806040c0203040b041d0702 68
    0x2a0030050900d04070712004d014262401c00c182110810420381583ca411140701c003403e0b58000e403020800210907600007550480c481c501448101c2d040039a00c8103064100c9800a006284c194500300800c11035510000c120010907800700684100f4442e4440040a46c5101b680112f81c1c2d4010681c00400b141c01c290301900030402031109100d040c803400b54080140d03410414034503540c3c42c280c075194801440b842a880b600f08440b00a500d0600c4604010b5403105c8846800c1c00003140d48000d01030301c0400c07581c20006c010a07040d00101e101400c04074441005000098090000e068450000403950b41c1258000d100140f0001414094940d11500d00c000916801040074148a05940007030050040d041803040340220b1075001520180c2ca4149189806001800c10840301155041500380746003403230075a1880c4e000320440c1c16208901005007510344d5a806a50100c00d0300c4031000c001c0500700c02d00b1070500314030061001043c2040341c5801840141490180c8110840ca200c040e540b5a80000307084800759 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 714418489 1250 714417239 714417257
    0x3050a0c090509070312050a020312010803030f150907030e030d05010e0106020c0117010b030c07080a0e0f10020718090503030a0509010c090e010603090f0503340c0b1e03041b0501 79
    0x40c013406d00c02442c940c0389062490702c0c0d00c07241008925600822040840d13004110000041e07c1d60040020350142201d001d280407280e8801003202e58000031000e5150f00301c800e060026503a1403181d44016420b187d10340603246066150303000501501c00070b07000006000220801005850340400c0680e03803502c400e080c01c1c907800d18580210080550140715640b0028000400514403a000004a696290380210000c0d1214141c0b0030041800001580f2180541c02c1d1103a4801d05142892940c05501c10650080000d81d0415200c0321000e0305c5682d43e0b509840d220502500054810f0000e075110780074212000030f0034075080020900391040070f40000180602e0707400034040c1060110042c0e040d81c16505001c1503004161410340d502c0c00036444041c001c8e000c00b2801c02c420ba52420306041504002c3c1c02d20080c1c5c02d528040c0200310b0507091a004060144024040000c11128400b624502c003118842d210440945580b0070381d6507004903411108034411502d000040481e410414002c2e01083c070b040007407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 714419739 1250 714418489 714418493
    0x406020f0a0207080d181436070905030316064808150112090602131a070f0203031303030203040e010f060906110a061a040b040506220603050a0c0905090703 69
    0x300c0c1060300400f2602020139840140c1601c524110b01b5404075040c0e802c101008d038442c12207030700c2550144500600482200400c0b06544105003000a54100030059031406000d20b29414402e500e00700210f03540c60300d80074031b400c0d015401405e83c0d00a002009201110700c444065108410606048004000750011040a100b40d80900346030350003039244490350700d540e00480041c3e5840d400484045040b9091440c440304000c143e402a0820101040341559016120054a08201003050303d00040043c240240c501080712041d2603000c0c18005800e4903e41620b0159400f404a41500280c001d6400040e040000301340320009180102036420070403100c981400d00c001d002580c00d104074410450400405c440040092040c4880305078004d004000f001104001c189900e00700e419030501c10b03441c1c40c0c0c803016641094007485110f03800c02007140d115021820280380047d1140500310002c19070341c241c00700004800f0000316140c280101c0961066600c2c1036580e1003030364070051900340d103600402c0302000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 714420989 1250 714419739 714419777
    0x60a0212070809070b04031202063103030b1302031f08071703190f09050108060d0318030803090114090c090406110f0d090b07170402090406020f0a0207080d 69
    0x41c014401e032814081544a0f04002072400c3c0840d0441301c458040000c0c00010456004003401500c02c1907000daa2241c1d07100b04910480401c5140d410005a003d2082d28001c05900a06100080c1c4a401c0008000c1001004904201c09406011130304990010600810064809038054406450365140e100c4609025000c1d40740c810a02c2050b14100c0c0004550062600600580304c00620a43e480880700c0b00c0c103070b0020001407020440201140c424070021403e54481d1510780d1181c28042d104e0400540165404c5848504a0444083e44454040c0c0131000504620080d4082c40900001060748080e400700c0740c0c035420001d01a8071346d0394882c150055203911000300b10742d4010f40200001540c0c24407104081403d1144555100e012180000c50842d1507001d540146001b900030300d10308440e981e800600f500c420208400b844580120080001c00626228101c240d206214100250408000030100c080c40d4111104500150304410414031a030201000616101e443c9880c240c1c400d1103100f00d200c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 714422239 1250 714420989 714420991
    0x7030203090a140f370f0f0606051207140f0a172518050c0d090f050609030408030711010c0b0103060212220609050f0f0f0705060307120905070e09030903060a0212 72
    0x5c5100110003609410720040c00720b43c0010701d03088104040f8141851814034001e06042c05010b101d0700c07070550100158400050340c001500e5242240d50710a00c200c0d4100031103090351031105588001c00840115000301c041f000d2009940301d1800800000908101105134001440d038034010300704200408004600240c03800c0e000e264000c0800007540d440300c40c100551446403090050125041060400c100002130302441d00c0140902c1c29034406d9282c29005079100c1c0708a1150340d0440e070083c0204000300e0030307204800c0703904c06050400000802051380c6020581000b6031050702c140c1d502007031880d0194801e04403258081803517603003001510603003c4500015200e44d040500078a0b40c4200b541d042100c06c010304101440003204541c1c002000c010300c590307140c8400101c1400c074050024005807505100080c2c9010340800d07154803000c2c00e240400c0000420400006803001d1007465400142c02129450007170080400ba4080c2d683c5000342810305141c2140034100d00800c40c410410000001103c030412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 714423489 1250 714422239 714422323
    0x30206130f140f0f120d0c0506060a0f031e063b030f0c030721020d020a030f030c1b031d010207180504050f0327010c0b07030203090a140f 61
    0x41300030001c24804241c0c03c000301900700b2502e100b410700700e1072025040301070203110602c01c43c00c55205640d00c1003400301000e00c91040302980301402d841400000c203041d0400a40c0c4031050807144004059464000980c0c550807202a4503240c000750340f00410040042c0510303044150801c1c2000c0b60003900d0708542c0d070b01c036815460411040200302c1290041c000c0c000c480c800380c2c100c0060700364800760219190100080c000d0100c094801c00c091100d4040c00410184001601916510061440420143e01600ca039814000412480200d4083e00100b03030081049524002d40d1050060070702490700d0740741382c000c22092a05541c002c400400c0098010103109403600e405d80008a075a456928141e85441000d04a500e0382c0c1c04041007011a01000c150494122402c0e1a020401c1da01924010b40f180403108030090204c12501c0009100c41740a40c00854200c00c1c8401240d00c2080c403502c0e440e82c05550503000c508541c000030700c81408a50104562060700105030040c2500803540c00500da0082d1544040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 714424739 1250 714423489 714423499
    0x100503190f0204120b18070e070810030f1101020d110a060228030e10020405090a1a0d03050712050c031815030c0d06090b0609040b0604030206130f140f 67
    0x1010241e441640c060320000c100442d652241d8071041d10b040100300f141100d001480700d62041e0449012280001d03a5021034602c0e90f81c00c4900c1d140c03108119440030005081d05c1c00c00c0d100b030b5000800121692000610680205044045443c0c0c44d0002400c04003224000300402064841082040202091642a0b03542c41840181d4582078a44010105401009249090415098034085958041d00320010f09400c0c0f00540310011004000c0c07400702d0107640079540d00724025800213056500241d0080003207500d0601e003401001130500006c0c03e8001d148404800054010a0013410080403000e4581e000c50141016400c01b004109440d5980c0100c03071750445800044100b800ca562648002d5400c100d020021041e524500041c0b041c0456000107941440145020300c0004c58004a00c52070100c0b8200030103892600c100c010420001d0911001c810794845d070304010010069546d50001c0003038450be20180e442e0719240c418200c0900030f40394480c0030060719940700e60556030340301c1800c80032429003225 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 714425989 1250 714424739 714424751
    0x60109060e120109170c07050603040f020103020c010f06140102060a1406090408091521010303081308120403032a0818190809030c0406080c012a0b0610050319 70
    0x2d8034094544072001a000c900c40c0016110b801c00c0c03d5004020b6038205104542403d540c0d03c0612178144001c64000d441140840240c80056200790000c2048074038101c00130440101100460040f240c40d503110708040141e21010030310300c0d60140003042d800103074a482002504e14400c100401054014a058070564241e03002500f08941031041d100f8204e001351107009600501c00c40c0030300c1540311182c0c0e0600078000959040109294011603030589515942d200340c9a212103109207115252404100d40c80c00050182c1c181c01c0300151301c0300344a00c0c0641e4002c10010104041880c6071441000a00c0d89292038170f11182c010350300084070ba60408405284a10910415500340e801d01d58030103549042010080f1003003090180700000303000740070f10803000d0301c003190110810402140c010340b16400460308401072303070129580114908080050160014141c810446940000e2451060070031194210070600f07200d1141850407645905d00d6035800c1c12480c50038500d4106201080c541c081041641c0c540e2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 714427239 1250 714425989 714426019
    0x50f0d0309030c06050a081f090b030109080f0702180c03040b1b03070f0801060e0109030f03030908070c031e021c02130c08010905070c02011d0103021b06060405060109060e 76
    0x810980011604045030462076522030713200518070f03840403541e000090310413000724880e842072003104200010140c0a003603515240c40c503810090326030150f4169140d5610f0032044080740c4c1c030f01c00501d80c11088401d0140d40e44031501c100a40c1001c200401e81e00d0900b0340781000a4820020126508150484080a82a075076040082d803905c0c0304540400319a0313004001c1c002155045502e011081c0b000d900c5080c116070300d9840484030b6a204003040707800150705010400c00b16450481c1002c4060180c0744c045150125510b4011442d80308120441c1d0404090a08000740701080c030344018007007682c0155822001080e000a41004c4c10041171200961a00d00f16404640d20301c08500c203484900c3d42c3c2445000340030000603000310024410340212900780000240c18a215280c41c105a542c161280314501c0ca400307003501c81c000000e032481410b241d0300304200b80001c482c081103454100b2080f0020003c03860194140401e0391000b41c130050600c101d071402031101c1070f0440480c41104070141d070204d16200c064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 714428489 1250 714427239 714427247
    0xb03060a1e061107180509100510061d0405010305070f08030a0e0f04060e1303080f0606041a07020d0c061814060a0315080c013002090d0512091801050f0d03 69
    0x280c2c4007903c04501c0303d1700d4075141840e58100512641410080c0d5542c1d01402c0c9019061703c100b1505561207032101d0105122050103440320110010324441d500e10819000004070b01158000c0c1c2050381d455001d107104206e80c04203107401c1c1e00a4a508005141070a0b5007610240601c0680e60315544202007170b1190109503151540038100801c1e100c1034401007814100c1d000790603030aa800c4103900080c0100001540d07000200403072801a40044c01c010700e0720345004032508210498041d03007180782c80100a0000503a440c200700a04240c01104086940d5140c5240031b440c80c40281d0181e040e4506052017040405009a8101040030003540c03810358843c4051812130060070400d8080a80c0302cbc0034003001c64800c50000e041440c1c48000e896003e00000040c2e410700360f648000d501d0341282c80c0181c0c414014904160060104090081d02c205030301c55941c0d890074142241005825440c2e10040760040242c9406c0800e400007100a80484289505100200d05641c1e080c1d21501c2c083c0e0740d0110703000101407103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 714429739 1250 714428489 714428503
    0x2030403080a0e0a241704060203131a07031a180a0908131d160e010c0203060a0e1c09290f0301090c05160212030c03040b03060a1e0611 60
    0x80003401c1c51600e5200010410501703051000040c5604010241128020400c02e9001e40c00240b03088004d98842d175400010358001480c03100c48465000e546400240000150340956410304801c600c41c1c03400c0c640040c2140e0401400100346511240034400307a44600c05d184a415086a90f0084240d071080e07140703000742c805050014468440016070918074050000340c003064500039004410604a400041001182c082d144440c456881c003108402d0b4500503100c03a0001c007010b062150f202e00940e00028100701c2e00700e559141c03a5440b91141041e10b00c007400302c0841c12545558500364001c05800080c20440a0b0007440c81441c020000b003005a000d0036041d6880300519011507640e62050388501d09150000e106444005044c114100001400381d42551891440521b10b80032094040e002c02c080c1140e0340030400190b01080120000c28001400188041c0183d1003040e950781c10034205108200b0510340c004058018600302c84200300c9040c44c540d40480b500341c80c0c100c8950104c481034500b03140d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 714430989 1250 714429739 714429767
    0x2e050a060810020706150609180b180a060b0a05040e09070302060c070311180703200d140609091906060506040e0403081b041809021c050706030b0102030403080a 71
    0x2264100c0c079000b4a0301c1d03400506040748109003c2c030003224441c100300c1d40c400039030042d000800c00c0aa07050041c5980082c00005181d0550b0002c25132208050104055100d043c4a8201600d4003004001c110b00701406000300500d80c4d8920b140c68650562801812405030780a00441d040c0700d80d01148000c0380411403007002e16001041965500c01c100c1040b59541e041e440102c0b81c107082124000300501d40409060146c1c80c2c0b0840d120300c0340daaa07202c102e00410600b5000242c201210750214280d842800c050032074416200000148103c1c60000071074209001070200c0e20a9015004120390400041103440f09454149948881c0c00e50034613056010f4100703a00896040304011400040c0180e0a618082c002c070b000351240003071034541d001054605000e41d250000312000400040110717018004003403213200d404400000d1b03080c9096000404d440000401044101c2c85290950140481844003074010007507400c082000e030848900203500c2c1e00175407001034002640400c0e109a42030150582603480d00f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 714432239 1250 714430989 714430993
    0x213030b0a1d010c020703110102012d06050411070b0705070503070c0e01080109030c0206090d0f0b090f0d0206150109090e10060902070b180c0d050d022e050a0608 72
    0x215004491030002e0001e10801d1040c5901950809102c00061003008a12183d944c040d251503800d41e20b550540f461200c0c50301e8110340da618411201121208082d22031401144038459150000c408460143c2c2c0e020b40107544610316140071814080105c0f000c48000301c1c0d0021001940e03030f4403c9400d4030103028582010300940400107440e010000e80014080c290741c141c00000300d141e629100e0140c00c80301d001e0401408102403000c65030161801c0b4024001008008108000405c400d90ba00428100c47d408200c440030143c209204e500705081c045a646044e44100400890200c810000d40d5200040d1000030700b0380c0e500d0b000d2955a4400c82c002005042450424856021b61103481503848800144092a052414801181804c3c66000f02c030642c6805c0800042d064640310364110305003c4088200381d0511030311075004002c0d00e40c1d00300e040d0143e0140b00034145c20011044080c0c1041c090304102d8100c01710b1200000000c200206058542c1e038825070000501c0d42c0c8481c4200001c028580081d1294 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 714433489 1250 714432239 714432241
    0xf2403040f1a0903180a050a06020109021e10050c15130b0a1e0519060e04060f060b030a1a122506021e16060c050c0a0501050d0213030b 60
    0x805044150703944118414406055284003003451510510819241c24900f90001c015680d203c0580e00620000d44000404500c201640d40b0000340140c01c8503880700f40580d45900c041000d62802c6104003165030102100e2440e2500e070100007038002504001f01c0c105009010507480d4102c03608100b940c44901c10044201d05506003407140d950083c4460310102c0b070000c03a810004043c2c907035034015500001814400250750020303556030700380a44401854800d19908400e40c0e0404039003035008840060a514025840303609040c20014141c407c160340041d001402d120b01008100c03e07290443c0e601543c803a80015241c20a07801d428402d0451481d8140d000c00780c0e0070010704250022501d01502c5000080d554441078036900e4200c006a094030a09000d6000300741b03503130300c0ca140d4881248030b800540f100762002010700401c18a103c00d080e400c5840002c52440e0000c041017000c02c0f90b8808604100c401408051404000800300d204101e00c0190098000c01da10307880c40004142c0c5409194440c5920070710f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 714434739 1250 714433489 714433493
    0x31104060b04060809031210180c080711210301061b08030402060a17070206070f030626031209030405011b050d050d09050709140708010605120c121303030c05090f240304 75
    0x8c2d0795941c1c0501c4c61045c0920b011241c1810040c0f10328a0202059140c7d02c10994401b042035404811082c4008118002c0300422070720002d003044000d15803440303610026169410440020410002254180030b03204408240714013003003001003070329070269045449540d20381c40400116940c26142035200300429100043c080c8464000c1040b5124889903901c100b0240b040c0170007201682c086203c0c1480c20382c4440d0054454030550920b407100012118101c0c2c1c0381030308105030b01190031070880305030703034650000305044c0840d60340250f1200c11460488000d42c4400c009450780341d160220a8108024044001a40c122040071364000200041d00b03d003d0301c82007640c40e5501405411110314888208010a00040240d40901d21070b038161211651103a007065001e2414000303c14000e04814421030080c4004880740d0383c41040c681c410714600e1814025980b0904d0003a0580c1c01c103d00c41802c7c00002d000d402c038543c0340c110b8100c104140482d605d2120f034040c00000381c4040392500704000201d20000030001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 714435989 1250 714434739 714434761
    0x219020106050102060619140111030301060305040506240d0c1d060f0406210201020102041a0a02010e060601051c1104030b0412080f06130e0303010f031104060b040608090312 77
    0x100b215020b03021386032280c0c0c414040207102010200920941c0008000502010a0800e681100d0b018103043c0315011034801c40b8a9480c2d500244e201400007a1240c040104200b01400013039080030011350400040c1c5518520500c3d0320f0101c03003105005003110003842d8184500e80c4400c400601c0508828500b40780c10b4840d83c4c401ca60704944860044100c134001d8890f40c00c05200c3e0314100c13910408031080956050501040912440c141a030440d074081c0408101e0010030940d400616101505580c1d0361403003100040d080d10140c800002150700100c007003000304e0b40c001d0221405440d8140d8000310f1070801d403040b20000c0040b8a000000c0240201e8048100951204054080d602031f400b082c82400c52608100c695100480d00b5084040b0014041080c41c2003424400d64944040300011031541a1410ba151954009a00208245c0d24450301081404846003240c070010700140c6090003072a040010f10720440c4100d1144000708400b02e400203030741702c02c10720a403060681845400d031070750b05008000704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 714437239 1250 714435989 714436001
    0xe190f11130e0c15071b05090a020307121a0112020d020a0903030215100b031513020306180105100c0c091b030509060714030603030403050f061b0a020307060f02190201 74
    0x6160b030303c00c80304280c0d1685030514859004a03824102d051400c100355840c1400080405441c01503d484090302041c9039880380d24081c0701d480241001a1680382248000f400040403409a034081c914002c0b00c001c41a02d003c0d030503c50104282415202800841011030003441810b408021180c070128090720a651301014181c04c40340280d086680380031041d030074001d202006035003580c455903196604000c18900b490146901c03007100c1d1000c40e02e411450012407005c0d41d1000c104840310364004200400d03840c04400e4046c2e85c540e600402d100643c101008501d14509001d5220140a06042c480041250b28202d22002d032402840a11280b111610540c404440300c1e03c104020a06180000700c185100084451142d0b04903914072881ea2200ca040c0751550f03202038909a0180030070000840402d00030840312003004002d038028078152034030110b070800c0040f02c01c40c04645513404002c0d111030a680001560065900722000141c03000c01c10102d078001388a0f0300003c0706817460042d4010415a0194044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 714438489 1250 714437239 714437261
    0x140106060f08010f090c050903060f01050a0f060c02090423060a1b050a0e01050c070b1305040b0d1202070509040b0403021b0307120f0b01180e190f1113 67
    0x2041c614020244180d404010074051a201e105a4080800c205807480d00074401070081803c15502d44111840403d082100441e00010484141d034010001c60804403503200061030803244101002e82020401010001d891002900c074400c004046800d21003825404041c02d281c01c0e940780310b10300fa5410803070340302c0d00200c3c1c1d03070380e0702c1031030204000e2050007030030a0004a042d0660301c040c9070006400041d61108a601a001d04010003403192324120401045500d028204c0420490f4803580e00d01e506010425aa80181d0300031400c02e80011044d0319580c02c01700580c1d6021400c2c1024100c4903c00b203180c450641e0105621041c00f02c00e01007448010030b43d0394041da02a50a0301c5211000c0d030152816201c03501941c0e9015401400c01300b104411349400380d034031103100d10202c003044002500e0b0281181ca003a0407889a078a14020081540c182910a15035041e481c034002e054403500c000c80c150794070004400040d0584280303480d10340800086101031000c0480041c080f801110180320180c000342610030075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 714439739 1250 714438489 714438497
    0x307080f010525110a0b01180608030403020603010612090f0f2906130f0e03040810051012060b0316050103180c06110a05030a0804060f0e0a1e14010606 67
    0x70440d0307071892036408044070208086071003d0030007540080700e01d400d20154148050080d420040300180c40006014001d1480074041080041242c4007802101e000d0341c0010050f90042000f00010f807104070a5074111142400c00e41d003400702088011014000814002703185501f007106c50300c104105064007008050080c0b6942007684200b0322903140c08421808038a000c500325200003802e41c6848010071641059030303039020500690880b082801d962015075101000e800200f02441003d000300001000e640982106014604240c003ca03190107005000b1103118460516094040c03000e681c001945c1220003400b00c40030307214030060344000d100ea940140c900080c00d0a40840f10780c4031986c03185840303940002016010503e009400c1c1d501013a01c40040005014154400000ca0350500180518030016190700149103000e2815034110b4440110b0703003c01c903181449484c0c90080004182a150f54800851580802031200c070101001c0100d400508010105105003860380301900300c00201c54560300c0e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 714440989 1250 714439739 714439741
    0x9030711040212010b0f040e090c040e0607050d090606081e120a0e040e010b0d0813171c121112060609060a0f09051518031f0b0604050307080f0105 65
    0x41006070300c180b20540f0580240040103002c1c0e502000020000301e01ca5010003860607584030382c2480c01d010100c41004154001d480782070f0050030540203a800d10766400c000350540b0300e029103000d000360244000c4084210f5486070000d00b00b04441c1e01030800b0307220300811900e034068040b4085081406c900603070070540c001d071911216a11000750544030021050344511a5003140401800010403240c2242c1041e592940e5182145440358103040070303040d02640e0902d0356150079030003030400072035580e000b08000f601441c415044200041440d15040d509034003030047e100d503c0b4008803100c1c130f0214511006645403181982985a40348000e14100d0116040380e0b0b0035980e0402001720034021010081c2d04038904200d0108401e200ba02d010079114034505080407034070b46880102d004002004116100510006036040c01940d5130300201c280700390214014000ca510045154160680041d6040c03811038803404904e00a649002c01d440140002070b0441e000e455840030a595a500c104901901e1946440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 714442239 1250 714440989 714441023
    0x12040801021903060b2b1103040501060f031e1109010f050f03030f190306090203040c050f09013602131a030103050c010f050d0e0c0f1906030b010c0b090307 69
    0x2c001c000403110560749090400c0085008000d00c030300e0742499401b8000f41e0605030b040c424590322030079007502c03168035041e6140c0c541403900a00319800e03a00030a01d52080260308100003600201e1500c018009003040e00300700e00003440c18080f1504251462940540d1060000c9240c01e5011142c9044480456410031a00c261105264507403094024000c1107900c200481180c0c61070180740050000000d10f400212070f03599a100200700d800c1074508407440c44841f00204407074501600c0d10341d03e03480102e4003130b84994034040109111039a0460301c038240451154140d0201e07c000e4408130117141c060b00b0259590000045001c3c0c0b10500f900a80710808029102075445030061010749041e01c0d44007009010395496407005503880d4489050301d008015041103c0c11405149000784d0701c0780f4034080010402c1e03406010800800300e00010010380107019403074490000c50429202501200c1c124180000c81e5914400102c90200d84140c000d0421000c150500c41000e40000c005c001c0d0798018030042c06298106 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 714443489 1250 714442239 714442241
    0x1090b040b030a020705071d160206060d020f030a02090a06170703050309060f072901060f02030313080f182409040507200705040e010204030506041412040801021903 73
    0x80c019081c07808014030000351a207105a0041c0740b040d00030411189103d50340c07441c2c1045100d1405844c174140301c2c1d0000b480712490720090a460000101d0018116910b01040400c5c0d40d070704c01540103413040600e046009050f13101813000100312034025084003820b2a108002c0f1015010b0303840313629911880603223402c8513401c0119403181680d5002028501c0c200c207440401806800280c601c20001e8000c00c021400a282e0714102c843c0003406178191041d90a80007800700004405a100d801404031140d032a041e000d40c08000c890748186800780c0103a482103a0305007100240242080041164000540e009035070001c00c19224442c6800c03660074ac4114950340b0011545407200b114910b038401c050150700e0342071505400aa42c006040c1c6801040680047c0c0c4d008013224580301c03160316503003018005000d07a082501601140414040080d440c0034516a141681c030440180064540607040c614800d50361024405c036103081c602c041100b5100c40e01c68030890b000b0361110050200103a08440181029402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 714444739 1250 714443489 714443497
    0xa03152c180a0b040309091a01020c03071a03130f0c15020d09170a0501060f05010305010902031005060706020f071101080603060f070c0f0f06060612151809140c01090b 74
    0x444007410720b01c0d2040d580c0c011808000780c0210280003001101041800c1c40e4031813500781c00103004440429000b000d0019041c440c103400c0e0a406030300030030341c18403110355450040102810803004942c1e4a9036205e40307100034800b2402d0000e19401c0711440c1d407014403241111b1142a1a4500e1521402141054040c0e0382e440e9000710100100f98585403c2100d110341015003401c6802d11400e80d407120b01076a6440e400c440c4640c20184941c070340f6400900143d6070611032a0b01500f0212011480c604202d0145807444400348619441050005800b100700310160f011b9075138086100301511b2710340f0010304e000552a482d01c0003840c0012481000951140b40c0040c1d10760080c441224481d00c0758484400484080382184800d0700d006c0740d60071210000560782c084030101d0354000c0f0000101903003000001400018007070174840c07201c0d08100c101480c002070b08040c4001c45080c036203101c3d00c4d400b0800d1107030050b04d0804000b5126060114030410310140101c0c4174180420240d0b035642c0c4480c5c481039061840c0c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 714445989 1250 714444739 714444781
    0x1b0605040e0412030b09010e090c030a11040c05070c03060501050f06211305060f0906061e060a090512210406021e070b03070207090f05010b0a03152c 66
    0x10301c030004200441c0da076500051516807140b4000c501d402d0328070042000c83c18203900c0600313034603071500811511034010720940901078002c0340605921100d9880c2c540c0b0541050400398811507aa000001046000c1d0003141c02550707004020300310260b40e80c00c0c6980244000d01c0b890b4018107030188100028500302d0100d8800000f500300318a070780ca2a0b80a008103009009088c4901c007081404441e001c40d40401c002481403407403ea02080728604180d00a0030b11002a121601440e01031000040324038034450759215194080ea40180c40e0814a1000c03104240b9a03802650080610141491034603030124148410946070100a010001d00200e80140e900c107038811480103070006445042468941528100400e000c00c00300c2d401944c969107a0095648240c1d110350141e4005d88081000c5621340c040c2401c0041088010080d075031400405125900c12141e06004040d03583d80100031074480d80c1015400f034030401344584050320080309806503c0002011080b001c00580340015480c2180b000b04003030100f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 714447239 1250 714445989 714446009
    0x30604080c0601270902060405031b0f090108072706120209180c09090c04020415270b0d091704050f240705010605030607050d050708090606060d0204030606031b060504 74
    0x1303007890509000905185800320b9101008010004e003555003080b800c0c1043c8004c0071766220521921040000c500c460f6807a8600a45002d0b004000402010514508450405403610300705818031030300300719214644c1c00803c00d203890031101041416a40036034a2035a4030070344102c0310715114a80d85004900a042c0301d40d0745a400000320020174249480415082001c5501311107280d611000000d050b80c00c0398100581c0d91755005181010f0036400f9407000c58035906c10700f05040d5400c0b4480c00007040010b0b40504038a40d180040c039010b26041ca580442d10840d0084e0005921005d44150100d807a0b01602c15688103080401c045042d614007142e00c55840594462600952503408103e03542d00d811045007900d0955030303264000f0315a201401b00314400c900980d2866950300c0f0b0000d03624100c85020b007800301044400c1c000c09c5880c02d8001000364114004440b025125200e1204e444081d10aa03000201a9810a03100008205801c0314107100b00488c04294214540c850404071054015485520303081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 714448489 1250 714447239 714447299
    0x7090e010c0207081f0906020d05041205121305030909010803091509031b0613030c06030e06070c081e1333081e1602010b0a14120309030604080c0601 66
    0x817064003084184203101190101c3c4500eaa5110074040360051810882155103803420401004580c6403a024a5540342c2041820a08514614010010010490882040002c00600c14000c082054501200c80100340032525a15400d4503600c0340c0001d134000340184a103400c1c800ba42e6150200fa55506280036005001b030300f41c000d0760000c58004a80c452a00000204202611003140b2184100590300034400400d00600c1d101008041f1403402c0000c2409812010178440c10300d501256001c01250001c0815441d03101c00300d504442c007880300b85041e0790f40b18002492158a415058804100d910000b442d541451580e01c40e042c11000002100e101010307a007809621140c000d075441500142424410088a90340905010280703106440b0000b0740303168815207820161382401070098200c41554040c50080c40c003e4000c2610001c032003071034400c4041c4c8021444060707081050300d04e8400000c0448285040904000c1041d40c05005148000d0080100200f6043c103800940c1d01410718010111342c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 714449739 1250 714448489 714448513
    0xe0f0c060906180f0604090c021b0303030f180a0b09060105010c0503041e03060507120b10090b0d240602011b0f180b041818020d0807050f07090e010c020708 69
    0x1020100d4a00c281c2c0000e00304c4034084141c80e07850150014001481c00040c24510f9040041d01c1d010f20501040244480b4040964041d14040140c0b6007164048803c02c800d9150305080420b02d00784480321588500c169141002400111400180031740310510640c3c2c0140d803900300440f003140c1e40400c06807266104100400007003c14a03042040c025074031000c02520f42d00c0b44e0310117084c3c2c0c1040e14200001280058010750418051040000344030f0704981800842030381040c0034001c0009882400c41000c00450318050781400e0f50440c2070b07280d0302c106170b00d52803c0c0300001a42d400c26440c041c510040d840c002d5158040744d448071a5010300c0c003082d2a040d1a03c1400312007190303c03d0840100485d41802d00740c0014440488102800c06091003240315034410710860550b80848510b500c4844002803215000c8001d6111a207003d000b0a8005414076a0b450440c1049464082e045991820034400e1007000912840c05902c5071048980b40130090201d5a1440000c0765101030a0140c02401d411011503148 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 714450989 1250 714449739 714449767
    0x20108060607030215090f030711130902090a0903030b040e030a17040c030807030215010b0315091605130b0a0c03031a03060f071701080703020f0d03080c070311010e0f0c060906 78
    0xa8082d0840c000c0390380010030140001c1c1540c0000008a40081111130200070030f1034100040c03092f02d155003004210100c1d464000400c070302c00103040c80b00103583e036440d801c00b4140300342c00100038850050310510041c02461011a40d80c0d0004041c507001407001c40355143c0d04601c00c07050358080c9400c6a1440b10302c50564a4102603070384030303240071000c1d48a94141558074000103c02c00d8020210441000e0300c0340f812040800e100400004003501c5018520104014110082c040345204690b0b4504161280019400c0c1d190241054004080304500402c104aa80d40d02001c0f00c8403071442030303505000f82c2d000c038000c920344860014074241e03044d001400051000340300380508aa00400b240303440481ca000ca414032038000d0034207811000b01500164018000e50a1002c18494044426603104c8510005501e004000d88409040b803900d03018006001003e052040342c00a03004c4107080004c21560344034241c0142c0c0c40c0d2a83ca5031081d24010391740c01d204540390050075103a04000181c00c0b181b8041a03052004e07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 714452239 1250 714450989 714450991
    0x509061504271506120903120e0309060c010f0f0e0a0b070e100e030f0c01080a0e030f0d090c090c05120603010612141b01090308090112021303020108060607030215 72
    0x40220340d865801c681d00d045a0041050950452140306051414288000e0403552605e410b0303290603007402400000698880342000340f10210040025501e448044c6e51400c520030012425480140801d4016501e00c042d40a007075549503c071700c01c0050400042d840c0d429a001c0c1507014003280c100340d11090124400c03001d80c681c001c84a10b051550080150300107003900b001c40c4a050001001c0da14548050f003010070058003981c038134074010000850385600084c50032038004c101d4040f03d81c48084550307000100b00159541d50f14003003100b9031100350102601c801050344e03403400d8682c0c010781e4000203400105403040110801b0740b503a50a00c2c0c40e58681c6502c20800000e13100a806650701d6400141c0c0c0b20b0340c002e40c542c803c0e204101310f0840c0d6181480651511f614503a00d1400c44404032000c1e141a0b0700f000303001c01203d40c441001901c2e801c04c2c40041c0e503024075401d41c24000600014110247e500c0105081060364401d80321810540c4a240910100b4003031003000901581c400c0e00c0c101c1030503000101075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 714453489 1250 714452239 714452279
    0x5060409080a030f05060d050a0212012921070b09030a0f140d030c0509151603091a0702151312080909150102060a0b0103020d14010509061504 63
    0xc1104680c0740e40c0d11906030b00151080300060341c0d80a00070a41107944c0201c6800c46422914002450500e4031000d0312046106d100a210b1201440c81e050f07268002e400120a00c543c01008105941840310030440070074002c1c10342031040200d02000802e966400e500300c100d020b00300005040c5a800c1103840304495100c52107403a0705100300038840000650505030038070014410601501320528105105182500290790b000a00d8181082003803c590302809440391034100710399440303e40d400480e51407824450210328103851415042481d040c1604183d0390421a407a001d20206091400e0b1200b20240c011001c00075403001d203011245090301e0340e010141c1480701c950328014003110356a2040c2502c400c44000121a03d11000c1490742840c41e1040a80707038010981140c1c801440b03000c10000391100b03c010400c0c1c110503540c0d2080016130b48a68103451001703204040420011504c0f0014900000302403042e18071803207800c0000ba6050605400384905a03010b07902c858185030411120559540e025516 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 714454739 1250 714453489 714453491
    0x9150c0d020d0603020f060a1e0e0d0308040308014119030510090803040b15150319060305120715091104050c1603030e030f2701020a0c09050604 64
    0x44140c005092005181d0300e0308038140000e40900e5441403140d820390a43c9914440c6506200f1102241d4102c000998204404808404004108901a6603030716260113200e0b006a040c0402604141e0881503060066010b80c030b500b00f00d0780ea00c1d43c4249a0a518100c0800d100b2804884642801c5541180a62004c4040f0303100c030b44050560003241410300e01d102242c0f00b5611540c42001800014414100843c1c111030040c0440c62950301d8180301480701034001400c071980000040c1401d90212403820347e0f950b00070440c4240c1d015000460110340c00984651084d05911002003544801500c22a401ca95004001c0c05583c111402e1200c4282c00050b0241d40413001980341000a00d00b80c440d110485e031145209a840d0002c50050104582c0000c10040b00e1000070070000002984809142414a41c140340c0407072400c1100e84000d0841c002c3c0041c002d8400c401043d4602004c01d890b007140781c403403460510310110b5417040300120f076211a5088003424401c0032850500c12800b145d00065449200608 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 714455989 1250 714454739 714454747
    0x6021914061006090e070923040608030703020115030209040b07030609020d020d0b1503130305090d230c091b0c0709050106020c010e0306131a010306150e09150c 71
    0x4580c00e1420880d42c92020003080d0409121007130704400110050300c1c03440c009030650f1400c2100540201e0f900d002d1500701c1d0a11030900d0018501400c000c050b94000900144400c46d5200e5005a40340c105500c114059403e10301d07810105119444a00100c0e0740051030100151141c0d21034041c0800d010380003004140c1c8442c4007083e0302c14103000900f030101b0f04840060b603074158142018210b030014501c40b8413a040c02c0100884034581a010349030400c0305880d000490a135107180a5516214400394039030800319030741406051203c203103d0140130b84000103000c1194031038400455151048041910380c45a541004a015a074080c060690441505001e092500452000f994501682540410040380e00d62005014095050010b44c000c86020f003864007000302d134040003035160700d0300801a07590301c00040001c200340001c05003119080c2c4005800e038080b6507103d0070710001400514440c01480100300c03800048080e09610003d1141040c4805007805040d1123880441104c0c01429034908410280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 714457239 1250 714455989 714456023
    0x6070305101208091008060102070510030605031906180f030302210916080a050318010903080d0b150307021c0509040609060816032d06020a0c02040b030601060219 72
    0xc202c0c0c101900031000c803902c40c06480e04002202c0d901c00d844030708010180c014055541d0300050b00000351841180c0c281c1a82c02e201c40d085000703003402c0d404240d040c0718030325500c10041e04002d4400100ea004100900403450310300000d4100c0321507440001c0030203c01410001c0480c0c032980c0980b018941641031781c4100042c020380310901d00401d41d0010101d0f04440307044030380462414026001000ca45000c0c8c500c0048544465440c1c0c001d0019000501d001180c0f00340e000d80c0b2079811f06c0091035001c8407035900c4121259080c0e00030041c488070640640350440c0241405d00c078610030f9912640081c0d008040102c13900b903035140e02d0104220441d09004003880128404c0d0364034090f410140a802d6400200c062500030300c0d03480c00a1510482e208445181014000300b040703501034101c2e0400711130100c0e19030003030100070a0742185050340103418644081025002c07964001d9000d1203150085600380030898202041540780d000a00c98000036900c903071587c1040c0c5d1202d084862030203001d4079210007100180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 714458489 1250 714457239 714457259
    0x9020a03080c01051b07080d060806010815091f0b0301091202100b0d080f03070c081305040f06140f030a050f01051602010c0e060702030a020a0306020301061b050607030510 76
    0x80c0e08200d48540000ca000b00d100c4600348a541d0f80440c0c0f480310650068007601040c1054400d00ca40901500307000690800c8a5070315400c00c900900410048580b40d6950f200710b552035483e0300042074910b402c0d05022981c0306400141d00106545400071040d40040301520000080c10160041a0195260350741003010603042c25404211095540140c002100682074440c00c89a0300c2a580703103d54450482c81011840c610160f0348401d4189044580e04d844500d010b541c580200b11001742143c60000f030034403590b580e8690b200c0032100103480c140101e1004840301004c0c0c0750b40d40034003000100051140d076650f10301200503000e031005c042d06a5004c020f240d1101d038280348907404010103681d1140c083c0b00042d081b1812108503102684020404400c142200038500c0d1303802c0c000c0c2446058045010815542c043c4401d01000764010303e40c002455403450104040c0d0001d20544020a0060440c501002c0d95281c0b4051b1060340000a4001b90340c1740003084c1d0040c14050800d60460ba501c41d0081011646 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 714459739 1250 714458489 714458509
    0x5210a05070311013e07030e0a080a08040f091a04410615120c04090f0e0705030c06030c03180303010303090510030b010c171c090c0501020309150304060902 69
    0xa208030928042c0c00b07001c12900d10303105c000c0320207407008100340d84620a0404820b44900c1c9034589490342d4070b4a00340700040c0f8500c0300d03034100310381601a8644406c10004e2010040040314007040009c00c000d0756917a00710044404a100f000401c0e503202c456888240361a07440942104028101c0703201e900f4a2050412400c00c83c510100c00041d5040703420280c900000118a81c8040100c0d011104600003900d018443c3c09050107844007071030030101040040407500203403009001c0c8131600b0484519803000f41c20250110003021012402a80808246ca05020550b440384810180c08189551181d0103200856400205400c0008e1003005803441d54030801d0004500a501a69a8a840d603040074200444101002e131904180352810360141100d0360050246100d207034000d1900400700d10345200d65001840b800c507102c580240055640d04003080c0c161700c10004c0d00d02500d1102d00280d210740059035644102c1795402d5008003a642d070a041c08020400840d4464403c10300410080007507030200d004100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 714460989 1250 714459739 714459761
    0x40f0e0c09281e0b0604090c020a08031509010501140403080d0e0708060a0b010c120e0d0605070908060108030c070b1305030d030b011205221e05060405210a0507031101 74
    0x5250740d0003d4a240602e55000740000c5800c0040200241c00c10020b4103034442d41c420b25210540301d0601c090760a00904c99810255002041550f5134a8010f18206c5d20b40e9084040358820f04c6413000200c1c03994418800040000c40c074105161070b060554640e0001504256801c140c2c040d00c13409a0507115a0500070700c001002d00c80001c20890804082c02021b440c1001c501a040041d841112404250b803d419012402a1814800100305000c1d002c5002143c0030000a482c50382810103124800e54001002d008444c8201c0564244d43d0701e401e10561244220450031304503902000041c0511801003000702161001100c081c8a10f55035480801d09010300042d100c00402d50341c1c14402d07150750b0002c00c821018080f01c1010022071070300c0304a102d1201c1c0040c50b10841442c3c050320000030000700140e802e80b503501d1040c0740c903c014260b10785660355501c12241125103002d07801c0314003000001491503401b507511082e94a4142254041d013180e043d00280003ea0420081442c007498071402032041d141260 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 714462239 1250 714460989 714460991
    0x4330c0609080c0d020d0f0210050c2a010b0d0503070b0c0408010501060201060f080a0309060f200c04230606030703020d15031407030503030a0504020a030209070806040f0e0c0928 79
    0x10b0322411020303081443c00031814050110b045011601d0303a43c04511080720383c141300d4001642c2e0f0bc41f100341003c507011303201c50505102c04130700050701d021741c02c0f03140340c00f0030381565000717000e800e1081003072086a910700800104503900900160340014000038145a1040c1e43c5d40c043d50425503644401429903000b03038840c10140c1d65502090040e141001d8004000d130410740e00602d9040715a6400500440c564801c03003007001880141e44803614841c4c0701c0c1d07140c105080400510054405466143c4881228a41a100b0380c6402c60281c00c4268245070805155a440103618090b03441e030703080c002079510082c4180c0425a0820849942260f1440340302c440d404848034214846040d4682444508000c4c0096803d950101d0b02c10400a0000401c40340e20901d5800007048a0b100c03440401d05152840c1c100a621001c10000c000b21142c0c0a04190301c503420071101440100b07074022842d411188080c491000640108151845500300a40240c3c0c0080e48090001211160070805180152b440400c1000c15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 714463489 1250 714462239 714462253
    0x4020705120d0c1e0f020c0d11091506030c0c1e0a020910140120010507121103040b180a06180c170c0d030216060504330c0609080c 58
    0x249010303100f0b10542c1416814110741482d4080c43c12401c91125280600130810141d840742c081510038810301b40c1104001d840300d12660340794a08400341107203400c003141c0180561400550808412403459542101c00342c15145103844e03c03a00c1403041d03031119055038200c1c8601c0741480e00d03000348a0840b5042444103030103010b001d0b1403407041007103800c40a44000780e13120007100184240307500958007400008027402c1404000d01007207141c500420b5200c1c4020a1f030f51815040240480d04000e071130242c90b00c8032200b08001d14204014101601050b140940052031107000645488a19604240204507000c226092703041c050303503010305940c8400c01440d041845114940c04200c1c0078071205001d0100c20751a40c2d0100400f40303600390303641048580381d44101103d200ca4401c2c503009001c040b83c211f210f0a120b9000546407034014240350300c40c1c407034034030700c0c40341502e039081c0b00c4000300c00c40c06000d001491201528216074504503152900001c050303981c0740d0303a195074200149e8010001c000d500707140005001d070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 714464739 1250 714463489 714463507
    0x703261801050a0c020c0d110a080313090608100b0616061a0102010603170f0403080d05240102060c090303040e04120306121218050d0f05060a02040608150402070512 73
    0x70b484018012280450401103943c40c0c240e000f10f401c59454400f612003001402c803034141040700007032a560207a04100d0310240402ca5910101c000c0941800c1014540d800540d40d00d42c51049030700500c140036207134203c009010382c01c02130780d0060810f03038800824007400d09114660007051440f9401c81220019070b02d134a013544103c2801ea52150f040400d000030030a40b4510b440300380360451902040300b98070b14001080c00c4081210b0095401a5812581c0c4640fa600710300f0340000184404c0d28494400c1400d42c0e00c107001883c000000da030900c64182c7c050072154071030309503d034216044039507806c0d403501050002082d01007220751031901c15402035030020680d2010040150850300183c21a4240302c8035101c0b03000108000030150b07603124245290400404c281d0000c510141092600540d511180c0550071005105441815443c0c15009070b00f5116207440700480c0c001248198070400c004510b401c2c00007109400c4400600c01d4605000d07001500d482c20f0790340c6460500061000c043c0b1681008614800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 714465989 1250 714464739 714464741
    0x1522120908060612060c0306040912030902090a020a0f031e1406040b030604020d11370b0405011d1c03080405100506220e030d0618020703050703261801 67
    0x140055013660102036010106042c0794580b07800419500d211800040499100d803903ea003c1c1d60703038075045495010207040c2c0728401805400300f00e000b070b48610a107401103140d1011a100701c8602000d2625041e854001460701a0060304074450800420949418101c850070000e001d50100121001a8460249840740c200030403140400942806035108004120040c2c4481401000d42508054038180320314044000840c60390308015078078005c111080e054003030701c7c518aa54902d45c0d40c4500b0f002d81110740ba041000003038022840303440d000a0341070703a4a019405040720000958070f0b0250001c582d80003065000d07903055041c04822000030b400701e01088140041801342e07031080b03503450130709012a003420000590040584012110100340303d01c0c4034420010300364010f2044074805d00949403220010600c01000344414400c100141c0d4403440c0351606040740b8801c41c1c0f05a541510303464180081601c0813152150491581d04242d40506400b06520002d8114a07105034161240198510070707806410b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 714467239 1250 714465989 714465991
    0x20d0c080c03061e130c0302040c110d11060c1b01021305010212040b0d050a0f060801021305041b0c2a030309050603040b0105090603071d07020f152212090806 70
    0x2d00761307941c00655100e1600030707440d081d0000c09104d5075811001c4035003085013a85e45d26a000a500c00c4c07415030b1101d41c1079080411800442c40410503202e81c28180c0c00281c0358210300341144403103034006c5000203d0701700807000a050003a82c004c00b042801042030601d0307403c80e4000b010940c0102c1034103208100d190703810045128444540b044403404c0500e81740e62030001c1d00031403c094803029143c00000e59610000d911008803030b070b0168801d00c40c450b80c0c1d51105000707600c045c40c0900003800c0c41c00b02003140d040600502240c0d0b0f01d10000c0810300d03e8100e008941c400c10400d8102c5141c1041d08031000785594000c0b81c011030b03000c0c490004491601d18070300030303000c0202c507270166004410501c1004040b611101da1141160419a91180c16580f040c00103402d08465030040f6041e01c0c0c2650242000003000c0c1c061034070a0a42d902200c081d000600d200d0f035078a0f04010700c0381840e54420400030700780706030749100003511031020911030440e403445584800c1c6c02c0b400b04003088006029481d081012210070040c003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 714468489 1250 714467239 714467251
    0x51602160b07030c050a0c0302011425050c100207052b0201030b040f090b31080a030b090406200a02071208040b070b07030e0325020d0c080c0306 64
    0x814550a401840c01182003107482041041c0c440030541da4203041c000c0000b111825840300981c0c0210003640b80107811807500d40400c1c3c0c0000c9d00d0a4001c8801c86068013199086442a441e0804d48801c90140d20021484540d0450340c6000308400000a503c0d100310000c8026240e07006410724606110600c211040c111414840000c0b840c040c607019543c643c041240565020329020070800c803280c0111300502940d200401d80305180c66a440300b44120b100c8d4076400f541054400b480d299408c10041e4810400c100503c45400240000d03a500090500340101140b401030300b4086080580e0700005400f5000841d400c0e20400e480c1c0900389080246500200c06102c10350902a041003091031000796186514042d01c1910f0001c2c01150041c0000f0b04141e60083c6503081015681e000e281c076080e14071030419902c41022070b041c4842c60300041e00c040140c40501a19a17036112404803008040c11140e4100d8200740d8200718076041c4140071540f80000035002d8203084000301454001d1000341481e2600003080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 714469739 1250 714468489 714468493
    0x20909040c03050f24060d0c0f0501020114070f08041103060711060603210a12020d060f140609040218030a080c070b03010305060406020a12020a021b0910090f0b040609051602 77
    0x208841c5c200b02c0320310070908074240386040c015640e5600825401080c81d4409440d1281c0140006a4040030b62043d0381a98020307802031005003125040d04000d68000c1c2d031400007180e00a080d002142d403113000c0d016805401080b038a4420618039011a05040003611000e0004503507000c007100c0c13a0703010441382d0b4000310f00340e000344502d0740001e043d451000b45c20480c410740550005051802c6a1060714449074000006a0440d514180030081c000208002c0c4240d0032124202c64000a04081d000d01024030380c20041c0c507041c80c1c41205070401000750b0080503400350343d19404a00d6040d40c0c0342001106044c6224407100e40e41ea090350320500380342c4142e82c1e004500034074007080103000003803000c510590007541c8941c000d601c43c291082c0980b42c003500c5c1003c04219610205900380841c0d0b001500110b41d110450044000701f03407074030511504003800c48a070007a2034243d00c000c11001442da07100114074081e078440010b2089a100008040c0c9045034000c0a0b219151404e0100030201500030700120509400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 714470989 1250 714469739 714469753
    0x309090403050d062402060f090606040b0127090b0f012a05060903040e01090504110909070f0e01050a0e063312070e01031a09040204020909040c03050f 67
    0x100040406000610007000c104001c103041d800b41c00a60007060107402c00c80e2503203894041d070f40058000449203024003401803243d00d0100d098001c80010881c01043c82c00082c0040b50382e80001e00002c0c0c001400d1050402c1180140d001002900d100d80200034039012103a00c03183c42c500300c018020794000d27801d250301c40d031107564500c051070ba0000303441407a09207001000140088003401407a800c1054a0700540180603410800001d18004001002902c4408042039451f90302d62280a017240d5040b83c2c000d200c1c1e2142a03280095107441c0e58142c1e4440e21000490300c0c501e03140e4001000488030340e03101041e18048840184082d140514120014040c1199a4406464080001081487ca080812a0b421a050514110000c0105c592101070308149840c80c1d890305101c4104100a5045541900081c0141c1000509610030300a4060602141c46403d0849295908015000348050170481c0d0080d420045414252211040c161056000d8846418584e242d400d18608224501da0b140c441500700c1c2d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 714472239 1250 714470989 714471007
    0x818010914060d0506060f0406360302011d040e030705010b060306010c02220203100519080319052101180902030615030c0301050a0e0d08041a09030f131703 69
    0x100c2a1891010f4842000c00c141d00c13424046000b5103d9a8071540c034204000401056480d040b507a800c00c00e5210310382c842e0207403d250b000c11140406c03002c0da041c001260302c1030400242d8400c0c43d4000f0900391b4a81021044007002001508560b0301500c510741a400102d5080213002d4280b04200c40b44400741c940303a1462030701000007081c0056194000384108070500261410100c5039410300c0d0b070040c0b00e410440d80da091100d8440d110b580c0d113108a62140306104030900c0445000520342040380ca0440095092000071540b200300141042501d1041200500801c0002c048203401e501c820102440c103a40345505103425040728111025008034180c1c1000414070068a0000d40c40b50300124001c0c1813040c000001000a041c110240d401c1c640c11740c00d04007404241c4005a00420000c1403007012280e602c1c041074801c0c0c1c4c400740221809050920701c0a08100c1624185902d07a601c200d6103000d1703074130388100200c8800c2c19400080700070404003807802c024040c80c0c1c07588807214030f005411001076040403d10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 714473489 1250 714472239 714472249
    0x20a08370f180501140f030703050a05151023040b0406030c0822060b0909010c021b090112021512060102010506220c201c0c0203070b0a0203070818010914 68
    0x5441941d041005004c0c41e00c1751a207242060711050a802c4003070342d070349080c940d00c024040c01d0113444a540607441c2401003108080000340210607014080d00007804001e0b02c0600b591016900346000010000806011115421780001040540004188151107a003050350003022100340380c102c0d80a102d02c0740207021031300043e505105001e207800fa800c3c8004030a10b24001d405040328440344c5410050070341c207000c41548117400c00b04148010780e00300c0e0072201038549140d8514000100194001d00903c005118009a03412031010440c0050561384c00b074176902c800c50380f445d4040c45040e0b1900b0042001d0240542e428004c89030402c42c103c8a4a51102d0419502810f07080340ca122140c02e01e03502c013803000d05c0d40cac06200b030603201d10300240c09644411520481140c81315410b080c06410900c0403a8540f000c540603625400b000c94014005040c07880c1401c2450486900c4403003500e0540c881805440000344401d00107003400594003c1c0d0082d01c0c0f007a10005003007820150082e401800724014094016228 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 714474739 1250 714473489 714473537
    0x90608010905090c0405010b091f05040e090f030a18050108040b0f10230a050a0e0c030408070b070f020616050a1412010e25020a08370f 60
    0x300101c00100d90726003003030491400107502d030b20f190000c1c180000000da044081002e40301e803040c19200c0001300030700d0591110042d01030f810011f010032014881441249003c5080541c030071003401c11078054085800d0060b01d1900265910000501280005c8900e656101e010000411082c03c00402d80d08242c0c1d940d42403480d00074070101c4425450780001c0c50b486580c800110050143d110295840c02d1441c0c482060105591490743c054030710000300140718107008041d202200c0780011411060b40354103079081000c0d840500151000d0400340014008607041410310390240d44507131183c04214502c40806420480c0003449100003040181c400001603402ca012603441310001d00c0c001143d00c440c040142c0607801102100d0340e50b514083c001054a868241c4454040d581900f042007400802903078002c800603000b2110390050308410000c000040040d07028244510403031803025010803920002945120704c81c481c003600c41c13914188460941c1e4120030588004c40007440c05d5011008905081d03400b42c0c403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 714475989 1250 714474739 714474749
    0x170a061a0909072a050106140607080906091909090b180a0201030b190b0903010e030403080913020d0c23040501170a06080d020601030c0e010e040303091b031a0709060801 75
    0x130210340d840841500c00301146202410901d0201420040760401c68003c041030b00501d01c950480340f03900b000354038100c0d040c0c421070765100d2581841c10325900f06016140d0021200960442000d00b01c1105040b0310800c01c001404003000000b0342810359090030019074001a00c500304000b66030450241c0700401281c50b000e910303020701300456901c01210128451180c0304041c51007480907160041210a0f00700002c00e12010308400900891442c01d06068592080344001840e1900400c02d181e1b4a0a240300440b4200710701c00710041c2006404104001a190b940c51040300180d07603030322942d42d0b000364a04407402d195900c81c507440c206820100060301820780140c2e0400c42d04101000102d440500307800c0130020b0080f03c010755907191070302c0c0c0f00a036072070070280402c4800c1503030b0080206202900c001d419040740c007940000250380e103d07605c040e8010000c081d010f0f99001c81d18010780314002400140000114469035002c984c042121400010f80c41c4058000410082ca501b000c12030540c0c060031881c1565 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 714477239 1250 714475989 714475997
    0xc05030708160504150305011d07021b040b060c0d08070302031009021b0f0a030f0314150d021f120209010206010302060a0203041d01053d170a061a090907 68
    0x8500c030b090035229405564000722491a030300320402d0a0300d5061704180e040307600c01410a00414181c40a07400604002c448460060340040310381c0404021124282d260a10060000210f0a0418000c00c01940c05165200281c2d4050100048a59441801c16a0051091404509504004090b80c41d00519840786580c25600850211049007401c940050416003500480b03000040281d0900c1d11180e0401054000c503081ca480b110f1500d00070b0068140b0003c405c0704451259032142e07880c8216000c1d0135015900182e0071036048005031901c91800c80c801c0314009203c0e0fa0088450340040c500c0300b00240c2c10010900501c070004140c0d8002a29a055a07811161241c07141007821007245503000b07582c484e0b08914411b0b403120904950039070149059410a50751003821a4800b1070484c1e41b10b118001c0d00c0f11307210300c03400a1081c9405041075451382003442e14000d0a060302c9400030307406c013600a561a00c040e690b2034104200c0003140d001182401507410031311138202100000007441455000304440140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 714478489 1250 714477239 714477271
    0xa06050f040b0301030f0c090e030d0e0a0501050a0501090c09050f010e2b03030b010309030c08032d0105180705220506160212070b1606060e0108100c05030708 70
    0x40c0c000368007607034060300880952540b00e41e0741c1d0401c0644124040303400d84251400000125038111540104000c608403035000718a40300080300d010b130041030303610548161402400c1c0400d0025400b8081c10b4043c030150400820b055050400c0b90044072485c07444401440007440c0300300300d580c4880181c0c506400c000d0038000382000800010489c4e02d114492083c245803440c0034285d8040620009002000b8000e603410002c1d1800007005504980c000c0030082d02040309201d200000545101c000c0d82e1010030109002d04502602700011007422851a125004500300c10050000b420f00911072083c22030485145150750400c99005811413281c1c2e00d0003000100c000c0300c060010b1617040500ea004100c0941810342d40c5040704000020712058210072407103810303194903540341c3c0c581c00290300c010b40349941a40e07480c080940e2011403019540e07410071503542e6207070007000603080084a074450013446500090710300c41d0b1290f03242d00f040300c50181800d802d008081c028003006aa002040e99400b10001c8485068 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 714479739 1250 714478489 714478507
    0x70c200a0b0c01050a0c1d0906130f06050f04150b030702031309020d051f05061b06010f030311060c0a032f0d050901020a020606012303270106050a0605 67
    0x12844a4001e201d500e01d0010340701c0e41d6003405600140c400c60601508020804800c6000c89140d002504980c0041d1001500281c4524090404c50b0704000014161b14406160701c41c02d2043c3d5900800e00388e000343d83c402040206050404e200516200212001c11a21840c0d016a49290303249000c1c402d100500800090400741c02001121800010001c610712016501d11185000e03510155000544034185130216803500d542000400c86003008400b107200d09030902007070050070f0300400c4044c1107242c5115002402c1762130911200d03000c0c24002181c44540b504604000e041503003e002d000c1e40c82e81c008420080c0409102040c1c50185c1c2e11860041803540341c103070900e01c040340440304a00c19984c0f400c440803c1e00c0c503070b140140104141c0309821320044c0c2d46e0050321400c074090021000003503042200000d46a42c860260911940072140144100c0300500d2006003a6400495006508030003107501d08078110083d2a00c00c0309480c80000034001306007014041480840d8501c946410300c103001c640b01c03003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 714480989 1250 714479739 714479749
    0xe160f27090e0c01052d070606052d1903170703080702070503071203050c0d02100e010501030f0303180b070518030616201606080606120103080a03060503030a1106070c20 75
    0x100e00c003006c02c0c4458450002d81001d02c01000c207072007901c4c031801500d40704e410a02d440c2410310b034824000740c00440e68240102c0c24009500c5404840440041c0b0103400400007801c1c21040b50600900f0159040d155252454040c10427075014003c0001c1d503124600400450783d00141100964902c84150520307060145001e854134019841c20b41200d0060000000d2489d034001080d904d1008451001d0100320364007a52542221030038040600310240402100c00803034002d41040484500100c1c4e070250000311900d408401407001e581e0310300058000100c295540350320071205c4100c0c04003203010342030908200c0001c1c003190841800500510001d401200054200180c100c1126038030030064941102c0c034401c0002c0140014020303007000c40c694002040301070800c08140c80140b1408050322300c481e400d64507003901e642c10a000400070140c58101c049080e440030b0001d081c0402040e11550ac1000c140303e18a418804011704483c10811901081002b080c0300184007640307075521000d95807843c0c9035000812 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 714482239 1250 714480989 714481057
    0x3120f09080a1e080d1a01090605090904020a03120507110a120f0303180515010f06051b07090f0b040c030c0507082a0d02070e160f27090e0c0105 64
    0x182010401045c030811060954201600c610b040003011020b24000100543c3c0b262003501680c1e0015006000c0f00d80b150800c101c00b035030031500042c0482040390b6a50b554026140c0054060400a0b8001c5402800c000c54800700d1031403101c0c00c0300c1007041c25090840405007524030351005024050b80d5580141814025841000400d0040c1b800060303444140c10070b60390f140005545482d103680701c2400040c0d2503202281c05e10a980307280c0e1f43c0900d00402404c49100c4000051000107850007040e0001031950210f2054aa00f001054400b00309408880108002c0310012880c10040c1400c1c442e003d10f01c207501100311400503921403c0706032503600482c006080c5203003d032009041e000000d05d0b4040f10413800241422110625400c0b10310050312400c100f101050251000c05c5500e1380061050301c058003030002543e00340301c149030541c001108180113403414100c01041c3d882e4240020000d000040281c051151422070307403c010101e60007940002000c03403140401c24401c4c1e440d100b580a0206501140e81c1e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 714483489 1250 714482239 714482243
    0xc0512040c03201306051f090e130203010b0f0a091a1203070209130201090501080405160312020106050a0e0f04020d0501050a0f0507020f060a0f020f0403120f09080a1e 74
    0x10107400444808410803c00c03800205511642c03184000c8880501c0b075005101c2a960050010b4180340c1e2410300303090000a0311039130035050151031500441c00c481c002c0d0711584100d001c0c407140000c20183d4014142100c1c21140301d140203001c8050080410789540315650200c408041d000036900d9003c0c4108541094102d41ca558440d1004c4641c00111600102070410b0f00d00880701e42100da12240d035402201c2c07400c0b60009000c2440030104008960080d0340b45944540100241c84c0550880341494131150604d0300b045940400740b03d16000c03000c0c0e0900c15000900001c0e108010301908018032a00400401080c1640d0720900e0307400141191030b504013005441d54418000d01450501a0a80b0064440b9a40c290019860f200003d10f450b480042d20001001850010300304540321350b50440058203481e0b81c11204580c08010000e0050f42d500e00420046d13000b000c0104000c401c00000500d042e0300c20300d03031000b08444900180000000416018041130348075001130101110104111b10340e2160081c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 714484739 1250 714483489 714483503
    0xa020c01090b0601030506240a05160c0e0c093006181005010501200705030a150b060405060a050c011d010b041d032502030304080d120c0512040c03 65
    0xc1c1c000c00c0a4000c0c0640281e00c00d072130920003a030b5440148544a28031440c502d0070340300203140f140b440c02c92940051003c0d0f02e403403504500c0c00100c034040048488401200301d8a40281d00d40030401150742c1c200403600b2a00c058201482e00c1c04210020300d0005401d132640e41d0f44da07009802c1c600a25a9000315801a45207002074503d07a140c025540302da21400c100200c00c01c0d000789840c01c13204120511595058500c16100c3e06082c0b01300420b141c030060705008a50380d0920070b5120214507550b08124281010f80300309165170740d28202108040c25500030610302e41c000e40702800103000700e0395031000342c4100e011b540c0b4196840d001040300103805009440c0071260071011040c50318031560010b401440d0020403e881c1404205011001060204417041c000180781e08140802c00c5150a84503d1b4111b88001d031610301200c07080394000a0565009500c00071030b991080160060140e08455410007040b0440c01c1048041c8005002401600c5411a41c074034070764a84000034204428802c40201440d04020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 714485989 1250 714484739 714484751
    0x1b0e360a15060e0c04240807230c16050f01020d08070306050a032d02091302040209090c1306020a0203030f0c0a051e0c150d180602070b041509050706080a020c01 71
    0x560140f45d41c054019002d02c000202d0100940b4004000c0303c00c407602156860f400140c3d43d503070b41294a001c94a040c04600d8011111240a50350041d01510950b503602000d000c02030b180c0d15941c0e01c40c0c42c41da80218000c214072a268206c81c4e0700802c181d0300c100840c0c05e28000a0b960700d1411001030096401c032a074000500e420100500400c410054007a8100181451a54204005600403107581880c02175001010340000b030310b00d423019030106524605c007030405402c0ca1001000100140402c80d19000c0004000c10f51012030300100c2e0000c4010a554005051440344a80100380c03644200e4114004803000041c45d912015030400a13076841640000035a00c80d10100420b0280744103001080700b0041c401c2521004182c5066200340b566070741c61101c4240340c10302030140d00f000f4102e0650884c00c0307404c0000224000c2019030000b0021248581c010240030b01d03291a14100803101940801c42c010724100480001880020b004002d41d021400c001044d80d85c0c01c00c2a501034442c0702440d0350b81d542441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 714487239 1250 714485989 714486001
    0x1020f0703110907081918020901090b1906020307061a06190801050f0a0905060102010b280b0f030402121e150702030f04031b0e360a15060e 62
    0x400c0b5641180d40c00c845500d0301d40c60b00701d002c944000741524440080c0c0c0310140c01d40200d24007640110780e004a0100001d8081481d600051003484c1c00341d00070611252a0a0000298900308007901c220f02000c0e070a03e10b07418104030b0000d540f4010014000c002c0b6944944d038500c05c0d045078450003d4180c00038181d99a80500c0c02e9212a8494036130110001301e440f8100115980c0340c032aa401002010141ca1564120729009608001d03000c003400c2941595690b02c04219141c0743e00d400c00210031910101003000c00914082005202c1c2507a200f00044802030200c0b5108140c071404903030708540c046510008101241480d175042051680e1400d205008030519461082d0006c180c98042c83d1000358055450390390b042c01079803079120705005414540d00421003800000e8140000c6c44000c038103107822a01030340d100c1c0c142c4603032680305440c4003070306d404000c94950001c80f1002c0c18110103842066284440c40d002e4001d55074440c00c0b0040208225510b0030803109241241e4881c10051003440c08045c824100a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 714488489 1250 714487239 714487253
    0x7090e0c090d1218050102120310090501061706030105040818031203090129010c15060f0e19090804140114070b09060a062304020d0e0106090f0b030d030b01020f0703 73
    0x10340340c080032544c5408541301100c80040b114040700c5040c0c0141c80c07025800c10302111035910040240c03404900740100410320002610a5074040c002e1915520802004140c03c0a4480da0081c44a44a41e0401d801c01001401d440c0c19580c00b920601c044580798005140020b042c00c3c082c60000341b039280007008004c0b649005411610040b001c0164545070b802d000b010000340d9110741202e907030100319440c84000010320400c40e20403900c1045c50000490700d0312002800c3c3d84590b09c2c3c1c403980309000b6200500c060030f10741281450003c400501d04100e050155940c0201034040e078407c0a4164450001100042e4000d800c0e55010b00c074610455582c4060a24084220580a690581c054480d6000161901070684560000e031079051582807640c640b845a005840c1c1d041814068201d5028000030000c80810700500110414020001ca031041c1461b00040446204400280d8641c4c100001503000c0d031000300d8031654013541883c000ca2088100c0f1f0043c1d1030042c01464010003807141c85000000d002c61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 714489739 1250 714488489 714488513
    0xf0f0b0420030303040f0803060a030807030c060507030c0e040b1306030803090706020d09090b1c0507080d0f0905210a080a0f08012403150e0405120307090e0c090d 72
    0x2503421800c010110700030605541340070803140100003003840e40040c8003140c40e000107158002c00042148510544981d502038258000000440211302c1c210500030421525008040d40800a803074100710341101e0220041c084400700c003141c1c1c081d6584202443c0c203a20394000c04a8070366414001800101e0382c0c0d152015195004a660341c01901035400b0204580f0300c00f1800b00b44000055807852034090400500d10028004484004c0c1d11018000c0310450302844c150450350814081e0b0064403c291408040604006031a000c100030061486042c2c16140d40080c10b8034140e0700252071100505585106c0301c800080300c08591450b070320800c1510410800040f000700b20701c0307200303684110b05038200d800306986845003030048c0442e400f6102c8100c80c642c020210b42c6021290a40341c081039a1200b1074070510552903541000b03104500e0003040106018040207280c404141e41d4018900e980350118004020130401d014a200112511002c00d012421071002d075010aa8001d01001464a00b4581038800d004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 714490989 1250 714489739 714489773
    0x90d051c0e130b010c080306031903030902030105010e06010c26040b0a0f0c0809090912030106020a0201020f1606050a0201020910030b0f030d050d0c0504090c0203130f120f0f0b04 79
    0x42c0780d05a5041241c058003803420665410f8590600b44c8110b56140300c1d080d00010304c3c207a010301c207001d10116040440c0c1201c4c4403040c0a42c500041c010b400340107050a481050300000100b02b0f0705420700c0741c0c03641d10401c1c1951203a00140c52246103103161b008030b014a02c113085042160480403070b01086c1c58881c08014207101200780c4403803011000b210070a880780707068900041d21030301c41448080071350b0826041c025030001d0b0070001c2d01c08482da03040203680e260704203030441c0e401a4400c5041c0821035030100716000f203030544e0304000c20981d03640ca4414007c04110740903a07001c00c24041f80c80c0c1c001e103000350150f890344140101102200001000000c0080c611702c02464899420100d80303400318180420000e17007400c403a07610700d8684000300e8000c40107841c8041c90f60040040030003001513654402e1160b1040d90319140d018644d2901000680804000319410080c448a40500100241404801c41e9101198801003410800b034041c00c00c001d040e034030b003c4064000701c80c56003004100011004100301e260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 714492239 1250 714490989 714490999
    0x120b1503091c14071a0411010207080318040e10090b1902070203060402011b0605010306200310050d0c170610080a0c12050c0d0317010614090d051c0e 66
    0x40b110604040c0007002c0d11007030300201d14004500d808282d40d034401404224050040b250140055408904000c44116010348145000c3c1100803860760b41030203504000c00095000f98180b40b4021686c0c3c8a54079400701c2a44600d6444949010010007402001501c802c007400070045032005040568210fa400c031050380480c2d03180105a0001d110341d20036150301ca50003a0040190b03664079401550101ca0310182000e0007250072402c40000340c0c00e401004e0103580700d0500421000348031982c5a40c1c004a07012005174008060040107058440d40c50a142101e50868031750b04160503500308112503d03d160030202c0280b0100c0c0d41d841c521000011440d009100c064940d00c8000e075240040c0d51503491400004020f6040904104003103003002800350000380c001c1056928003030600300040d11200110404401146004c50300c07910004240040b42d00400316410481510396109000302d030a886076a5130b031403103443e5030f8801501303100d41044100982c0c20349000d4107251002d6510044c0403607141a01043c800c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 714493489 1250 714492239 714492253
    0x608060a06170603160306091101080928060e0a1b06140c1507081f03150f151805011e17010b040908041d0610120b150309 54
    0x2800c0c050a11000c880555481c61003050076030700000b16450740a00788550622880d861152a1540030244000440c4610400500b084d2241b800096502c00003501d107040c4020030341041402600821445d02d011180d2990704040c1c0d451107811403c5d0080c014010701180e1400715002100e450000310001c034039010b441012441031001183e44d1111810307000f0311000502c0d00700c498215030007000241c0a0b07030703686200781c4940d91851444d02c100c41d07808561072000070b600c413814400d441151408050600305003400c1860881d04544590106904082450a41d50341d6041002c68462540d80210401e101c1c2105880c1d0300369440d10400c1c2010000030181400a1a01000066a1341d1000248014010858034040003514000f1400d018014040642819540300d4811800d00d5440348a0007071042d103e00e8256807603504144041c40c0b5803c3e00543d50f03a00f42c170484107000f0566160342c012049140c1030f140a6114070441c0c2d0303113540502441c146158210240600040001c003200f0040c0d4420031000c4120381003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 714494739 1250 714493489 714493501
    0x909060f0e060c0406030c0210020d0209240304120302091306050102010c0216030f05030c060a0c0e01031e0b03030f0f0307030e0a030e06070303021b0f01150b1c0608030c0105010608 80
    0x40ba42e082e42c1c590020501000b04022440c000d400201444100d80180c0d4032402c0c00300c01c3e4030180da01403415100d1060340060184c0051404904610846001003100b408089110148400344c0c480078101070404032221000c01000f43c07194040707411410014003440000b007810300302c07940940182c0c01010b0140d403c22841042031440040c148181e0000c2c403d554400e035207103440e01815a02c4222065801d40010846001c2100c020000140581900e441c0003c2d10074034200010f0608201d924920b040500302500000001e40640c0c01e40070460a0120005148003c0c00020b881c611414142c0004040041a45c00300400702c407020758400d1040e5181880b40c610b154100785c2e105c9006140040201c3c03451009143c45041c44c8001d0402684607050040c90b00c040e6882c0264900483c1400703003904c0c0d21011502c1a040003e01078160000c2d41400c400d48541d060000300b403001d0145c100c001c0007520444a54846007042500b0a50080c1035040a6980d600c4504540754040c003c240100d2010030034600104107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 714495989 1250 714494739 714494743
    0xa03060f120b0411030f0d170c0708030a050a0b0a0605031803040e0a02071b0b030403020f030906180402070c0b030a15030210030c020a0c0f1d10031b0909060f0e 71
    0x241e01c1c0ea1002007060165540e50300e25518040c00500c4503018400c5611400c9111801c118001340c9040315202c1d1800f01090707550840d101c10b0010700e00400a60b00f4042d050000d665501641e800c0714000c840451940e66000d0046d0051200203406a0b010914481c00508280c10000660080b10031900c150001c003c00b400b080d42e80d1050744039410141d411040014070b18503203a03020b080d00030f00c200981410090100007140d200c110980021a41000c00810300c4105601001801041e0002101460410700303c28002086800b4042d42e0550342c40d0700c02e503013000550b640d41c1124070045c1c2c4075810b04121a184c006a0255401c102c550005051074200441035043d4102e00c2c80c4101d907030051030b00380590300819003140501041100c200551140ca0f2103540060ba100310104080c2c58076042c04240b5074605a0f211800010020a0203550a0483c0500c0703101505103403068242c0e9000083c408148071510a000c4000101d82e2008400d03526181512003003082d2030700064000702c00180d00740056000403131419 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 714497239 1250 714495989 714496019
    0x603020d05150a21050307060b1315150908060708220809040b1f21090b040b0702190302070e070305060a030209071b0803041a0c0a030209060405060a03060f 69
    0x55008807404801c10a02d44044d10a50301e1040f0301d00c0403c02080560b80300362668000034030488078103840321441402c1741440040756490484c001c1080c015029102c60f4061200160f008403804856210060003405015080220082200d0b004803181460301c070600034040320042ea04200f41c2c0000c0d0500c40c0704202c004216103800c58024030483c0c82c001200c01040700030070310f1002d0729800ca000003803844c1400ca88880c81465070801c3d521f40d48100140b40c504510507035041c182e0f21b07003000c1c6040600c2000c600c07000c0000742c0c81940580d0311070b210b4680d280181e181a0501000505034450030b03400174101580401c0386e0342119031200560605464448041d401d45038111a00d0390410400003040000d4640030844c00c1c0c002c0c0c1c0f541480002c1c00301d0201c8480d81c56031001000c2e1180c200000c28001003241104903904c0c1e20810603045407160424100c1f034030340361240e0a2003101700b58020400001c1c1e5503510f412240201401080706554103004407014016004074030854010b0310542e40001040000a5001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 714498489 1250 714497239 714497281
    0xc0b15010e0316290909150303030f101d01030b0604090506010618060e0102030a0f0e2d0102010c0206040f06061d1005030309010e060f090405040c031205181c0206040603020d05 78
    0x2c0350801c45040d0600c0041000140003103407824010240d8200c48d00c0a1004500030003550301c1182640c580a040c407114800581e001e402008030581d690141d803c46074480300e041d01d9024880b180c13961200c0e0001005001030b04c002626501800000260164021900462509020303d002a0300ca50ba1001520990020600300d805600100091800e01c1c0c03007903601c1c92030000c640c02d1082e1255179020118100001c050118004200c203060300c04500c40c0a10480845c1c0d40c4244028449030070b50a50080d281e0001900003006800e05100c54002c0002c10f070002005440311240301c640100000070a80c070030000c00c2d0303541c5d900107404480c0480c1c1410044210740c04400180c49201031034a4160a00c40540d21559244840180901440415594900540d0f000324080c00714100c6440c01e6007060940404090031013400e00c40704000181e030354214034030101d0000c0000c65040a0301c40d000318021600a2070118001d510100024011400903010b038081d11900c88944804c1080341d58a4800c08040385203e404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 714499739 1250 714498489 714498569
    0x1a041502060103120f080411010908030c0102040503010e0c0a2603070602030412300b0a170f0a030e0d062c1209060f0f07062306010c0b15010e0316 65
    0x9408140e1460f0072310300e074401c180740290125a640c0315980c02c5410419402d43c1507500094100b00c10f150901403590813007081300140c0801409100054498038607803080c440c1d001082002c0d0b84003404010071016900a909043d41d0740c420952030400000c1d442102c2c110307044420f02d0600b002003807054585134500d144410f503070300c440e011420708030401284900e500b640b003d07100c490821141c4c41d50352080000b0f1110001221940101c003000b40d042040c03844a040981c2e02400c51079011950214811800c65015101c00034074440300c0c04c008001c1e24403124a070110304a101851200e01c2078541c64518280900d0341543d011070020054440c0c141b082da10255400300042c400306080800c070340010300401040380400c900d400c085540d0340d07060fa240800400011020120300005000b6603003031450b4442024a8040461007007541c43c000f4804010700950010901441c0c4803940d64024422841489002404c99846c1c18a9514500c140c0c0c49500415001c0b0807090001008941c030751101200030082c07003035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 714500989 1250 714499739 714499741
    0x1090e06010903030806210601380f040306090c05040e1218010912080301060f0c050d0e0a0b070809031209060d0b010528021c091a041502060103120f08 67
    0x50032500d611000c0c01140d8020929a030342200912001c80c0c01f041031081c0000342c0295858100c40f6003445103180c0c034a0300d50031501580102580c0d032596203481d45c81e075000016500c03180c41800e003003064061500028121898075a001d000d0081103d0284c2c21218125400d200c1444607050494964a032070311248034581e000e001e500340b80d1071402c0c8507401c80300c0180740038040d565840501c078003061807220080c2c032080c500000511103154824032109802c1007a080c6102030b502035507600c039036500e100c4040104000980041460590f140b48801000300850b0303e0054484030142440f26082e4821540796210b4422601500101880a015128500401040c0a0070600800314204c00391021001c0d880c10001e00f0002c40071101072a400c000b00803142030700c042600c1c190752100a031034407014800c80281e00b80403084141c0a00e60003100f40342600d00c0b00400540381007071484108028001c0b81c0011b0483c1c00c0152030b8094076540080c02c82e04a038022003408441100418050390124070084d48140000ca1100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 714502239 1250 714500989 714500993
    0x4031a061504050a14060c2401080a031205151012050108340801020a0306031407081c05040819151a0618032a09011508090f060906010501090e06010903 67
    0x2246103060014006903d0035487d6020141040d259606407103522450741091514101040365081c0509241001420440c0541d1000b4049040c0030058162040d21b42e00020140c0d50141511502102d0140c078001e111305080c000034098210040040307103130915003800041d038420000b0700c400081d4034041c00016111040504000e040440c0c1c00d110b0320801c40714200050f52070092004000c401441d82c1c000402d42e007940381000103103031801d500345050b6100034014070010501080148c1d142d14021035401005580340c0050340c960003154080601030088a044800d47e00c00003401b20101032051030300000480c60100740708210703540d41d50209101800c4000801107401e040000b000c03419a09031051715140000f0000a16001c1034251035213a07802650409004240b01c0c0c100c0010548003120151388030b60604800411258060b000d02c010480c04e500828038198040c04207c110301246001e692080ca000c80069030741d082c0030300c101e84c0040c105132030000341010301841050240300305940d06242c0320301c0c45d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 714503489 1250 714502239 714502259
    0x3270604050d080705070f140105070210050313020a08030d0c0f0504050609040b040509011e091a0408070b0103260a02060f04080c1603150b03060403080405010204031a061504050a 79
    0x2060440322a0f40800c100c034003140003004100b00401000003003181d414201a451500e0031459070341d10f07040c00000d0007080016607e804080320045550b00e00161280d48840a4910004038402e0182d080700000ca0003240c1d401c8048000c0c003800e10030380c00030b2015160480c022102c0d034a50120050010348140300034000e45c0b60142c020000303204021303c045001e486d024009004c5403c2683d9100b1280e548807010014800b03450800345190200240401c2071100b20b45402c00800028060007006d00c60309400034041024071030548103059007095036041150b03101d26000c1c0e40c0c070034601d403100a2144459848180222180200c485040460b03002e810117440c0c51400055100e40640111401e400a0123071700d0002c5400c005100c56038000f00300c51020a46581043d001600d80d000c101300c51142850403201d415100050710030340240d0b061030048044d1b6214185103009008981004200f2424500c14982021200a084d4000e6200301c0301c0d200e05080031000301c00716100b00c1c81a2b58000d0700a9400b00044244 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 714504739 1250 714503489 714503509
    0xc0717100213210506010f050d170f0a0914030601050d030f02120a0504050103060915060804050a02030610030219030b070e040b0603010e0f010801022b1b020327060405 74
    0x920002c00d40419181c400c48082d902c40d4000402803038407030030460414044e00b000010300411a000c48032035081d00308008600400e1203440d014210140c1243d00f5481c42c1528000c5542030f15445014507115011440010b1002029100f4041e50400d9020148498074000c9141ca04980c3c0044c00043c00b8246075800351000e5818081250550140141544000601c400241401e0b031181c0d0b030b016901c0c0d0030700c0b0014085a0198100900451801d5400500c0170303803680800c1e06554550600300c074641d5480c80c206150040040c0025003601608080c00000c48101c01d0680c1600d200315080092003078207e40e081c580ca00c40d807001814083e028004030382210700510445000c0e40002c2c1010985c50060b1000c241107038400c2e800300d03610303904130000c1102120190180c2400352081400039482c04540c80f10805035607500300d10912100700345c2c452110001207154007004c44040714a20206400d0f15100c0041e440e900405034500e0110200030012640100342c013150307904503100500280c1054108400c0c4100701780c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 714505989 1250 714504739 714504757
    0x160905030607030b18040b0106140301080304060509190803180d1a060a121505071b08090105070204090507150906140f120117011a0d020d060f090303020c07171002 72
    0x11424800004017000042030340c800e50240d281c001c2c0d030703502d841002001050b82c0741040004c504107100504c419840071046034115846403500f244c4941182d8001254004a00803800d030012b442500020010b0002c80500060004014a044040000e009000e9204a4040010b200f200c2105039614103c07604031041e41c000202800c164800b9884a07103040d14621441c10a44054005030b41c280c441140d80c0c02925413040c0e161618022807400d0031840b00410703d00300e070010085100030a859007140d11420540d90b59640084c81031000180070b0811a071659058000d003280705410303025807010b0394003590000003218120340d01c071004008800006c0c4c0e12a040050f4a1075009400c004208100d5810704d00d8602820b05410144440c0800d2510507003140e0310352070752407140c0d200b10104c203030255290140306440da60140c40c1c0c4c0c903000005107481070081000e10f4140358100c0c94200c03034205059166011f0071019a561081390340141d120803003c0c0c50305050780720801c61a030080208a04000c07594000e00040340d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 714507239 1250 714505989 714505999
    0x1052a071703070c050a060909051b0a081609080309092e0f0603140f06131b0e06040f03020d0309030f0807051501050a0510020a0b0c03160905030607030b 68
    0xe500c444501c40c8000c8031000400c096030010416a0034032901c5144880144000c0b80d0f00d90f01240303010006040d01905214a02c1d080d41d56070001052407503000e5098420802140c0420b030348120b80c2c80007600f200750903213060800c0502c102c9080011801155400c06880a10000b103060140d000100195100001d03c1d1080420302d81c403a4028406403025003064040c0c4e095041c008031030500c0582140c1c2c1038150b0244003054101050603004440c0185050f800c00c44840e80800f540e507603880840c46102c0c030501c030605120b20740400e1007e14061502400481110344c1d641440c4400d0303040400c07005000c0e80c002c0000060202008000518101902c8206180b00b0300300201c445036251a410b440c0000d0307200c01d5485000005601d01000018018507918440705500042c140d4102000f00b040300000340100f07030094001603d0b08400f54000c125402d50b141d44028455544e02c0e0004800c140307032308161034000c1c000d0708201420048e580150401401c0e2000640204003a50f1407041c11805412980c03211a000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 714508489 1250 714507239 714507253
    0x7020d020c15090319080a1b0f0f03020f070b0a020706020a151d0a0b060411070f02130e07090b01020c0102030304050312040c18141b0304060e07051c1101052a 70
    0x70010b1848241044c80c086c0c10887c2d01e801c07084e000a4409050700310411150b01080c0da24600042e0400c40c4403001076000a60005545070b031f07103026490003015401003507a610a0030700c0040c1412520008141108055090314180d40c2d5540050381d440e8241c2c5001000b20401641c005040b080591140c022007503210690a08164442c0160741800e00c514025104a01d0711410407045061600400340e80c00800f800680c5400c1440d142d2a14000c514030000b40710383c414403001c801d0300c03020350082c9460401c1c50040d501c601d80c2d26140c040c010030091505501600407102684030560002c4147d07442103400002441c94801c00d5400900c110500030070845010a04c0d075004517a0401417041c40f9030b0b1820040000807000013514100020350310050006000c2c40c000013410500700383d00800d40350030507030200010400b0b09003c43d80f1820400f01c0c0c0c200035084214042a00500c01e40c03030b000c1815550040c0d4070141d91046043c011034052180392203100400950811484800c12004880e0104d1641a0241d50354 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 714509739 1250 714508489 714508513
    0x602220524030702030f0a0e04180f020420040e150105030c04150315120308090309011b0204020412080304060f050f04080c07230f04141801060f0e07020d020c150903 73
    0x1140d007214207d9070000d08000504034560415114100b00422194031b0030b42004810340e01e07a5600c042c0940700900640d11007441c40c0d04290012410800c41044c0030109454640394446441621412079203400c0c10a585115210907501440c1108d0007410300030001403a107400c180c4c05043c140c208042c22410580d489444103100703181c503c51074002d81000100c046980e0311908004102c0c000c00f0300303030713210310340040002c948581e8101c0c0c0011404004000100e41c00f20039400010000c0c0a1548107200e2110500da0b07807001c000000d40250720483c801c00c1d0422642c01030a6001d0f0440300b04440318030750403800001007008190a80041d1002c01c003a1000c4134085902c42d800400741c010000c14100b00d070803c00903602143c1c60080d44101c1d040780251030800c400844003d01d4004010040c00208802607a0601514040001c1d0007804c00340c2407a419100d180c5642e055950072103901200c5280060050b00555400e2520218455500d100024501d41c06051201c196000300d500104c031081c0e049c85101d040140d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 714510989 1250 714509739 714509767
    0x10509090c09090412020f1b01030b04060306050703020403020306071107030308040807060606051c05060307030623011e0806090c1003200711010c030804170403060222052403070203 80
    0x11003540b017010880e000000429010b4640411400c07040b03c0c58101d108610180d0352004544000c0034001d1030045400c00394080804d0003401d55810140000d410082041000740e0550002d104a910a8040710280e0307480d920102c54200ca8018004600c2d0880349003040440c1c80b40066507041405000d82e0b51804a140e41c4510440701c99903c008049400403406802c80341d02c2a03604007005c81c03052414000740c80c0400004e80c81d501107001c000c000c1d035502d100c461007698040441140f81142081203104950b110b88110a0310411035820040e009d40c2c11a001c1070390000401c806018101d02c1d002030806a0f2140100316000302404138841c1007540e55203200c950144014940c81c00e424000003010342d10324290529941007140310492a050005903030252000076070150740345c0d5001d0b800400680307040041410350880c900c81c640c80a440b40d40003060300704039180308802070703a54403168580d4814811380d60400e22141d01d4a41411408011150301100080d4180c0d030019940700d0f0f074500c10f40c0d14011078201441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 714512239 1250 714510989 714510991
    0x320d0810150804020f1c12050a051b0c1503010509060a031e05010e07030b0402120303060d12030f020417210d0905010b031501080c03280507230f0f010509090c0909 72
    0x400346c4802c01211806004002c901c0d140110b0881ca0414904140000054440c0c404c11960103c0207800049901510209100c91100550018034815040e042e18007224a6900203029403803191420502050f0f0b146132041c5034508590340800c0380854040c0c10102c06800340004072007940c6554132228808020740c0103200c01005544651070740d50007410721b8010f20403801512010180c2e00d03841041400115610340c44080d8485902c02a008010708035000110f000c1d0290714080b803581400800c001c105194000ba8820030032140c0c40403120760303a03105c03a40100a8605080400d528420821600300605c0c460340182d14114090070000c2920f20340500803c0c80d1041220201a40c0c1038030100600903c8400d1054a508120480040018000c090100c410358000000e4880710111150381c05002c210040c0003034801043e0510014040f1305082d82031a8204d401d00138240c3c4901c180c510700aa603880d026130782c1015404103958460420300c14205001d80450054500d06072030070240070200860791103440103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 714513489 1250 714512239 714512269
    0xf0f01330b040602100b030706080f0403020304031721070807110102070803010801240e011701141612020301032001200c0f0f030a320d0810150804020f 67
    0x14251403c00960440490700d140700d491f440398201d4181081429480b440c41500700201c0e500c00740e51034540e480d00343d1a600c900d50008010039807500c2e201c00442c0da02c0003d464005105108070b0354078043d01e0003000301240c00b00c41c5100454001000304140920900401c070309508100001894003070aa12958000c2d04264000348a0ba9110340041184403015918041e24502d0340c0f0808200700d06141900c041c158050248210094030070603c0507540c0c009400c024125924414034450b54180700d0050124408a0904000030440f0080d1403020400c441c4201e078101c0790400c2d403030740d414284036160a0f40b541c03085c3c00c030504102d104440d1289000c0380c2d42e181c2e80d0001c0f900c80101285241c0c00103102d0040040e09689203d100300d0784134400e050310301240c042d001552001c80c8941301aa80c6004946081c1000600b1310315038010124a032640e80009402e44075490707540c0f22050f45a840301c41c07103140007c080c00b50f44010100f0b20f5400520350302500d00d0640042c8014100b181c10810f040100300b03500540104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 714514739 1250 714513489 714513493
    0xf011707120818060c0303040b22051e0d02070b0d020f1810110a060b0a0f0b030a050109050c121b0d02131e21050601080f0f01330b040602 61
    0x1c83c0c1c9203105a116034444050644002c2d041801d254415504c2c4d0000038400750081624600069034a100c00c101d030941d500d44030300c01048490701c506002d6694420b598110321405000074001000303001c00a1800c4104010754000c00c1c0780e60401c00e0300019608400001a01140c0a01042d0a40e07807500d0041d040d000d0701c0c01100c0d44242d5107081045610a14005810306000d080303c0f06500c2020045914541c09400c500e0100b03000c941c01d404904543d000c4d6100345c040601c10000807422403040c2c4001d40c050f00111000b4003850340c0381c52a881c02c8400035078450180313200070410b400b507141c1031091080d445800010541201304248108510a0740b0100c1d40300c0308258001407444880202c0c006c844040c115211104044400c1c020103144040001d0040381904200c0c1c2c64406025484110746078045a401000e441855a442407007923580c0f407640e900300b820360203a01808580b0500520503151505065880000030184400486e585a94010704c0152005111303030340403400c081440020303c000c160a1380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 714515989 1250 714514739 714514747
    0xf021903020a0f020613030c300210021608070c17160503010510031b08030d020a1205040c1a0d14060a0b070201080a0e0109050f0606040b0a0e0127061e050303030f0117071208 77
    0x32f00b0104030701a80e56596106200c24400310490708850110b803035000764190342d034412a0500c00569040c0750300c80c9101000a94150b03101400101d40924150002d0880d48000b5440300e040500342d8004551900064a00040401c04203206440d0001700d0f8480d03640070782c0401d8131002d0403820340d03005184081d000e80c1c0008030070f02401c1c0e0100307104074500c41e00c035020042c40c1800d035a00580003200e407003141c640003130fa180101a01c02c09001117031398505a070f8508100001c00d11540c0c000768103007242c0300d510038205078200003406030707840040f5400c0680c140e60f141d0741c50303560784551001050901043c9040d5907a902001002460420a664800001f1801005035141c21010041603031041c20641e030003140059000c1025440085a05043d5049180c070308098004c0303003060030400400d0b2140e0700009420074038006a010060000c0c0124622091340e20030805855600b03242d5039201c181c8a01520319104c9004005c10790840c148510550f6401d01541c41c119031304c1d4003050300e00784407100c240d503120380010b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 714517239 1250 714515989 714516083
    0x312070903060e0a031403060a0306110f04240503070807030f2c01051503151e0f06090610050712050c0106081b120601090f021903020a0f020613030c 66
    0x400e58806511b800f5503071324070b145480c0c00070a02204540c40024103050b210141d6042000e40c07081036520b80008030380c041d902d40b9a914100300070901c02c040c03047c0110b4810320303812040c64400c60880740308110949a0b42c3d041d48911004174003e051b01034100310055903a40c8040c84541c0d048401442c0f241c140602c8036805402c02c1c000908448003d4000c620b814001e280000b540e85001c9032050500e007440b0880d01056503182d00c600044240d440603d140c0c600301c0750400a14020007440320340200c00070740d003d0f1942e980310f8081c898801c1d003242c800c0d404100b0500a08000402c05035100002d04034a142040c1003101d042d8549080d0307a0603030000c503500d40100b041c1c91800c1c42c142420b80d10b0500211000807075002c422414546036a07043c05640042900c0d0321403e4240c0c18a0340442d07510700424007181c0c00030030301c0982c001d0003900081580d40000b10f01114425680b840003031024000d020784100d01d40c4407080b82d5800d4074081c6108408a850444110700f89070105940105140c0c0004c400c81180c01c035160306 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 714518489 1250 714517239 714517247
    0x2306160c0f0f05060f0c0613060c05030609060f030106051c060e19030f0311070b0105030606090405120a020f1e1903020309010e130905071a04080312070903060e0a03 73
    0x1582100152660320881003101d01e8004031407000303e030026904190340e9001012414001d203e440190801480f415041c400b8402e43c01c1d1079000b065015100801c101c0c0c4402d0004c403250300c4203554a075032040c031000104242e840e01d40b00d02071348200010700028105036244007060156085201340c074403e00d1002c0300e58041c00054001c10605042d0b08020b4000401501c2d414940c521803030700b02038100010384c010301d543c03a40240e02466600e403040182c0c6446521f41d00e41131491a038240551802806200c01140242c10055406405294006c001c2c01802c1069505003049800c010942c2003144030740c0c4a040f9400e041070140b0305040000c0e055030f5204c4e00544021314a0403040c3e05825844003c0c80c2e50000209501005407003401c602417078036072038003ca41000034180900b00801c4030081e5103848000000c01c0000030fa000120742c0c0a4508150601e5071151080050060b0700c0b0f041000c0c0c1040103054140381603904142d500c01d10703e0805043c8030f5240c1d11f50304102c884185800c40141e00c800c1c801020b160300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 714519739 1250 714518489 714518513
    0x50d060501050309030d0213030506040813140333040c0e0115050a0c020d0203011e050c07030504090221090d0206060a060e01080a0f0c030207060b0a0b0301230616 72
    0x30b0905a207542801c44c4815a2803158070454a24281d010400f50424814100e2190095400030304940301d40c02c043c1000000e40c0d00c8140300000c05402110005400050fa81c8070b2030191000602500b0b0080c216414020b0350b80c47c9400120200d065018100406604000c406014034040e0000e41c1000b401c117940d0624041f01038104880c040c500800310310100354050225100c2d0100e41c9000b5001049074400b142c0b144075600b000075815424412820b100301c0001038200190f071701c03074241444203403600d11905480d441021380c0a070005004002c10301170341506800614031007585116001032000d282025000e021016201c1e0100d50700040044285583d0401c41290441e41c203da6140c8000d14150002c2c11500c85000068140079145c00054481210b44e404020031001420050155510200c001402544000e00c2154850702e4011001c100c2d0901079000300550302e09105035850b40e4208415206800d030f442e52451080c808540d039a00d46078030b0700c1028140c070628110b004400032041d85046803400c49 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 714520989 1250 714519739 714519749
    0x3050d240f1208070c03080a0804060605010f170c0c01021902211213050741010810030c030605010306050a0b0a17030405212a011101020910050d06 65
    0x144504248202442d070b02d42c64000076404a60503949001500d0151800c2003a544040d00084010660440503504504928842ca20801c2c04000841d05c030300054941d104034940d0200060524511101c030b02c10002d0300c10360044004886681040c003824002402d80e401038010000d604000b10954040c0f60301000701c6031546c10040c00700151601e5100385d98265001d40c181c48030090001d400441d5080d110048040c09658010741030765040768035020f0307400d5131268201c640070303040444642403801c0c2d41c039049000b8912072039240c030b650781d4621075001101c48030400744c00b2000c107441c2c038030000002801e40310101c40118441d4034042402d600d142444411601c00401b0100068200502800295103100700003068070865070440014201034003000386103001e07a8008680102c100600f01ca042904588030b8005140510100c40319412552008140d4a0382c031200d51409854503214820250b005440320701d030380d080a8000600301140e50002034400341c044c01101c1c001c108001400950070b48280241c6001d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 714522239 1250 714520989 714521009
    0xc2a03130807180504032106140301050f06091f080d0e0616081303080d0e0d02030a09050906060c0105070309110a0b0906032a030a0507090e06090403050d24 69
    0x916000c003c0ca08080e64001844685a0f074400180c2014001c034080311071380742c40e040e0310311000c00c0c142140c000070819806004c501c000d0307140d03851a2502c0e050003101c1c4500e41658101e109529240c1c03d21200740009000e81d83c544506058001c81c00190712800401400d500c0b006101040c00b407540544405c0d90310000320b006100030020204451f503d041403244482c4d00c51042039503800000106603495449800091541c000003c00040c00600e42d00300365130007001013055554407203c00406907584d04c9041407041c081000d480c0204101c1c9000c00c28141c2c40140648058a002d001c1040d41d42121002c0fa00382010940e240358210034004c44080802c0070080036107100a0503400c01c041010580103111503144150000000101c081030603961380400100d001c584000040340d45485100207070012a03410070310780d10740350000700c49030f104e140078508860903a105090380d074a81600707001403140c0003013040e0103210702009180308240e500e1244446401c117420850082c05208240700327000c0c00d040d911102410b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 714523489 1250 714522239 714522253
    0x81e04030c0b070321200c070902040e010b1602040f2003010b180d0209100e06041b03090c1e05150c03270d08030a05060a06080c2a031308 61
    0x10340c1000494106032008120640b045201040c40c60186c2081c070482e0424140c9103454101c800850301c058200c45101000f910042070f1512540c0c000c038042e0340709810b000c11540303004001c000d0040004010403c00001d40407a20106034010400b6103858030840010b42e680c07120360300d01050324a08007007100032010030010b20f035525155040340366004a03022220726a0560415170345550340e410007480b0351503010305810301c146030240304980c03545000d00c03c4d5140354813400b00081940c501352040340103d05d021243c4841c030400c006001c500410510300f00300e4500d10704000c0480c6103d000002c01550b070064004040605003042c060080b51000807651070381c030001c180088d03640c02a002c02680c007407101c60001042c04504c0c00407070310745a50078484030310b80240144000c0b50a002859005510410a030b010074401c2e5107850040c4901d1502620030720001a620001084100c65110010726a000140c0d40c61200c03640c86101d00300c11514a404010b9195000090300468500d060000c90010074507a0060038072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 714524739 1250 714523489 714523493
    0x70804031208060a06030b190f18180803130501090506061302040e0112150c0306030c080307021008100b120703060e0903090d03090819020108060f01090909081e04030c0b07 76
    0x4085114060b550a142d101e00300c94000d07864815820f003c043c0d40d000030880c0545c9d50081c1c64080f4001d80601071030300d820482000300486042c05920780285900110100c03090300390b11040b0b0541c10142c00380c09a401c548440e02d0200c0c0007409001003103402040680044c0c10036204005e00d51452420910f01c084c01031100304a0341407034601403411070355100c020302903010b074514181440340c10840c0001c254034900520306d041c1d95815804502900d02c16003080c100192142c0d0350550380c0c000c0e130304000e60100a180482da403617840f48401da500034661809910704a51034112720b040300e0f0800d14644800f040380108004140754036020b014010314030081c8140d01070a0000d015a107034800d07007034074500880001d9200001c2600c00c5801000a200f414244d40c1c1c5514810110201d030403010400782c4c00a0340315030104010385020402c031442c001050b11600e10f01d62910300c024000d41114502a600018148540c1010040b105482040d07081e1b0201004d1b0340d14154940201c081c18141c0003161610340901c04600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 714525989 1250 714524739 714524749
    0x10608241003090c140a0902071e0c0b0a080406110c071505040e0412030515100c05031608070b13080702041515050a0215090a03080702011107080403120806 69
    0x640d030303000ea4061650030100c250603000340418038401401c007030103400001559510050007406058044034111170140c2d56891410503405480c0c00582901c1051007203000d0501c1480c04c032203219119000c0c00c0c1e0343c60780c0c601c8402543d8105074004008180714904010810002c2d2140302d0300070300000e80c540e0424000c210440c0ea1a101ea000d080d0814001c40c0701c1641041c007132425200240500c6c00030001e640303010b1420703041401001d4145008a0b082c4800305217240c5400c00c7c40910b804014102c452840358040702290341405c1803500f90303031074042040b13140040003002019600c000e0041c202c0070707620b0081c0e00c0c0112541c000244141400c000d944180070003e441c1d00c0032551a541c044401040c80d81080d00490358a8580394402ca1a200042420139600c5410402404040707400340c0039562684040041c3c480d408004440c0100380c0c0e00401200d00c0024017860007107400124903c00001c8000c5000000301240e403000c98150f03040d04010404104000fa0000e45003501d511603d0b04a4042c10120007040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 714527239 1250 714525989 714526051
    0xc0305011d1609030210031a0f011d0a0902030f010302030d02121e0c0106060e030d021204090507051306020a120201090314031b0d020d0c0516030302030a23010608 72
    0x26400c20003590003040092090070070101450b0000c03c003984406c124600a0001d01101c400110032445651503e006445c0000b02d51100000684881c0002401404c80c42440000b02080076400207803491702141501c0c55101951188481070f00c1c80d2420350550040510744041c07080e035501198040f8030f02110744c2412806882150401c00482030200007140c14101036030154406042c802e40c0782c040b0000d81c096010010110003c0c058044d03c4410203106400c90301d4543d40c800100e040c01c0300304010070400045a01090340010945026030504103e0101100054401d600c0100141e100c00502e00602440d01c1c00203c814030103000820101419a501500f450080c40708000d44400200c00204107180d04054484000600c82c032290fa030348400b00081e8002d4011200e8500e20910340001d0b007003140d0040d022070f691914142d04001c01c001da5035500300c01a500061500022540b12100c8103905034010540c04004c901d40c103030107109503040070300041890000625130081c0f60b44098008000d41e403000505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 714528489 1250 714527239 714527251
    0x4031415090c10090914100902040305150718030b010e010608070f0f02102405090930030a0515010f050f07081e25030e0409150f0c0305011d 62
    0x16103d01e42c46040075140d207501ca60209203a00d0a00740c4c1c40301410030f25404241300e2510201410b07201500d03200d0f00c0d02203006a00000306a136200d64a1802c144252035010b0360b001c6517900d08100301c03903081c0d041e448001c05154811100244110018403241c102d11030030703501401b12450121501d00e00716100420729146a20383c40240401c1d01c2c81c0c07001c250710a010240450a003250107001480784010207200c81d0409640800c14003500f80340101d2107280050303031140200f240000031301c081031152182d0340b0809c41148503545140704403a01e520010101c58042c611961807808009011300d01090703824010143d1503821410810603184141d1080d0700b00b000d46090400d00c2034031075203510311440d10488522400f102807244c0d034a100200311910302c45070014001441805559548005d62900d2100e00b148401c60007800329400403100e285030b0505071301100c1101d00031400800c0059011402c1c00c21602c1d0b1424280c0a01e840b461012032458160060b28014036283c507000501e0710041e80d0402c6c984202800d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 714529739 1250 714528489 714528499
    0xc030e060c1006180e0a1a0901290414100b0a0e06070c082a040908070f12020111040e0a18080d0212060409020d060e010e0304031415090c 61
    0x5484004820464126840540c05007000310545900d601c9071301d0660810302e000010b040049100c906000401c0f150751280d44800c0440e40b005044050480c8920020400301884d90f03246100070013800890441c0070360001651490034449030140c180400e542c81d002e440800328800800b40111700122040580459042e82002e948a42c1e50304400c030303814a070480e261382d40150007103070203c103200c01c540d4104c0c102c0b0301c2da40864010f0070f0351a04450041c0e80e54502d8100d0200d612415144a05054010310301642c07041c1085454038003c0d85c0d8640b00d0f4070b9001c7c015a45c0801003c8e002c2507071030302403054440140d006020302d13051034500502031020b2000100101c1040b522010031445004030b10150741100c40c0d11040e0103807101201080c2d003000350809120007150a20740310101d0784a04041c0f00e600b04c0241c001d0105a441100c0e6102c0c08081c1ca0b80c4810201199a5030003000d2103540188003400155110707624800383c3c0d03410448413528004080c40f440d8030020300036052102c00c0034002800304412906990f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 714530989 1250 714529739 714529747
    0x712061d041707020306040b06240406140c061f12080d0c0e0904050d0f0c02060901030c02190501020c07080c131a06040e090708010e030d0f0f06060f030c0c030e06 72
    0x14415940103c0000940501c142c0e0306120400c40e44a00d0b45200d010141c64500c0340f000780301c1201c0d08100f202603147c0f0050604000900c0018892032004684030090300400746000d900000f241d1400c2d8044813000c002d0a08600f140c03140ca042d0f042c4080082003c00d0301095003e066031503c403010310800700d030030140c19a45c2e1486800280030b01c0c400040f00c400101080c07001d24050a00d152a0144c140b00703100000d1081c80303004500350080148511454010740341c1810080f541d030040d001040c50403100c8066115202c8a4603030b845410480c0070625106e80300260f19030309811003080c90a40b03140c01025594000402d44042915504039240318241024008903014000c503158100919000e5035030354124000150200b150004400014040e408007030850b40390781d0f5100b00310b60803242e000f1210100c07038000f0450740c44201e59a4001910000d070f402c500042d458103026146003280c05135440800440c2001032042003564062148500c0c0d44001d0900c103201c1c940550700145401d403942c0e8100e200714808030f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 714532239 1250 714530989 714531023
    0x7090f26010615050a0e040c050412030e031e060c0733020703031b08071d040f060303080417120103020904080d0509070f0801020403111c0b0712061d04 67
    0x14204000802000c0904512183c41c00c03801001d6510100340388000c40d008402c8075000341090b00c2404004203180d0f03039103400d003030420700360b0124148851800d4040150009000b01c641d901444112507259003190b203d240c032100000310740c1c01c2181c024021030181106010b1080480c007103c0d44c0d20030702d264110401840c41489280c461001c92507800e174005162000c58034508140d01a405000c0343c17000b0207001400201100d204440911086492100240152422022a0940c3c0b800e95841d0b0400a001080101d000440c080071603000f03500a0f070026075850184014040702010700020411103c00b0103103070800400e444014540f040c40020300413000c1d00d0000e0188075500042c2d442c1010605030034060713070810b2151036585a000b405226408400315000160414052003110101c1c0d900c480c83e034640c1c64180d000c0000021203c60380ca40100e45110000001030b03800c00030284185115101e000003464040c1105085590b03580250b11b003440a580721250200c445040c0c1035100b80d0100400301903803180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 714533489 1250 714532239 714532241
    0x5071401022106281518060815031b06030912120a050f04031b030c0615030203010f1404060b0a0b0c07090f020a020318120f030705150103021507080f040602010507090f2601 76
    0x1402c0203103c1c1c082041b401144d004d5001c43c00f0340c0106c01031690f400d26002080704064480c802d210707188408202100040805041100103142e20810440940c2d6041003a040300d881143d101600c0c0e07042281d5036404000015019100d42500428400b0905a191401e580c015000340040351500c11030040700c2c29102d040521880e01c40b120960b1151040c44440703108140c004145c440c03800300720f1295017807015540240340c0030300c5032842a0f96541030207080c1c2d84643e12001c00910500350040d40051035050041401d00c0703990000d01c01c040c0000c0c018140c4526000c110000c850001102a82c0c1900401c8180240c2e42d0000649050358080148100006070100c00035075101c190f07142400140c024210380454400c0d010000d4130010b8010b400365013054400d2840b00810303a8007400002e506c0b0f48805040140380c0c903030b08041c0801c43d02c200c40d124034110740700c00070070496005a40420b0050f91103c6c10013203a82d038009424001000080c81030b040c0181028010981015045540444101e42d000000112642 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 714534739 1250 714533489 714533507
    0xc210e06071d0a06020d03050114012c0303070503190819020d0b1c050c0f06040e07050702131d0a0b0601110111070609020a0b0307050714010221062815 67
    0x40202528180c95440c04041c3d1034288401c030006c0481c0c9804000a0070040203800f1103c0144147c3d01d40f2051040e00b12040071000030ba00e0201e801c459a00100c1c0d82944003003004248075801203001b50303180c1d0260643d000c04404c601c00715004200700ea1043c88110903038508551011409948096124181c42025800a00c0c4ea420420b90141900f1088a520801c007a107101340c841c004c00036200f184c10410240880c8071101024143c00400030041081407000800c0c94541001840c42c1481c640649600001c101c840d942501c1140c0682c3c0306802c103110b503682240101c07034042038006018410303075075165040c2c8204014011418443c007280316450301c4c0340c290300840180c0c10400d105a142c141605018000f0b1010700f604902402401d100442c81ca02e844064911a007120741e500740c6824080e13519007084204070000d4424940d001c0c820941c00880380f408408026079001403500607460000100014403034085030f40a441c0c03541c40f0041110242d041c480348183d90750030a0310100b0071410f800480352052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 714535989 1250 714534739 714534797
    0xa05090c0901031202070f0b0a1107090204030804150f09030611040302030102030903220b07030c141b0352060201050a0c05041d10090c210e0607 64
    0x101c00000300400160001c100321030a0654200e4800507240c888a1040308183d014480c0492130a000d40c41034148918001c01c40042c0803070640b21055501c1c05143c043c0c0e002070b0801c840f88040031170103020b04114504082001348140c5400c003903405581034040c000c03441e580005441c6c0c1e0749400d041c542140c15001214011580507000315500e03d0403660700d82d200d410000b490341ca9540c82c1500041c80d0700210500c81c00f074030110304026103441070720b039402d0709c4801e6008070484403000c0d900c51008617080d0a01885804294180202ca40401079100f01401d05080201241c0d0007240310752000c0280300b40c0c020b05001c1d80170108000007034031000c13210f80d0240a40302444d0f0100c28041140840e040341e040d0806400b40307610300801d01003080040025103180c05a400364615030b440c081000814410000140b039000359415510a40320fa440399204815501440d81c800c012a0140300f5112000c3c001344006d070045005041c04000754101c180e0156120a4040c10800c10000341007400704404c0c0d8003808045e5001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 714537239 1250 714535989 714535999
    0xf0305122d221403060405030307081b041211041b0c0203010b030613051606141b0105010f03020a090c1e020c0d140d020d0806060703050405040f1e060e0a05090c 71
    0x6038007402490180c42c5003c1c3c42d605014800b21115541800100c0e1400b559001000c7c504580d03640a00322442d220041000d01450f007846000320015100d0b0780284064001c0c5950628190144c0c141180400e0b842064540624540f00c2d002074501c040203400300351100203240c54542c211160000a025060011030107074140038000500c266170000241070001c1e2842941600d0020100303500782942c1100c10711512022441e140072031880d0503000da0003440c0348401e4106204420102d51030850840700260001e844c4060403070300a20651512881041c0100807060007800348822039040203244d1030000e00e40503036400b00d5541081001c0e0003030000284200015000c4013110700542002498906015003542c854026082000c100c0c030301c04190182e142031151500b41a9485107014030441d503110b003030194104101444041140d55032030164509182d454035000c03698803940b40c0540501b200030741220203681d140071410084075051034501c50307100540c40350015207690399030825400c3c900d0700d5621603405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 714538489 1250 714537239 714537277
    0x90114041802150301051203030907060c0516060906032a0806120628050906060f0d06060803070309050a151b082704200307050f040f0305122d 63
    0x42c4280f07809941240d074100c882404101141610039100d10090b101080d043d00080300030701c040c0d0b01498000e180e02e480340088801201b810700d00f00301405a0307038100038001134000608018655260045003001020702d00d01010302908942c11014003400c101e10042444001c00000b00c01c1e076a1105661443c10780c0f80156070061611090718511650318090b02c0517003801c0c65102d80300e40001c9204080c4240c00f0000101101c1e1669410030441151194441e907100070b4200c091000140d61703009060042c07030308034000c584846051801401c0c942103504204c0c05016800c0d000c20000c0720a5125001d81011814041054008240c55030a0724003034042c05021003200103002e084810396450000d017800940081545411010410030094416a215404071302155400c1944080c99840007150440035038140b0500d40191014601110f80260b4064119019420b07810002e1040901c8513110048003658020703d030402d8451041c00c001c101008200d001c00784d0300c02c008405001c0c40d00703d560401c00c0d42101d07005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 714539739 1250 714538489 714538519
    0x1101091502010c030f0b030a0201080a0f150f121a0c1303080a1e0207140301141f15120b01210b030f03043b0a020d0b090114041802 58
    0x600600000540080d1500c104080d000c00e003071046c02c245a41c000d026103010100d0b900112076111000c1d101e01000d0b5039900b120000c1250610881d04036060140004034450314105425100004542c082500c2e00381010301d0000152004281c0300c11f01c4901003c881c81ca4840b4440b400d03c902456002ca151420000c5010050050410250048010a07036920242030054602024a410103c507880b0243c3e06c01d91081c41218010300308070785010400350000800011484201c0030b00c103000e488001d03441c041c201d6104102281d2017061400b520042d0a1014081050b1100031710420040314804d05c0280e9070030b400308280c1e22941c40c94024150b074012400d288060440e03404014010104160f1007841b80511611030004040103482c119144072120360f4012001d04100740c642e003481c03581c80000045901051060071100421079014146441d030042e102c00201d10000216100316040511580a10004004528185a40b0300d1800820341e00424000d4000c0031a154034140c511000b0740c0401390040550f2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 714540989 1250 714539739 714539741
    0x80c0a061d150a020d090210031b081b0705100516020714060414030712050c01030e060411060d0b0a120204060b1e161208060f06040b030103110109150201 68
    0x15102094548a580d200101c0d11055680c2c0001a0510804003a000000341c41c03020380d502914455814440110f01070f6100d90004141d00100320128010035519000e40c0040516003a0605686845091503106402e01241100c840c005844c500a500c4500103044000c001041c0f0440e1a810f00308641440745081c00740e0001c10021030b1010800051180707040000b1001840c03a00c00e950280080d00c601c0c5400e0510503c0c80c3c499882c19505a094070940100203031a120000c09210520300440c003030f20000b943d2400040030b41e00c0c01054100c06a000f10280000300781c1c2c0e0448407440e8034084602c42da4800f40c01241360f01030649449010350004080c4000551049808011042c642c0308490402c40c01d03441e101d01c2d05203801407030f00d0a406181c80301000c118410503000181441c103600700c0340c103a0168056982c0b8070f160b00304c0c84045000560003424862030b030602c0c40f541c81c3c01100803903016003020b041504841d560f0105202c09011180410005240c6900524030900a44490910002d0030f03e00300802034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 714542239 1250 714540989 714541001
    0x13051c050f0a0203061f1e1a0d060509090312040318030b0a0c0f1b02041e0b10050301060c06180210091404060303090302091005210105011a0a0804080c0a06 69
    0xc0d0003400b40b0b10001e610f0148001140c0554585203d404140031f08201c01000f1801c1800a1320005e00320411700428000ca240360f030b1503c1003481d50207041e40d48680301550003d2380c2d2a5800a03004200d100c0038800c090301c003c4190317102c8031018201c603400c0c0e549a04088407000d440300010100c070130b12010702005026110040714800d4816640c10300c041c08440c041114401003059a03180050400a4140300145190b5002035285000500100f580c020004040346034680110900001039510010151b0760b003801c2440c0d81d0780e1715031410850708643c1f4151003e0800300c1d0300c100080c611546c07001404a018440294030300e855802808200c040c031010f0801030003800301c900402c4400040c4170b0301c21400e442c282c001d990a0baa40359a800403140c2c82c0d5402d214068030302400c0401e00c02d40a020119151b21500d59040c80c1400541003010f00f089940f441030300311807040c0c00440720f00601c1001d290203202001c00300d41003489a494030031030303030313501c0b410071610764004c59610a1070303400381c02e40c070b80c051040e50f800070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 714543489 1250 714542239 714542243
    0x3260a02030a020f0604030c0b100806010b030603010b010f3906020c2503031416050705130510031b08030d060515070b0a0b01052107030501060513051c050f0a 70
    0x40e550140e9800c0c0d910307030b101710842d801000203e03c000c042e40040d0341c0b5003500ba00022000010b40005031a00392103410004242c00807141200d000c010402c5602c0c2c24054007500d9042803c081404034050740f0020000205889542c0031504031103005030341c554035114094403000008040050030201d6150800203075104169240c090301c070310012900b8030f50141425500720810000344602c26441c654054400881000c92540d035260180300e030048030682e038214041807520440180c03819505103400c0005078a001992200900e02c0c003001c0208401d403400821081c0ca400c00c1740c80c051580708007542940b00f075103900f001005001c0841e0011030b1420075041203042d18000c90380c00d407085000780c91301200c43c042d0744005030800d25000041586c100c01030780301d14094641858041d1404080c0041140c0c080b031000c1021141030782c10f0707042048070f65051141a001d04640e02d000e42c60072a0803002e032504001d50740502d901c544890140714015010407030900040c1d5612000351070003050340041507034030303041a5001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 714544739 1250 714543489 714543493
    0x3070f08220c0303181809080729010f0506040b090a180f0501060507032c0a03080c01061e1403032110081f0b18040c09061e03260a02030a02 62
    0x100b8101300f50300c20002011307103071b0910310341201d03014019414000e08018030046d110a1380410a241c041041a1003126000308039a01c000484000c0c91200308c443c010590000014107a010000c0c4030568035102101c1c00c980d0b02042c0c03a601d402c55440094080801d41c0d215155080f02000c0721283c40845070803945285c03515140401c0503a036141416129440b0b915401000542d1119058582802c881c0d004170400100188600c1d25408190104100341003e03042982d08031008181108030003024011070020b00f001c0c442004840c40000900d0712041e4142c0641d807403402424000d05842e80b001c000f5540c0c14520900b07451081d940104550001e0141520310b55101682070101040440002506681c004120300240c100d018041c0f0300c900c000d00c055600f02d5841014000304030101c42e440c5110900440c09407140c0711180345084a04011908260702440d98003021440d013995541c900d100c1001204d40245419140001090116485808100490900c00030104803d10003a0307001015004c6c0300300703e0302 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 714545989 1250 714544739 714544757
    0xc0501022b0606030603030c030815041e05011d06150d02040b18030607120e121b0f060103030210020d23010609050a0b030703021c1415010503070f08220c0303 70
    0x75040b4180c2e0031780c0c040503000c00d090609120000e44207484166020b1a0f00d50303504210810040080c0680310000600503038188150800041c2030b62074492240102010888000c030802e980c0c2802410316002030480d8801c2007aa030181c0d080c3e01d00b480407a00d0320ba28101d0110f5845403a0070500034107030000398400c0d59204050003000c1b124100003c001d4055502902c4051213892290303101000b812200e80400828003c2011000440d0341d10800b801030000e44140c0001602180380d29540f070035008081c48102c030340c091001000402d80100380c0c501000602031016a0354260950460007a280741d5042054070581c00c0700a560481909a0041c10303030b05035594100140c0d68a40400a1280b1140207044c5441410400702e03844500a900070500088c0c4103c1c1d540e81e40490042c42821070b40c001440c0c0301c081e8012420031101200d254840801d8801c2405c1150071070805200003010025042e192030140003c0b4030207d509400700b84803000c02c0032017451030700c90307840000d1914800d22901ca201c1140400c1c1140c2c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 714547239 1250 714545989 714545999
    0xc01050f100b27061312062a030525020d080709030818031f02090a090c1d01110a0614160c1205040513020306090a0e070302010c0501022b06 62
    0x30303048401c84854000000c00d1002e980f01104080f08031480c1843d4440d0041040c1c03d00c5030107003014a03004250304e40708001424440c1c184203050369152039240544c030030f81c403200c0e910b942c9624800c04000c1d0468503000526943e140a01c01c40c413228034117908240b18505a0401c040e9074001441c11900300fa03551010001e40b1078034019200c8201c030b40401841190305122a0110080d081000c00c041c00d07004040f603040b048008001100c44100f61200000d098000030300420f0390600369048001005241c03800c2044403001600100b81c0c04400c560300782081c1d80704a40e018141e215580d5105410041803d607088444603217010002810000400110028800300090000920b4003015840d519180c5480142080b182d40710b010b0201498000d205011003448041059201e81c00e68183c3e001708800c1c01a903a003004020801c5010008251044160034400d0744105440003050440440c1e078282400740c00d002c40382c54050f0190050346c0700c0b01c0e48000300e0602c10054014003101c0a54000c90741204018568540c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 714548489 1250 714547239 714547259
    0x115080d030b01021212100b0f0d05090a0c1403011e0c02011b090608101508010e1803040b0a02010f140f010e091507030e0a082a0a0f0203030c01050f10 67
    0xd85c0307a04529640910013140581b18071802c15030311208420560300380035120600150160491450115110030200b1528082040f070320560760408250720051010b9400c84e501c8507080f0a413070082d4509400300604644060701d09400c000c5883c02e0400750456907000c2507114100500101c2e42580066080c03488803207503005130150203010390b00d441c0d4406400d1401c1600a0707427000300240032a503040034500800103044648208202d5509115a034212695140640046d03c2c82c1010303100040008101c811996502800402c0314100c1d0b9840c00c2c8140c407400c1030744090303005041c034598041c0210308043d00ca2004e100550811485241414911642641c86c0da080000c401021103050310a42d0100303d210316101400710415a00ca0342501e404200403140100103400e10411480880d03a042001c50700014201002d0b8440c0c0405004a22410b4902810020250f880380c21480280002c0c059148540c25510288111030103081c03500c00074001c50400b034100440e03000048036018824080c0c0c80000c1808248 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 714549739 1250 714548489 714548503
    0xa0f030503070b040201020a05030a0215010e0603071403010f020c0120070506040f02130c02010c0306080a0b0a05071e080106170f0610030e102306010207170115080d030b0102 77
    0x80000c40c10a055a62041d0f11040c010f44240e0540c400d0500190000b0000c20050141c0c801d00d6016020f00003104040101d10001a00841c0b28030712100700b007081d5030702c00050700307411100070100304002400100082030040080700c25400b24240005511780c08000150020241e400d642100d45404880c03803032003002079004a180c02031046e00030002103404201400000480c840c0002c0008144d013502e180c40702c040b22503106035403015035111070040c1c160076050f1241000404012016004101140e660803455000040801d540e581d501c0e40440e083d24802d820000003002185207103c5010143c6002030007912091113928000341180d030b0745030b0603004841401030041040d080404103a803520400c000300c52041c4101d0004043e0349440403456042d0030000b601581d100c81100046a80192885c4000d01001c50355810451803200f040c880e25980c0003034040c04480d00444000700700200c9034400c50140074200b18900c11804103041c0401c804601064080c14111b06840030840003100d04016030311000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 714550989 1250 714549739 714549743
    0x90c05121f0b25021806030102160303090b060a15032c0a060507140307110a050616120e061b04030b070e09090a0804140105070b09060f0117061504090c03110a0f03 72
    0x25140d801d0b12030740e51000104d00e81051b002000541040f10b0103600311041d00d98024180c00080d00d501101c0180000c00a4484d0000000e80e1406040e0307061108244448800d1b50343c00d020159111800c1c650440c248038200148800c2c3c4100380040c5000018041e55000044c00503102289000041b400260207070594030003460f4020821811a540c55106072071038261000f81d4003085c0610104000011000d1000504c103485050301000b8800c00800e0080905070308208c111106c0b071505007401900f8000040d941c0e402180d080030700c80d0010b0f000c43c1c4400340e80520b510080c1341c04000c1c0140108540c000d031300340c0742611056501307420340d6454112807030390f03140b00e800054031040c0e04020a00488041140381c50712444103052051900100d5a0350110340c81c0c0440d4a81c2e095005603062018207a40f10340c000740101211781c00b541c8150b880b00d8819880740d40c00341014101101c1c100d0b1017038031a1556040b8609042e04421300c003000700c3d81e904044035050141c101c1d242c0f103250400e0b80802d8038590504440c007525 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 714552239 1250 714550989 714550999
    0x60503011a0703030209041e061403030d05250302180409200a0b040b0a030e030a02070b070f12030c02010e150a110f07110109090c05121f0b2502 64
    0x18003107031002003140c0c1c401c00054040540800c800714064039103004607a41a20075040c04100c56800070042400c549040d0000300010b904c540d01c2241039a00081901c0d802641e41d03a0008082c0c6490717422600c580030009498038800c1107034400041c4140c0560107000d8113022000b040380442c08200c10082220390091005080c00255841d510803d200d8100c10304060700060440440306403681c10994454101d5403180c004c0c03060000d607041c0c200e80e25005020398030820303000950a0412030705020f9202c1015000e02c10507981e000c40c050b82405049090000c1c0c640c0c000c440802c03c181189001005884540440030240d0700b044141038444100045d4082000c1005600c6405519000d2030381c005025101c55841600400b405003035900e454401c0100314452007200f41198200324040013415807800c070f0340a45030b0030b460400c981c21070030b811000b261310181000b8240b034100d564141040311103808040d01c0904407146c595021444802c01001000803d081d14180391801001d644244403003404c2100c000c2d088 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 714553489 1250 714552239 714552269
    0x1509152206150807080604050d030204081c0521091501082802030319031a0f0d0f141f0515060a021911190e060f0307050a090606080106050301 63
    0x85031641d0b100310b185000503002c00322025900c8145a00d00741c066000a12a6003206041c0020428208030365440300e45ca40c03c5c20342c2014501111261211124103000c2007600c00500762842292090b400c44a01c5003040100058100207400851802941103c0050092080460070303281241c1d000310050483e110040200b00e01c101c41c8800f07001d0b160201c0c0c0f5030300d1808408400c81005a60900c09000c000070001a0b408030004550001420380c3d40164402525103960450601e240d112580c0045410800707990301e01200d009032811b090350a2840c880901041204002c42500f0680405c15001410303201d12011900c0d0b5215100c001168400da602c0396009200c440450554205003016084a003107600541d801041d8540070b8105c442249042200c030052003a48034800b919042502034100000ca56040c1499030628a81d000c1d405005042c032480744019a4009515940070400400130b0940030f0123003441503545204107000361069000e0722000c40c200100214009110324240d038120b0703061300015000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 714554739 1250 714553489 714553493
    0x9020108180c042409020a0f0c050a031d120706270302010807021e01020403020406080f21090a080f060915070c1515051014040b0306010215091522 65
    0x10440703134a9040d0766104680b0011180e8483e10a12001021800005030b03550055150003042400c040442d642408400d403401c2d004200001307480e0a001c1e40c503040c00b030170400201e143c0ca050b40600103480f960028818900c800c4521001c945d503c110b41d86520784401e12404c0d00c09010b60110401e26050420824900030070140d0702c2070b2007090300b04c0c1090055981029125055204d8400403500403001030790001010011030405208000003085200040e1545043c03180314940c4500c02e22070400c0d0601c0400d007140c003034112000202c4507071580060403408103d50380d5082e65101c400105100ea0075000310703c0050803015002c5982c2c14800f58441242070301d0f42e90900140e5082e40f1740c0714141c1f000b24080e481594640c0082c8901d400c504041501205d982d454101005070b0f0140c560035050420481e99181456a003004d0300391000e5807050201c443d103075130740c080040f40303400e01100003480c20116107418096400000f10361840c80480303525040a20b5640c0780c014041c444120011015607840c11108140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 714555989 1250 714554739 714554741
    0x30917090607081602130915090602090a0e0103060e0a02061e04030b073b010e0303090607150c020d2109140d0905090705070b0709090f09020108180c04 67
    0xd86800200602c1c1000c0c2e05482c3c8803482c0d00301084a40316050900d040d6019407a02010300c4d080b130ba0840c007041c4060b120030381d504001c5400b1070001c400440d40b0745ca034180c00c001da00c0c1c059450540000d8181180f0a948030305039000000e00303100c03d07a070092400100c42d00318800031403940f2140d03402601e02450f0245910301191003a0990700d2078007074402c0a01c80400010000b441060191a4a50368980485261a6800501d801c070f441c1401c0440e2809103e01600c2c13508202602d40b140007400c0ca0220318100c040402d045101f58a5100e9002000050700820007100050600c00b1180d101410480080044401d036540e80340341d003441c00454900d140180c814400a01009404201c0d210081603404403076981d0004860004454043e41e0089500c002d00c05511401c61801000d0403107400c8000d00344580301400920602402500c02c09902c80092403190249200f500103046500c01004840c494a0380c200c02008805400ca001548100206070030007012841740303107440d092001400d41020042d0401c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 714557239 1250 714555989 714555997
    0x1406060f04050105031806100e0601020a200315070201062d09020c0a050a0501050a140610081e010308180405151309050f010606030b010804210c0828030917 69
    0xc145c1c4079550b5641c03000481b090241038090034070700d10004801404d0056120702d01400078000c41c11984010310010128806805400803204a055044004591036020a00384691215283c040c0f10241c0c06124045505500030300848107035a840001a04100d0060140076082c2c00306000440440078040c0025075465004029a492020442c1e0400c0219590361303003400701002080d9402e9641d4410007142c002d640c0102d0600790480b0001012500e0500d0000b458040003656032404c21a0300000114002d4180320222483c00603540040050f40c1c0d80d190146031a4000100b10060840c81e5058190504260181c68020300720301241c110f031440e144090064911151a0f07050141da01e8451140200f4414040b14070070102c40800407071650305101307002d0261480300070302e1410081aa400c10010840340b000f4944107420202c000039100c04111411a505610444094410100010440c3e02c1d000c04a6000c1d115500f0700900c14203004145806a0407a1017032200a41002c90707481050090303684003c024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 714558489 1250 714557239 714557251
    0x2303070f0330120902091501090b041206090c08060903030702070e061c11102007180c03060527010503061501051606061719020a0e130b09011406060f0405010503 71
    0x440c8046500098031b48841518100070498180c0c516000c03030f5038840a694007420540c00c0740c5103080d180c18200110300c1512007010b400c0310398a4219000f08403008041c40020610801264007500300401d00c651280d00c25035812000d803007000400500c1d8824421482e02c65040204a404110056070701070040e40350705441103a80070302155260603203954404401442d0a400c1ea03902c000a01e00c1c4e2050421042d0703074014030290b1380c0f15110400004046003401d40d0145100800400c116044000c150003030b103440d4000742e90020004011031410180e20007000c21241303601404884c141d03640d00516071510300645010030700d1341c0502c0d24036040354011001044544801c3c2c091880084054440b02c080301c0c070326080b03003c0c1c20350b10100c91110031004002400c1c903020a280086e00e44d64043c2d0015a0704402842aa40300700c41d014006403001041c02e26216603103420580c0d540707030742c40c0600c6e40324002c00c0703880c03146030300403d180340440e00505003a019210200145041d062030035050000540b001e420007454 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 714559739 1250 714558489 714558491
    0x100b192c21012414060f0706090209010339051905040203130510060b03011503090f11030d051e090a0b07030c0c05010302132303070f033012 62
    0x14404074002d1085021481c0410341d0111208880564064400b030641d0108034040b8181c400000a60303144030442d2001d500440b0717050384d6401c6c0e038641080070309404080650f01050700030001050000001401882074400200a52a07100c24075004109205003d0b8400c56000b40e00f2007400f00e810500032071203600350aa03008001183d69030380002c050f40e00031282074002d1500c4c00e402c003041100c1040044015208410244031803070905451441e01c0c0414494009204200e03025610070340c2c082d5100c110825040048988101040e0820040c403d410f042454024800c20000e05056440707031080c0c883e4080e141005091401c014a4000d000360068100154012502000001e51805440040154600c80d40321100d0106d600e080460306046190b1081341410b00410441c62581c0c42d0000031401e03621094000c9004400e03441074420800b40003181550544502c040c080343c00b00c007042000d400c803881f4103081d030000c43d404222202c4e02001c04020040ca5950045c1500c2803a00035500c0d050b00d0f04020700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 714560989 1250 714559739 714559789
    0xf0105120a02040e0d02120c0307060b0126150d11040c111504110105070206161502040905060a170a03081515120106030c02100203100b192c 62
    0xc0c01c95103460419000d85e80094503042010341c0612400c620b200c40381074920301709828413005544a124880005007038540d50001e0031700f503a00400c0502001510030300300c445405110528001c50380710668854840c001441860310305890300c1f010500760b041d4440c1e400c51805d035a19043c440a000704011071001d020003504d070b1003d02c074804c0040c441c0f035400080e800d81003820241000c1c11001070401d41c141c1001403c011480140c2c03900c80071034070040d00d58402c41d080302c28141030500700104000c9269241500008001070909103e40241d400345400b200c0014406540300b41d5956180340344c071030300c1500750098059540442d011726001580400c0c01d41d103e01c045d0306068001950a00305c905843c4100c040440d405254192281d00c3d2030252856007820440c401802c5000307590340c070006c11200000c40d0000b00150410f0070044050004240010b0881e44461a000307580f040700c0300300d0390302000240c440c20355001803407800d105a00c030300e6010b91158141c26591000744000745400440035814240740b10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 714562239 1250 714560989 714560993
    0x207050c0d0302060403110115060507030314100501181202060705010b130504060b0109030302120d0b04090303020c120316050d0b030a0b060111010207050303130515010303090e0f0f0105120a 84
    0x1004007101039200e580500340074036041c5000381210300a13003250300e410fa150880900729080c0c5171b00000107582d01c40c2041da848401c00e1600b2809884c244107150303010318000d028002444020540f14054030026200c030708505c003e104a103181682c4600c00c40300368403020780d01c42c409420000300904000340039400100c1d102494401240c9089410b50707211980a80da44104024004913114107a8000d00910b010100c2507e0b40d10025683d10309092100b04010001a052011010035031110000c040007070018031507040907060240094101c100b142c1d01c43d020310000e150303202d00144203d0b0310523000380e0b5034903c00040c00301c01103816411110600304100c0d590307030318000c1a5a0801451100f5403140c1540401031800c0030005100107120201c0240b04c0c0e0051014000203070002c4243d90303000184074004d1202c0ca1150800d01d240541040302200710040c804004414180c0c0300b0f60090907209000c000c2c43d03090320380c8448000c42510440d4003a00f01044a4010b11445c0b40c203c418aa154040c0000c50b0b800300c1c0b0715 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714563489 1250 714562239 714562249
    0x1b070608061002010b0f0112090b090601033f12090b0a060602012705070b0f28020c09191109090c030103020a06080a1b0216080c01050d0207050c 64
    0x940029011444150030040c03140b401d40d00031001e03000c031031009001200104012414140329a90954188010500c40a240880c07591141c26031036007001440d001820a9183c00d80c80b400e0170300044c2e030009071a4502c042000c0b0301c0c200440305001041e07042c61030218800c016400788030391080243e00b08003110811589400040c0603088160b80907501c610301c02c0c01c000740c00400f100c0d0998001c000390390501d1304480c05500c87c80e0000580850400d004c294060032442c21608003030340c91b0000c6003084004603011215035044e07009411040002c001e0a011000d9401026151442a20001d80181d204512003001800d114148030f070006483c0120882c0c0d142d041000270113851481c503021001803030105e010300203850b21a44058000008a20b07240c41c550442d004500c44003802c2c0185010b01400c54080b0742208025071164808540c1082c01003440f424040009483d170f08c0c010401c2c01074400814000c50318000102d800010f803e0144c484520705181c000d010800b07500321100586540c040c08500211680701c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 714564739 1250 714563489 714563503
    0x190509010c02010c0315120c120309030501050114090103080c0f010609270c031707150b09060411190207050307030501021c180807050f0a030e01020d020c0906061b 72
    0x89a0004103503140080300c0242101e49450000301054100100031640c0b80700800f507181a600306110302202c99555081521b400d07103d82d886803485000d00e10030030040c0759000403150143d911a200901269907901e01488000191410155104442c20b00400c0000c1c0c800000700721918100d0184d030b900b0340c8600d43c002d0848113141d00102a00e52101c0d440300e06010b20745540345801c07801644094075040c0755142d80340111110300006044126803100c468408044009590903141c0c03011584000ea90850606000381c4400400d0728010030f0b0032404102e10307240c1030080d140000d545109180c00c00c06882c80d0552218034080e00042075000b40b1801041a44050042c0d0001d18000c80c00175a80e01041c4c203005980080e600081e10110745060034906121174011012614075402c078661548030b1003541000c0c1c2c104054054501103510a0384140810190040007003da01c1000f6000d83d01c030741000e00e1041e07031100141da8540e64000c0361038000034041d142c0500034000001e20414414440381c0a250708a25101c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 714565989 1250 714564739 714564751
    0xc18130609060614070b0402060f0315040609090b070e0a331d10030b1201050601020f0c01090b0d020c06010e010918030e010e03030f12090706020d0203070303051905 73
    0xa11220240114a414000c2c80c0c0202200e00d00601c031800c001d030100d8203d01400000600792030b50b40340450700707664440c1d09a07150390f403003010351690700c0c104000c69000005a4030141400b440c200000001c0a1840d4410300c0d4800e41c011070300243c9a036070080300302c81d207110021103103901c80c05810000c05d5501c51404111074036101070301404100010280c0c61345801421400407003c0042035100700030507200600c00402c00100c269000300712141d10790015000341102c0100c2c1500130f191500c0380c000121054000d03501841c0d00781c0a072800310040d0606a9101e8400c40b400e03602299078620b081042c613a13074030001c0001c0403005100508001c0048202c40c00c154013130b808829403003811001030180100324801c01d40c81040085010b03a9400440d075000d4080741030000d2150600164101c240b4203078900744115400d6070100140c099442c161841641d50380b0000f030341e00e10002d201e5050301150030b5000050b00300b004803450300210308092440c0d1342140580300c000e040380c468110050403103503800c03141d0003106d001da4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 714567239 1250 714565989 714565991
    0x3090b070b040b090a0c0e0c21040318050a0e191b0f02060f061207030227091603021215010b030414120d110715020304020907090e0c1813 61
    0xc102800c00100030f00000d01101034030f40210b0104000542e800c0d01c000202c840c55007100010740d0f2103000d01e50260003840c4034003582800100c0c0180500d1702d810a1b140c03203540b00c0e46035a518088042032514003100140901c50308801da080d0305000c80c3d10039030b00030765101440345407040403030503002c1c00c40c81914507103000c01010211070400c0c0c030b20342034003c0100c0b4201d0000c1c3c401800240f4000e0326000f2940e001510744d90291120105040c0c0040d01444100301840c0c020704500c1052201e5000d14040a2203512512a010300401c0415090b11020a1003541c0c840080070b4003074150b08607020048001c003810000d84291003031605003c10074400c581c0890007010390210103500d80c40c2605000c4c64541e4041e042c4021604401c1100c0140030010064400d00511010001036400a4800e1250340d03124000c1c014010344121552400840419001103110f24400d45005519840d024002c2c0c41c1e10285004500106c1003080025600c8034541c0d0240120401c1031f480000c00d0700140001c00c0c07000c15015030b406065 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 714568345 1106 714567239 714567241
    0x1b060f01120503251b05010e04060e0a021c0c1707050a0903121202030a06082407030221090a120f020a02090c0c07141302040e1303090b070b 62
    0x180c0c1c41940d01242e18058075096101d140c0c17501c25140042c0d0614040300e0306040a0040c1011680d8060b00b400d0184ca03400c0150020f50000000c844018901da003207403c40f000c0c1e90282d0b9808403001d0702c0b000d0030b120304142440034124004043c03000340041080b0b1440401c0d4440400012070340c01ca070381d20741c0380b040c0e8500844511007440078070190300340080240100f641d017541c0020220f8041c0002c450002a5100f09061012600c1281c601808140000034031218000c0d00100a00201c043c076000c0c040302c03c000110503500702602d1001e80c0f80d11035400c24040000600d49620110100d04144509800c1e12000079901d112251009000c2c0d0340b07810100b18021900e03025500f81101d1741090319205074580e03204041c2103200c4a4103910a500b981640071000e481442101c003a0b483c0241d00368150398440f0700001144017072800c01c80400c081e581c40014400ba00c1d4018100880c884c1c0d00907645 = true := by decide +kernel

theorem cover : BRFrame.Cov 714388489 714568345 := by
  have h0 := BRFrame.cov_init 714388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 714388489 ≤ n) (h2 : n < 714568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
