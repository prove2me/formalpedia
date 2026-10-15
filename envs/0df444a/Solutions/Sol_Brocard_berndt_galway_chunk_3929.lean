-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3929
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:05:14.978388+00:00
-- url     : https://prove2.me/submissions/a8b58eb7-60e0-4336-aba5-be014cd552d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 706474820 ≤ n < 706654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 706476070 1250 706474820 706474897
    0xb060702010c02040f270c05031c050304030905190305010e0d0905041802060f041e0506030a05101503090b01091e0905152505030c09040207110a0b 65
    0x1442402c5100160915903c0410900740d10040013841c4031088501c003c680c0c089140c00310241d026100d0400400c002c5013421802040140c0003030000303041c58400d541c42e010070f8010400802001000003005d040c030440308040240342c041c003180d52851510b62010704406160005441a40c245030030200c00b61400100301d914915103580748029207061808200c060400c0c00195001881c41c3c500c582c0243e41d40c0401850841c985014450703036a490561019100302d80400c101035402402c090410954861908a03a8082c0454a000420b0f544102462801c03e04640100500714121010b88070210707010340c08201910301a080c0c1c00100d80c0e8425580c801c4c0d032207103164041446040c40c24031078400390f0398108081d013612480983e94240d072170100400f0100b8080302c071000c090a00f88004160100700741e00c0031003105298038140c0d282d4a410303001c0303481a201c0c801805020320b078006814000c0c00706103a039a04100700c006000d000134994503070148070a50000045040b07015000036022070505844040240000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 706477320 1250 706476070 706476077
    0x1002060403140901050418091b1a0f0306010f20070e010b07020607021009030b19050603010b01021e030c0a211803080912010c050a02251202060705100507030b06070201 74
    0x26060414030340c40c203501d09501f40d1320709840d890311a0000e02e4012058860b003d98031402c48055140c401280f06e8441038085282295000300121690322007800c0c200c3e540100d003030070b1203003800c61014021901d000070f0003400c0b41d1014440e85680d50120000c05c0c20f20499001d54048030305662144041c7c0c11521400c00000c0d402a0200030311001400c11410307611090350103090103582c4603075a44a480c4000d204686105d4260505190a140c0e00d4040c41886c1d000315040d002000103d4150380042c3da50002091204445040e030411480540350410403604024010780071345002c0c094030314018207604103403030070240d546082240b0841100e1041d21500980e944a08010110524544584480d0780c41214291703000030120700400d0000c0b109001d00c210281d956070350650f8a8807903110090a0140c05050540001070030503800307901c042e13800712420540b04070060410f807914031031001421342d124003a8014801d00070f620340d400e01e03120280c0c8414819019514203001c0101c805e42042020711807240d000740030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 706478570 1250 706477320 706477327
    0xb040f060e0f0c0f0a020d0809010b090105090c0c0f0a020a060c08120c1908041b030b04111c050708060a0608150a451a060f100206040314090105 64
    0x1402c618001050f044550809203929103185050810010341c0b0502040015038017111056440590080110f80e001403444001c0222032078410000300b07a19410700c99075201c0c5002401003071076a002e070360032510680b40103401c40303a01c2140c008035980c5448100700d0507441281400070004229028030b50120072207074010016413402c50450404002070034060b1118082c00c106101d0801d21109030042281c000a442d151008c162600385015900204035560f250040000c2c4072003000041d88910115400c10b5003c845041340340e441c00c1c046501000c0340342c080064900401c098006025012514100303691408069405030381d034001c03042c4203640c00c80c803401e00b0a034040c1403060340c00048104440d422040240000c128040700d03010001d00100c041e25010701090108003449000e828899401940004000c503a00c0d013005644c80e14052007030340d082c22040ba4241640090340581d600041006032003001801007201544680740290340704c9040314110b0100c0c00c0b0b098150303009861785c000d4540c0001c0c143d49242c43d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 706479820 1250 706478570 706478581
    0x909010b03061609031211070b1911032233030509100f020a0327080703111204030b2a090301110c010c1e0504050411090d03030b040f060e 61
    0x4001907007100034420821340e080044000744007045ca40d000901d640e6104d8201c2000054901c2c00c20322940c1c021807111104200342c0121988911045901c0480ca003041000e88512020302420b40c414030208401c2104010443c002c5142d07900111341c16503001e80d00c610340c04582e0f5851010905a0041d203100c00000e10b4803280c0d40705109400041d4072500260a40b000c03498941c40c00307400c4c2e4031140cac0128105500400c03e80c02881e807611405648090000d801d182002440342c1c0c0d01882030301c1070f00c05410344d080000c041e400d060061000b403100006d0041200c0a050003c00160210340040c0021a008070316040800ca0920030960171041101440c2c1c80c5042803020121000010703405a55840d42554072807940b001500c1404028040304a61000007268240c080e0350000e14034485030607504c01191101c030000d00c5c0382d0b0b48601501e081d0360003641d00040034000e6240100c007600501d0321455018a111b0701e12010180c1c550010b08900300c00b44d405010b035540c07120580080c0e4a0600445041e2100080080c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 706481070 1250 706479820 706479841
    0xa0906090e0a09020d201c0b07050a05070512040f060c020306152814010503041214040e1e09070308030a0507051603081b03010e0403030903030204090f09020909010b0306 75
    0x86520b10003440b19003200450354038030492901c46c80c050341d464200120007254608010000c5810109120002c00c06400715030358081780c1c83c50150000341001000b04010254a016404841d070b0030341c010086403042d40c0504000ea1782c42c1c3c06401003c154102242000625074010301c00e8440b00c650040140030300766241c0d1902c04041704d600030100e5000b52205e11a014280c40c101d01c1120003074051110300e4045007020140651000740010150400804104100c089140405280e030745a4881c51708072003030344005042202600540e0020901d444180d01401880d8425025094440704820403903c0c583e5214404545c5800d030310722000e017181100708000382034507446130b0000c0e03440b4407141441420184c011129140f010281201100411000400d0041241d1100141c00f502403080350014510340c1010001050104081e000406160b122f800c110105030103601550090482c0380340030048144070b003481c5005003d803800705034010004203012418401040c040d581420310050014815616150342c9079 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 706482320 1250 706481070 706481081
    0x1b1002070f030c030504050a120209070f1706150309060708010602010e070302012303040812060306101403010615020a1505130201110712080a0314041707051903050a0906090e0a 78
    0x441c1000001c000101d1a5500c01904c0d2380603008514480c41075200a105024501801070514001d22110048144c040c0d5449085040d0880402a07000142d0702d4a4012070498095030029184c400070100c200400d9941c0020181c0c0704821a03501c00c0c0e01c607665400240c2c2255100c525640d41a048181d0500165009030f582e02d90748544040d04480e60584091850010740054a00301c482c16000549a071a1404244d000f54005004801a06850900650102c04c100042c41038401c58041d5000211256800f9808140204400c0c1a00f169403650303040c00075100d40c2d404034219035142c07202540000280103480303140c2c4103190b01c2c0800b882c40140b41c1c0040d95840070543c1f030071207544519a404a05e4000c402c0e441003905200c0c1c01c2650b01c581c460400031302641c85504401101100b9502000041142e40600c200c10f40d010346411a90360359181050790602c0030400c01c50542d070340c810328000f040580c854014080c0d50490b0740c44041081d161031045403c4840e500c00e80c1011304150000c10a00f10303107075102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 706483570 1250 706482320 706482323
    0x70e0307080102130f06030209060414040207020a060e1201050411010806030313060801030309090203060a03060e03130b070b070206070806150712030f0b0406030b040f050a02061b1002070f030c 85
    0x2264400d99881e0005030990740f1a03136600346000304425082094083c6440c625000d8590b9041c113505140010000c61002e00a5200d910300c2292010750810540d21190b044410840c0c0250500d00d83c075449500140c8244914480c5500495110041813a080818450603004070781c41000c01c440545040011103555070041c0106a250000b00010b1000e0282d00725428010b2505440340001585142000303010310a0a5200c0b20000f4010070400040e23a07a001018000e0780d81c802ca000568180c0118450b1943c014240302c03603002e02d03840c00c000ca80888042e000d0700080d48940300580365940e40000480c4c940c80d003a0782c02404150b9140100300185040d1407504d0700a450100501d0602100e03403901c440100310017482502280d52070002c0110f0030401e0064252810b0b003a6030a00034145190340d50218040001c102403c404d150780441410080b00717004503a10150020801603d0700240c0348600ca4040031039648820a202d0b4040c1ca507100b07260383c000e8600164014002001400c40303900d0540e00000707216030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 706484820 1250 706483570 706483573
    0xb0403020708060108101107080d050a1b03050a0b03030909010608040303110f071b06050f0f0c070b12060409021309231b030c1c031106310b070e03 65
    0x1049440040088a00a252000c010454032505541b040210b542e0030b0801046002d0400038100400c80e0f04084802d0010820f20000d0940e56901200004111b092582501a1011a400c80c1c6803603254021501880d400001007200b0030140040582c0c0f442180102500141040010803040c5d01842c10954054064100460100c1260101c081503030f00041642c0e180c02c0e00420307070000340407061892a0407040818110905a401c040c1c010b0201d000712034010380c0000700003c03018120303540601034a800c1d240b6201200c000680303410401c2555008046030601d80007018002420f149454040e106807950060449004100d00042c030758040d05004a0503140381c05142540c1c0490075400c192580d1030b980b540003903c200080c40700015600015000000e00c6903000c038070b6403010740e61152040e0b0102e401c1072030104122452441c0684020182210444079070040750104820146201001000442c5c0d29002c03050590440c000326038031500d00d010140049990200003840240a0150f1740c150800040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 706486070 1250 706484820 706484833
    0x3090c0608090606030a08042102030a060209150406120f091b05040c02011b05130f030602130518150301060f080708010615050901210212072006040b040302 69
    0x2251241144040e610403400101204104800c2e502c0900a00c1d030000012009040201190303100c4a01070b01450164200100501450594451a6114212105078041c06845a41039642041e00c02900440c140e03901070103c44402d5840380500e8012541514007544030500c042d0f101d03003542d40003049907420340e20003a540c40e000d038001f040f039400d0004401803030340a00c1d0503220f042c030082c0015180c0600c084401d40e8104804055140000d01ca003800a108905c0c103181c0382e42034985010705900c52a841038a008209500100510841c0c1d00108055001545030b070342e00e41d646500344048111000882c1c0407001d8910041480c1e80f411800c507070055240140049819910f90407034002440c07041c1e004043c03d40c0102010041c0e460203001c3c03c00203001d00e560258075001c61180180c00e80c860f041900c0c0c1041100e030110b020040c3d0001202401d581040f0046443c1d03200d01d02c40d25044002a02c210380810a16803000504903070460020449038030640c00707041c00307807a950b0300c40b148508081c004806601580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 706487320 1250 706486070 706486073
    0x804060204170606010e010306050a1203091a04080c010e0924061c06080f1905100504030e01090504021606050c091206040c06080105090106110c030d020a15061508070309 75
    0x1440c91035a01c51003d003450741020070000d402c5951041009040c07505103041084290765003580182101e61041e0b6840d03400c0302c14070b8121200c0203141c101101a1030314904110b00e01060710040d00030749001604407030a44000600540310188681210740e44038660718005504480b440541003402820804214607840300714000508540000340718000304d0034040d003809420081c03400785100500100000d09100c1c40d002403516183c101c044100c075030540b4282c80510070010100a0721040110302d0704100190f0805240003002c0b094448001c600081d6034600124962806208a40380060920f800c0b100f0013900341d0700d15000d0940100a4a04110301f1704c0780140d03c0d01c40745400c26070b031002840034081070b1400380342c0041145c2442d040842000081c0006129544404003514151417160511140b1013ba03100554039001c902210260540148025002c025400003200c2d0b140781d2140d8180504030146001c803008841c000d216141120100d180023059aa0040d041560405050f00d0301145e540d109 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 706488570 1250 706487320 706487339
    0x1112040b01050414190e100c0801090b09130f0507030305031806060102032a0307240501080c0409061b050a1409031209062205040f0e1c05130b0d050106020a0b070804060204 76
    0x40c4c220b200740048d1a400540212584041c00707070f0152401140c10041e51044030080761480c2802050583c080c0c07400040ca100f40003120b540b034031b001075009007110403251300c070328004080340c0090750f00080041d182401c480d0f20780030110b2203500c1948103a00a41c101450005032000302c4c0444d1001ca900c0c0040d003140c8400303d180034001084554003614804c209482054006040c8204104401e40e00c5403a20b0014403044070003299000101c1011500404d03030000c6c50400b20010030761101c80710781c2d05134810042d01d0902d030001c000d45915011610740511051032480c000000d845248c0345507034190003580b00420030003a000050580d6a6001d420030b41002d840004e0800070f103400b00b01101c158016020204a9171415005040c11204030007400e01c501354085032685c1d6240704400403103542982580d0070300302140c403520968104442807141d1008641c1c1e610710848065101c03035020500d40d030902c400420b01900003c0d2400c90f1561102d0000810303601c410046900c0d110141045400703580810000540089 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 706489820 1250 706488570 706488583
    0x90f060c064d040b03060a080a080d1a0612060111070806040b091905101a0105120402060918010f080319050c100908030906010e1504020903011112040b01050414190e 73
    0x12240c0191762401d01104200028120398044159544840ba14000044420742502c0315011400c202140c0c450500c00101c020030140703002c3ea904030318049200c2e40202607504e500d90007681c0a803110366008404410486c1c40f04102c0c0160385507580910041000180c1d40000154803640760000c1e07401803040c8903020505440003c50aa5159101c8840082c4810f44c61003001045401d00007011401c180c124006080e5019031f0039922000c5041d080040c042d900c0b4402241c100c4c0d17500900301060042c0b07186030a40402d0080c052544421102c220101d402c00000046562281c81104030a010800426044a8079807050b00700e0001405041c60000030035803d4041d0304586407103580c0141d00c038a0301c040c42602d05a4141d110a1820b040e15007801505509900324505c50b5005540140c0c0c0d94120602190141c100400f10740701c2c0a1000032800740d030301c1240c01a1070003648950400015a6170ba541040240e815078002451805080400f0502500450103400c0110440000c04904506258190380c1004ca = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 706491070 1250 706489820 706489829
    0xf0c0709050903210f0103060b030f011d01140103050604020d06090b011805070801210602120a140a09050304140f0301150603060504110a0e01090f060c064d04 70
    0x92010840321002c0c5180c0c82884e54010003281400f526240c080045250000b0600c0048d144554485140750f06403400c0c0540294004100002e03c81e100041c00d20f24510800201c6102c2d080d40783c10402a1629810201c07181200d400c1002481e40e9142c0d47c082100380244000b0417a000c650720428107002801032130300b69008003064404110000d0740c441e085011380350300030306031801c111103c00140b044400c843c1c40031501148030310404031040c1142c0740c408000c0c41812a000b065614000800a0203205c5070080d809506002450034101c2d11144001010307100d80d004020300c9a0003d000620119294006400704510010030800707180312481e01207401c40700c5205004400304468a400d00160f501402103c00920301900e040001d5281603960342d04074001e084100042182008540310b182e842410707204083c107400504c1d00204c1d956000b001c3e10210b80450101c400b14103118100703804402c94150004814900d58224154a000c41529041d0a0300541c24a0420780614041c0503c00990006000030300b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 706492320 1250 706491070 706491073
    0x115081806010618061110020a051c0f0e0703110f01140304030e0906060708030f0c0702150705100608030909041b03050703050c06071502070305090d060c080f07050f0c07090509 78
    0x15846089100c0c1c4111243c10410900901b540d121a007a20300150b1300c210108140001a240d4650040896043c4182c100700c0c0303040c02504848080904146d400a150703071881c55010451552080d1609495200903c0060f04514405282103011b041ca0079541c50001c005140003104105510398808060f0410380f0103a00058461070084c0c1c40342032552840c0c1e0401800c840032800c0c18ad03607656040191000901e40500c45401d070011031403204080b0180c40c00c0d1980101000016a0f8140302c4004c2d54002000558803441603114806014605e840361400f070f41c6c4c040d03000e103190080c0c04c000e01c28a100007070001c580d200705218246640310420b480c480d01852040000e444072900d58107105180c03042c0d840d141446200200070020015440c03030241d00c12000003800141c0c94200c10300701610980103e0381041c2e0040c40ea0080101001100d5118034038540903600c2d1006540c980c00701c0c20000c00021191100031401c1001114203d41c003043c082d00d5401099412101079075101c0302c140e002d603941500c5080aa = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 706493570 1250 706492320 706492337
    0x1314030f0a0c060b01230702030a0b0906040308100609050d0c0f0f0314010e0d18090f05011e06120f09120203040e0a15051309060608060702070501020601150818060106 74
    0x10000d05001d9a04e24080920b400183c4030702c0d032243c400002201d14040009040b002070040f0864070309100e0100003a404c0070705c034042860f00e084080d8880208540840004422a0008400580145101d0145c504a5441c010300e1800e01c010701c0440705011000360f8902030024400100c50285c410740300050560545802411450f52034030b01d4140081c104003915503410080440350032040021007440c8100300d86000016100302004480710780c1c1443d08501401c60901e400804554a40c0c1c104904a074102e14005050313031120032880070003c40300d010f100c0010b1040414940b1611054104c82100259042c2c0029015156902c0200e4200081d0103c4056080401c3c00c210841b41100a00c0e409201d64000380041405c10311420340c4030884e030140c2c520031110340008030040720300c61b88031444e002e9000c00304000e2a0784a8400c15030718502245c00c50014071580d00c0110f885d510104465040300c0e0f64442100904219031820b58001c1e0004100e40d098051541c2c0301c286030041045100d008100a4407010f05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 706494820 1250 706493570 706493573
    0x31b03090a060203120a090f0501020f03010312050910140c0a14070b031509130b0a060f0f0b030a020d090b0403030f0b04090f14030c070b0318061314030f0a0c 70
    0x200018140d00150554006102c2c2c5c1c41e001910300d860580c4054041000100b1151618244801c02076640f8060308540c400700e000460700032404010744c10303603008103618600689460f6044603944203030355026030002801040048031030300403450719071040c9440f02042c1c149000d0405140c54410400419a007034204641e0201c02c1c81d10034010300d405400740395000d600c3d502d01142d41407240c542501620740152984000680c0110850411040c0c140e8132403004079450400b9010341002d0718840c0180100a9101440002c0d40d240940e000412500380c207031958150754520b98243c00035042120800c0f6510b4a40b1850b43c002140c0041c013a100b18441d4900140305100c420041044441c0d2038003880c0190301e411918000321389004c0048502c20f500c8400d003040391004e045510b01b980507540400c001446185c40104065a0501c0034601c940350111a0104903030032404040e5641000760340c507101c038512640054011601c51039030f490030323180d6107402c076840e202041c0700c0b101980c2d0040d40c0d07030000030742c0b4440c6090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 706496070 1250 706494820 706494829
    0x2010f1808160e0f060102030403030f0905060c0319030203060f010e0f0d15150e010302060304170c100b04090c1814180c0901030b07050d0b0306093f0705031b0309 72
    0x2500400c004810214174502800042c2d40c0340700d680005000e0014482294103401c0c40784426030058030000c0d007019181d503107920380f4940e0b0b90011120405c003200096110400d0303d20078429203201d0500107000540d140005801900c0820800940343d0f0405680da058040c1b545a003694202e03000d200300c07602043d001080014008460300c2c92303881d880c950180c910030410006600300d40c5040d85e80444901d5a6511a403070455114824291466101c0d83c001c1005a410800455020003a01514105102c0d500c8408104400c40355000d500409100d05e050f000d005820003401c8540c2c1c240d4402c035001a4038803020098001002c0b08036840b8002c0c08480344c1c40700100b0030a20115003c2c00d800d40d050b08081d41950ba4000100b0b40c01030044c0304001001c1a90f02009095800800b69a180601503414a00740f0b500815182c1001850400d036060042580808011031840c040b81201041c40c0c0d200040762a59582030701550081b8000d0341c0c01c1c4000d004908080105a61100308101c6420045603120002010700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 706497320 1250 706496070 706496099
    0x714010923030301060c061e0903050406021216030c1a0f01030c09021305060319180c08030414060a300e070807030f0503161a1302010f180816 63
    0x780207070018001081040d410864100d0104da00c03d401182c1aa944c85100207615122100c0c6000903060040700424140c2040080042c4c1786d080c1c0c29100a009400314490461003861500042501c0750700140021034868440403803014850103400d01f1062806000300000c05041d074074101c0d041d0403038004108000780c2c5038a00004060080d025030400100c04461a04c0650a200d1140280300c00000250942061400b000d44c1108503034080000820072a03401520202050088580d20f40b42400807540a80010545044a46003207913040d1030401003062002980010144000b0701288404070b0104e002030101d40d000354031507100d0041e10b405904030080305643c440042170034290400e0b0300c140002c610100319141540e400000c280021103051409030710b540b098503000848402003600c182c0401c04003030300c0680450f004000b5121541c031401c4510740c814191401c028082190040446401409030b07104540c5500000000700345140d40b6030801d4100b20008580110181c442c0009200e01e44ca00e6400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 706498570 1250 706497320 706497383
    0x1b060305070c0302250b0f0301050901050123070602070803130b0f01081908071a070f140306010806030a02030f0c03010e1c050c030c032703060c04050607140109 71
    0x244046800d0303c010f51078116800e04500760300b51002000d031210100340c0d42c010081c2a00c0f81d24903503c610412040e0f810b60001c0c0205886010040000141984510704400741d04a40c001c005600c0140341079a0304c01540b2000e01101c03010707000c0c02440c0101b900b40e0091481083c1a108500c0344121a2034589880300e0001c1c6503841004400300180180fa100050281c02c4003e111001c01030080142010703041070080300c50051000c0f0115000044101220154a001d0701d001e445004c2c4240141105442081e2042c1c2d203401c1944081c000503c00750f02c58903600d03402490150a58410a026070046401c2c14400011701c800d03a13010821440e050704007489080102046280603107420340d200c01c0541c002240c89028079081100c04110031500c48802c2c0300300c0d02c03110b200e08120b0740c0d030f003a0700541c00c1b075560b801c102c04030303e20a01843c400b035540c100454091300c0b914941900038a02400e01c010801075401251040d14410843c50100303a4080091095040d85800389551703910200402d43c3d81c9459940c074034507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 706499820 1250 706498570 706498577
    0x50603010b01031104060e060c060a1b0212030a090809090a05010f23090405030c060f0f1e070f030b0a0e04050715022802030303130507060e03100c05071b06030507 72
    0x1104280d401400c00d4030305075401b91401968020072000040c500f8042c1026459143c0503620070700040b0302403540003c00151060403074007180c0f0700d58102a61140108454801e205000308001a01140142d0101c01a00e104841e850305103911500030400e00d01c01222034410680d0303181c0c01441903002c140001c0303004194459100381400303203e06440008500301c0300c0d040e018441640206040190500c26035000950300002c13158240340940c814190a6025100440c20f0801e050105004501e240210203004010752491201e075202d201040303500781d0380813140d141015038480c0403d5071039858400b08001051003802c5400e450509091081c200343c071542c04107030550070f030710300d035112568000c54590010124180d066140c00b2882c052106881e041c140f00035854000041000098840d03100b02d04146d50050040f81e00751038807100145d0300413040500c0194180e0102d05001c45d411800d800050302502149402420621260742d2101c60100300b0928240b8420944030074468141d06114044c2d00c9000d900c4c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 706501070 1250 706499820 706499831
    0x605090f0c1c020a05090c0306040c0e010c2a060e03010c0207180b030c04060e180c0d0204090602130f03050d05030f010b07030c0203060a0207020103200423060d050603010b0103 78
    0xc0010410111019010b05054a0314004025035644540780401000050004040762820000810b590b52048560380d1080b407400036036070300a52180d055809544c4040e100d07408501003a8803500e08443c150150102d41c0798020000000031282c1114500040440d03455888004440304101030a4502c4601c1c8a41103501035502041f00da800311380c0e4621409812100060400100000300f070411140d09003c91300241001c80000703404150044030307841000154640101c10590140342c80d12001000802e9074884070303005a02c0090329196101d04000c510800c0c00501e03016024040303200d400300320385c030150000314074441c02c105003c003d20500200c603030603242071490341c40d041c41d4400ca505018060743c07074596030102c2c2080802d0300482e032030b200041d001000c9a5507440c02a035960065409070500b00c0c00642041c00010180b080300030300c0103454081e20041400e19050020110110840b540c800c0818010100d60a00b070ba100d02c401040c552000d80da000c80c00d40f501d9000d15080d1404548114109407501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 706502320 1250 706501070 706501093
    0x303070803060907140307081e01030302031b211207090608040f02041e020309011d250e040c060f0c020a060e012d091e210803040605090f 61
    0x100c116940b106048800c80034503100c907a0211807240050284903006200041406009038010b00103a00c500e001c00b8030f00840c100c1c010030700d100b004000e00c030040c0507a0040c4a0708800149005842c1c015a003400d0072a01d0660b038075498200d49445510b20105592800511032080d0002c07102c54070f9208105041c9a01c08901d0418010a4188018006481c0420541440e0110f5503139400034060414a2606801001e8606964030025403058600084a610700055a1310025541c1501c00300e11141102420071181d60b40321100b140780040e400d0100f0188001400320b000003103050405e000c0d030300a1040c0d210250a190001e070140c0e0308890100d0501951242e69401a562140700c0c001380d03605841d01e1000b060040006841141c0c007404401007401c140000344030340d15056104001240400d80d19002d07400d03901c0b2603004048034501d02829a00d00f0f030b51000c0c40090700011a079a00828010200703905444240c49a50f403640050341c00b01e4103180c40d9014088042810000100c0d8081c445000c0c180f8180300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 706503570 1250 706502320 706502333
    0x61216051c0c0e04060204091b021c1205060d0c060201020a08011208094606080106120b030309040516170106210b031c080708063007091a030307 64
    0x140c41a1069400908000313010040c40c0d4056900074100a4024450a841282c100341401c64403001c540040c07040c1c05224400c001d40d4520805001c2030345d280c0310032010305030303507080c001d030074010540ca411621905000300020a4401e20350028a44d81c2d00060300e90603001402412402c2c1a48034083e02150f00000101080000c400c84500c040201c84800e11146400083c540982050850394500201c0100d40d0302c45c6a031038804000e401180f01d1843d4072a549810040e01d503030b8401c0c040e0500195506e04034102c440300b02e50154220320001800c603400c28036014001019100d0480c1c64130400c110b0021500c0c08680c2100c10b40400c0071601503100d040d5030500c031006014081c40260701011308452040c0340e606007407c0d448110381e03c0c40901920100b05682d00c1050020f5074038144c150015001500081030203201d01d81c400e0040d0001031158000d8094001803030499001207103241301c0c84040e00302c6d083e4880420000f070f1006040944021030002c01000045c1e003449001110b15001c1d804c20404400059070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 706504820 1250 706503570 706503593
    0x2a140a1b15050315032d240c1b010f0b090a05071b06060e0a02070c06051603030903020c0405090f0c03030909161803080d06060201020a1205061216051c 67
    0x4041c4224064289282d002914041c4800d481c2c448228907141b9542900307003e451031030030444a48046842030348840d500601c0b00040d00c103546000742e13525800700d0800301e5000c4c0104240c0440349109245c036444442c1c6182140c41c2c1861040ca4203640301c04143d1241022144503600c0b00480e101080a440c044001411540800c060200345401003401c000c10450b080d0b2103c0c0180007103666011403443d028940200a5014010070785401c054048000f801d24400c4044541030752580d8200791b8040e842e0f035020740140c082694210154010004143c0c041e446520030184100b600b0001444901d20120103507003803800061540340280c004000080090b00c944008a0b002400d45480e001044140d100031030f2103041c2d002c5440882c51201c00c0010600490001910009000441c00c2200c641e80342000d90803482203001000c04a00b601c0198070100d1a960b200f00e82c840c401400c0388010302d069903451030606060302d21910360028980e0702031100e4149403030741c02c540a0411a0140e0300c0984e5031030b17106040b41e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 706506070 1250 706504820 706504831
    0x40203100b060f030a090c08070b091003060b0a02074502070b131205040323010b06040e0108010b01111b06120a1b2a140a1b150503 58
    0x81d241ca071045019140c06040b00c04001030ba00400b92a0b0605000c06005010010416074900c2c3c0011303404142c018010401c01c0031260740d20075845c40c0034024014441203503c006200414075a4804c000514000c14000500502c1303415805080c542c0c2c100503c156940941201e00c0908a100206444e805996260400218404d0781c608a0800ba812031209000e031189807030003091950442c0030711255a24904426040750300c03414a0700855800040c04070780900039803001400042031682c0c5070150b040203580307c1c45100c840900100d916400b40010440e65031060b8480550f2002c6600100140f40003886a00c0c2401340c00d192050000c4110f1541fa903607071030310090901c8007014020040007903689080450340304004072840c1c140316180c0960340000501407844466510081000c41134040742c491000032281c08038144a120720038640c5a000b49880180a80071515516000c83c0d03c02070070340802c10400700c5032141820905840340a07000c10b030301441c19403000c650144210303003181e8025003007001d807070303001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 706507320 1250 706506070 706506103
    0x703030c051819030501110d050c12060105031b041502060c090303070312020d060f0501081f090c0e03101b03060509040b04080714060a0e0708070311010909290306040203 75
    0x205a90303140800840042c2e48020300319844d05d4007444203a00c2c02c4024202343d001a2000300080e0f0b4415809545d1031060b04070402044440e00002a055070080b4080c42d0000d4000011035010b0150a03150701e07041c2d000303800180500066100c4100000ea040141c958030007460240c0c98140400700011a640340101e0070002c05009070a0b0f40d1855541d070540c10703a410544030a00078000720b90344421940982c00e260040c540043c00000001e001e0041f0705000d8030305000c1c60300e149180145050245030003801040303007030001c000418040003015901004141c15000560500140a54201c0107080308042c080d0090418141400010421943d40e4041c1c01c7d841900b04500a52a9403680b92200036441088401400c50044007081010403100090035881800c0003081001a4a8032001c8507035600d0391885000d099030b1006806000280c4801c2c1c520b0304180060401c40c5039280c171407000c0420b07188003c091004460103844c890304e00700380d62081d0940488050b8090040c50030590007007502c1d0b171001070190929 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 706508570 1250 706507320 706507339
    0x20310020a18031101030f020a1d010e03160905010e0403080a1a060a0e0130020a05120403020c010e0904051011190c0b1506030103120219080703030c0518 68
    0x110302402202c1d21850100c820842d51075141c0c40c2c02100100004641400131340b4184490f645070101d4805c0315074000a40e100c40030700c0705031808030511035080d0711020b80c1001100c10300c200c0d241d102000011450140640408178031810409840103d480581c070140d10a6980824000483c2d040f140c1d40d600b0071754880011590203601207607901d6200c651030740260000000508042403d0f40001c4104040f00d00360307070300c5d40c83c0b0181c85c0c1440301030b80807000300c0e0401c00413002001048000e180d0050100442604000c0d0403d081c800481c8d010810455042c0c0260700940303c101c0b119039200e03035600910700044480010314201034885580d1044601d10b1a807055590300604048528405c09030341001d00407003074102d40300700c6d505c40040a05c1212002110040700240c0402e81a900c0d420b4941c081c190060701306401c1d46e00c1d6407500155900c50061140640c003600d08a0603010304900d144c3d080284c016402c5660b035000d145001812104400c00c0d060411900340b180047c2c2c42c0300c00d04000d25008080740c5090a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 706509820 1250 706508570 706508587
    0x80d0c0203160f1b090f050a05010612050a18050a050d02060709090c14041509210b040809090f041101030c0f0e03010e010c020616031e0e0316050f160302031002 71
    0x190485135003000b00541c400c41d580050601d401d60011303000340b0b0683c2d5007807003d0345404080c0016500c0a0003088003041d00c40d890f00141001640c0030641c0719011000c0441c005800c0034001c81d40345051402590b09801940e40c0ba0240901000349581c3c0210510003412245480d41c40108140190300403170b1001a1103481d41d5044a20035481240001074101800b6030751384c1d440c0c00e481401480c071849080400c0001a00058032541080002c50441101030910080402d56880c0920004018402c03602c2040c01d00c020318054407694002441900c001071600900d00705420a08001c10032500114109800c2c0558180000e61068a9800860103424a40800d0702030303000090141c48046580401356190818510146900092150040c0302d4655081a1502200b2080781684c03101e0b91800c0c1242000b5503400c801c480113502050021610605513414640000c0b052540d4050811081e107090b880b1506a0104040134041081114290105140c42a280d540403035207500011101c402c0190f4082100b00d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 706511070 1250 706509820 706509833
    0x1030c0302122b090506030c030a0b0319030c111c02220e06181b090c070b07020604230a1101090e07020304030b0a0b0f0d020109090207080d0c0203160f 67
    0x104110405281150f00104451550040403110442c030320000700c480d200001c0d20304000b4216401486900c6840f495592001545405070092142454241c41910705118200c076801242c06d414602c00c2d51645090151402c0c141300d40c181104240f41f01e0144070502d842980581e8100100b400c2d41070b00c02ca500030141074a013100540121001804050074184d410140303a8010500b0362103400c2c1520349107181401d90303122a40d01c0e070704d42d00e81e102d00d80100c119440f42403403c10303080c5500c504100040741c54142c6030340d101804000c05440e0301c009030348a4030601c001c014070040141c403403108401c16860040c5104c0d00c0d83c3d5580c1c1c0703880805803a50342c810b07443d41c50691080300e140300584036181460100d4204060025581d502c503100c2640c10254600c0032070b02c00c1031580140b0303e8102008103250350400c0c4a404010040074070403001c0741488003030040060805050b0020308240d45c0510030150300d640e451039000e819150380200410840d042003007020501c02c3c41e150300d1004181c03c02404028100c071464800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 706512320 1250 706511070 706511083
    0x3070c030f02030f070807060f020c07030f050c060714100b06040b070c08070305100e06070c081b060a0c02011802150d0b040906020a11150106050c1509030a140301030c030212 77
    0x558207035000986031046c021500c004080c81c4c2e104030030030090001208034a0007240a1030f42c404045170000b03401000800c40318500f00300054041c0042c1c0300f0082003003001818503440808100c46a140b16080c034080c21600748010b4035048030f00701051160b064500e002a0403071040340501040340501007039a03401c1c02408034445000c0c100f00070458007035640707034280740380c1e41c0145902e15810700c0c1c14110202100348001c00ca80d800342085e515402e105110554585a250300544109000900083c1c51081480350401000d400790504c018001100c1518103402402c2d40d0a0700c0d0072124601520044034010303200d01e0b60780340c440c003103109600380c84a03202400c210140c105504119441402c0001e10400c0c86541d6001f491a4600c4d601c505d40b60118002b40b054030703208008000442c006d00a80104005030052005200c00c2d03080f0070a45129143c1d41a061144503000c0d20304c11003540c0049220030149030010030f00c8038007442c00038041d81150b24580c0c580c2c103c5160707400024010130700b001c1001640c0f041041407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 706513570 1250 706512320 706512337
    0x1090507140f0f0f18100c0b0105130b0907030c09080f03121f080c010e19061817060601030c0912110112240501050703050904150812030114010503070c030f0203 71
    0x5242d43ca05d00b056440c03540594110141e407040a91000f00c1d6203142c0a04440701c0b5850b4441a201880ea18003010070804002060070314040d01c0c0c42e0031401b2030643e500b109080c41000b040d100050030118404c00140b82d904a030300b0444840d80301000b020000d5600100b550307141c6400890007882c5965200214074620043d402142c0045c5441802040e198030100b0709813580e1000b80c0c1d031001c00b0014841000344096000148180e201202001403041c01c0c4100c000300c144031000d8100d140070b82e80c7d6084106200104440000e41307904130343c0901100f986e0501071003084c0302c030a2170301e04070440c181400d1842d400b00b100030080504000001c0400c90f40d004442012510b0341c000c2040200010f0740c014a00300010201418404440c00d50700441d40e0f60045003a5024160150748035070400c16014103201c0100340f40c0b268640c103241e00c88000513090a08000c1c03400000e080c560550b4403075160071440051000d0007042107050010500130461100c0d80446100c00c6550140341c60892451110000d074118802d0180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 706514820 1250 706513570 706513597
    0x60f0a0311180403050901020613110907030b0307060504051f0206011203091a0d0b1f0503060303040f1d070306030b04030f030f050a060305070e270304090c030501090507140f0f 78
    0x801c0f083c1504030014007030403a000e0b000c1c0c500326a0ba00e00400c8080800c45401040c004041a44402906003108450b603c0380c001d050018540e4601c0c80040d01d412960ba001c0800140001014001c0b030038001d90001e242900c004151180d615800006511080140980e400581c4003100150500d84100c0c0b85100914103000e0f20401144d410003103052960014119034030303036410f041328980f00b41045501c0d1300f800e07004203066030719144407854111940d500103001c855151100b80004190610515243d07401401c500c03612044441e4204940444a00d0040c8910b0515117030060400229031a41400d690191780340ca0101c50101c09202e06900074079410141e42401032404082124508166014100b580d00030412110140c0e40c0d03002d40729404000f102e46a01505200c0e01c110b40b560680d8500368801809041070300d040a80710508402100e0403001c820300000d8480004110341c188910903103030441c1045c03601040d8020741048d10001d0f171249030601509228000390038020840380c10f0540c1c80700e041c80f00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 706516070 1250 706514820 706514869
    0x90d03260f09060f040b15120f16090b09010308030604021b0d020f030306060d021b100b040e0c0915030718020c010c18030615090f0c08060f0a0311 65
    0x500d00c005040c2102c10719001c1c400e03940440c1502c00c9042c54030740315a60207000c00c0740a64404940603000c90010000c2c507041a41041e0384040980c0c10301a018200b640702d002440c0c1c020010582d03c420740c15940c841000e0514050703505245445654525041d03940258285950741c94807030104000f40700f130060194000d07039890142c5011103008281ca0f000340c54568200d400034503c03070511944030300c0180c2e10306511420402c18500714003650f0300546060402210259150291000040c0c10483d650250132122076840d00c9603540da191511030f6240f6052400014a00100a40c02103000000052b020030001e414403401541640d9003000144041c1608403004076010840c1c01c1c81c60003940203050700700400e5080c003034102c0d101841440f180c00c00640250001031a00e1071071f1150381c01082100d250300c154590048000c5006141c5000701050021203460026041c00307040802481c0301c0014091904c9103174a07005590311030350340443d0f00d01a240c1140c144103158000000058a02e24130b01ca000da030800041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 706517320 1250 706516070 706516081
    0xe1c09030f0f051e010506120c100201020f0f0901030f0c0203030708220302030c07090b090f190c020a060605060406050d111603020f06090a031706010c06021306090506090d0326 78
    0x104e50401d03032a000380d8000c5c8500d40301c01c2e0804c4007149400038503480640c424900c418031031415007407010690806000040c60a4a4404050420390003240311004200000441c0f40840d40c2c103204000031140704a404120032900e03c0402074803803001801e410308102e00072002c5442c505424540803074a5095100c1000c4580c25884c005e9181e07000710000305d945c2d00498400080e103a110740150003485100519440440d9180300d074000d20b000d0b01800f482c1a0f0083c0c020b018004003120320421805e00e030030b07030000d040450741032601c017094071200c0d04142d0250400f8401044456048400d50300c1c1d42664403004070306004900500000d50282e582c3c24103c1170301010f02c55081c1500462614003061284c400e890340d48d516003509079960854858000e001400c84c0385c3c5d4070001d1403400421a0020414500b6000002c499200c0005a0b0000c1404400000d00420300f00581904aa59500280000d48003a410003010307400180c840900010050b0501c9941c1c103950031042c10300c1c10141860300a1a9101d100742c18034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 706518570 1250 706517320 706517353
    0x6010201110a0c020906060306010804021c0506010e04050f07050a121103030a1817100e0c090901240b07020111070308040e04120e030c1017010305010e1c09030f0f05 73
    0x12608144c1c0174950280100340d4500b003500803a0310880701a19941155252903080c499284030858040c0c4810708103107800d9000030004c0c44014000c0090b18190a0035040506015081c00901441c03410540e102a604203e69210b01000308211003030a003002c0038070a03a5050922100c0d0036814215818040043c0803e11140c01c00c15006034204200042032840c3d484032000011000060400340b4254030050880d03c070715107039410000c09545010103540395000a140032440d08a000c3d6008001c4da51601c58184100802d445481c0313014001204503800c0d5454400a5641441007850203410481c074500d12404400301040484000c1d81d00000302c03a6a140d03501400311000109072012103a281c0c44030b012a103154030400c00300070031410040c05896024001c82c1001b003907540c91801b200c01d0101c01c1d042e000d41140c1d00c200581c000c0d80168000b007145404a9aa9402d06802c1400c41c80c117078840440310204140d2006541d8140ca034091440d2801030003505001c240f40e003407190300030524421a42c0007086a0305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 706519820 1250 706518570 706518587
    0xa050d05090d0f02060f01120804091404030201050901090c03140c12030c0106120803310302010902310e0118030c11011d040b0d020303041e0909080d0506010201110a 73
    0x8941d0f07681070103650460b04a85800007a900c0c543d000c52514014403005083c080c1040e05ca512440c111071409503180502c02c140d611449083c03a40010103c10002415020302410f80c2c441c60001c020803110080e90354400b50a045408043c1001d000b094461400c40d40420421619031001082c00003a405c032450210f0343c85d48107c070854020f50030103c0008150f6195500715291a612541c050f09581d1a83d503140e10100342246014a9140c411000c020651080450b80b20614000c0d0300104580500340103200780c000c6001c00d840c0c0c01244030301c91700303010a101d2000b16075410a0410085001c40f03035000b05901603c20a501c2040581c00c1c0c290110425420501074525940728051040380000110010f4a0706008401d407258142458401c4209074503290b803003400c40a6000703001002c5031401ea00400d01e1604990043d509044d05e22892880c02e030bc00c0c00d6000e0080101000a110800c05135139510030b2405906c0c1d80d010425103a40c08505603a00070b4220310000e82e1030a0b40c05442d00c03200c0d88014124003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 706521070 1250 706519820 706519843
    0x50621090123091b0108040201050c0109230c06030405030a0807030905061608100f140a0911030601020f0c0319020f130c11010e15041518020f120d050a050d0509 71
    0x100f03250b10040031136140b020100c43c0080584440a590780c541c0c00648241e07200c4031039024113541e10350000c0006a0030030130030000443c80d007a40c0500c0e080401c10b114940444d1140d0303640300319824002c06c000110000f044a106144900d40b4003040c3e10707950000d402030a440c060040c0940600c5081181d81440c0041024100c41c1c0785d035035041c15459010b1703805440d60450003245044506614140700c1113503010f01d11890241c01404000d10599070740c03044822260242600100d4500001c1841001d40e410801030300600d0304440601a85031501001035034500956030b400b00285180502074007950350325601c0443c400809410040c101d629030804d00000c0064555142c04035001503082c021030001481456800307860070b4024420310400c0100034a40a130010310440d02282401241e4040940c1030003804600e0460440400405003a803040018004180305450700031500d03202284040d000000b455084862141002652240204000c5907540310320705401d8001410a0184540703943c00151804051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 706522320 1250 706521070 706521073
    0x161214030f0a0f0e0a0501110708010e0f0f062202012006010602010e12120a0209030a0303050610031a01030c020c04180515010317090d020a18050105062109012309 72
    0x4042003d802e480c078106411081c4e0304101c140307000f03001c5940180580d2018080030030451b145d987e071320fa543c5800c0d100191188a059040844031212143e41005802d661100e00400b42003036280c10400003013a603d80214100140d000101d0f0310f41036901480604040403031030f883c00045d99070098491070303469801703202d0000150700c1c21401d100d42c48401b00c2c10a0811340d6a8040500e04115503a81121000d4040c252140b0281d08201400c00d07a81e0400c0844000b07403090724085140c0c540304042050f0510400119401e00d801e006c1202c450055031241501040d4090070005034062160004034a41820b094401e504240b40400300802e085c1414554441203100300112446100d6061400e84800d60130b1100800c1015131050140d0144c02c850060403080300084c00c155541401c7c1e07000164088510b5100d0a0484018001c02075564031a0184c54090807090307943e549401c0a2042c0040c405282d00400310074502c05c080840c1d0000400c2d0070074503400a00c1c6139035410259181c614240761704415982c04845 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 706523570 1250 706522320 706522337
    0x1e050d05040813060509451909020a090c0306030b010b0c071d0105010c03050c010207080c06060f0303091c120509091617061f0906030e161214030f0a 66
    0x103503115030111126644040c1c4458012189003440001f05a000c803c00a005004a00c11b480d010200210009112080c0192078003941485442c0400c3caa00b00030448280318142441e0402580b14110b441d0125050400002a2501c49810032401016079410040c502032a01c2c0c00000c0083c03900d0f0140028820910a03900c1c1c0a42d210b190800200b5050b00f6041c580340024010000ea60142c444098014000c0c10824035004a01c40c070309007203031300134038080754113141c04161440b140c1e1007084000c0c1d00c10b42c00e8800788803030105940041c0c0c0d280940305480348100b010170004440070303242c0c00d101e80602da40010015018209490040c055070800d900300b50140c000400001c155900b0f0200c3c1d001c281c4140c0d2601901202d84083e400c4100030010507298120000009108482c00401c800d0401b08500e0360f1040d1800c1e0030329100400742c6201d244071000a501440910918954000d050021245400f00da4080210300346000c4c2e01c808202c861540d01030102050040d854241382c0020f103049070b602c0d5075400d078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 706524820 1250 706523570 706523579
    0xd12030c0c0b0a0b0109030f0302071502190b090f010207060204050931080c1605030709140c0702190605090910080c0409140d05070c080c011e050d05040813 69
    0x82444801c00060a00c2c6040c001181e030b210310a034462580f4410616144442c95142e0701c1c1c0c01000c021441c8124010ba010120400143c4402000c444001c1d0041c4054100001c5226a030407120000e84d001500d282c3c01440400c40c568400c001c05501c108182009640710180f0f0704001c0b00a400c548206030240c2000000200e140c0c091703d08000c4c0012104000b00500640101e0350441390f45104d4045036180410059122000d1040001c814103803240f240c0698035509040c180360602e2540d90100341c1d25410020045850710107188900e0748180ea01c0c00950300c40406000040c450030710850f03c0050052001e502060084c0d211000f00310190041c0c0b61030003980c40301c124882c40480c0b01d108107410303a0409070000203030745010342150251a0080c08039660340d50085101d14201000f080c01e00003c40c8001a1403020026800c40110090a880c0c010b000304000010010341001c02403004020509581401600418001c1064030601507034104100300c00e103440d1510406a038801458032065070442840080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 706526070 1250 706524820 706524827
    0x110f0a080702010b10120b101403150d060b120105071b080405040204060210060b070f1e051e0f010203060109031b083408030a0c0203150702030a27230d12030c 70
    0x203250078200e0780e465508103441000011a0b410160101e4051020210081e2f2503940b00c10f00b007175485005038400100355101004000c00108041044011641040c080042494000441440303048500f10440c01249252414400741d00c115002581d1062011a002c1003195001a0011080005c44030410001d83c03910414821800386c2d06000f80f182408690030000288491300051044050040d1811141015a1103e040012070302c030003143c56000040007440d0384d4013008000385400c4440b00031851400d00c100020a031401901014010140290090000c0b80304070340c86000419100703098411222401f083d90300030140380642c91540307907016400c2481603100b05150008480c0400000d40c58002200001c0d1140007100d0800d9a1500401001810103189080018030407103281c0d01039a070703d800750f5802420785031101e038007610403e5502c44101d00049103074a4a0081d1001c041c1a4100e5080a85038041c04158540c58160015207290340c2c0c80800c4100b010240e010040c0d030b201480b16011446007203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 706527320 1250 706526070 706526089
    0xb0402030d14040b0c0c101e090b090d02190f0f0b0315010e030705130f0e070308040504090204091208180328020309031b04110f0a080702010b10120b 66
    0xb0100c402080104221071070004004044248207481500d405100c400300141e05054480e41000120303081020000e0525040d01c0301c10320114007401e080f805a81000e100d00c0711402035007412406031001c1048442903540d865401d01d4a1050185180321860311440d200b2800c5401e449114007003a00f44502007560300304003013a41c3c441c4450740070700d9141130080801115080041c02c2d01c0c1d5094002d584001c151516903c01800e034621500c500030070350b5000103000d00211f880315496a00c090308a002e050000803040f008580480d00d003110086540b0116000140080080341070041800009151582e015908032a420b4812502101c07a016083d04803440b82d0f440c0e200308403c07400d410404100d05444030096440d1401560514411a4184140c80c07000c139203084040e0800031079024031442400c16a1500380a108070f41501610460700700b0b01c0e8003811000754048c0a214506015015000820f030303920035404036409180c0140041c00c178152191010f4030075585540c00c40c5042e420218803e98030f081c0306001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 706528570 1250 706527320 706527347
    0x1e0224090411040b13181b180b0304061409010b03120f040803040f080c040207030509060706111b060906040b04120e060409020a02060916090903090306090b0402030d 73
    0x40600c0c00e0651001c1000078046070082201094061002003103207607400c000b80c0014a910310786001d50034103054003440b02802c02000500d14900749031107003003c20020008500800c1d05410041c104814016034413500b81940d401c00501010080104070030701055411140168480411021440c0c8a01d0641800c1c1c514080c0010b070154081c0c0c5540d2501c01c1000d004042880000913541d0519840d9460141142d01c1940100403020108100707000c80141440b81d40c12440080320304510b040709a03540038245001d40c0c4c1d035081c418803001c54024240701954101140310820300c4042e554335044800142440c07100e0b220a01414859080054010ba1001541500664216040005a651310b644400034807144d08807500410960350828401c0e0344840d40900702905484402586441c0b0b50540203107003050040003d0304692169000c0d10784401464a00e0080d52030281d00443c51020500b0103442d03a10700c90f80000c1403140380024810500145000b0180a03034170071070a492100034420012207000040e40f21 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 706529820 1250 706528570 706528639
    0x30f0c110316030e060301081c110d0e04021c0c03150f090504050f0a0302060f0c090108070e0301090221070b04140418150504030320070b040f1e02 65
    0x40e44411110520740b0320315851003450665280b0100c0c80204110350820380c0700061541c0071440c1410403600001d01060a45d210703280c445034412422001d0340d40c2d004000c0c03a400038003400c0f000102040d10341e40c045500e01c8420580d0005c2ea0901c0c0760100c00200389413103d0344006440c101d0a0b001d4141c000b80c60208540d440c2141384001c0e410180310300e004000c09801107030917114001c0c3c1540a14014816a01024000d8010b0100d07440d01a0051039517010043c07645214000800130241aa80c0100b9950b420101500d0456410ba540c100403c0c014404031a01035406590041a00d251700030b02c101c81c81d11000302109031060b09540d640043e08c10b000b24042c110300d0300880e011003019401e043e48410355440c040100391101c45142e8580302d5801031010701303819205494034100800d0540600444a5001c0c254900002104550105034442e0160f440d0040501286202203010b0003032000e41001542d0300141c035801080d00054a0352600419400c2c01c07402940d64119030360b2407844802116140304013428 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 706531070 1250 706529820 706529827
    0x3140402091503070603050613020a020618010204090e1b0405010503030a1d040501030b04060c020c0a090e0106050319030906080408030103020405280b0f1c080f070f03030f0c1103 79
    0x34208404210300801d030101000c984500c945180e0303000c1007800000c04030740d103000070242444014418000c00e84c901101c0082e00400409a2480e40045c186501585040300424401c0003445c80c140644110b80c00311700c4130390500c11341e010700e000041868016290211404140f1080380c0003031005481c404d04c190b540c150028046d505000f03005400280a81d0442040b40d448110034500107007c4510a820aa50b03120101d401c010030040b152042036420402130006040140c050000124100f282e40249111241c49000001c14101c00f500b2400140c50b00034280d03080d0000440c044407000302074141c00c0c0c00040340c0031000a81d003030003680c0f00e41c09542c0040c400d9241d41e0940d000d1001401000d00140d540d00c0c070b4440354800c0c81300030281009403a5185200451108a150300300400e06080d05800c030b109080c0c8049201c3c240d03d2950340300161070340c00000d035900d40303807032204034282e80c0036400c030241500b40138031034490402d80d00d030744000f000040c4880c003000b070110306000c115041d00f50019400301c2c80d0b0041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 706532320 1250 706531070 706531073
    0x50904030e010c0f0b040602030601031505030d0e1305150310020f0f0a170a1a12030a032c1c030b030a0209090118080306010908030f090d030c1a060a06031404 70
    0x7401c80d40840b074007440700b00c501e104c4030340d4601403c800304603000d40c0c817180e0210600c070300343da418010340c1201a20300b098406031504102c0000d407240e500140050074000306d01106a41a00c8421090051005003c1d003003040c0e14004c101101e84040070101d01d44640a0008c134000084914825901504009040203041014880840c81c0a510030700001c0c003170001050b900160700c4141ca00091062407494004548442411414a0204003c400140c46050861281244001c00000b9645c080302e440c6030114981ca903224285840c0b03c0c103020642c180290985429401110014046100030352845403400d13900341d0668200c048400c800d0340c1583c5a001401d208015113092641c09403c00708200001804002d0440446400820004d04452483d03010041000c01d6800440c8200104505400b6501e401c40a02d943d01e158820303040403d10503900d806401c01030500c039a19105038190300c0b0130114416108146005c080f8841283e00502c5030032080780204a05100e401140070070030075403443c010551145e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 706533570 1250 706532320 706532327
    0x30103121809050703061a0c030d15031a04050712021305151c06060b0a0c0f050c0405090609010b0f0d0303050c0d1518020306090114030c1207050109050904030e01 72
    0x180c0154111458407500041480d10b001e10940b401136000d41c0b80010b4480c0f03030035110701c1c01da1248141c1400b01442480880d00880e070200c100d424401d0355a200007400d5440340300d00710342e07404580c01c041d00002c07450b05111741103080790580c42d00640c0503000300c1c1c1001d9581c00c854000308414a42c02500b000e024181841401172a801644e0880302010b5803e40b15103035803001c207100ea80304101c090326507284800b4207820710003d0b1180c00090b145010109280915504002d40149136031003004009035a5200d2040600c04140407280d44803800500901850800189043d5035032025100910f9951a1074101005031404165094810202a00c410480310607a1800d400030040102401080c040820031800c05824520600071003401918200b5071641c14080341150600744c60700e807801424410002c0c04655070f50f40c20054110703018001c0c00b1209441580209040648200d45035400c05d10400148401c0391000ca081400d483c8203a803040b0300c0c295200c0800009030700a07913018000c03903410542d00c91594403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 706534820 1250 706533570 706533587
    0x804020a030209360601120f020607080403020f0405040201140a0c08070b01030b0c040311090628090c031803111e0105100501050c07180b060d05150603010312 70
    0x20a28440c45550b0b401007000590b084640c2602c1260041000c401c29400d1003c507064240d151030522007024040603000d55400040c021980d20400351080c400822a4200718401c1d10b81e806031149403260041d29142d2030f1a00300b03000803442002041013018850030248210b5100e607030141d41d8032003010230075801200d02d03903c000c0e000760810031444142004500d495004210f6584281c124034105d40c035600b4055400e05c801340c440c052114003044100045441000c0322004584200c80011080e100d200010b400c10581c41c00744450341c5900148001080000150242202c0030241d0600182654081c11012a8040303202d0524011a100c04600401d12401076080180280e208136940414103028400d01c94030144000d0413169100d000b08421800400c0090009200a0900505198103004640e444016500840e003070890840d017041c0148107940c002404020024009030340e50f03001000600c001d02011100703400c108a1880d680416820b00100301ca040b41d41044015400146d40380c01204c1100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 706536070 1250 706534820 706534823
    0x2011202390102120403020c0901030305040603020f0c0d0c021003020703050304260c0303010602160303020a1101050f0708070c1d0703020a12060602011a0411040b090a080f06010612110a0804 84
    0x88108000715a078900c2480180400e0000c0101c0401070300d464600246032000241429000344681001040020740000689043d1801d900700582c8403c1c00c060f044155008400030541140315100482e103e503034100014000c1e141c001c1e148040600a248010390a0388103500c4000c002880400004010401001d44e029190304102071400c1d01e0940c0581459950b041003500301001e40000004001d00740d01040f0400b01020000c9034440c6161464034069140c00001c0c0c4041c1007215074050b06200c582c440c408448104910708400740c0c41b45a24100098981c2103108202c0e00400b070320b10301003050345001d064030713401c2101c440843c4820358074850110080d4000c82001424002c408075050484509030141d003000d01520307400060000300342003444100000350412a40140d182c05082501605134030101c3e400d83d0860005555944d8440e030214007004000d40c4840102e0056003080c00c04041c02046850494450f580c0380d0391918044405030044900b5110810740082040041d000701c3e0740a0b000480d8401d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 706537320 1250 706536070 706536157
    0xe0d020318120d17070c110f0a0f06121505060f0a0306030818040c170105040c09030c03030e01230d0902040f09080903011401030c03081b150402011202 67
    0x2004000301861030000c20f816601c0c08600a08000591028411403d0354003803100d10301041480103c0c0c480c6810040002815402840341021058590b114a00c074034004144241d41c212a250703450300010241c1010203c0e5010590805400807e0030441883c80707002d50b03400810b01c80c94660f08610426850340440d034030805040e00e031003000010501000103480c01090340f4009408001101003004100d4201a0310001030241a841c4d0f1104040021809419100b007600c0008007407850140c00c0d00c42c0b0004e0341c8000e182446000003c0704044d880b4082c2c8003401401e0f225501c2e09080203040320f01e60076451484040c02e40051000740304004c0140c010380202c60002d000060100d00341015107055602c510fa09407021600015003100350306091081c07001413013150800c030b90303254115942d001d0565120f03c009004150017050280111302d642000b050720000d040103c800140a080d1800019035003140c0990108140c0b6142002c821940e008036081480291a01070441c407041d400d00e480031750140f40400d0728 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 706538570 1250 706537320 706537339
    0x70305090f0303040c090e031206060d0b12010c0212120a110d020c0d09120203060c0d11041211090f071404090e0106050405010909050304060f17070809010e0d020318 73
    0x4800a00043d40110700a6900441507070810f4500010383e0300d011500840c03540104452900110700903941c0f0381046045414550321501c0d10001c601400014266592040012048040b0080150701c0340400304007680a4034481050b0405080060154221240c1a6055107001a04a9451b640001e86000003e9001402c0207100459141240c1001c1c13088a115401030b04011101c0d03821113a2100140302041c0c21128010b500c1d400700707854900160645250007008101c0c50b090003c00d0300006050380418000e19103880e994148881c03c00c1800344240d501c20002a0301072100d0400d61202803180031000c030409910303224104219004001000703c04c442c0501880082078004250280c0000b210141c400401c08070300740760400c0304807103040c0d000200c1c21b4600f6009074001a40442518210f0700c0f5820400d1840041510607250805c464060011000900c03040100d502d1304130800034000c0028000811402c108980e00e141c1c2c0b884100105005640709010601ca450103041d0600c044000180c4589034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 706539820 1250 706538570 706538593
    0x90f19061404050a0521040605130b0f071214190c05010e07050f0a030309124d0a0b0a09030b0c0910170103060b04021308031c0504080307030509 64
    0x903608040e101100c0c960040713007015003481010041442c461400c1450f0126442c0001c141c495607204600c504c00900002007104140c1800c141c50060013030400c1078045507545880304203c01f56500a1008445202510700410700e0140308030103102c400041451882e02e008111400c000e94841a8504101007202041c074a40c006075081c05000c0c1e154070564001c000482c1001d04128801b01d030346103141d0241d0812001000440d40c050038041c00c4070384480c013000311611a4100303c010b81d000b44484200303c10481d02100040303001100b400e04440780300c1d078190001090407585c81d5182c0f0f0a401c1041d51150340f904060010012200c01060f44200d2030070914485a031703030f950300d8010340d00458407440f01003008207400380d0301d00b840d82c0700d8440c070300f6030b86004030044410710b0007204480018000500700b56660842c5640c5a2a81c2d030441d0184c0c032403074401004c0c0036aa1000700e6a40c2d4800c86940444c0c41c0d8001d0160400c01e2180691401154007885250031035880540880081030000d0a501c0c461141081089 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 706541070 1250 706539820 706539851
    0x14090604152c0d021b130c090305030c06070318020d02010806041515230d0c03060b070b18030c1e160b030403080121061d0304090e06090f1906 63
    0x2016001c0400b07000d40e0b018564001e81050105c144440c11860f010010010a036a643e8094203401c110790320004140300900d2003102c100f00b10ba00000e09902c40060294402107000a4480c41201d40d0b642c107002c503c21040301402100c00e040d40094000c80c0100505006600815074030b030b4800340103040003d20894407450303019105002e81c40650109d002c5400e00c0016a030042020f01d50403844658410701c0e0345900c146401e1f9100d04414410855501c03496a45500d10036048031006080c1c1c6205561105464244034030070038400c0c0c0340c141e01c00c15030704c0d0303034003000c200100c15240110600c50280c01c103450740d11240602c50720100040000d40c003c072400761a1141041c840c00f4098260f46840a449140502e40541088010380240305510000c42942500000040d041000c181d44008003046000c011941380b814044103408400307150102040c04100c032503041d0702a42d1002c07140340884a20362114610307140c8441800030481d0075a00411018048140c07603107a00c1002c18801c4d5800222080200d4100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 706542320 1250 706541070 706541141
    0x103091115030a0b06030907030303110405130f0501140f0f13050108061504050f01030f0201110304060c0c0e52030507030b091611030705011409060415 67
    0x584000c1c00841030108522981c0700b010707203140307060b100a480d606203c40c1d004c0d59500580b0004040545801d130b040d01005440043d01c004201c00b03040092040d0249000c0c00c041d0068529000549141c40000613010195403c81d8601d17250150080b2085c81c1108180181c0301c0401c5603154005640ca4800c00c074001c09842614004c01415002c0c00c62410240c3c02141071610100080713115605003c18070030006074107824281121f40c01031340c401d804d00d518401a100c001d01c031214490140401309000582c1c1d50020482c1004c40d105000032143c141c1c41e800c150034000000e072601c83c201e441034401c1d510321203800070080141c0210020656400d40c110301c8001c0c10416803100c5401d80d0104080e070700051a8150141e075030041924101804003091101c0814580e060081503400b80c01000c1040d02c1c2e400d8010182c0c08004440d00d800c0d04e5840d0b50a041050107460000b0300c60707480143e03683c0010b0100e540491a6800f9691142098054081b80114540500001042210350706582c15102000d01441e1484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 706543570 1250 706542320 706542349
    0xf0f090b0c0f1e0d0f170a0c1101140a020a020a0519151406090709080105010b0702030607020d0210151214010c0905030c131401030813060306080a0201030911 70
    0x200140e481c880e44440c02c105001ea42140312150b042c1c010010008081841521480d55190503c50301c02019021143d8101d20110741000001580c181f140d094200c1d0404100d4556507200c0d01794003080f03881007134206c0302041c0c0c030ba010915250000c00c038450071035001025820b1007441154400c256603200e440c140301a10940201c0090a100d506003040104000c0051040104004210340480d9414072032808600501c400c0c400c012800c00600030b14061403010000d00710040081104d580c54010780c0314198040c0000b6031192180b200040c071860710015400403000c043c1d902503c0c01c1c076220100c0e4006041e0400d5200120910000046000009100d0038000300c0d0140740440655212a0b58260071140800b00c500104140705405100310b80700007420001405d410785010f0750b0303501c26900b43c10040900310100081281c0e142c0000050000400180241440b81d81043ca4401d0f901d610503422114280320301560307a0020101301001d5030280c0e01c2401c080d402364004840010800c80024503101ca0200c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 706544820 1250 706543570 706543573
    0x315150309010203010e0105040c0203070f150c0518060c071809210906020f0c0f0604050402031e01050109120308040c0b0c01061802032a19030b010815010f0f090b0c 73
    0x400100754851513807801400c06803400c0040ae440800c000b512446111006000030301305000820810008030f440b90034000c1100c2c010440e90003007040050056006001941c1590502c81d03c1003040d2600100701e0b80c0c8441804000c1180c54940381421050f80c406622000c0000da4544020001c50b5144010115804d84100300d0840409003a001603d2076505410000443d80042c40050b1400c0d00050011050745046603d90040300c4200000361441c891600001e40150012040c4020b18a440207000c070580680d4030040e407607a80b610011580b6a003140300b210041c5030303070f8559440802e0017819104d0f0014014400703403100c5c98a660130074556a1221607258a50307951003804110b01c1c007020000c003800400c48a015031440c1031610750044200e118080c03008501d02101090758650088100712071100c0041181003042c0380490b40003400800ea9040801c0c04140300100107010038605008822003184143c45031340100203110000c4a8500c04a540c1c0c2003404a100b0000c150b05003a20f000d803803418075040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 706546070 1250 706544820 706544827
    0x20a030501140f211c0f02010608030a0507060b040f23070206040b090102070b070908070b130b0c1c03090204050609040b16030e03030405030703020c10020d081905130201030b0303090603151503090102 88
    0x280c02031600d00c0c850664403c5909d045004c3c41540800310880b01241018030380182c0311040d03403d001c0010104101201d50081c6400006003141085e50004070051509070030603840182c0f26211282040300407640500140c004100090010340400c00064210719040c00050a10065603070b0100560401c7d1442008101c1d0054200128841000004080d2020541c00b0f800c0c854840007480c22400f450103000d804070b002240c414006901005030100c008280303128291a085e41c080003400070142070380164011401c00000980070f0510b05071003405160b2040e0140f00940d01e50545088541280000000f01511900f070310006004c100701840c080e90180000d180c0e5a101340c07070702070701c0c040c80c040300c0c0c602440c84140c6041c055600481d031410306000fa800c11200c20b5841803080922511b0b4070f007010280c20300d40014401c2e00411a501009184d200381c034100421603c450402d5900c3c000d07801500d50010703003000010802c04500b015131116010192038501018500007a4000701e41003107404403410707035021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 706547320 1250 706546070 706546123
    0x4030f112e090302010905090c120a0509160e0402040506060c120306030f0105010b1c0605210c0a14040911090c030f0c090108040303022a01020a030501140f21 70
    0x3100144509481e4101185418559030018042c19014821184a0350701400001d128100d51002c03252440c4000b040c030301075441e1100c4410010142a128200684541c810b0442a0b01002c1004401c0c0e5801401742c050603561582000080c0400409150708411706009895518004010481090346107030340d565285e1901d0020b15250a00840001e01c4581c1030a0041101210010490300c217812129800398090402c1c0301400c000d40181d90050343c0002d03100c043c2c03e568610004103102c000500c1d10603034610032155410480c15180a002e418a0000345951742900d9240503446800703054440c507070041e281083c03100040c03000380d011a102204404000100f03e6100010021154081c1510010500704000c01000034100180200001c080c141d0007d01c0c1c1c000300130200b80c4400c2c061000d24403104024492048035010390010103844021904000020416801e2021600e038111030241000c60b01608a80801400c1003c20b50143c0000000e41c48084800800380105061980041800710410749030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 706548570 1250 706547320 706547389
    0x40309053705040f09020904080705240f0a0606020d120e032b1b200d020f0f030f070204270c0f08030a0f080c0f041401020105180304030f11 62
    0x900c04544c40380d42c0351903940300050b0380300780505800c1504501d9013500c444c02c42c07510619000604101c1d00304c880c06041a0701c42d03141040d4030144134108907440072609450b07142600b01690b51074002c03c40940c100ada43d081d082c500c46c0da13001032902945440890340403060202e8a0440e40031099803007940d0710449010003a01a00300c11182c1041e1502800c11013000f6081d03211029007c2110083c041107540c2d5400b403110312219020000c80c44854054982d842d00c03080c0c01a40c0c8021014080c1d545024035514500e440c0408011f541c0381e1510000c9403840d0400d0742d070800009102d081c0d813400300c440007190f00225028a880e24010110302c55155424002cbc10544044090702d85a8800000c50b8020000000e44640c40000c90014034851b040488041c1c565001d1404203000344040b450000d4000708001450a000f0848444200000c0e0001c118940b1042c0240c008100c0301102c940450340304120030070010b4120203991040a005091070300b404142c80000801a440d0f600d9120a1904140303250861181c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 706549820 1250 706548570 706548581
    0x80106050103181218090507030905100b060405130608030703031e05011409060f0d0c0f080606064914060315060d0602030f011a0304030905370504 65
    0x10341024003200c0c3c00880c0d5400c1c2c443d400c1c4000c20810403510815111001d070b4095010009003400301c20600c101d180c1050001d00800c491801540d451103024015000c0204a00c00c40542040207485285030900304804d01c00304e41d55090803d6400c039614400011840c0c0f003807000c2c0600764400da5003c100f6881340c55031070011050101b0100c40b4946440010040f4503400c0000003500b8000303660140040d96a20000340c81840c04bd0000354100101f103000104102403400e04806807040c103100402c0050b120000595210303c1154800e4100c0405c11001400001c0856030904481601c914a9060900c64500d90821041440e1107030700c4c071006542441c101c807003e001c3e01c0b18843c0c3c91000c2d4011071411400095940d40c0c0d03161145030100301c2e40045580f507150848004801c0d1b401540030341d0350381040c40340b102d00d00c90309101e074400074940180c041030082864811680aa90142d442d0000b860800f000c2100d6400c0345000d18155628211085415240000c000303400c10080c4c6c400c3d21101c900e00801c0c04103882c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 706551070 1250 706549820 706549841
    0x80106030513060c120f090b011212120e03070818030d020705010e040b090c030105011403040c17031b060615070f1e06050a020a030b09090a0308091006080106050103 73
    0x505000030031000b214210741c00c0d04034940110010403100d40c4281c040e5a00d681042c0000707042c600f40405000700c0c1102d600b1691a840c03050340001c04070380c2c1e1004410f045c07e010322002000ba50702e0102d612a40d900c01d41e04900d112910b240d0000b8141d07101c0a02d0303480c60780401002c5905c0c01000ca0076089104824042100f014419009403502c070030010802900d58035180100b07414413004001399003441e142c41e800919102009005080141070100c0e210701c4941092040c140018040f08a4154284050b420359005e0366120355800320741c41c14450340381c0162807030318520f990503c410301803018602c0f07581d1640406030260034050b08440c1026010301c88851200101040c0d010b208001130302c005500004440ea001d0f4021410f10311000d40311200e0074041c0210746014005608000901c512281d980d4000c000f00550f5480402c60001c0100c2400f03544401240c41451541000c1e07042c001090050800e554000078240a407040c20311301440140c00c0b5090768103d1700d070b180e640300c00074000741d60180f240340c4240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 706552320 1250 706551070 706551077
    0x1f031a04050f070305090c060708090306060109320301090b0a05010503070e0114150f030a0f2328060518013804120605010b130902090a050904050d080106 68
    0x51402506500b24103002400e030000301035503100020001c000c144140120100010b00380d50381c40100b0f04041182d43c0090317102c1d504c00e00415000c20318541c0902d0f641c00441e41c000d101d0398403161104484100b00c00c103010042c0f03014041c12200315102c0da803e205c0c0c0c846c060f114849805140c00c4c0001100121503050300601c1c026072041c0014440b580c825181030381121684086d401e803075500140421805d02134002000f100360000b00300c8062840b810381c0036501c1034520783c1d420400315040b01070384000c0d20741d02402500c81c001526003034560399008482c510390008204c0003603400460302107900c5000d0303544020b240100f607545000500075840d1900c5440341d02c0f044840c45080d030794104140c80c41100300301c00920141d1040d00200c00d91072801c1c4030b00028001e5140e03020366101c5a480c0c42c100345904108504880c203525000c00401ca00c603007001903400e108540c070710227080c0c07508102c1d0100003580081c1003c0c4d03101480c4040001d042d510348542503c643c0c800c2001d0848028081c0001d411058107070003520a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 706553570 1250 706552320 706552331
    0x3131712011d060f06070204020904091a09060601020a150b0301091b0e130206030f04030c020406231008280f1e1b0e0111121b011107080304021f031a04 67
    0x1a85e1140140c90031300d90100c5005070b4582c0f40100280080460700c40041110b00d000c08600b1942c1e42d911000707442809510280d6005696400049071208410003000304210518084000706248603400001c100c1c00113000050300d40c4c265142c014065000311404107080315220300c1400020001007440380c1244000b000c000c009801640001c006000041c0304403207480c1994002024544904c441007040c0ba000383c000c0040da41c8404040501e042e119440c42000c0060701c02c052040d0400748568034811003079660f204490317207500162444c2107291003290f070760064141c0c0603600740720710700d2141c3c44011510100000d282101c02c0c0b400005000c040c50f813032040390b00d8a20815072001e803034130740111041f1040c03404588a52489005841032003680c855a00240728804400d070598100c5401402c807140000071036052200703a50105828ad030b940700300b4043ca0b15401d00c40d401c0010f040f0000355030040d00c020100c03208004800300829079003140740b10040c0001c6d00e41d881b1070300388078103451948043c01c010707a000e005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 706554820 1250 706553570 706553599
    0x100605100311071106070813030209070804050607030f0b0a12021801030f020105030a0e06090106050a080a11090408120c0d05060f100e0301151205010c0503131712011d06 75
    0x9075002e03d0340c020f02011206800e00503039503141c104035894980e00c52420b5403901002c0100c03401801c243c1c001280030f00703621700104070114010507800f44201d5004000f86425a5000070132001303029600c20412001303848289850340c52fa10706508034050111341e20b81c48040c4000d401002150303004041404c2c021034403180117002240c2000b10307080300146c0a0034200d943e0788650650000404411040c000580124003e00c110f01e007064011004450003101c1d03102119464030702448c0c984c0e0494a00503c01c1c00461150070050034030800d40c2e035100740116002c2c0e080003400014005500c8040321807200d101c2001884c1c50341710031503115540d00000140e5039403c0548c0410f02060401d10b070b52141000380601c0e0342c040880d51f50250000d200803000041030303503c2155103030101003001e520554200c0c1e943d401d10b40c515007610300c03403401e8074414a0504500e0128901c0c6446001c50031030980e18031040180100800e580b10340500050038000c1030309641100d0b02900d0901c038514104000743c45588290108be400d02d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 706556070 1250 706554820 706554851
    0x61f1a030406240e0705120405010e011b02030405210607110709110306010e13110a120504050d0f11060c030405010b030c06250b07030903090603060b030109110c1006051003 76
    0x4041e034109400c5801140c450b00d8046d00d141c0900c009800d0382c00746030010801040380c1904041c002e03081c1d0b40003e1140c2c6080070700c0e602c440c0f03510425600043c4d0040c00100010320700004504100659091101907001c2c3c1340b580141090300898002c0007080545480c65282c0c4820803a0398000c0804000810800c9a158008030040c840602404e04229216020350000c0c3d540008110701502000d01c1041600c0f050780c094002600940008004500c000e40c140c880403200b0b02500d481554410301400800080500079241d04d00b20001302010030050444088192808001c52801428030105140d10382c5014500345003551450303244503000b900400c84103441c44e20303140196055010b08a148800c0c2c031501c0603200d03c0d074218024000c3d1001c5501c0080c07020050300f42d40a24002d41c0a0340d500300303100307445800603029a520f03407082118084040004220102c02030340050f86003040282076914043d07880d81c14510b0040513401c2c0d09061656000100090725240882461a001e01d04042c8104d0811b5600e05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 706557320 1250 706556070 706556141
    0x160303020d170c09120d12230601140d09050105061215010e06040f14010f050a030b060d0303020c06040b01080d0306081002090301110a030b150c061f1a030406 70
    0x100001000841d01c4401941c0b40020780c001c900c45801240d21000340044d0040c09611f5680405003c00d10385140302d001d4011500703910150400510260f0860380b92640110780030840c0038030504085e0402d00c4812b400020314002c161301c00d13016500100311410702108100d16210f009150040c503900000c00b52660000c2c4810060440c0d83c0800500c0095440002050180015039000421a07103442e103038051504010504034103942e00d44101807241500d03881445004015800090106507081c00083c116280c4100d00113081c5100b4500035041016a28140385000e0050741c0464410010711300501400000b04900c42c880d104900d02440300502d08a4400d131680403100c0500d000c90303000074120001d03440c00d4100444074044004419513030b0070003c2009000300061150b241c031600304081c8540102201c1c0043d15403045140014000781c2e00d038a038028100d0749081d00070701041c2010180029110205c150aa8100036201503c16503d150900d050402c4540107072904002441018a0038400110790441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 706558570 1250 706557320 706557331
    0x902120403140903010207030315050a06050304060c26181915061e0609050f060d0b030c04050106051b06010602120f0d020d020705060a09080f0a11160303020d17 71
    0x3844a019603661900014403d070424150991300018200041580c940c0c000c010320b022103c4103001c01c0b5202d004211510f5024400c00f00003803018004a00030807019800301d040c010740790500a400c012000036130911002c01e0880c0080348103285040011424005ca02c02d00f9082551002d032101c11070201800c18010b444000242041307100105015078102a503200e80060140300c50341041850410003040c035130003440d00034840010040c10002031103003041d05c3d140c41ca041c070042034141020410860f10700140b1030f80e0401913051045485c10070058465104090103001030f079551558401c0c1c4804103540c190080720404000360300c1030004004542e80441c103041c90205180d0402c3e0748840c41249a40a40919110071540310320000c0c1c6890000b2184d0300404c80c042c03140058552a54424000c1d80486010351009030511004102c10294035220400402042c1e0715130500e402b000240882d080d142110101440402c5890120b0a0041c140c040103060000c4009141540c0382010b0400c0c0c178903100102505 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 706559820 1250 706558570 706558577
    0x10e0a062102030c0409050a0c060c0b06090c0910050d140105030d0f1808070302040c02010209011d010302040f0b070209010e150f0a0b0c01050f010902160f021503040f0506010902120403 82
    0x1c040031980d09018850061000074400e1058501390f0030500e440e8000310000300c2c2c02c00450040094868004c0c4110881a500300942d0405944c0d000284400958010040d0300304003810842ea124941d2505c1c8040390414143d5960340c3c69000441011007101c80b80941050f07000c03102d41c010405070780c002a284000c165185000103c41481c00700035038450300400c03000c044041308103001007410000040c00c40100d0f4006c44040c000c003078144a09038200c0c4512211039001800c144240548050450700ca284e40000c10f1500502d4951b40f02d07400545a8603d401101e06400001203180561421004280c090101001803c0040c1800203680c0c2c080f071034a82c2d50a02070103241c109143d4a81e2402c61a400520711050b910741d80726440c00c030250003098126028502c01c1c158a0000c10000050b02c2a20950020311480903d880d609407a40d4101c4100c0910480c0e03c6600311981516003002400914060b40c40f40c0c1c139010b1410f140b86000350400c48160800540b441c4103201e240d0101c0c240c00f409680142c1c0605 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 706561070 1250 706559820 706559879
    0x20d08210a200702100c02060a0e1009150e0321190e090a050a09140607030c020706050d02031f240201141302010909020a0e0f0d0506010b0a1206090203010e0a06 71
    0x140c280d0f001e80c1c1b6440041d51040c8041a606e1015070011482e038140f0800f01d44102108644090980d5407c01c140610050248608881d050300c034000c14030005840f2380282103894041d45940015a10f0310360f00d070081c54400000ca600b03410103460024252a5070b80c5402c116110035050380206d070900000a0000e20155210004500000455440791301541e41181e040e00c0041c4070f810a099603280250340ba040003901c3e0108082c89244003041d0784007500d1095030360504c1d1620158100d8080d4102900204410900380c1c1c820280d205030780a203000400d514a001280c2d00c001d02104110b1021008030942075906100382e183d00c881c52003401342d0303111080000062174426280012100181c50313400500000d4400990b030311002d030700f01c45a17400300d4504031100c8a00000c202c042c019070801146004005a004100511401c0107103030141585100714904102c07401c007590002000e461050340302002c0c0b1076000005200c082c5c408002942c1c0101402c10031f006803440d11001c0c42443c07101c0083c0d1640c001410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 706562320 1250 706561070 706561099
    0xc1506031b1905060a0f08090a0210030903050415020a02100e0d030507052e0606052107020f0a03051b0303070c0206090f09010e0708130f020d08210a200702 69
    0x605440a410013410300c41d00c1707401022002d440781c042c1e01c410401251640000440c108000200d100002c1d901400351058800020019809801603001c00c50a0100c103000105029200c191020046400c55000f48510307211401880900720007001d1000c100101c0b02c02400131603c80c1481e072030407640d00d440c05956503880d5040084c00c181c060405c0c0c1500e80c449001d42c200d40c2030560300041c0e044480a07410404a41c2d03c140070344180c40b8070403500c026400300349054020188080525640819a801a0b80550400040716814103420780805c5000c80c5000c22120368481c0303c01da500009000000045146090621014210745007040c0004d1260000042e0407103103864400d1810990040a44010503e50310b608007062409001c84849001030003c000141d03141055180c2c4c050203a0300154000c20394110780e000c0c0302034080040d40c01d60308c28400b04800c00b44002c0c0810301440450030035031a190340d42800d00c00c0038141e80502c040c03c2105419100b8900c100100c040c100d4030110790480b482c40321803240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 706563570 1250 706562320 706562359
    0x71409150d06050418030801180e15070e0d0525080d050d0e0604020108180c0d08090315240a0902130f050904150f09080c1506031b 58
    0x4a10032049140021428410007140e40e044107007640c03001c403018452401080c02e01d0045542844000c0c00140780e0000400820403090140c2c41e40c0706098501003180c42c0000780c8585070040c0c24051122264080d0f040040781030303104901540c00541200c20411020154594580c2c03000f0194101c00d114005220a499440c0851182401414504117a446120420b4805081c82e0441c0d1800044030b4104907051003a214046030071481a607050f12a040340340c5510b1049041e0b081c0d4000840d00c2840f41000c1540282e5881840c5035855202b2900c0c1c41c2c1e034104480906041c108000c41c4d0003c80503408082c03204031914844510741340f494019000203407090200001b089040d1907401103510520006111a1500030350010000f0307a11045240b018407a82c510034814480303400c0b10050000f202c0c1041d211603110854002c608100c41c0b00e580400ca104442d10b4049c5250b1040303070a05020307804142c20b102051109000141e02100807000741c5041800074464010034905180c80602c5000c29119001d82e2110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 706564820 1250 706563570 706563589
    0xe1f060f030e0c21011119120f33080c1e10230408151f14120c030a0605100b18120a0c090c05040b0c01060311010503071409 55
    0x4000301400a01c013004a1407184104490700d94220725401d0040095501c1401011111a001038200003c60784d0500780302240c2107004001c1108243c0d84407000d002c2d40d002c09004002400003007081c2c601c55075040f9000302001070710300b44a416208e0240354003001300710408102660401c10585092840102e4840b140020342566034003641d11101001e03910b80d40592042c441d21006c840f201e0490301d20440041c54852600580c86104241d078469070050100c04180507826030410081500031110000555115885590356001a008003501221401084c581244080a41c0c180b030310280c14004c40c50b201003511114001c1025042540ba1404160b80e0405021b00030003c0807845007503a100e0f07a6464101c40b10640d0960114452002e4801d02c81c007030340020030420501544002d2101e1105e203081c602c0390251410015070001d20109000024a6000c418020504c00d640c1d500001400f605614112010044030070215041000520401803940e40042144076500c48804005850ba0080e000040c522071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 706566070 1250 706564820 706564843
    0xd0608070905100e0925090c0c1101051321080d0e0d0e0d110f060a02060f0a0902031b22140105270606040f0e1f060f030e 54
    0x100c0e2100000c0e0300659548032901940a10305410303555a40d9240900ca00c06050b60205010340040c1c41c42c20301a610003800854500844070740c50203281e940d82d030441c01c41313120346000000314800c103400b0002c07c5121214001136000c02d00300f00b41001640d030399220812500c1d000b400c521300001401d41900030f040030b40c9200d41e1075100c9055a81c581280c009030000d80411002001e07244030310540c0950303407406054200c2c1803200250000d44541c00c96125a0f004a41801c4482d8120965108680464503110700900034140b007074000b0495414100031340c1a480c0001407002c8800d0b40340c8889107006170780c0854040740000207401055076100340d5400248200c410301007000c5c9440f40902c80d0000c005c14a030000341c00700c9903141c3c41060583c0d0b0780060003d1051181a0350704140990240d84000044ca80d901642080300941101d003010780310201c0d100040c8403038002d000311005200400507100708940d05001c98420441204042918020380680281600c015200c20300d07880d801c41f0011a14100890508035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 706567320 1250 706566070 706566073
    0x14040e070f0e0a06180507030e06090124060504050108041707060506030d030e07091d0a061d0d051e07020d120e2b030215010b0d0e0a0c0603020d0608 66
    0x15541c410390418503001d8802e2003956800c031000078001d0340341032281604964891071100305001c0200108001040024821001e041c0d0351034102641c8401002060b200b84064000000c0403039a00b0f01c21205c1802070f00c0b801d816841014000e010841c0c0c00070a840440380207003030242d016200c600d0020f8800c00c2c0400b04500711180411880b09000481c0c120701c5c00b55000b0340540b032042c11114400c4040c1d960a078a4080b107a40308150404c8030341c20641c414000301743e4009004803010440b800c018140100c54800b0307500b95448450440c40001000d070300c6884107414800406059060a0002d0128001c02c0082c1030340c000c410030768070281140301040350000e55000708904a02c00c90352030005004d40c02c0e0390090000400c04140441a41010307107800c61581e0f101c0d0040318007060b944002074034100a00c10100c00310302175407580007049605800f03820302070210143c0d03040d151142d0341903001c1215040c542d42d000079481a41c0e000d011a82d1a003041d001e982192901583e1942d010000c0740140500354011007a6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 706568570 1250 706567320 706567333
    0x2070905131403160c060806010503070c0210020a06020c0f070b19030507030204091b02071d04291e0604020403030503070c08040b04030308040b01080c060f1612080403020d110714040e 81
    0x401510f498910300703941b05038a5016080d162800111828002203c02c20046100c2070340f4140903113440c94850794500700610480b0107650f15562804181e820104055045500c514114a103000d014000d801c0900702e400381d56030800004111143e001ca40032600303801850365400102d022540700f50103c2e40036181d441428005052244900e5240c64540c1810300d0040c054040045402d081c43d41c290315504007941341803000c07a01d550303c0c1c4058848681c003540f004480c03d6460421007090b06102c0c64415a002459a5500058a401120182c40c0100b60500c01c502c100703c1480066006810743c1d170060050310382070300c40141c5850300c0c2a01d0310035600200d2611401080020030154400d030294031852190b1048d69060340d8070010203035251500c100c1e955010405004850301d88620798054400d41005480111081c0d04c2500c0f01c043c4030001c0512440000e44034000c01050640401101030783d01010b00d00141407081d038048407901c441e01c6005211200c0c0b805a0032042c03d640d0783d08941080b52042c4241c80f003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 706569820 1250 706568570 706568573
    0x3060a030c0b0d1b0507150f0e030c0705010c0804031103100f0b040b1206040b0c04031707030e030f1c0302040b0a030b0a0608060901033509010207090513140316 71
    0x920341004405840807070034500712038400c5120301c03a40074082d4800e860b41401d050059031101c00240c00252580903440e070b130746000c10701000a80551224804140040d59452a42f00e4940f41400020b030800ea05000009000900090001003203900702d0313411003c41c0e40d0008645c0c0c0041e00300440a652042c02e1800c284c49040044403a0344446400c2070100d404014404400c010700c91104018a035524003034002100040c00308444846050780210b082e080145059125610054452881070f4902008035011510908141d00a851a41c4511044bc0101744141d9400c840695070b0014682d066584403c1049400b1b64034002d80544024001c0040490380350750041400400a25406a00c0f6115040804001640318080c140b4180540406400075400d80e0071034507000d1010b2000c2c41c0003001103003a03401d02d2044846022a1080b00c135a1140c039259a0740d0a5000207207480050b03000740c0d50301d601d40000e00c1400c1400d00c0c600e0b05010340c081041902807103078044482c00c5024510890003030b10380f0b0500701030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 706571070 1250 706569820 706569839
    0x10c0f0305030717011208130803040b07022b060f020f03090f061e01060819020a0e010e060903060105041503170301090c0503010b0a0c06020c070605070b0604140c03060a030c 77
    0x5118904039903680031190240c1c088901400028482c0000340c1d203031564286c010030a2207000301184110300580020050741da400f500c0c03a43c1d006501ca10205103005c1038003000c500c3c01c3e41900c1c00c44150f000c1c0856407400c640000588000103944000d01080d929240b41a0107615901a2510350304a4649943c50346090401a9150380544d21320071401d0245400051b000d029041140001c10002004900d050b0300300b21041d240810058038500390513203102104070340c2140c0f40c0020402450559103020354440040000342c80541600c01892290209000a0301c15460010300c20341121001c46010844241d5603003a100740014933003028085400c0c43c0100310b0403091400085048518040c0100600000a10200e400780028051504200c008010003070a4030310400e00422002d0248500500d04881400103505c0d090301d0750320207008610302040070700c140b06109400c1540000165803c3c44420754000d01481c4884004000160121001c00030130034903200c001061000d1035002038801c8020f5101c10100c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 706572320 1250 706571070 706571077
    0xc0f061d062b2309010c0c030e060405040f0c030b240f0d020a0903031803030f050c160609080f06070c03050f0d0f0f0e010c050d0905100207060603121d040b010c0f0305 74
    0x10007020854086444c25005110b0418003107200d50783d01c00b0842641c1c2e000c4840d004044d0129921140500003c1384903039852084122140c1c00c481d0000d501c1c8040c40000e02a41c44040d22948030b07040500504001c0200e050000740c94025451004e540c4000d502000000c0e40505041c62107100e1002c5003540c525508108524142d90007130306c44802e44202d4508414813162503000007000a0300c01d81e2800d12160142c2c2c042c1c810f14540b882550113581209000710b002c0c00f0990f11000c0003c140301420040c10b0000d202c0e1164204501019040914101c131003c1c4c03500114080040400c4000141d11140c0500c0409840106603c0c3d4030503c0717000a139280d5040a0320b60170b12000c0f012443c1415442d240001445000300303000c19034075a14100000504240010711031200152894082c148503201c48000c42d200074003071284111030000c1c1007419828026089241d000d100028015005102000074000c800c50005003202207801141032800540125030701c040580000300650b0310b05c40d04104254020026 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 706573570 1250 706572320 706572371
    0xc090608310f0c0e0c1c231503010e07150504170625120f090506040b01150908030f070c1e140105090904060207020d0c0f061d062b 58
    0x101c915640c40b42c4c610300715038006441c03901c0f010404000d680300a00b00c4040605105580382c00020b40740003162150103440070078050103854044214204078400c600c200440c19680c4007078000b0407035041071541c500da0f9043c0c01e004981e00240c04801c0704000b03d11032000c44000d04401342c4010003840c4105803840d555071090302c3c540381c0c0c2410700341415400c01d002c500b0b190b1007106607510220741088075500c80c0028200c0b42800141c06031240c9101e40801c000b001041e004910501c0840c000b585080c900350b01c090b03100c1810104010a00d0410400007030000155130b080c080c0e030400f8581d10021440c0046809800354458000f8940003220b0403c02d8a0030b0340d400c400c80d440c2c1e0601580e2007020707c004543e1071141035074103588100e0540229000c42c010b503000c0d10129102a02004405004d40c039406c031a00542d5111003c1018004414040b2582c0080311105006444000d0a070041c1c00400143e40b0b4011540482d844010f051885d040c0c4000c00000719800112103101040102c030791000c180c2903218401003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 706574820 1250 706573570 706573583
    0x17091002010204080c1e0f04020c030c0c090907030317060105120705090406060302040b04121a010e09010e0a080a1d12010b0102010e12030f07090306050709090c090608310f 76
    0x404100d075040c1010190407400360301184120b9846c1000c10452800400121582c100c0c0d800d100c143c2800404100400482c0c000c41300400000c454001000000c40d801829450b6a0300401c0c010030000360414800c40081403103000b240c03c142d90320760048481c2e0140c0284a00c4603070300344003406203e07a0000020aa003c00c1618180421901c2e04801d40c01e910a42c0b0640141440411041159888030314400311014894012040115502c04910007040e4081c1c11000745601e0920900200d20303400d1203681110004800078110900305622000c00344d01441290405104188805110f8145006240074041e03000900701603a030500701038600c0c024500401d03007902641c03030950141a80c050000b08070882d21250b1502c41d1440c0c0d148901100541e00c007900721802d00031400030200014101c0d000b0544900c880c1da481620300c0d03213031402400603108001050014010b9440c07080c0800da0340510758a91003000d0b488882c02a0700a10084400303141050700c010690030201062508005d03107081144103035805001d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 706576070 1250 706574820 706574833
    0x3070e09030f0a09080607140a110a02030105160908160b07060216050705042901050a050705010f0f1811010e0d080705060a050105101b0309170607140702010c1709100201020408 78
    0x1a00d0148502d0880c3da108c040a020300c018043c421242c0c840c074004040107031407000c16554042420f598050707411160192081800141482d800281d1900174404140149104c46031740c045110040d0707a5000394011024000b944c2000e0018a0301141e642200a1580b486100481c2c00d082d41c272a50580600c0b41314070306100c520781c4001a0215105042200c0142c0800c114074840015183c0c1d40c072501c04141804010710501000c0740081c0302e20103001910000100e0121009052023003150840740070030b04034070164078041700402c0001c061a4441c074020f003011030380c4140034400210036450300321000740b2a401c00101d0008004010802c0c0e80144c02c7d03080b003801542d8a40040014021801d6a20030000343c3d08003c120300c0d15078041aa0482d68040d00740640583c3c1c50b03000e0b01d100c1c01e581000400f860350100061021321903024940030584002c04030010304003541c687c0000e100c0c082d6100042d140107000d00324481a0901d10b01100c290040c000d10b80c1001e1200c0c41c002a0107500710740b058420601910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 706577320 1250 706576070 706576081
    0x80105030c06180907021509070f05010503130201030504110312070c0f081f0f020a030e0c060310090506150a1d01080f180109020301290f03070e09030f0a090806 71
    0x240d4101101d003d605a03041c00c416070611442a100604050441c0b10b000990010500c3c2541c0700c50281c80000c01501794541404608132742104680e00441c104441013041040851480311100800f035424a804103181d2510304200000c0702c808110140e0601601d4590b10b0ba5000b03107130040a2203403055120541d90303a520a10309e03074191702903c42c0044642203451002258681e4a800181402c0141000103074111420f075100104e80008803c0c1c00407950343d941c0900800c41c2082072081809044828a16518003190119100201445012860350300c60000c40c5046c0d68000070802001c0076100c00c1a141d0303100010051004081c1182004100300407a9194815407003480e04900c261f0320901100c0c596242c0c070003504d1010510001e00c0310a550b0b5205500c0040e40c0a001c3c614a80d2202600e40f40000001c1c080103002405c541c0d9131070311030f1000201144046e1000b068240880c0c044d903a4440aa0b0b58040c20070f030441c0719030441d140c42418001500c030384603134201d20303890f0507100d85108032051036950 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 706578570 1250 706577320 706577329
    0xb01030515030303011a071205120a0c052508161401050103110904020d1227050d0b0712020408030307030606051614100509100506031b100306080d080105030c 70
    0x303110940d0b0103410800050005840c2241c0e1a180408503845803454100f643d2618942c51714944d820728002000003810100386d060b4264441c0d00101f8002d070410101e05900d101402c82e200720720390150302901051140070504110300f41d00786802d400000d2070303646001c540c00e40e03d164a81440c0480c1c102c24041102c041d0040140b02c1e0034180da0b1b0001c00000b240500c2820026103100040c8100d900030401c001789000100081d901c1110500c13180c45000854841ca181d621501081c0c011002404441282c00c100540e10741da110141d280d0040c0d5808442e0b120540700300e0740c0203a518440d0044c603000080000e04000f0010007548100c2c61580c1c1002043d894920440b054455208039915000304542c3c0c0b040840e1481288008043c20350b001c4451200e680003483c0140c8004030f031100b0361508141c1400c11810070324040c1c42d50101007107014061450340c5952079400110201c04c028001e0000c50702100c3c18500952000001e8000c0fa021200c980219110040005009006050007400780492003600d40c1403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 706579820 1250 706578570 706578601
    0x708091626031c0207022707020709140604050a0e03040b04030501050703230c0d2a0e1005090310110a03060e01050a05060c0109020a03030f090e0103031403040507090606030b010305 80
    0xc0c01c0c124112142c3c081a010000303904103107420f80c1d0107a9211081c800840049840e180d0600301e00300803554610b032182002c0c0c201503c1d5031086009074240240e400c91017401000255101c10220340000b050b40310080180f00400c047c059000741444000ba0200b11803840364050320440380b040340280318595070100210140c5417005009260b002244004400c00c402041e0f40c5948a41c80da081c5e40d003400c6600c6d90f18000e585040e60f0741c02c000303888510001004440c0e040204038245190600501090340c00c0046882c05035002d204000704100825001c005543c148100c0803d0b001c95a4117002c1d0004442405245500161045001c240390250014030551484c00660490780001c1c42c080c8000e11b00000e0200e1584440901c51895603500050750060741d4040c10440a107001f0790750600401c40d61a005000660f00d5048010120b650500402c00258800041c0710100060500740e6101d4485240c01441d00c41d0380d400032007020f0706214010481c0e961550014001d68008d0340c0500ca2516402d489060184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 706581070 1250 706579820 706579837
    0x1e09060304020409060e19110402032701090b04030801061b121202070f0b0402120309060304020d0f060c02010e01060906050901060f09180b040b030114070809162603 73
    0x901480058050b1030b0076800100ca90340603076004108802001c541506043e202d03104c440c52041b251b202c100602c618a0008515044240c03030840c0356060508034118070207900b50000301c07010b4400174004840c51013900041181a4804624005401c0c14900034040381070134041e080004040040d401603414041618580c0542c00045a07103044180080c115101d40c090320091140940030000200041c88a10704459200d0140c2100307003050803d0700c1080507014240c0c0200000e41d1041c4124105580e1340b40840b034002c0c0d4101e071084160030b454035141c40010403854020306840c0c584411101091b4040d001202c08a074120001c10078103482e140a001115501c0c02441e400166010040c040680251000f018070f41850400c0041159030b0300c0b084407040b03410106c5504081c4c440c041145103041a0144007410345007200244000d60300c803015403403100d034003e040008001c14180400d10b140c8081c054514144821001c07840d040c1d4540300215031840d00221fa6068800d0030180850110720080142c48414 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 706582320 1250 706581070 706581079
    0x30303020d05071d0103050c091903060b010801030804120c031406040c080d08041203090c030f0c170c0108070315030c080625050a120c02010b12030c120c0712081e09 73
    0x44040e0011401845c0c01044000c2c0e00e1020421503401d80d2b41d421601c880301001044c207c50250452130070000340c0c0c0c02c44440a05000c8050f005100141d640c40c10b44090301e001900b4101c120f642d0f4213050010002a0f0302c007422941030710b440c410514002003400c80c0300e9030040030100c2d0712503030317a0405c1a9207143c3c003490040051500800305000907c1c4c44140c0c11b1902261034045421015a11561910342d06540308032603140007946100c0c00c1100c004040001031803c1d09000c1101c0340b003246030584415244010904000900000403105402a03201007000a4180e1280b040d068403840e0008840d80d0a01a400795032003000002000380511119030038164040604001c1c6000d6006026a8141c00440d5894240400322865840846051040b100289016400031400912001c14000381d41402c002c2c0038400d1700100296041d0103000200c2e14840c68800c4c10596449250a140504003081508401c5c5c201d080c0f1528501031101c400050006078001c103900031061910003244100d148101d0780c225400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 706583570 1250 706582320 706582367
    0x5030f0a020d1a0108030a090e06010504061b140a0c1223070e0c030613060635040c0608070c020102212b060824060d0c030303020d0507 60
    0x182050801e914a0b203124120384501d0b003104040400104000741c01003072581e840810107911096109030402c0080110b03d03400b2943e403d0410001345a4800c80c042c0e0414403682844261007810722404201440313405c0024488400310144442ea110314802c0c000341e4114180c0200450f0800c164001c58030b6a40c1d0051260014601e8958840018602004450014024082c00103000d10400340824441c541400c912540d13860100b00300400b4104403110314150500e050401c4c401c40c0c0d000a1070300c10311144a0040303c3c84c02c0e0681880e10054080300008804050704170140001c01101c52101001e40c2c1094440c801c83d41d503001d40c00c40302003110280190041e444080001f0100140404c4400b55210510707515140480303450700846d14081e4400788040303241c84c030300382c039141610b4074850480a0155030000d010003030b070300d00d903004441d0340144002e21002c80c0300008039150380d40d50802c2d41d50803948402c202030800e54a040c060000e41004444051490030000010040781c13103584000c1111108d010082072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 706584820 1250 706583570 706583573
    0x1c0c110c0a030b04021804030c06061203080c0319060b0a0e01211a060a1d030102071104020904020403050a0804140a05060738100801020f04140402090402030711060105030f0a 77
    0xa10004c3d000340d8000c00049030103440340f2964402e5510442c041c0d00d0701c3c0c4006015203040e1044880a40c020ba0440c07504608a40c0003a51280425800096210886449481d45000c541303000035240d0500101ca46000740010b402a10080504500070302d94446d00291401e01c2c5c01504c0a4044866010701010b0110502c01c0d5100d096101c83d0800110b600000001c01c10000820300b00d501010301032000c1070660281c003502c3c80c000e02020f480c0d000f0035030095040001d0780d50f420003032100171000244141e8010500541546a982c1590010b42d040030032500050254144190791340d1040c052000140300780c0301400110b040107003c92040f2040a408a807500e541903e450310003510301c0a1014405111101120840c0d050352804051220010342a221038100301c407002d5841e9115078440841a4014040340d26040c81c1c0c241500c007107400c542d010801c44401d84001600034807c2d4130754140d000c0d01c084107110300306502c81d00c1e4140071820742c4201c520a9807100b00b05980c603500030107600e22a40c0050403400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 706586070 1250 706584820 706584833
    0xc12112d03040f09090813080c0405071412190912030f090804030f0c18020c160501170702070e150310050108120c010f090327050d020d03051c0c110c0a03 68
    0x20320070380907503601b0781001b060450000700c0c8042039200306580d40c401c40408400740341620035030b40c112003c2d0410115101d0303a94030f04001c1d8014202194980da0051000844c40c84c03560403090303580d028003542004900160f10f4803840d03d80401310403800203072814000b0842c0d506540b065400707454100c00d0040c1007918558815000ea0700c1c0c2482101d0b401c031303e804002003c3c000b0220000f04640c0d504005a1500e00001145207044410448600d24001c4a2410010b9980004041050968410020500c4d0f0346404081e8074090440e8452045250181c0410030794210325180e04a12417800c8081c2d0f202014017564441c00d030f60081c01910065080f00482d041d01d44a804010001c02100800100d00c500c020710390801100d19002007a0042898040605089400c140c10340c1c0260604041e0148a0340c1003002141c141000c0100c002e0081031400600002e15004005927450150142c14031032800e0b43c1001040d0261592565920104402d5444213003c83c0c0081541c1130441d60140c010760a0904d181c4445 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 706587320 1250 706586070 706586081
    0xf0c03191109030f01061401140d0e1c030912021f0b031213141f12090209040c0303020f0111160311060103030903020a0609060c12112d03040f09 64
    0x28840040c04000b006100e40b4180001c4ca00a0062000041c0481c585034200d00380005080445040007560b91818040290400c19596042c02c0d00d2070004140c0f6007520428502480751034041c203100340c5e10300842c04a0340d06802c00c8a89901c81d24008034440d281e9903003a0f81c1d92500c1594080ea02c0b001c5100c1c401c500d01c0c15070100510380b000030100c40080110b00d83c81c80007607010301c9001c1280c4407444801d00061181070031204a0305000c1d5400030141d2119218620302c041041134140030043c540c4c81000041c2d03166040012020340080c200c142904140c0b40180d405007941c442100580201d00c035000701d0110601c90000c040249940035450f0021507010201e100c1e0400c58202d003804503200d91488c6400081120f83d01852082c0c5400065030304500400c02110466408035041042c032850504c00154400354180354a5404590300740d29100c03110095840c10f054a81424451140405000c440d0b01150701c0d40b03504c0007800364440280c2e1030b1000080d407070384118001c3c09000c0810200802c1a051180d001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 706588570 1250 706587320 706587341
    0x6081b0f010c260d0510030c0b031005040617100606170406060308040e04030e0f13180203060c070303180b070f030b0306041101170f010b09060714060f0c0319 70
    0x34900001d01c5100c5443c4410010100700e40d400004914a10600b10178469103805ca40e04090b40c1c40f03094550f070ba440681140c180a0140d41c0f2001101080601d0b0404142e20050400184107001c8107031100e904403174600c8074052440d0284215900e20348400014445c200a90700a07566403c00c3d000950100285ea1a000c1d02c00c60300640d0310000000803a110b45d010f08064180034402c000107003000d00b030007003020f90381c00142c0c0e01c80c0d0ba1f800301c0d440709540c6802800130b060b88250300210b04d41d49804102d01154910600180d0140160300400142c0140c1070000d0120030300c03e880400c8580b41c0404900c600c070034100c80080100b0458008100340700d010b65540f5080c2d800b107290204003a210038001c40c0c20030360107840455603c051400000c0395580c00004112160011751100f142e28505210103000c0e00302c040c0b0409410010000d40a503403038403240100c86105400210030001050f0f41f840c0e0f00d40e5400c045803c44500d0b6100008202140e403020200c1e40513540342102081c00d414688004402003180001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 706589820 1250 706588570 706588583
    0x5030607051806070c0f080105010e060904060209033f07030822030224070f14070605040c03120203040e0a0c20010603031d13050603010b120106081b0f010c 69
    0x84080c00759902c41c001d0059501c05d4109081e590f1800080b049011a16001240c1c036904180061140140e003a0600e41e200600f140d8050031034565003460780c028071800d400a41c150080300035000b0351200000501103208100300050108036003208040c0012124000400b510000c1040b000b00803c0c8140b1140d50002440003141c0760b0b0710248a004071500d500c58200b02c015070040529240b6480070036413400600303ca4003141c0c83c40e91030186c100400701110a8214003d00c2401c51a180e6244442e00075650025403001040010f0308150800a00d1003445120841d0080303443e514400315103101105131011601c450842c5041c42d01c4150303441c009007034049005004c002031440c1c11980081642c2440c0103110400c030000803070505500303008100b03001004c0f43d0760448031442c04e44003c2c0d80350380924220072240035a00081d240c031403130f0002c1c2c05000741006096000b40c01c0c94401d50131031019400380e401c91b0540b000301c0c0c400c00c045403000e9440040d021442030b844241030760768610550003140050295842203a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 706591070 1250 706589820 706589857
    0x40605012c13090b06010903030c02090921030411060f0a03090501090206040b070605180a032307200d03140a02121305031203010f150905060a081509010503060705 72
    0x40031076400c180003048160b800342c895400105004110200e00e030460b0003031a041d00c407241191000391080290845c001e008400c100c0010f0078110051240d205003403428820354440300303107081c1900e01d40e8100b61070a580c0d03034243c920888058074020040700c51a11080414a00b044007024054004240c02c920584140d500d03154040c0040c0d0720b1600400c0900440c204843d148c2c40f041c180700045690043c020a40c9044081c00d200c0c8011000604c0c009255140c504002054120020010510003c0c01032070004080440c2072020490b40c00180450202190150041c1c007000d00104100307090b0004025002c00e03031800d04804c030100e6050042403140da090040394403591601c011441c06a100d08a400c5603041c1d640b905222500d02071010000c910300910445045504000c80c401064105102e020354805d0480340301c1000500400c0c024004160080445490b02030100e4081e015400407211107400340c0f401c4a00b9003c52601800306410b0701e0010300141070303130f59075248241d90651000380b00303c0202d150074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 706592320 1250 706591070 706591157
    0x100305030706021c14150105040504050106050408060702070506040b160506010915090207050303062404090504060e06071e030f06080706030c050f0712091805010f0504060501 77
    0x20002004568810302c0d005030365004207801d03100b04e90304941c407030110700e0300b08180d075140d802d0702040f05a040350740c03030994401c800391600041e165446a544420f404c02c3c10040005503c0b90080051b00c1210305040540300c0e29075076180101e85440700784c014903500000c284018000a50b2101c05469000c01071500581c416816032180c1e45401c2c4240e10807031149885561030340d1003500c28080b410081c400048192706110f1036586042e04c030300004000364000e0032543d04080d9040365885002c0080103a02298585d6103440b1900280a4081117900303a60142c2444003810b00c82c100054514814291903030b881201d10000080c0d00c007000010b071701480400d0388849002c10b12074803501c9003000401c2100c0050460f40e2520f00c0150aa41d02502210f007809400d01800c86d03510480e5080b2048240c2c0243c3c217101010121034140c882200a8010828050603080c00c64882003280e4006416542031003c0100702540d06c40400060f01d07c0c901032140010003200a044050b4141c104c04040000c0e54401000c070750046 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 706593570 1250 706592320 706592323
    0x30c090f06050f04090e10180c1404140a050a0b090105010f080403051e1306090609140a03120c0311030306280314061518040201080901090506270708070509100305 72
    0x31b1300444001d030b0b00500c000d03122881c4603214452460008101104a10b002500d89240359802841a42240320b003294040342250380d160b20000d00290134911407032140c209112100000d00e4110f441a001c1c51030224490090328002d00c00b01c0c100e450503510380c0011990410112501c640c00b0b44110140070080c001c0301d07080b0142c003000140400805010a458400e01240d415043c640c91740008184000040b05100290740b01030420195680c40b12401d00404600010480e4880d5030340c000381c0740c2500d200c182080d0755400f84024800f580a5070382d20442c6480780d0722103600e030320041d04c0742d9900214160424000a2720200034500d04010307000980043c50396516240e0703417040c0c01c007100d0303400390040c40400c00721428940d0303d002043c1066803410350b0302281510702803001101500103414032103c4000039000c940250042986541d2040c10f03074540d420004466000340001e81c1c2c184604030345085c10300185600015040c01110405e00041001c1d40c90101801050305000d070104010442c41400400030840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 706594820 1250 706593570 706593581
    0x50c09060d0f1b120c052203050607030e0d02060601051818040813080a080901030f09140c010207170a060e030705030408100e0a0b0415141501030c090f06050f0409 72
    0x301c081190f82c2c850080040c4540440d01c001c0c04210314056000d804c055004080d11460300701070b030700640401c051001d0340291802c00c0c0d0000b0158070450f410000141da044c0c10404d003801c0d80ca170031030f0304441040070300366182c4004554050001d0820700440c0c2c840707055280070040b050b401901c1e15103554607070030400506441c204c130700743e6140200140281c006010001e840c00200340c1c46001e00080c80d10355607081114800c0351030060406441e40000d194551080e0b11105485034004501c1075003140f4030803081d84550300d07488003e0140c01482c1c400161088091800c606036003815010749400384242d41c9100c0180b40c1e030300d02816640b0051048900150f000c10051016116400c024034072100d12600607020345054a2500c2c5854102c00e01d4840094455800d854000c0c0d803224a1074000e42c0052010401449c3d03c0003254400341c1c02d00107101640161508400c2528400e036400c0c846101b21007401d030b5038070b4254810420817803042036040141174410070181c5105c1074181c400034a090f0343c1c1d021030002c2e00c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 706596070 1250 706594820 706594841
    0xc04020318070e10061e140d0e010e070504090201050912030f0a090e010b09032d011802150717070f06021810140a031e050702150109050c09060d0f 65
    0x3c505818802e481d80b0301e0041c80014003962074000d1b16103994002510b004507500c004e8100707001181c41c3c0c1031084107580083d14014004040b0801c1560a404149da0180c00288001c0100e801140c20104070380c1007a001d040e10498042e16094509603c1c2428086000050864001c4900050200203201c0c40810014a040852596032051481c10050b04001c0608180d00002d00c041c01002800050348001c12080c00f100e1105e03009614070484490b5803411108a00c014000f02c3d481c115006285401c0460301004142c003c1d02c40d06c1d00d02442c8010303840c80d0b101e000e502500e04450b2050401d80703101c2c1d14008010301440351215419519040c0d48290a0b0b8102d086c0601c0081c05460b040c103440d0900302c003030009051032490802070701103064484035124440d2400c0d2908058481451782d107001081d030000d4200c00700b464410421450a0342e8029101c44550550a246080303400000410705243c0c00f4003030091b1034050440e40303010382e41c4041140d40d40c40f00041c0c0003055143c2104404c0716449104400099 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 706597320 1250 706596070 706596089
    0x120212071e02010603030c03180503030c030406111605060c010b0913050f01051012030c1505070807030c020d03091407080606030c030102070f240e03180d02030c0402031807 76
    0x1078500c039840210a04405800e4116807406800b000401e034058800300307001c0d030181040360190410340c001600d15031250700020f402d440001040c009001c4004010030480e0840c3d921409010440b450395500c50050003008001040750070341c00d000d5841c0110003400c00c50b07010000040d071307040514080f8005c0101211024020402a150301c01406014014010700b192808000c0240c0e16094402c201c01c007030140104000041c003a0a00000c060140d000f80c82c1c850340054862800b50304400400c0b0103002d00321031200024003170001243d4841d02900510003550507e401904d07441191913000c40c000c2c4a450300540d1001d581402c50601a08140000c101074100600500b0032441c05006040c030b8030b02e65115041c000d071b00c10054600841c03003080080b0344841e030100d01c40c91581e0074038810540a0b040c00f00882180361400040d0b056504000004094500c00000790004c40a507a0040000c2d01078448400780d00351b04503030252201382c50694002c0da801a0803018540f03400600202241c0b41a0b550741203441403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 706598570 1250 706597320 706597337
    0x408120901030b03191101020c03120306040c0c03020a080a052a06060d0209040609020f03060f061809250b0c07050906040203010b0f0a020309091302090a050903040612021207 77
    0x3030307580c1030241c400080c1083d4014140011400c0d0800385031104000d010b40803010000035001c0303e0788240407403d00b401004088450080079002d00c0100b0703600c25680d051040740340190350b13403205000310250702880d03800d0f401030000300c005901d489c102640040c0792282080780400030303003900d00f00050325202410303449412141e00410101000e4a44103001e04418415000c00d004040140c2d40d400026521035401140403681c00d00e5071002c5001c09c07203448038081d41030043c9002c01c20601001030071b5901c5103004036150404290740010380c140280e804d075002903070f6400c030385c090002100e81c100400400703c210160f22a0300700c4d900c4004400307541005a0440091708201c0040000d480c050481e2034002e01700315070452a65150540c40f0500344921214400a03890220700c81040c180203000f0307030301e6525000d4024405403503c003680150300b902c0c2c1e9804a11400409001c110140d0051003241d214094880086280504180c015a00b6100c3d10501d800d03442c0e020400c006a030681c130340e0103502900942e107e5924 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 706599820 1250 706598570 706598587
    0x1005060d1401140108030906072a1e05150703080402010c0b090709060f0f0608190f0605040f0902010e010507020d140f0d2a1109010e0907050307030803060114040812 73
    0x283c148183c0c0090916031045c000007607a50b982c081103c9005a02c020206007803060541809020114103c680d100010000c00000b4951003040c001d0a01c043d2401594140f80e84030410404210800e4026103003c0800b4425280024098004581c001d40141008541003101d030740d03480803d040440c0d10580b541c01540040250b189580242c4010f040035a0000110074141040c03280000300b5071040c00104420400440c1d001540ba200300c00034007140501c284106080a800f00024250622a841c0594070f0700782c01c0034a003803940c494407032003a80c141d507045040c01401004450b15040210143d90140c4880072120001c0c0d405410503102c0b000d000007810040c0954081c080c00e0805818042c820f00c10036890201c406071414052540780d94200c0010005183d070f60400c031784466401c8803100d0f00060124004030f0890f81042c00c6e50301c16944c0104903054161900d0a1548446c200c2c4002869100140007150f0950b008641c900800f090703080c801824a07a0381da003240d01d0507005c20303c00506064009450340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 706601070 1250 706599820 706599851
    0x18090d030c0509100302030601120c0309020a051e0108070201141f0b04030507091d1f15120803072c01080c03090a0204110d0c0509030d080601021005060d1401 70
    0x150020620705000f401c00101a003c103482400940c1800d04159000000482607809a00e4800780440940000c105811090307001038000d100008047e44612540c03440024240317810491100d44101c0c101c102c001500040d4015203120790040d0000c4255521040c110314003021203100c06204001481c1c85280c4004c40b9181940c640505401100070040108001d1000c6400000e400d82116800d100020309405203500e10410000da11a074034103940a0702e004000c00e0015600204000021700703604008086041d003403030744040502e1240f142100260111000407401182c05541d0140c4c0e142011a699401d0800030f0100306261252040c46589507610306100f0350744100a40d071700a1450500340e295092840200b82c4e1030510440081c45075480b8060700740b51038421003d0390720754016030b002840100321185003d00150020310702c1d40c1c003070700c074003420301d1419407140c45102c0c092841a00500b14001c40e00c2944000b4000c018030843c0c002010b0641702c00020740d12615484c0c025490300000030b0304001a500328 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 706602320 1250 706601070 706601081
    0x1507050313060c0b071d0a03050609010c050c0a0308130606180f05071b020d0605091b0301021614030c030324010305100504021c0504050703020909190b040218090d03 73
    0x2e0104410344542c2c0000071001034a6581042d0503083c81e888508130104500d031301090f13440501d40c01c919035440000c10000002555401480080028007088501010440d000e0240c00031010f801e0b07100c82d5805010a00a17821983c10601841005400501c103440d0070040d1400c0394890000204010101c649403c0d00380b0031500300040c090000d120307606080e1401010360240004100c00701611052003011582d0703074a00d1801081c0d000200344450b00d02644825100c0711011007203541c81c2c9080910714258a03040c400c4400205070110390b8150ad2075661a1042501c12004401090380700030010401004010005544554034210014400f1108981302c0c103030340030b12409558140740c04e28081c0a21152403590103000c0c4c800a80d001620b4101c6540290190b41410481d86030300c500c0c010074070050040c013080c4001903a000342c4a007200b03521103e03042599548052110b901001c4c02c43e02207000a00303200754054105000412040380341070081f945085480b410b503402c5101e540b14481c3c0e12420394260243c1d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 706603570 1250 706602320 706602329
    0xb0108060f06030a0201031e05010306060512010608031e040e0f06010905041505280b030412050a050a050f09060a09050a120b0c2503050c060c030103051b1507050313 73
    0x1c1d0a82050800310f9070340c10700d0800c000c1c14103444d412001078142504c04010004801c07840c00b4803031035035242417001c0100a907000b054014090320000328030f08001402210102c46003840110b250501d134041118140e50190440d40018008001c0011540301400341c0d10301030345100710f85801c1410101d0001d820000141e1109010380d0804200d81c8003458008000422590140ea400c14500249240020541103a201022a030b040b0700c40c001c0f9420100001035031050307210300031041c200108450203581901418480c030300010b20410080b014030f40f00d8030103480c11070040000e9904000a400001d01c0c5500710b0403d0788002440f03104100502d19103100b05a004020b2252100c400c0007564030750f58003404006201103803204001401d0700d15180c40b2002c03200c580178406041c0940d00200e1400810136400202c070f00344e15200342c4000c00c00000030300003203e049036801402020210000001c1801d144041c00000da40002001c04143c2650100fa0003030201c0343c031a5001e16a5480c0d02d203100010b40040b40c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 706604820 1250 706603570 706603591
    0x1030f0b03100504290906060405090604151b0c030221040308030402060c0307080d060e0f042a060309060f050705040e100803120402030c030d050315010207050d0b010806 75
    0xc0080d02600c0100c0c078498040020903010510350b64030309103107801703d03421102c0382c0300035409400d51031803911008000ca01441c00030040c0d86803511003030f081200b590000c0d981c1c219950440408180050115049154001612100410702c441c01c4408054001301c00000c400c04220414402410182d0600c118102c1d150303103002c2c0e03026401d40306a8000ca2400340740801031804200001207000e664801045e190750184150440c0d954024500d4096840c0d0803140f80100410305020020a4041c40c840c452840382c42c80c0501d10019540340d4454511021150120140404403185056500684000100d029100548011440c60014500007080703900c00749403403807090703c0c01c1c0c10302c00c10b03d038088201c500300c94400e020066680c5420107440c890741620303403084000b40b100007000b8407000100f1852a1244e4001c4065440d0303400c442d014181c5a51042c0000741c0011001c00c006600307125000034161b0185018411034204540b580c0104400710b0300600241c070300708400801000991406c010301c9510165844 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 706606070 1250 706604820 706604831
    0x14070306180221010605040315060303170a020702090106230412080c190b06120f0d1d0306240a0b091e06070609060b01020a0209012312010b01030f 65
    0x1074004000a0200210008071600003504500300c890303485003181000300d070680402a65a40b21000f4150f83d000344000c139405401c01605540300140707071141c90112501601e80c10145043d04a551600f914002c060040790343d4280812070142e142c0070407041c0685603d03100c0b025001003506d04202c412032148540225000100014084034800440b505007096110a0164995008003155801c1040142c401c1811803154546502030103088402140500000d070764501a200d80d2005090711104141d202c140c0c00c2c5e002244640700f40e03110300c008a00341c2c19840e5805401841c6000005d040000640c0c0c003010104506480380741c072030482d0b02d03136131030070faa044400000e07c602d0209059480e00806803424400d400412400c0a07070821450707000e8425600034600e40d61521540340030401001501c00c00c0d0f684901c0c2240007500c55000060a144554006007000e0071a0301e49461044555040480c810030007113182c0070742c0c1890f1038041802190403000303800420350500020005040320045200026401d00300b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 706607320 1250 706606070 706606079
    0x50c010f0e061008070e090304081209010f031413020f1c02040e2d0115060201090c06090506070609050304050d140607090b04140f03030a0203041d09030a12091514070306 75
    0x10b2028211481b24144c011a039848982c001e0941c051070f4400003040c040c2000d4840105062401040e5400090321140041da00c4402e0440440b60285c5c8120944110304001ca00e01120314011072285a00c018801d001440000000c030303045c58003036030407462948040c03c85001180750a025018080000c0b1008018108000b02074601d06e50207550f1480301040201c1c11011810000e4110f0b5080000d20041742601940d511002402010340703500c02d035000d1170005004039045115203804011507400505150900c0100e4a03104028131002e141110340d44010480055070340c9138500d50540050007903620318101c1d40c840300b14a0030484010945801c101c04114188401c0c1501800c4d41e05441100c0c008089001600780404c102140003e1825810b05c00810343c040c480b80d0000082c829281a0b941c40440205925a242c2107101e00761401e04090300709200080d8034910401040380312004090010a421a50b46c440b940c07061000c5945004c0c2c2911000d205402c000b11140d400c2c3c20000625003048040d250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 706608570 1250 706607320 706607323
    0xb0402031501080709080d090302032e0222030303050f09060603120901020a050703081801080115080714180a08030705060412140d0b0f061801080601050c010f0e061008 74
    0x502058107001501000c07407000c0784150301403030180846e1000c030340900900300d102074075544e01480200d11912940d140700b0070011412400030380d20045128550160412108840040d40143c856480c003180030503c1403800c15151030030403006500030340b00010581800002e92070400070007400389009600c01c03418000d542c0c0300050009445654141940d84a96410340108c2c101452844c01501c184030b510004000c0c041508000c00d110300e00100c0c03e032081101c241c010b440d418402d224000c403400300c541e00c14840500682a581d4851074603e00342a00424404210496800a51661a0f0a44001c00f401c40d03a0400c0c00342d400c05884180021828603909a45140e44d95000800007040e51011034030861285004488400d10301e195401c4850319404803003640e500070300b43c0d00c40c2c1a01c00d060740d8141c1503160620700c048a0600d94035040d080c40d103003a44001580e49240141000381082001c2100e900102c10a11481e1080342010740b01143c0008030340710b1280303020809842c0280244042d4420818100c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 706609820 1250 706608570 706608601
    0x150106020a0818090a1b020d14030718060c15050124020321040215040302181b041212050315040902040209042f13060c141009060b040203 61
    0x42c03000d8100c0d90b800f2000b000d00e02c40c0c05800031060b080600074081c01006806508440304031184890f04510f0401800c078126501c0e9200c0e007460012481c8034003030791840c1441d00004c6030300038114104980c190818001d4403081c5155a403000c800a007800032024100608489013401c426000041808254105a074504240c400001014000700700d548007240ea0314001c0c03017580d80380c41501944140030030185000421002045900328410711800081445d250818001d680a8980142040760400d02c1d1801441041070058404490300035007807034007900ca00e200c0004001400209091000d8118185130600400c20307040700324024020244100109a031300e41c007603040c407814211404241c074041800850020b208103980740d90270a09000403400e50441d948030105804e0005a00b04000c26880310f9201d0003401440c442d401c0030440b1075400c0050364882ca103520196400303102504040c803501480546802c03003920212142d01e440d0303130b8038900b409014811404903030320640e829451803500403603c841503903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 706611070 1250 706609820 706609823
    0x3080c0a0e0d03030603240b0d0b13260712030b1c021c05010902010f02010903020714030327191401032a09030209150d020f180a060602150106020a 65
    0x290302c2400d203014948290890b50096421000351143c00e8400162500c032030800d4501c414110f41003200010702c03800c0c0a400c0c0042140c0100d0690701544400c0c0c102c0d03240404000040e40c000412a800004600c0442d100040349100100c0781c80c0d440c202860140324407410845000241454110040000d84454510010001000500d900001018400901e0001003028030001428601c0c000754101b00055000c0c2c210f103030003620360400403049040102c0c280c0d50301440c010010703008040100301034544040030610a010040a0f81c1c02c20700140c001940b400e1005010203805416002c6101586c1424014110180c130010b075003488103420001048000d824604089040690b04c48001030481c5030b400c041c030190102e0b01f60400415044440080101400c0c2c0000c0c0e108a862002003081d81086040440f00000050400f001401103034007000000c00082903015000301c00a100c0d069440704011240344611b40f2448006001e90a129000380340083c611240024404080c00510038590009010680603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 706612320 1250 706611070 706611079
    0x80708042103380a0f05040c0e040c09030c17060f150d05010504060609090b150f0d0b01141005040e060112050f0a15050a030204090206160b0403080c0a0e 68
    0x200d084004082101d4210741000e1030000c03c503105244062040c0044440658071181c19810008004100d0308501c1a0065544203810070070041c00e158112186001032418805805150b60000c2015200352428040000c0c5a40005000308400405154050030a07400060040c600e0891003590f00c1401030f241e601d41102d02e80000f11942c0c1da00e4a034040441e4084e21402143e07205142180c060b100030f4400b102c80c2ca0601e58041140f074400d00c10b21480d0740d040f00f810700440c1c58492002d14018200004542c0108000e900d11a0380d0711400006c0c44894070403a10905558580034400f15001070023501c0c140308002c420003440003164010705aa003a1181c2e98603041c0c01d51103903c0181c40e4840c6051440111501f00800c000f13080e812010010b1083c445503509200007140c02c5034140a801c00b03800f03982d0707100c3c107500c4061025060a40c0311140ba40e03c0501000e00e450302189106007c011801c6048642081007030410041503440704040c1c1e000318800c1816401e040a945002c3e04140321302c090030780203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 706613570 1250 706612320 706612373
    0x1e0c070b0a150e010e16091e0512100e0102160228150e0d02153001060f02030a0e22050907090c14030601050c07030c080d08070804 58
    0xc1c2065406101e140800c03844034890165200740712401c550003403003012013500c0c2034400203620b585005910707403c2580ca41d503000411401c040391049400c0c2c500c0f003e59036107402040d01150b603031500485c0011044458008240c0d880c84200c881040d00c2881949034007070b0340180201d45c07008054501c50b10784194122121003640380404900107014110b1410007407843c4407294002030380c5c802000130380411072061380c507030b042030501034140481003a00010007500500f00d03500c4001c9a242c600003600c0300e141c00c0d880e01606401103500d0414442c089007840c0800589010041042d0760704103842c0440600240043c508005034900040c0004188541e440c1c00f490494a0b20074200060109031000f0031118502040305042c075000956440105000d0003400526061403048011f000300c800403245c030040f4400c6440c40d41c880c001111240c01c0318080151070322480201000050543d011040941001c10040191805454005010302009040c0c0c4e028051b64806100c041218094000c0c071034076202214009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 706614820 1250 706613570 706613581
    0x180b06060f0c06100f0b030708010b09030106030813050a0509010b04031707060c1e02030403050309151204030f080c0f07020906060d230f0906070e041b081e0c070b 72
    0x8a6200389203454a01d809030b030b0700700003600c07660800210940c1d40c5c24130200b4101c0d4980740d11074802c1c0b009031032038000310340140010841c21600c1801070040700800f4001003249a902ea0320a811070304040345c201001d07215a981441181054044038006200450f4182440c0d4540711001000340311f039001c0a0600da20101030760070f500e44901d044030103e5a2010302044030049902d00286090a80101010102140c20b100103290740700205840c160b98000340907510300307503e00741000410a101c1d080040c5c940c109108086003074500c0700401d0310590080c0c44000c4055a23201d00242400001404d00c405c140061103034410704200d5006032005950306072184611600e40c400001c406018640b000c1c850203090001c1540035003c034980c001641c449610382808243c48400101400420845400da0281c0c48600000c0102c0c1c4a00c0d110320768101c02078000a110502c06d6400e850301c50407640c10801281c248800d1100c042503000c00c070100109018035045035418005c030038905070b1040703000c05444159000702090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 706616070 1250 706614820 706614847
    0x90712020d140a05040c08030913150503061602120403110d02040b040204180f1b050304210f0f0c0206041a090d06050f07030b0f060a110601030312180b0606 69
    0x85284040310440e90b200d14020b440380d03000e00011601241c450383c4140000400c0080001510249072000341500c440e1100c900550f0014a15810038680540400c035000500d030b01c2c188900b44c0922110000c0c00200d010410001e0719040201e54040c2c0d03040c404101c100003103001c090007400c0243e41217400750039110340c900001e406003141407a4654820b200003000908801c600c3c43d00071024400240c00d1040910010000044031426036140100031406802400c13424420802113034418400c048950205080714a0443d4003504040d216011030342d0000583c100039000408480320b00e54a140401e80c54405502107071641c000c91203000d030084040403188c0524150311003030721846007005c0d1504042030540e0034050094171040d550504440000070100302c44c3c620900421030040d030060302c0030160700c10002c203020341075200c02c92180401403402c0c02c030b043c005414004107000318000d544d41001901203601703040403582070101e18401e1415a2212000140181c0c090681c40781040780c400c5e480701842000d62 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 706617320 1250 706616070 706616081
    0x8150603010e0d02060a0c030501050a050f0613060306061b050c1219080315030303010b0306061305030609160b18040c030e030a080a05060d030e04090302070b040f14090712020d 78
    0xc550500035800f03091a5140d00156003407150750241c600b4000001c0030441902113510030b0140c036400c484411014440303414041c0c0941e0160201130b00c41850704400c43c4a541c1a40b00303d40041002945408007040f44075072004162a0810740032004030b4002d1026998280ea4011100c00319004000241114a100900307128541c0b4000901f08481c21418007490034143c1640301320380c80703490300c2000004030030300703080001c00d580c140e07001040c1c0c181c1ba40e280c600030001c441c0c020003110416182042300105141d1418440c2c18002d55028000340051880fa014455690a29400980408a0522040d8500c8101e100e080b40142016540020030300b5502c44110040c000804000449100006000700f0180d4001c042911584103008104400c0d01e0701c008000003a0140107018000940c4c0201036481da00d020392018519520030b004a40b400341d0395451743c42451b0455031002c00300c274441c8802003240c40c3c0c0035290340010309801c81c0c14981c18607102d42c0203401c1070300d1300d4140002540d0110742c0800c0d00d5040c2e0702c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 706618570 1250 706617320 706617341
    0x50a0203091e211b011205040206070609030f0314100303181512230109020310080f010c020f0606010507240518010b0307030818030a080a0521010815060301 69
    0xc0c004070110b041240d0075143e00c640104605204180700c0748011180c103070310940880c00580d6114a01e07290314000901903c00900140c1c1d00013020016440040d00310700ca01801c1c035201e6200c480d1a0818000043e04948903a6603903544610b1950810002071000f943da801582d030300d420100300302c03010040d80140400b20394001c010323800155000a154943c225603050003032003002000b0b201151782d403940d40c1c07408403002d404815006000c4c0300501003980d981c2c0141d0b50042144078080000c9580b4008645404115903203014a40d540340078503202c030f0750305104841c10b800e070140c018592400c0440000b06203208440e0302811641c000d04400240084480465043c6040494107200500f40b01c400240c0e607a048114681081d0300c1c00185c21480e040110790783c001c0f280c11441490600c00a00f850125080c40c0e040c0643e81400717085036003800114844003800036400300b65a05915410001ea200c81083c034031030301c82c00592840d100100103031a0006401c0003514100d04c083e0400740c4514012070b0160030300780c14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 706619820 1250 706618570 706618579
    0xf111f0c0f15091704060e040207030201020d060e0106030f0216240509070501090819080f0904060314120f25021c06061202010c0602090102070b030421050a0203091e 73
    0x1806069610990020f14a40b03010309140070000140d8041c2c083d5a129038424080803819411601e20f15103401d80c0039041d1a406030002500d4040e400300300c0011140540c21610b034600b0000c0060000c544d15104070820b54a10300350440c6000d8803223035101458003040d000100010700d0882c04c5c44d02588003003041319400c00703103010a11850510000158417401d05001d51400900c0340c010000e004000020700c2201c105000140f6600b0810548031002964003802c920140030904000030b0081d42c40e0b52007890001c6000d4810307812880728a4810b2400c0c040181d21990041102340980e8103948442001c4454184040003141c1381d40b000351b144e00b905010b20290280d031090410100b03005010200b1002d400007482440100400398580703501d400d84e181c0078600680082c00c8604948000307081a80107092101050045501003507940b01c858030756034012901190b40c0014070252116246441034280e00000c050300b0007038180074240d1402036a9010b43c1c0401445114040c1502400d50494107800852110290 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 706621070 1250 706619820 706619843
    0x609010c120903050d08131104022101090b010302250f0812060901150509120f010204060f09050102010203010605030a020a0905120706020708061e1906030f111f0c0f 73
    0x240241c24080644410313140c9004110150b080d16118500300c0b4402c0003000c020003d1480e00d9203895440c68040340b01c8075081a8200001201d00803107001c800413194806402d65050340c10070018805132400001e600e414540144081502030034100728100d070401e03d800c01c0d20ba505c5641e0810140c0130091403005082071100044440141c1d00c400d148070320600741514039582a9a80c0d01195010602d1001d40c800003400a2002041d80d1820500004600c4c1c0481c0803038440398061312109003280e101d64896030214203807040408810350416602c3c0000c00c0d00740002c504540c91308802400f94440103152291007540041c046a500703000c0c0101e48050280074100d02164407144241550302c07845401094050302c990354000a41d5a000900c0354031038504d00e50700d48000c0780e0103402075000100c05031802100d000c2c1a44022851401e9106100080d801341e9101c100b45440390421503d910340e8003015900680604060b4000340c1c01d000d1002d071034a6070074503000c3c04041036410084009002140010041603180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 706622320 1250 706621070 706621103
    0xe03030610020c510a110d0903030801300609051b0f04051e0402031f06060f03290f090a060515070302070515070206030403120b010302180609010c 65
    0x21800c0d0404155005244e00ca141c030756011090b0384c101c05900b000310075466140700c1d60b4039500c0100a00715170080c604100303000d40902c10344d60b8207003981401003d00240c1300400800a0641c410301090042c611032000c5c0b05540c420b0184000014884600000b2460f2116003142c01c01050f40d000c054000c0d001000e95140c1d406d200018246c000703003400e8451003024102140481c514182c0300d1240140802201e01c4000c0320300080d510a40e1100410070b0f641406440440b000f0b41c00244824010034184010000d01c25040840241460040e18042406c00d46402d4042e81aa0b1201c84828405100c444402c2c2c061491040000da003440461000350304402484180181d0f01c1950b04014241c4078200c405403004000e4000481140c0074031940600164006c1c0317801c00c00e41c20f0951405060702024600145400540d80218104e5030080c1d0301200000d0a40c40030718594003070792042c24111082460203524104565000000b00d4800049951040c00e00080c54901c0760302410360b18044551000440c00e500010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 706623570 1250 706622320 706622359
    0xb1e191511010b030c010206062701030b160c02061b0102041806090b010302210403051b030304050705031915020712050a02101b0c02190f0602100e03030610020c 71
    0x2120141c07480350309081d01c0c50034510b0046004000e604041c0e0092215580ba003040008035840c48d000030001084e03211041d01880e88140015018502604d0790700c250342070140031100c0160544007542d040020101d00702d00107941d9007046980060001000c000640c1c14000d81e240284241c0e03202c01ca0b10090207032080000042900320301e0880c0d0000c0800c11038003e040005406a210b00c500a456540e00104d1800015054102440e0864001e2900703a083c8440c18102d0f800910329489411095032000c0208410040f040000001800342130b00070f800008200171a10041d6100e60000604030302d03a82044950210859042c0c07448141c0041424010081c8464040e00310380c071070070401d401401005107184000716140100c8400e03060a0300350b100c0c004032101c0c2c200c07118200404100da1000304c003000e1000725200707050320b000504803403401c403002d00d031030400064600100c1c8005071448601301003d00301940360200c256136006109072004e00d90300352190f104074100703407814141c3d50f44055808002c0d1030b00c844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 706624820 1250 706623570 706623587
    0x30c1009030623010b0a020123150a030816060e070b070c0b0310090902040f0603051c1e08040335060f090a020a1205090609010b1e1915 60
    0x40e44104010800c440f404040a81e0824212010a903110700401440100000802000304241300014049160400b1703c070714038203401c2910103c001000280b003030004d4031034031800812400f00c9110001c03d11303541e118202405001020750b420450340c921182400195000f2540203200300c01519445074403018154003030303045007000344c469825020010640d0380060b01201c0c000c03c11700900a0006250009182c040c0c90382180c102d0308940c4540030a003072082a40159809103220ba4060120545c401c0d19540900800d81c48003c02c06c807070781109025194140d41c454807003000918111000d41c1d103034281950604005102a103c60602c00d2505004140c04003403001074101c5450450456207807030303082002d203030300070f640803603124242d14086105002030f82e000b00440d401c5030030040450a00d00350040c0403101d04070340e1042240c212104000c91180c0138494400541c1d4100c40b07020822524940030081c800c1e621031807034060f91640d4820402155134040e07060040001d42c2d002c82a01e401c2d140014030501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 706626070 1250 706624820 706624823
    0xb07060c020f060f060907050f13080609070501120203090c1302030726070f030b13090219030f08031b0d090308070f050a05160507080604110a060815030c100903 71
    0x5501c4000790700e42020903c6801044a00f03031060303003a100d01c820000100805407205c81070160400200c01600f4036070016050f04401001d800380118505076902e0b04004008244403e990807080d001d1003241c0e0041d251411036116418016100e03910100c0f403a1504000750550b07980001c2c10070104001a05030703002907218402d66501c05485001040074521522201402260b025000500150015105503030388040d011140c80e001c00c0e405185404100d00b4450a100c4110701b40d00c0310203030025410084001c1f094601c0d5848081d160f0380c6140c40e0b510b042c003040d42c0b0003401d5410001c04900042d8106200c1c6600d0003013062080d94510542e0006001008000002c0700071407170b50f800042e0103c1c012840441d080000713403240c918002c0d0009044a0a500001402151607081d24020010500801a040140644a008000c40c0c10142045126881d41c5c1401c54814200300400744465036009035000d4008003043d560180a000d4100000c1c20b2170805142ca5410090701d1098400866010b0700d601e0459 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 706627320 1250 706626070 706626073
    0x1104090213031403030f0a15030219080715021f0b090109021207030504020a05010e1201020307051c0b010203090d0f0506160e030604231606030f140603061f0b07060c02 74
    0x7045043c562030722408100c986400c07116603034000411540c00c0e50400070f4118540c00001e40c166880e80d00007004100b42801c0070880d82100c07902840082001c016031805003858184041801d440a20020f545d00610b00d942584207418003454405400c0b15000f1203046040201040368035038542e0032000c0250000704101c28840000307804110201d00901c15540900d80240808580505003c0196620265504203d40124800c0e1400d01100300c20310246002e412b0680c2c4495441814000c10550750305880465000240343c041c00920340d0380c00108480400c00d090724404205891420001c4100084203400b4043d4025041048805242840914181061504d60111480c0381605050381d8000888000b41521070004039039118902d812284540360710070100700c9a8406803403401030a030340c51690041e001310380c590b80301c21a4400603006980d0744511010003a040d91412100081e83c500300589010200000c01d541e00c02c44004401026018010042419a81d500030780342550061040b0400100103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 706628570 1250 706627320 706627343
    0x2090f04020703090b0c032110050a0e0412030608010e010c02100e0c040b12160312030908191e0203210105010c14011b02060a06080d12110409021303 66
    0x80c9058400c0c1ca000c0c0340c06a4a0b0b04145007132030130981d10350340701001d0321109120600c02001500e0380a00003000c003545281e4481441d05013207034107510413015900883c4c0300b568540014885007115a08241d40150064203200092000e07000641c0101003540001501d942020310311060500e0540084d0454540d035402c03125148003140d849022103080b841c003001c890304a508580d06901d00b54211007046100142041c0d04011410074807840c01000300c0001ca4400c2c1c20840800600600f01d030f4040261000742024405441e16980300741c02d91180704503801d10300000c4080c05056600c10b460b071090480d01d050381c000825441340406035880d0828044040d0214810703c40710181c8100f0000380d070480d18103071111101c41281d40c0d00c04401000024445441c1e65888914200700089401d007001e250710302c0e40203041c049c2071002d0f1560690380c098100c40b036642c0c0000c50000b0019480445015800c0040000040d001e000000c4500d5a03c516404040340c14000300710010080c2c040c04021003241c0c411440b5a00c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 706629820 1250 706628570 706628599
    0x40801021b010c050708130e040c03050d080f010e090705091806090d02070e070e0d03031b08010317280504080f060105060f0c0a02030129220c09090f0209 68
    0x90fa0958410400000c0080c0311100c001481c410203801c144059110044d0704646504600c0c8a1a1b030403601aaa101c401e001c0030001c3c040280403c8220f243e00b4a081c40f102e10b00002203582002061007180007541c0007500042d07401300306104135000303000010991100c40c00c08003030f64814005101c0194050380100310118100c0b0b40c0c00524a00d6040f142e40107424641c1c40c0504840001100502d002c0c02d105400035030b008150341d101804400c0d41d1190b1400a0a8141c00000040405121006406000083c001800841c4201746e8950320440b0380c40b000340c1c1e5560148803086840c9007203455082d1403041c0642c407400e60354011018009880885003240e0803c5400307040ca5984060a00c5040d810090030800840640005801000c1031980c8004455410102e030707021908403180003203400456804558155800078140c0401c0c114000110303082e052001c882040c0c0c0913914030f25154084603d640e000c0d650495405038885400411b00d1a40c00c0187c00000011303440a90b00988103188260155203103000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 706631070 1250 706629820 706629823
    0xd08010b030c1b1914122d13030f061112061c0501140f0903033306130f050a0f140f120d08100605070f0809030d0c0c0911070f0c0506040801021b 64
    0x4401c01240002144070310700100750741c0319204000b040c03401f100c003080020280c400002c4501500551082e842801520601d0500c00120f6503030f00780c0001020810030040c0d14840f440d011035500884110f80c1110801542421107040c01da807032038000c0555080400300c1088040d41040b0a100d00d40e035611100d8561b032008074203520b920080340c60140e01f2400050483c1c00d0190000e01404001204002e482c6c002110703400030740c96821283d403071f0800d46444030090080ca45894078000c01403100f0344110a900d400d0034604403142449005164026026420303c05040c0c0d0ba01a40301050745020f010300c40070083c0c0c1c184480c3c8a10781c0358024030100300c01070041103400314011121004c552075550f805080400541d1102100c60030100d00f5641d010050104009668040c846050300d0845a260f104181e007151400003089022548056859840d207103490440400e0401100c041552110002d103001c2d84034a003412441482c3d03044260400004035001c11000b4055000745402d0445150340e0480080039a502ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 706632320 1250 706631070 706631077
    0x417010908030a051335210a091a04050c0d021e0111070f3003120e06010e09210a03020d1d0d08010b030c1b191412 51
    0x103000207410000101c1800d0650300480d046624000c4100b8400c00b44d8a400e600a1440c161803408425070810400541003041c120751032000035986100c3c100041a00c0c0225582d03840741081a1105034200006c20745038590f032050407155888500e5554600800019a1441c14121422100c500c28000c10881c140750a4000a400e5a80100001401c800074580d03044805001320005043c003e601020b600050000d0007a14090f01b4016079519007580b52401000641da02034000c1884c60340d80e01c0c2d2035008031030b16010360450150541800b81d10130f40d40f00d00040050a0b02800c14520f4040c08001144c2c41d4801244a405a9500c8003110415504507151007003140e5a024981d03605003040261130300b02c42c003d030040d000c07080c800800041c41401c1c51624030440c84154900312100c0c0c01a20b5480c081c0e0760020a42409000c8020040c2c1c00c0d440c0200d4000024402d812210846c103e09415807003000000b0452224010398040c4099203000061031300c040c14440c03200d04417680d03004a00c84200322403554400c0c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 706633570 1250 706632320 706632323
    0x300a06140616060e010b1504150806011403130201122906160c0609080f0d051c09110a05010e0d02090901091b030506060f01120b01022104170109 64
    0xc620084034800400000e588540c007414207003034030801d066000c150248074807421628690700100c0c0050400c07003000f036400e040d000c0c400c1d01403805104c28403110250441d012031207a110308000c2c0640d2552401603420b41107209100121403400010800c22028500d0b14a980510070b8a941c005042c003016490243e88040140950481c405241d502041182c1902e0a01105024011502e021150714111040040030300040d500540008000c07c0060b500c1205000100760040145c220025002d601c00c1d100c1c50035000c1d0a0410501080d8040c1100918003444a02d00d0310b0f080402441c011403a011400f10000b4414502ca4181c03000c0004207540145800320560400509803400b40001d40e0030080e068802030408202596500c500c140040d005035284004061a107400c07810052461808620f040c034010151030007a21405e43d01c1d00c540e600001080840380302d6000c08100e00c07410710b004034a01007424101c224509207412407242c801b12000000c0c0305940d102c1d00a05880b9984c0070555080c0c4080000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 706634820 1250 706633570 706633589
    0x2061b030708070e06270406030b0408280309060f0c0509090c1207020307110a06120f270b0a06030827030d050406020d1106070f0302300a06 62
    0x341c140c034071641042d0383c80703070590038014000305401001c03443c0c0341c105244450510390815400090203004c0382201d0034084044506000c038604582e41c2d420b28180250008147c080040b50f21086540d6202001c4100788003940c07964002c010445006002d001c803804181c942c2d600c0d084003640c9844103400b946145d800d5a0304c4680c0343c8101d00c4140811a20000c05018011506100c00c0000c003d120400354024180c941c000c54032000141000f501c112655544144204158070040240c0390b040079481ca1121030440000a60390402c01c40c000182c485039107400700c655044020310901c110a0481180b40034040d0841082c03c1d070369800c40000b201c2040c0400350000e5810b000f901d088110a0f00c02c01290100d117030340b03130b43c0c290701c81c001092030100107248034030101c0c0001c2824805030768104184c61040846242001c501ca0700d01c000e9640b585009440c04042141000354000f5850090b01100c08600a502c07869004d00c511040590300603c0c941200d0f411051140041800c800a5014610517603103180d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 706636070 1250 706634820 706634827
    0xc0f0c14190b0d06050d300c030c032007081e0a0f05070e0403080f06010f0e01051e0d09030912050330090a050c0103020c060f040c0e041202061b 64
    0x40c41800150041c0780f118032801c2e152080420716443d0070054011350703882500321600b121044500003014032103222007440c1160101450212850740002c00c2c803515509410103990f449424107084505808028020406009540308400e02120001d080d00c2158104c03029600f1280000900c400d256440107421482940300e2041980812481503104100da4400c1d421289100c0c0c0d1140c5005450070100c402b60b004c24000b400b0066155418000c01d0b62012003480c092611103c48a0050070407600311803102e04020340440e1042c0c03040c12122040700c86840340011181c1752015601410050001c44004034009100d1240c00550144a250b00074100c43c0e10030055418050502703038084616406802a421410301b1070841044002e003412828058140d070805400c0c512031605140380f900c46251001d9042500c1000500080c200115105811188003401524541c640d8144800f4500003a0807105001d0079100602040004441c12441c8015094013907481c0e950361070800722412a22800c60304072180042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 706637320 1250 706636070 706636079
    0xc1b0b09070305100509010b06091c0813080a060c080906010308030c130602012a09140d050105191515032f13050607050c060a0c0f0c1419 61
    0x216425520400400c21122590360702d0300d4803841c2c0001c82000151050b41d0710709000b035124081c05041180c0d00151011898500c115000c646d480340200d0320701220070701640049040040711400c82d0009001691103080d0781c0c0d1120891038481c2038040007240c00f42d2801110409880c01043c072548150030501c081d2003207038a10303102e043c083e62004195404602c410443e815001203d021640d0140000c0c3d4000151081c02c50784054284529a0b541c08080c8880c0003a120001c0d84420090b095070140940000d250345801e010410b07025004600070b2140d404c1204001c0b80c0790038454421780782860500300b4403c007800808100100c200030b010300200c40d00c0092480080c00d010b504201c003106009094000d590f0740d86038240e00f02007510120701008490014100010201c0c0c3c0740398501601048841c41d20b05005903075259640c0c14042d030300394001c03e40072800c100700e14028400501c0c15070304101c0401c01c024a40c5003500092686000e5403e110042640b500401d04113440a404c2d021121005081c0c0309040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 706638570 1250 706637320 706637333
    0x916090b0f01110703020a0b0c0d022a03010e10020316050f03161e030218040203011d0709091401151110050c130902120705070b011e051809010c1b 65
    0x11010343c1e0f030321407042d82000801600c0c2e410808004106100e40d6036110075244545034200a40c00d100d460465001851040c0c40090743c899100c034192600c502d80030301645000100c1d015005405494409004400400c00020442e4009500c601e0400e00710745030380300301c40c002512980034112800a100906100040c03a00081002c0c4444401d5281407000c0c80301200a020881e66980048400010b42c000c00c60b0141f03141554000d03007900364103ea0644c11981423108040ca2000301980d10b145103584640440c9295001d05008005003200b14001d010010711140801c6403075800380b05403400f65a14200b50400584039014881c8044a40b80180038880844d080354409498007420410181400700006046c581001028600a0900c8040543c482d0050340d40c2106641d0010f0581040c050300300081800204032098480c1542c0400031180c61007003040c5040342c0540044d4005682082c440c9420f424410201d034110303403143d2055002403090500400341156003504500d2034400d10303414500010f001800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 706639820 1250 706638570 706638587
    0xa0b04110f060307170a060608040807061d0706140708270310060524030106050f0912100b0f030d0e03010219080f06010f1209050a0b0916090b0f01 65
    0x1001000310124101c84030014825074070948007203012403c00280b100164100500140d030240c41500d08014140c509103001d010454000d10040840e0000503150003081043d600000c0a03110003421488280c003000002c035030b108624046c410106030402c2140032159580f4040b12110b90b4004d4840c2c1c10070484010300070300c04801c14400c580e03600480306000e510303480401c180021500a0750010504500c2c2105010b1101d02e2848101504130501e00f89001c03920303142003164115107045c41c1c4035540300341594032005070740110381d61140d201c2d01002c0b24800f03989000a40c170581810400c0d041045050305030420100100207007056405400000b69410403038002d0840001294000d0005894081011101100a1244c044420100d100d0b402444540300708a080309030306c044203081000b0143d4076200080c0440001d01400c1c40100d0703c45103961304000d002d01003030520340d600a560482c40d06000c1c0d5901c0d22549072005804040031081c400181400007402544408280a07000300300e841c402c080115290303003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 706641070 1250 706639820 706639853
    0x1a100f030f03030b04051e0105030a0206071506030b0403080a0b0108060310021303060f230c041a07050610080c0103140103111f0807030507050304050c01050d111606060501020a0b04 80
    0x5035200941380d4241c0319400344501ca030001d00c0c0d0b685512010007007660102c0c801a000300b03010340c0c400030030000162256400c64039240c0c2c000103259011090480c0e1b44010304015000213100e401e00cbe0003070004158002559a0003002c1c009418408070032024011100f0407400ca89141d45680007000d040e001505039402441184d0020003130b900d1003038032078864409490742d4107450400303160b0744c0000c50000c0d04c03031700a0130740c8035041c80812541a0803e10341d6042c135401107006020010b440031024552140d24075046400d800c0e8010207581040c5098a1030703804d00165881403010074090700e11210b013258400c0c85524040b8000546100642e400d5480d11260036207801c0c00d03207422100302d082c41c00d00400f0a081401c0c070041640c5d00ca80581c5410403004003900e10180c00d800901c10b090050200007007022a002f03010400a207032007502c40c104200d020001d404010351045030010001500d0030740401d07034024200c0060044070180544ea648400481c2d9036481010042c0983e0050380104000540390450802c1c800d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 706642320 1250 706641070 706641077
    0x170f04030c021e120309150715050a090f03020708010c02070b030c0a030b120d02011401030515071b0308090d0809030301170a061a090c0412080309191a100f030f03 72
    0x603558404505001c804d000c5044480e4400f0980142e82d1804180361a810b808034030125051440503507403451441e10624290000503120000207002681c10340c410340659801140407801e2013664200079444002034004c202d000c2d403c2a65001815000144000484008500242c619a20170041440c43e402c807280701c004140d00c81902c407125907039492110b403151000d54080c0600090400019003110040d21b905e8103241c0403100100f01040001c101080c038200f5030b118003203075552040c030100c0b20380b800706e21050740c03076040115910245503000032506c0c030400340f03141100c89040c01a001516070b0102180e0703812207980100010300c031800014080ca070400040e0f50403140c0b004459610401521680f041c0d0607146054094101210f00e4801d02c415088140030f1a560304d01070401e003d920a00980540207409178500001192540744104014400e03000034503003190a201d840d1400700d400c421400b0b6080070f100f1040000c5180101090100300c00c80e041d041459811500d15030710907a12008413002038003407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 706643570 1250 706642320 706642369
    0x4051e031c02030c07060f0929040f03050105090a0803070c0f0c0b22080c010302070c0306061202130209011d04090606170d0504050904060b03030408010606170f04030c02 75
    0x480400740c450300d50070038540141da1038110a0400c00c2c40c1119039805403080041c000c02d00038095821080035010b40c0c0b5100382800d42c041681503c000025014401c40a0501c00007500284288242c2d41c0d09090301d1240000340a6602c1c0c941515644110294015150140400204110034000c8845007000d038030415821040030f0681c1c0b9540311f10714039540800562071002800003450b20145840082213030210210000c0c041c01d0987c9030740d85004425507281410f50000b084800d00c01c00200c940001c55000500340030550b1100031034424a050440200c2c011a42101115419000b40c02602c2e807025042c1c0d00d40301c224140c0301c0e80c00c212801c01c003c4035400c150390700d001c0b0002c20618051240581014109a003100450130302c507610b40011041d44408000b02071100707021a0f6541e081550f04035401c0100411200400e00002e0b007144030381d5005200302c0d031900313100262280d005800c0c2c1c4a0f610014042980d5039a8030880d00c940c1700001c460080010301390f00582c10062500024100c0220810400c0009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 706644820 1250 706643570 706643593
    0x6210a0516081615020106052806090e070f03020c01050f040308070c0c12020102010b030a0c0f0f051c0303240503120a0507030f02100c030f050a0204051e03 69
    0x2040424042920103030450407a5100c5020004070394001446140020007954008801d1032540000900070001c03142e01000070880c096200350081409010700409080c56000480010034100c001030680b50700d0a29480e4000131780f0744c010304000003128544c0707000b03540599031100103c0e03240221034141d2050507402d0040c004901030034899144140100f41440056007003038140a440940c00600080801203290071410018402c0b0380c0e800c044030716407402400800d000344010b0307015120500c0401c2e01881402004003c0c80703081a580d1080b110343c030040c1c1b481545c59024486031b11003180a80c0d80c1001251480701281400d80d400503564600070b10700002d125940050010070310943e034181c10316030f0302c0300d070418069840c00380026105598425080b510700f409125018040d400f401c00054148490645c0041e99180203000c40b4079501d030411000c00c210108210054000c0540840813101103142c140003480300c2c0d00034403c4030107654005025114200c1d5403c4102d1680c507a00042e00d40601032914901e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 706646070 1250 706644820 706644823
    0x15261308030406090b060f060409050903071a0a0c090e060f0d080d02090103110a0207051011070b0c0c0102010b01052a0105131b0e0a050702010b030717240621 70
    0x10300441c0710f04804035040c04030741080160788030003400c3c4501c00d8003401581341207560b034801280d049455104005c0307180c0c2e03034006000c1e00350301174604050408850b4000c1174144100b907202c00f921420440c0401c00c01c650300800129011061401900d079100209804100249050b42440c100c9000c002d04043d0041c0c1503545161143c1c0110000100c0075802050303402041d078050050494030700c2d014100505200001e040290394980394410380b4000c4160310b401c0301c00c0074851500d0b1804030000d44211001c590f51105132550a910034103110350a40554581c4018961041c02001080e020582d101030400c20b1004501601070507011080450324107035260003a0303040083c01a1403180300d1800342030143c0005400c10716080c80f0001d22428099941d01c100380005414007058030b0304810110300020315550f0300c080c260300400754210740e681e1500c54801d000540c100f905000990003242c4806650034517500700c08917002200242961000c10107900c0004500e400d101c0500d404181c003400041c0d070b180c604000c80c1e9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 706647320 1250 706646070 706646077
    0x13020307181811010201060b1602010e03100e06180a0c051e040603052820010507020d0f0302120f04050f240d0c05030c1b0c060f030115261308 63
    0x4071000c030070124a1043d550707020f2107841c00401c591415241707040b5510a0f603140500101d500241402080c4403801429101080781c14442d04401c5d02c20054090700c0501641d81e401c0403603100c4640c207240040340e0b0f520100440d100c50480d0344070000554040c00e18081210043c01100340b9198100d440392056065910360203180015400740300034086014030f0700030100b52000e41e45d54008200f040220303001c00254000c580101d41c0028440c5c5002e03104c1c21100120f4491280c000c0c041c1d4003e03689120705c420322468804c040301e400d100e40c08a481c5038085c4030152146000c0e260180f035405805001c200502e0500e0309199241d1340c030040030f03200310614414444040311034982e900d840105001c40d440016191038411207020950760f091550452902c4506600103101d00034180301d9010000f03518031f00f426000c1200c4071000e8402400280c40d40340d003070b90000c0176070400d21072140350b0002d200b01d0a0050340901c0a8084d4000304440b510008082496000b0b20760b40081c000c00c00d1400b03c41c25030f0001c501d10034040d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 706648570 1250 706647320 706647323
    0x60e10032a05130603020c0d0c0314070503030a050a1814010f0c080a0c02011802040e01061a070203010605041b05181c1b052112070f020306130203071818 68
    0x2c0a4441c07215600c22485030301d854029000340361041004c80700c02c0700001a0841c607460360781b500b4050301c0800e181c100e4500040d0303203011008060205507003040010210103148206044001002240d40740000c080950390814049110340302e0b130445c04000308044440f01c1041800050010489071044030100044844041a0900040285080c4280700c2c0c1203024004000c070785d501c000c0c440d001c2500da1600007001c60501c02445a0b6407254100894102074004070010100245520001d10800c2c15104040c0d110b000c08038402e5103001d602190600e441d1003044054200d50a26192884802100f07442a5200700d42230311840804112002c0a0740e5542d1091407035140d01a04440c030582d079840c1c18030300369400202c0d10135210a0350b0001d106940f10061300f40c107158851645524032101c00f46015082c54801c502e041406c3c0e0b00059076105002c0211040d040191095040f030706590707a2505500501c03041c030352000358181c1146404001e554145481c00c20020018200081c210b05840190200c41202000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 706649820 1250 706648570 706648577
    0xe180309181006021f1e15051305100e060a03050a0c0302040c1b02060d020412111503010608150f031c020c0f0f310e07060e10032a 58
    0xb00300c2101c6000d26114018140ca00041144001d500061244014040c004080d0566a64014a015580f0f000c0301d1070f2407845113808014030703291820040c03000003041c01054014182c0700c10588905c8540e219441c8655284141582c00c0b5040016409403200003806641e806001d83c000400810342c14090013140d244a4214064060f1541c8103010642e004031000800380214803d024a84108501c541c8070015812214983d44410482c0342e68000c2c080ea4000d1100ea6000e22558410009110b0890743d200c001251405558645044005070340d101c2405003000181143c0080341c110b600d2048400320388040149400d84155140010034503010920380d0080a00c0c0c130318100121219010f1141c480d08001c1038038601c0300004000301140c921021031000c85c0c02500c0540c002442c00b108400581203248000f002c1240c2c2c6940b20329285c019144030f101c01805401a02400507109028020082188002070150b03001000d80310003e070000c1c80c1e89031442d914091614010003209800507490603120b0b441c0c0e01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 706651070 1250 706649820 706649869
    0xf12010e13050c0d0303060f0608090705030309100806060d09111002070501140705031207090303090504140f071101020d090c050607230a020310020a12060e180309 72
    0x484111224006440702140000150400d40803a10102d1401804001940c40c00c0c00c10500c2d00d8102e008020a5110548803070201c000418070690203800c181c001c01c030030021180c48a8550382050f4aa1050300c1c0c1c0d03d5070103130380c07445034180880c042c401c0d60781e00042c020400e034204018000d40f101640d6031174504540914064078207110a1420300705181010b680340c4014043c0d42d003440006042d410100d49810380850011a00c1c2c010414100100c519400280c0d0350090700d804e203020050200e01883c0002c03000b06001f02c1e00032905061504c41c02320440c2c030222003402c150b00d805201c94492032020342a11b0030007250741004510417030240020a42c80b0054200010617140c2c41c02c141003001c0c00d681005202e203008110280220302c01000508804207004280c0c040f010540c141030b80342c0060319800942500801c41c40d000192003030741c090600002c1e5621143d501d610317046500012661a80661903202e01040003042c5851014500900c0c421030340411285804400340005880e007003c401d81c190083c2d20342 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 706652320 1250 706651070 706651079
    0xe150904081228050402151303050d0807020d080f040212160e18031204062f04090b061c1a120f01240306090206040b0307020115080d0c15020f1201 65
    0x165881c849181c0c07030f103008000d9800c03d940081c40b0444c00c158910120b58000c641341c1e00004612441900955211084540103500e80101a04005045688501602911a400c07004030b00410300ca51094000c2520303000b0b156036035820440000d4403082d50350b0a5214200d49410403d500000340320107002800030341a81031a01210780ca02c00343c5110300701ca5454100780040301c5401c42c02034811360410741c80f400110f92414500100503903400911006c1e4030221040d8200240e8001480060080e10100c1d0740600c03001c0030751003d00487e07100b445d40320030075184604411002101c080d8000584104003510b141c1400f0384901c0003544184004207205030907008501021703401d2101744281618520407207880800c001c1241400b8961900c43d11018103881c0c1c8441015003107549142c1124090300e03041005e42c0d102c3c10080002402818240144d104803a10f00700301003020100000e805402ca101030782ca4904420f0359030703240faa03445004200036060503000d0040c2d0980c42c004030302504940c900d20640c4102517262 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 706653570 1250 706652320 706652371
    0x7081b07090e070308030c220b07051606050915040b040303020114060d02011b170705030d060e011211030f03040b0a030f02180d0302100f09020a0e1509040812 70
    0x600c42c8051a90740f1080f410800a6402001e0329840754000c851503803580c4481d81641010f1245c00175501550a00c50f0001c00d01a480c400a04403d500810481e1203458402110f80740f082d01034000c00300460340900058404e454210010f01c201401c40102ca814035a0b6110130904540168108a0240c0d4444003d154028444513000380e111808441080c0d450400d41c0004e0812100d03903030000c0c1c04e401030b00c85010030720003e00b42102c0855500c088042c0d032212241070440c0c580d000302c0681d500c014201500000c0340303500c0003a82c3d41669544490100035900b5079460b42086036200d00265018003039229011401441400603100130031013107082c0340e510030880100030200e1300d02e4001c050709103205016003071101c001c0340e40b004013581e800d40e441c0e940d000450030103038a803c50050104410324101560b200c1c3c03044113038018140c0180300780d0310b02c003626803181110568244110b078000c44900540c2015a031900d460400035401c10701036401c281c80c210f2004245507104004a40d40f49241c00c00c45036400c1d581d442c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 706654676 1106 706653570 706653581
    0x1060f11032a06130302030906090d021c150e0a0f11090c0d06051e010c031b0804180219051b03041205010b030a0b060607081b0709 58
    0x1500400c05004108070300300036841c2d0150202044c40024090800b01210742d043d0040c40c1000603032402e01c050b580150046079400184c803d00c2d00c01681710b120250420306034100020041c1c90060400552196046c205240e4043c6800d800c411108004500d43e0032880c2d01100d0000e10961905140481224030400c55511403094802c1c440c5070340c1d6620081079004546001404420340d00c004012655107100c082c81c01c00005015080f440d0740c815459050554440c2c01d040a0360f000300c941d210419180450304440884d40010188240100703280d400044603a981400d600d0803d010010050200100e2003c1050090100f110f02520f2540c4011710400039000080b03c0d166a41c556000740c1031118440c09442951910304000d6103418081a0042d204e5080041c0001d20b0310f5480a00c07106910200c1d00340d5a0640a005100d034801c003010421801a01c103070010041e10b414807101404070b54 = true := by decide +kernel

theorem cover : BRFrame.Cov 706474820 706654676 := by
  have h0 := BRFrame.cov_init 706474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 706474820 ≤ n) (h2 : n < 706654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
