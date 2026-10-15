-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4854
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:57:05.01967+00:00
-- url     : https://prove2.me/submissions/568238a4-3d0e-4d22-bebf-08ab8201ddc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 872841726 ≤ n < 873021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 872842976 1250 872841726 872841731
    0x510050913020f030f090d32090301020a05030708091f090807062d0b091f030b0109021804020a0c11040e030d1b0c0b1b16062a1d0402120703 62
    0x8281b200d02005550f031204203602d000c250480e08024110414612003c3c02c81c070240a4109a004020140f03046950104c1c2c020000c40d038689080c840075105170011101a4042000b0764000303440d0181c00300d0005445441004800d0350a11505a070600818407013a059601c03160030300c00d40c2c3c009169407080c4d202c0e003900c0b41040d5584104c3d0342640c1c1e5000310142e00b181c0702181404000400c98660407030b0540c2020154034038400c0d032011b8040f83c00c046640c69002030b0242d514000000b800e09020760082503e40d0052001ca4a81e08952062100341c2c030a1b8046400000c00c842500e1000c50a1108001d00c0303400000c2c4045480034180700d1861454208142030701685580d104805c01d0090000f400000c020154100288100c2c51625907030800d9030b000381706a507030340b0b10a5006103480034002c04032890000d00100e2035402560034240100100300240c0c4402c040383c0001e94030706100d0080303080c3c1c005007645596541c1c4204641408100d140b000b85043d540c00079000e022407d031f00454100c0c1c15115428070b6800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 872844226 1250 872842976 872842981
    0xa03051c1e151404020705010b280b040806061311040618090c08010b0f0403020d05031903021602010c21081933030203061602070510050913020f030f 66
    0x208002c803220b54901c0007940418039003c001d116800309180c1c207a428102c50050301d6071010b040c05070242c03080c4810355500c1160390b00c07050f4a04040a511001c50348250001861151301c48414803054403403401411203a9016100041d4070f0b103040c070040c00c401c0241d04000300b10706c041c442d03075040150410340000e0003080404240301c00341c0c04281000b42c014501014140000719034480c001d0710f81c403010b01990641100c0015001101c407102400c413401183e003d07045108551003802c0c8251a50000d80841c0340c9990f140c003d86844510034001c0c2c50301074018142820240c0c4080e801941c0080f10100100c0d4400002c40c92206107409407244000000116190504289001c10702a140c0720f040501e00000f151034184c10290101c030440300d01e141d242c074201e5001d90581c1c06885000030700000c0e41c402580f41c8140c204000b48884004c0300034105204c56021140003580f10020000a4020001101e000840034000701d42c0074502000b42e14030150f0118001450841c0854118015030300880d0580e4107681074070709 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 872845476 1250 872844226 872844281
    0xc1f030b03070b0301030330090510052205010f11091203130605180a03060e07050901050f22050a09110f090115032a02070b0403050a03051c 62
    0x26103040080110064905a81022420952804103010213010003083c106061481c40c3c0e40d803900d01c41c072481109503440a0075040303207000241031a0082121a4018041400e1500c000e034002e040c00b1f0008074405c0d500318888882d88641c01c1c0d10241c416038a070745d21500702c080f1031b01040c07003840e640018804503550b0300c2c03a009090200c1e41c100060f480b41154810001d07421114000400c1c60141c402c1413410039034035411028487e969020321428127a014117400000420410181d04c40b6040148640641d43e00503641c10401034010024860305400c0113288440445c00d26244825600c10000d038030b00c6440001e140c070010b5040302d508031511004c00360745240701c43c10701c83e00d010440000c1c003044039041f610413014004214400010300c110f8601401ea641c01d131610600070b030440c880c40e060781000c100401265210100a89642c1e0301e180b8094006d402c804240441d00c1c07001c332000d5941280c0100440310040e03400302c429511078502c94041c01200a59801d1803021401241005000c456145400142a10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 872846726 1250 872845476 872845481
    0xf050c120609060a02130512010c14090105030109270308040b100501120b0609031b1201091211011e020a0201051f050405130602130e07050f090d050c1f03 68
    0x55000c025800a0704011149800140c1e155000200794005620303496030407002c6045200b2038002d0365020180d1209160204015405000514140d6540120160240c1400819845090401c1d40010020001482441d1042e0443c120055101c0840c000344080000800300d0814050011000101140e00784814020b0807000036030003440d1888900c01d2545000000b800b040d09141540d00c006d51100385407000c5540f44c03030540d40078200140a44091903014244944121f4400c0d00310f9110340c401008442c88081d05100342800300c0e0780719400c201607010158060310264501107910801d9901c0d01d01d01d0302a81e40c5002801c1940c034240341c015880c0c00c43e9100103030a4070b100511600d4a0f5800e101d030049581c0e90701203d00b003100c40650700000c560b15011400c00344800d06000c0a002e0034000107088035001100864141140c07501201007500c3d40b14444100e5071031184082c020f41ca050140149861813400c5208021150300c580110b1b115174204001107804400d1041c07800d400c40e0300505403502c801e03400d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 872847976 1250 872846726 872846749
    0x16021203031617040201080603070306110d0f090206030c2b05070f02010c0206010504020a0909050c040e10061409120f070801060b07050d0e0111070312030f0b0d03050904090f050c 79
    0x34145030268100440080f81d194400400c042e0420503120b010075100d45092111b032001c1c503000300c0c0501c52942c000c00c0d00c100c1039102003c14048645803404800c1e0303019041c440c02481c02ea00400c0309185885d007030028074150f00010205400c00c0c2c43d500c042c80c031a280d1418007250711604000702043c90300d800c200207402100100314540075a4108105400001d90100d84141960301c101e40058a907094040b040300c207405141c0200c042d643c608424042c5040f5218083c1080f2b84045116004540d03c00505015040c11481170501161340e520300803189a42d03407806400c1034000600019103c0000303004441c0f401c80000780113801600300d01c8050000c0c010178014840648403070340306c051500603280c1d2a16034903603880e0529000c02100c281c0c85802d0740e1065000006901619080b50f14454403820403c000a210181c0c9901013450030096000c00e580074050b080c00420003c00d0b1900c0b030240c1e624240c0c0c0036070090502d40e1b4055078a030114000140012202d500d01c6028030000c10007190060181f0500d83c003507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 872849226 1250 872847976 872848021
    0x11802040b0301230703240312050c03161403210105031f0c02150a1b03050717090c06120103050c03030715091a01060e0a09110f1602120303 62
    0x10b0842c84d000080c0fa9820030107510000c01c0740300300e00ea520030b10106c1c01031140c881441800200801d07640c090050818401c1c0a0b82d005900c903c6c40c03000103e07020750701441241c080200540040c40b510703580c0c0c521807040904090042c0c454111030f80c050400c2038110741c4004902c10350245000c801316034481c001c1c800e203030141800f500141910380c50300d00e0720440340c1c502c0607543c1d031056100d984540f001803090010340c101d00450448035205040106400303000d01210b00d00384000c04c41d8290182c07100c500c02c0c09450b00404068a0307402c14820410101c99007000000c10b08802072007500c4000d1810340740c04000f0aa010154943c0300701c2c0754154646241041d00c000c0e0410301c240c0c4240314010100318243c1d43c044518885143c005850702c40c03071802e08100c25032001030032003101c00d1030000200d681d00309016040d104803c82e50001d55076224501501140c02c42c008a107418541403001d01c0c0c1419851006202c0111a0000108083c2480e0b000440001816502521940001c42409444482101254560f815 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 872850476 1250 872849226 872849231
    0xd060b04050618040b030706020d0e011b0b04170307030b03070e10120c05100903020306090a080a11010933061203050f070c080706020709050903040608090708011802040b0301 77
    0x9800001000d03400fa1051090802010300000c040560342d55000d07400c9060081e0a0310803a581d280c0f000b9441300c030900d14110200703001d11031503000c0d90300c69140d003d001d800507280c9041e00000340c0c5072111208030003082251040450191502c1c01007111b0080c0d80b142901e50741c042516400310082c5814070300a6070058032801e5014089c0114111400b01d010306507218049a04030302804d50605510144060303100720303001001d0200100c400c0360303c05500300a80b4001e40c2291169140c207818a03079503096002d0060245041840801a07440c419444512404001400441c1c244980c0c2c440010070030a141c44440d4034045503110480003410701881b40c1062040c24020410181791085903030851503500c500038200b00002814400c01c11040b01a6400160400e0029080303544602509590b484280a154094410311000250500090140341d101d00315480c041e504144c5880e205543d070550107004c8000364002c421000c5002c1c003003445403c0c0e600c00c20400341160032a5900500c000c076210908414060390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 872851726 1250 872850476 872850479
    0x7230405030721020d170f04141210150f170c10090b070c26010e1603170c030a03020a0914010203071101031e0f0510120b040204140a020d060b04 64
    0x543c0391103412802601907511002000b200e250038291045840010402c500d07011a200050518210241050b100aa0408103020140b00c042020345017081c44800210341c0311690040c03d01c400c0340c118605076072084030141c001a480c1c80c100804070344103400842c145504034548000126040040d4601d2401c01e0b40d50300c1c00d03d101c50b000180609a94024101d000900203030600c1040365105503074000700b188603900d41640c031094032040076040c0e006803410310307941c01c203070200300b0915021a0304101581c0c0244600c05c03842c41c0d581d800c00014400e00c0c40b0300d0410418810190b83c840280000c00010b600d40d42d00590300c00c0900c0000c1c00d00d10301e5800c16000005202210350440e60000110380b82c503a080000e0b81c040000c00c0e40101c014006060080d000000b00360300a94a500454004407004049010240216610790903080e003d841c041c8507400c40c1c030b42407030710900c00710345072880198126001030000b1440350b4503011a41c00a01090301c00a07040b5038001003280f06440e41c0e00c0383c000500500d40145280c10b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 872852976 1250 872851726 872851769
    0x100501060f080f07020c0429041107230303040c03050615180a0b030d020a0302120306150c12070b19050106091e0509090d091403060f072304050307 65
    0xc0c0b0b009100c1c0c2001005000429100c074001c0141c05d12042c002082884030030b589240c102d40130729444600030001c4070300c116031806500e000c1c01080d054070b03c014040d40c189916526030520503400c88075030490030403000050340f40e015000c0c00110310860240507454100d520310320701140b030000c0051034101c58103c09540040507548124a81990500703200c180000d9403609804400144074104a069051103021200002c1c0e5401140700d0310181c0c040c2e025200c00440054240d1514072080710301c01c1e0702199040854600c0071900c405004280300c000101c0b0746d80c1c0246114103072168058402a100103035a042005403920501c1c040e41c1900c0c0342030b003007481035500d4008041c0030504640180461460020314841c2640c3c88926a60001c03e0300071300c07541c0c15042009079191540c440c142c510300000c600180101d20b020360500c8000ca02000903000f0300080c0e0700c41101d6101842c0c041c0c4208100050720790f0141c030401103224a10601806a6100e41d9074a01e86001c1625048075070303108020021428070140c6a2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 872854226 1250 872852976 872852987
    0x8070503190e0d02390603271513020a0509130501092613090903050c06040c090c0e0f0d08070b0c072310110417100501060f 55
    0x5850150000701098080aa03000034024041c050702e41445009a5660703210760000f510030300010f01c00d04080b200110045003640381c2c41240280c118030021280400c0c6642403100055500031140c00110305c450740c45900741000a84482c0045c1d07465841800030345828407850710b4641d089203120203041c02d880d100b41d0114018544600c62a40f00c3d2070305a0002c1c1c1241034108041888503403000007008004080d2134624a0030810480d00e01c0150480290317110214601001c54207281c90034039950f0410b03450200032320080c28031087c00710200603051181d600600002c120090040d40306186c925070031801c1c06528802c40d4001a08a41000084122418070f51540e00c50260b40d0142510300030309008050405c0041da1003500030040078444402c04214410044102a0440c44d201703e160b031340b034411700c0d42040f8048000d68940140315002010045041c4c012035100e5080103c00310745142c2011f61721120101050340c101c1c0c0c13140385900015640031040f00746210700d9000d000f141c1055407014550b803c00a04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 872855476 1250 872854226 872854231
    0x7051c020906010201231b0403021518040c05120a060f0909050f0a03090e09061905060a0f0f05010909020a021c020a0501050411091005061e040905010605071208070503 74
    0xc0d46408020400303d900c00c0d08190f0818018600449111072110310034807030940101c5403802d00d40b10840070188034201000032038088a800801b000856100d8031480689a40240038400c41d944028680003240e40304c60003000c803c041c3c152102d54842c03c1c044c8984041180043c0102d1005103031402c244400070315404039605641d0280c0000600220a250440c501a90307020003032560b01c030740c180701020580c5c004040e006641255031910000d4441c404030300c0d501d0384181d64144211400039131544410001e60700a035031000b0010030a1844030b5980000d5001d42004c0d0b04403050f02440c1c02010301103540c00400c220b00400c25690114a071205c58070300252995000840407404070130710785003080024420071a294070103421400800550500303103410a101d601c4003007042e0280811070700154021f24002d04080c1200d8029058034500414800f031002800c1d48141c0c1320311000d10911012030a0350840c401c0a000c1c04031502c5a0b41c0c0c6000324140070340c1103180ba2003580e04000440003040101035002055a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 872856726 1250 872855476 872855479
    0x2060a05090105070b01270207020d060b0102030d11040f050a0b12070c060f1a0301050603061602010e1e01110a09030b04020a09020304030c030e0a05060f0a05090a080f07051c02 78
    0x40d1907060303880c0100d805214030034010307040c104a080081a10740e820781118602c00e55803683e25402030521a0500141d0050980196001681003000340c0454040e4100d203a503900144107070f91426000503500000c8400340030442c107213544003040078460b41d5281c414100c058541260802409482c0c15210040d82c0b0509001101701660700340803070035482c010398140c61010303400720040c01601d80549806008201951240761103a411100c0c01b0300c40c2c101131203198000d0300050b0243c001903a90003007441202d43e0308000b180c02c41d9a100e603807000015081c005801302c0c1d07140e51000599500784100c094291405c0c2200301602c0c50007080502e29081c2c004003081c048a60003208500356a0391400024003a00ba00e52000411034000010001056840030005503030520940700d0030607440a18088c003100b11042d010f0329400540c100500c21000307174104047d002d4441a4a8960700e80400c1d1400f040d8515126400b0305070740d038080c00c90204c1c41d00c0148070300e03005440140c600740742400480004100141080c0c0029 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 872857976 1250 872856726 872856737
    0x709080c060f0d1b111501050906040902150a02060115090e0708090a0b01090b041d0a15060f08070303020708010c1e0c0c1d06060703080606160510091505010302060a 73
    0x42c0071650160008082600700300c04980c01c00d052813201a1000c10100303054480c03401054103111a100c01d01d0b4219040e9040a050380d811651000c0c1030200403d4032702130580c0d05c4028402074008007104d0783d000344103841c482d501411442d41350214070064285e00d8400c2c43c0610440c80014441a500340132030070341c4100d081c5800303409500d0f0050480d007004000f41d000380c240c609030000460941e01980010510001c1510104401c146000c2e1000c82c44009540400b050380001410401080301905c1510440c210b66a000840594074400d104401100380d000302041d4004000c20030a050701031000e10300522041009004d4990560002004225046c0c2e9890580c2c00d003807022000ca03482000c00f0300d0b007258840202200d450b160403e1130030301e0049000751107010150000055240c109803055455140e8191140c1485445100411125810080505501542c0f00041101040003005000d10300800000005803130b1480d401c101340b000002510350440a8184001000142c83d1b90b01124081038491411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 872859226 1250 872857976 872857987
    0x10c08131a281205011716030302120a0e03010c090305060a02090d12030e07080c03010c021f050c0d05040605072706030e1e010c0906020a1a100b120709080c060f 71
    0x203480b00c01083d102c0e103d4440c5464004a080401e2201403c0540c0c0c0042c00c0701c83c44548801441e02601444c040240181c01691000d643c8103582806020303001d9003403e04101d25100d0101003421180d81100c54000110300000810900c1018803225420034100700c400d51410000c000840e021200c20341000306003081c400c40c01d03c01140b00b9800310018010f1882a5903d00740d0315054180d5035044012180d01c0395107049071691441d80000f4521041c114448100c13180280c48032611402000f00404014100004101124000c03590b0320949116a1140034006054204818014035443c00d2450b5031000080e5400c40c614150070780030f2007408a509524003c1540c0f00304043c1207040156051080c0c0080c024524214401641900644010441d542e204644c1030365503c0c080b40d85080d03401c030141105500410542c01c034000f8101d8141e0016111802041150fa0350007503078038940c80905100390000d14017091050145c0c0c04450500240086001003114000c1200010341c1445144a0b28a40b00b800088 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 872860476 1250 872859226 872859307
    0x3050c0603070c14070f1e1404090b0c0301060e0906030309130605040e06011a040f1a070b04110301050721270c1a070c090b010c08131a 60
    0x1c00403c5030760002c1d04003248480240c0240d0340d5100b034020b101420324110404a2111009880d4402d1800f503c5010a44140303840d00c101c080311200301020342c0050300c0c0d104000100700038409503801030090102c1203035a5807602600410400002848a1042c601c100600007103580c00015103443c024100d0301c0c1c444400042000c500105255032049030464140540000742000c041107803812280c1d88580642c00c1100d03845100303010701c6903024030551021081c80a000c24201d05900454107051010320514098213a180c0400b645012a4100e0310404d0031001c042c0c0030300f400c2c040c154000300281000140310342c4002d0903214080f054110030401c01d0307540413003a0043d0220440002100c0c460720081a00007503a04102c0744000345805819030303c20401414030b00904500c4100d844807034000c4a400b41007428465684041d000d00b600050400800b500e51a02140c0344070001c0040d07030854522100080e00d00391880d5901d00c1303c03178019100111305010030041d4050000c4000c40803152251004484620703205c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 872861726 1250 872860476 872860487
    0x10504090c091805060a0207021c0f14031e07050c240d09080a02250e131b0b09040e0303010308070b0709080105040302010207020a0b210907080f0a0201080f0103050c060307 76
    0x1c1c0c003506170b104050600c04120140c0c0c1c014844a130003503502020014005049074450000e10394000c181503440c04141c0045400e000c0a41c03000107900301078034036140c000c40c0d05402e42040c030000b0f880c542100144e10020040200003590442c40c054424204045081c4d69841138041410240080c110b8002040480c20869070f00c40071072280d02c03180c480c1e2500004400295a0030b012462180303c00a66500201e010540601a200b15064a011004645d4441c0c006414802e080300c0101da410b080034001d1854582c096014402410811110355250f410150401c410740d2072809030500950020401800803e01750000ca44409801500c041c04c151034161044620480581c003d210135440d0009202c00c0503419002456a00e00032580d100031561a0402c0118510402118400003180c030b0302d207903490603411154aa84070600d041039403503031603541a5081c140170308101c40c242c1c0c5801c001c15140440da0000ea2035900a4180c18100c0d070a5030469480580c2e5070002942c09201c0ea00c0071001601072407045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 872862976 1250 872861726 872861771
    0xf030f08160f0518031204090b190303030c090503060415150602120906090306010f1a1206090702010b3a120804110a0905151002070608040c030b1e010504090c09 71
    0x30f8229a8400c0e200c0c6882c507407d42190040d066064100b108400c89443d05403640407007503410145100f4454910760b025401480400d01c3d038818042d07084400145a42d0900861340300c0e6000d01c1d081c085002a800d4060110350100700c8215610342442c0041c452503500040180001c178071500000d035100380e03400008507540981010a80c5c5031080000100d008100b9001c0b51301165a00483c404130403000e448111814000c42c0304040c2410324240010380d02e40340c012001500700c01c0c640000213901e074001d80070507407860410f01c01884d0095402c030369240707024850049491140411098005014482e03440002d20458041c100341042680d50100b0144600c1441640c0e807003800800301c00c02e8554805500000e44811149000b00300048800001703582401103207440d249402c0d80c00350041d5424040c054864400c0a4070568007258000c0003c000508040c1045004280511507601000d080105141e40e0344016003016000c3c9040034141c00020300407403900d40580d03103846004501031700c609580c499550400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 872864226 1250 872862976 872862979
    0xd0807230c07080a052e0504060905030f07031e2f0d11060603060105060412080405030109060506033c0307150b0307090203010b0f0a0c0f030f08160f0518 68
    0x70b50500143c00c400001c0e402034424400c2055601e10050800550007222600c8585030841c4841e10440c100740159a000b254802e1054000064414642d19014555000382c0207080030502c0000c0c0340814150404118502103e6681550700d9013101c4c80c0006002540701c503072840f000030700f40c05032640ca5641c01c2074000364080481d0440d19010600980100304100c03d1429441c50301584022a90b80e06000c100c50b8160340c1c01034030717052805140521001205500c01802d8a0a003c20b02000c0703210754081c02180002401181c02041a003480020181048441500c010140b04d00040c1b140860f00512101c8891102c09a0815080c10423140142d0461003181d200078410360070103800502240c503135809001d14690139401c031041d81c1c0c1c40b4122042207120030700500c1a104400e0080341055080080100100c1950f0700d0500c45000256035685001c203051282103001c5514a80c400348441c0d4408807456200440104450307080d214100c0c068030300340c014244001007020010700301d6076080c0840e68983e0744810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 872865476 1250 872864226 872864233
    0x50402030a3c02010807031811030f0709060e0f010e0601031808070c0e0105010f0512041a0109020405031203060f0f0111030414090a0c090b07030c020406030f050d0807230c 76
    0x580c2600442c00c82804041307020400d50310110b04414464450000e1000200712082c905254035111159441c14010502c0d81c075100b51300c5140b5104006111042c0209002e030000719009091401c000c030b0b0408010f148505989440004010782c0c406558900d4100c80b0170300707001400c2c85004203a88503040e480400a40704140008042040200300003030f01c8200c450714880184541d885100440300c42100559910001d882401000308080704904241c0d003051040c01c105810210310b400c0400307900802d0f400040f000703170b000c1003c002c241001c0c03006880b5650740082c0c183c514500440056441c0102c030000038042d00c4003202a003440e0f40550f031400e158040290840383c4039503543e50405d00c402c1160711828010716485010074180403030350044a04008081d01e40c0300495040800c888015049080e080d400c0050503060640540c03110b10605000c3d50180d041c1000395411804d09500e0310f00007008140802000c0c00c00c1080b821780c400c0740c1c0803480d8450300a45440c034102c45a03000290142d1400d00042e0b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 872866726 1250 872865476 872865563
    0x40b0a06020f060a0507090302040f020919090b0307031707021206130c050f0d0818040204030804051804020f0f030f0102040914090102190309030216030c051201050402030a 76
    0x5070009409201002d15000f1030382e0301d5030346290702d1080d100c080d200ca0300400c084203014401445e0a401901441e00000030041c00d200855001842c10521210781c56150f00314030707205029008441c080d98000001c198020421036107965180e986a51050402c3ea80b0784070041600c0b0704554a5440012412160030211960342c141044d40340e605071b0302c07440d0480d45c10000010004150030b101ea1500c0c05607a000b81100b248032050345a0342e02540c01070358001c81250460408091950302d5102400c00f45024600d119291820b110a0000007011402c00011f11134000342003000582e690484400180420340d074800c100c41350300c0040383c50715034510180c8159500105010070300080c254460800c003c80d001058200c0d40341d190081c0e080f8031600a0f0131241c0d4010482e9031107410f02035040710b03040382d00c20300c1100c00d4403402e505000d1541d611070f001200c0081003114100114902500380d0494400e148008101d603007440d0380000e41e981d003140030040a201f403001c0c541c040401c03003d0401000f42c3c4007000650421 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 872867976 1250 872866726 872866739
    0xa0f1505070302040801060608010b0906070515091006060305090a02060a05090a08371b0503031b010c02010e1908040302030d170c04140d0602041503061d060306070e040b0a 76
    0xc0d0494095a50158681f210000300039210f0041d00d412203e00c680403924240c141c2e024041c10740e00c08001940c00384591082036801c00031944603e8460700c00710015040301002144908152819580100704040c1082c061003800040440c43c1041103074100d030a0740c1d07510507411041e52140a90700c1119031114520f00005401c10f030200da6802d0307a2404850b221030031201241400d1810b464a8406101681021075080008080380014240c054540c46401d00603541d940000740340d9880f8081e520819070120f440b01d08803407000d0054092200d4180000c0c401403195002c21591807243d450a44103000345d264940007840201002c07030f0051131b009400e40b02456049a400307841094800d40c104000b40315800058a00c80b104025901a903c03410301201746100000c2c10442d920f40074200949840e6070800000501c04244c9583e005056001d850100c1c1c0c00745041c0301014407201074914020710300c81440800910b60750100e8015408900c6003090707145600000c02140003889550a000d80080c020b6a020444 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 872869226 1250 872867976 872867981
    0x606050414090f0406020d06030b180f0f0d12020c0f0f0712080d0c022526070b0703090810021b0a081801020114040f0302100203090a0f15050703 64
    0x9441c0d007080e94490514002040c002c00e68001c46166a183c1d4440c1c0c003040c0018501d800801c10103d8621001c9000d64407a10b41c094030040540b110000d8420640d000d1000e0031080c000140041030344409402e2a081000c0080d03110345908441d0410070a82e0121481d0f014565410784070300c5418035084402c40413500c00c042c1c1c0e560f62801100c0f01035102d006400107011264145289403103a00c4070a403400c10000c3c0c0074180141a000440e00103501480801c0b54100783d0105070300651906a44010b07150368a8002c240559114024061844685250030b104d60040c00150450486941040403952690036040c12580c1c0c030b16640000100d8050303020b80c50a40ca0080d0050034400b82d400003c02a4400010b070003a5a440320110024580c030418170204846011003009a82107420600012a91002d580445821814212001c865142581d808071003415070411031041c1c40000c1c41c1046145080079810f680e034405881c00300424142620502500300700d5080103e07102c1c0ea02c0c2c040107014038208000060301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 872870476 1250 872869226 872869229
    0x11100c1e03021b0a0e09031c0506011103090a030f020303040305030712090803190e040b040501080106080105070207030f15020d0f050a150b0909040830010501030e030a0807021006060504 82
    0x5100d2050003040f00000518101c1c500c2d00000c060090f01442c0c0800030b040307103030f0080c5800d180d8002801840100c0001c0d0103801300104040b0302c001800d16185001610410740f00c0000882030380f0134081d6952948503d90584103481d04a01070b600250714500c0040d01e0340c46503400040031800049400e40401407200606005551740751641c131000c07070700c64180643d6401512651540b0070104c401d45584180510381060601401a001046000d80ca1010806440007130b4840030090390742e21000c110281083c810690020501c0c8007034502d2a00d90b480e824052185120003a2554048142d0f252141002d54102ca0703e600d045030003070204006207042c003c0104022150701540e6420810034030055003400010600740c43c072034a803c1e400c12010b28140b00900d41c00070300846041804100d4402e1060304c1406445145a02d1100018100200a281c0c6440b010690189040c1810a00d62482551010040e102c6029540c50603a42036500d509040345800c114000300c3c100d1500d031400c04600294068010030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 872871726 1250 872870476 872870483
    0x1c0806130917090906010509011e03020405031f150f06030c0302070209070f0206010e1933180209011409031005070207030308010e0f2206140f07020a11100c1e 70
    0x1132903585140040d100382c4101001d00d800618040419040090901d4410b60f95585a20f401410243c40f000820303e00082035854010003d80e24480d00b00000ea02d005e00b01c1052003515210480c14907144a4000c90b0ba541c2c00740c0410f00d902d42600c2404548660b05407540c581d0010b14040d468204100060000c06240303030070390010b0095200110303500244e04d00d040e0107880e1200025031441404c408034001040f03c0c64030505c0d000400313844d08541160901c1c180450008129200c0036040c9400344895200201031000b0003014010f00004550f80e8120505070381c0c180d9244035859403500081e0000e420602000d0312030011501c3c18003403281d2554005000001c0d00e20988400510341d0303c4010080b0818000c40c0e122540b9021030002403841020000002600311a2040c0d03034901120f65030340c01080c2d403102085001009404010018844580346c0c03401d8120381203001800c9180c5c000d40340d41142102e4004c2042c0615410034000e00b1091249207080760503500502120b460040f100d243c150400442c59056 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 872872976 1250 872871726 872871739
    0xb0702011d03190e040e01141f05010302090d0c15320f0f040e1014030c040b03030705030c060402030d080c040e071b060c021c080613091709 62
    0x2001e0740c0320760702585009040410300650070140c1d1811031100d00c1c0c0d14a6441401c00014034200305450b04e583c056115801503000c000311ba4080d84180e0f10444c0321000f004084420501030039002e81114425004058500a280140e0740e0b5071034202041e2042c40350b080c010443c0403c003c00084480345e056000600060540d036914000c01c001c0c0320030104031044002d514800ea120304880a4410324100200075000c4441c10700d508084010b602c421543c3c02c29400303841c080149504005000381801c0700c1d4006000b000306805034901103880401d0791280ea504486010365613a00d500e030071035901082a03912142d405000c4a039034051034180d0644075142aa022030191080c2102d0011031030181c040c9a125042000d50f80381018a80f003402400710788080d00110601c614050307100c0f0805950702100341c4050042d800480c01e9040b0480080c9880b502074407a1146183c1071007104616548120200e421083c2221203086014020724004010034907144020841004002c140700b0b034400d4103000d001c182c441281c01c4d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 872874226 1250 872872976 872872991
    0xd03030b0108071d102a02090618070305041b080a061805060403120f060b0703080a0b0d020103270b040c120b061e03030f0c0106120305070b040f08070b070201 70
    0x2a210400748801050303000030115803444403824030055040ca00e10061502030000742810717003880800281184100142021b564244d0254189580056006401651043c407581402d00c3c0c1c0b078008400c040c00d04020140c03141d000c41c00703001c40802d114641c946c0c125110103009559038081943c0e800c92240464078a403e0501c00c041c00103e1038001580320b42c000c00a06146da8950b0350031201542d8501e2100160356132001d00b103c116840c0c3c4500c5018001000d102641c2ea8203a04000c1c1c00b2407401403d081540c0c0c100b840881072515400320340c01c003165081c02c1c045440c10341900c2d803281c3c002c007011604032039803c180040014001d46101050085006408503207540f80c0710711039100307400945100500b4201116001c0354890030152400d40c0c110742142c0040ca51984403000007030441c1e02c00e820458200b80003141c5507210103c20320503180100005514490300070300d44e5602900c240200341015118842c00c00018040c040e1200b40c4020041e88810031966840e0307640340406410000740c41000056182039072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 872875476 1250 872874226 872874241
    0x30c01020903010608160506031e0a0207060e010501033f091d01050907052a030c1509061b1e04090e150105210f030307021606080a0513020d03030b0108 67
    0x46d440c020800755110a940b042c280740034004558005019400700440ea020307900146801c0c0b000d07850040e050190b0140e41c40d601ca080103001c0d648440d00c20301c12030f4034010040000079011016a031449140e07020000b207443c40401d01c4890441d01c21180e8800d09c0b162840f4403da250300c407420005950843d8600c003180c3c0c1e880c2c0b10403000c0b06d0090041640000544000c1480345000c0c5001e0b2034404a205996411003035550400044058074034520740c3c6a1f0b10110380501c0041c3c0a01100000911180030b100d494904044841d954074000340192083d20201c0a035025007046400450344501c1604e080e20303001158284c070a1040d40d205118079800e042c6445080c0c0b0b00006c001c40c0826042844200030043c0d0303401d0600300010555003664a91400070007404001e981402804080f00c00e18515015545a20301804041c0c00d01d42c0300400d000d031081e0503507401c0c40700c2c1e504203e1154019030300c020005019690034a040c0c49a0b034031400041d41c85070104070400101640342c1c12103a0703101802c1c1d84466a036191a0f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 872876726 1250 872875476 872875483
    0x1090506010f0f09020f0408030d0506011b03050d0c05120106050d05071b15021e0408010608030913150b07062f070303110706111e120406091103030c01020903010608 73
    0x2c980d21460803c000700aa050950058000d000e00c4840e02c03840d02d592200704a03d1588114100303007440380c490082298540c1c21129002d0310903461441c01e050b21400b03030780042c01c5100e1a0000306c0c5299481a01343e80003403040c025a010304518600c4401c580d6101c40010b8004e07002030040b4075130103061078002890688500c09814546017041e21140b00e508559560703100340c20050061086259080c013030016603012074940e140d134602800c04041d6445041100c25070941e200c94201100941c0300b00511440340c1c03111848216040d80d030050000d0100c6811032100e03184201c0d40d00c210414400817030352206110f810382c0070b10141e10000c0c40c0040e084400c808aa100318502c1c2c114243d03442030601c103260101340a034028103041060540c01034500a141d90743d001c11941c050146c8000c034140807030100c1c2e604028500c005001221070011600b0040c150b011182c2c1d2a4009200031305140d2902081d104206d181000354205542c010283c0b8ac451a903124211f000f504041c1d41207110303601b0b20710000b03900c40010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 872877976 1250 872876726 872876729
    0x50d0c0b070c0f0b0c04031103030304110123030c181504091a03033015060c0c040c032f0a050901021002040605090f01050c0d0e040e01050901090506010f 68
    0x12805105580d4407001070360850340000058410302c000202d00300008164100192041450700c41c415251425814040485808040c80900a900400c140710114460401842c2040c0c402d00e032220385800f1085402c0400c5d84103540e02d154941000c4240818005c0c0c401c0580000502105512002000c0100f0044002e050300d811100381c1d4403c0009011202c1d0729000080000711039049501c1c0020360001081c80d6601030300c043c60041440d0049100750030341c2c111454a4444407405c44200318140540c0c82151440d2642e091b0b44504400a00d0752481d043c00d00c01620b80200040c03081000c0402003401801800f5103800390401c40310b0794200ca202c880340300142c0d04d00500700415a41c1c1000c1c0d2103101600c0381e1307006116483c15807044004501141c02d55000030809402950b8a154a031000801804102480100709505200c014071841c40219000184046444024904401d04007011800f03e0020840d003401c011941d424801044400c50054101d01d10052003142203a2980e0390382e054011070b0034082d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 872879226 1250 872877976 872877983
    0x3090905150108011418090c0301110a0e060a090801050a09110301090f0209060d05160303180506090d06021308031c0209100309020f0a090b040507140a0c06020708040e04050d0c 78
    0x20f1070041c0098183d0440301418840c019100b8001d45070308200009011030300700c401003410340c81f000c90b845060500780103100d03611102c82100c0d070501e41380c620050002ca840b82d03c060b001e40000300d82d2298403485034142000902000001300100c5c101861400c02901c4200da050311283c40640e080050303410141300e1007003c15003000000b40c074001c0740c0e8204520481c010b00740551101c9001248000310b1001d10a802102c2007200945201c50f2644c5009460028980407420314402da0b14000c100c0c584504d01110061303541158201c00b80d40c020f16040009001d82d141e01c0c29140b10004002c522454008000d0180421001001e000654110f014030141d200d400e0080d500b10740818004040640660090302813580700800c0c1d11424801000800c10886c0c00b5800003070401e071241000c100505141c45220b40002c2c10386804840041e54500000b0a84208407181d000c02038401c4080c001d110140e4140c60321241d00031241a507840e680c0940d95000030307050b1800d4509005004140c40c10074000c844002c9890390 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 872880476 1250 872879226 872879237
    0x2d0405120405010e0616051c02070e060f0127060c0312060b04120510050406050412090b030127020c0c091e0103060b1906031b09081203040203150103030909051501 72
    0x6104c0501542c0d410161151000441c1003001000140c8180400344800c400081043c0d513a84405400078070b00b0031a540312a4080e2400c0040c40040e03218200c071100502001c1c03c0a00c411264032840400d41204c0941c0700c02840c8003003030013081a5034803480f0310ac440d50199039003682e545500c08011088030024803401c084c0e00404c1000304030f44802e0043c543ca0302030248007560240038140300384106941d0300b210100d40c22961007042108106008521803910781c035030724040564600f490b40d00440da10043c001d80014810866120f200120b007266982c0300200040c9040d92151441644c560343c0342941003020707109120070320000d40d4241c450b00081410704c2489903000c0c00c0c0d03440c40d01d603000100650405503410080c902d000705285030304200c1010007051745590001e0301004034a8608074020680700e0b18000c00501da04100500040041d1000c22094040c807661f6990b111480007a01c0d050503c00c03207400e03403010f14000005060b00401c014003203580c50b56092080380c1ea0100c0e2540c1c12003004003080c2c007062 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 872881726 1250 872880476 872880497
    0x90203090c01140f221401020c090a110c03041a031501030f1d0705030727051018050109050c0a022d1b031c14032d040512040501 57
    0x10f2090044910f041a03500340c0c1458850b4039a48150968054001d4030000e001410b10010360003840386030040181120811882d4444803800000e40741c04458012502c120409400704002079030940c44040d40c030702a00e0341e0550741c4641050300c1e602c4c1e42091140c00b0042d03001e64600400c5c02003030000c03644206401411316000000c848010f41c0100121b101540310300380d9902024250381c403194080005081b6200042c480c0c3ca1800e41094a0703c0c0c0c4a4108200401400c00c0700704074004d001c1d040c1d1200c00c0b043d090102d0300e07503103249100b4485c00381c0768001e80464111440d03044211096a00007410b0f5001100c003488140c2d0382009108591140d480303184010387c4a02c141c1369241000c2201030740c08035050303043c01d20960710401c051031038509200340002c0000c0401004240350300d4200900488c00e6214100724050510140f405007600001c102c0f50a031440000002400c103081030b040440c0c0f04090042000d04103a181c81203801c2c0700b081120220790902c0380c4400c00072036001d084252011108160745114005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 872882976 1250 872881726 872881729
    0x90f050705042c011409010b1f0c0f0611070c060f020307033f020c060a09080306060d18140c03010501180f0b030a0803061e0d02060304020d0f1b090203090c 69
    0x56010f403240240ca550750010b09205c0b011542c5418010940c5c040017080c2c50310305c0020880c0c004003010509420114894000030034a41043c2c003025640d07000408054910482d040900240001c1030b10841c602600044420400054240c0c1a00707441c101d986040c00325402e0360050383c4c0c9208108014010940354448828000040090105a5040e5010441c1c82c5844100c500342c144040030490420341d0303000306464515040801c10f2642c040080b0500b444000b03110303269401c0902c405854280268030002c0d60b000d841c10190004c403400c00751044020407000540c20004428009186240c085000b0103002458510b414002c40b4141c078403081c1803103200c0e04503004400003440740403842c2e1f24007500c803854500303980d03000d001e004103990203403a98507501d00d0680104103c1c01c0c00d034542c90000c021010703d803409649801c04507030745440d03041d01c0e9950340303484c0d40c000600000401880140341010b0b02821004022000d4841c0458070303100b243e4152416100c42c0d104099000480312010745a1120302c100203503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 872884226 1250 872882976 872883041
    0x3090312090812071a040303020a032d022b050103030e180609060109080a12080606070c030204020304020a2411030903060c090409150c020706090b2209090f05070504 73
    0x20305d201e04150045520565550034203803c0444003500801d50206005114507014015210508140c0d6000080212941c04480300440c0d07000e00904556070119181c8440400c8106140080300058000941084001c4480300980400d020440014003a04014812400d140215241140840d0300601850b55401c05114120340020421410041d004400281180e4103111001d07103140204074248101800c0301c00a800480041c00c014044c010801c01900402e4240580354156541101d01603940e4495000190800740c55400606200d07020132000368030402d251000c0014200591198141c02840154554403070152464958054020758001010003062500502d00000c0040c00044e10b050030351510f00313603c410600c403445815940c4071410803590b0100f10000040c15240707050340e1094208050115207001e0700c03140c9450700584c0a40c6d400807004186070307280904200b003800c111110355810546590240601d0550781405000c03404101818503001d41320902100c40e100403000b96100318500d05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 872885476 1250 872884226 872884237
    0x1a160507030c2c07141201031a0c0d020c1c08040b010509010b1222030c031407080f07030306050907030b0415050607081b0a0b04060f0c020601050112020f040303090312090812 77
    0x20003841c142c0c040c41217054000a024001462811860345605515045040d00031803100c0c69180c0e5041000c004c0f43c8485d400c11038243c0c038162070002d030711030701c1003c401ca282502064800003404400f40c00c00030800d60000403640b2031800382c070f128489a641c40c001d100c1031041c280507464200c001080b0300c1c02c200d203106880c1500080c0185050a62a514211241a0403003c000c114006800300d41842c050540c4682144c8120045141c40e0f840c01852342d6400c0503520880b16624088480410031505140c02544202d00500014040c0000c80c07900090090041c907011021900c05c500d030146030a210141c50449030282d500180010b403810072141c03600348190f0860240324002030082495601c8140703050042c607484a1040031140700780d0a040c0b80a40035550600f10b05101d0a240c019540c100d00c1c1d00050f4281101c20a081106100c6d40071192400a40700d400c4070580040c5001170300104240d403001e0712400301e03401a419001c203441c0c0d8090803600840303035100311216a8055810820341c113540800501c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 872886726 1250 872885476 872885491
    0x30c021b06040e0a0e100c0518030a0c030c1503090b070c0c12030f030e06041110120e0c1503090a0809060705011802011b020306011a160507030c2c 65
    0x742099900e03084111407620403a52054540c0c0ca441c00f114500300200101d2048103039211051000b511441d40088c128084d05c1014012248498075901440d00e0034448204511303005841d22001c00e0302d9090141c4a4402c81c85094800d42c0d10400801300113100748192148641c1c000f454070702e5070711034502c00c8a9100303000005607040c180e001c000042280381e60710031070300c0c2c2d078425101c1003140c0008050140803184a50100003071354000b04104800036146003110060a8402c450310000c241c10610b0440365000901c0042c40e83d1440d05040b507000d030300700181c411003041085480c1022003244549031142400b058406440387d50095503600001142480a061f040001802c002d00f00149510740e18290b5005242140001e5011001079080d5640000b8090038100c504c0460048001c40b43d0104c0da40752014800d420f5841c1e14042d48200c40841c40d0215040984c40c1040400081d006090898a40c1c400d031108480041e00f0220005101d50510708455042845056048107401150104214114000c1130341 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 872887976 1250 872886726 872886739
    0x306010e03030d0e07060804081b031b0c03060117060a090809041e0f02040f03030c05032a060f070c0807020d0b0c07020f0402030606071511041d0601030c021b 70
    0x3003034691010009810700003604030020603081d05030700307149041c000f0710b80007041045448801c000200b0708000c01c80c1c00c00f81e0415160041003c0310910307241140076034943c00408600c911449042010b00007500c06d00310354120306a8031540da80e40e1401c030311402c400700003c000c4e400000001f041d4285561000c01e40d140a840254900a9281c000900311181400c90303900380c071180300e41d0f814141020311508905004070601140350600300481c0ea0100c1e900c4c0d210003000c02215014100030008140b040d1104894038100ea450009551240a801d00d000c03400c0f00001881850002620060030500143c0545115101c2d0031001c1115162204181d01001c02070ba08994a80c0c81100082e2000280c544201c404012607a180c1241e803040200c0c10300700d03000b40c2d48560700600a015040e910348045402041e0f01000c2d804000040041103006408040e45a2260b590080b5000603801c900b0102c9004c84242c0c889054081e0b603c850064040704e442c5000c0300010b0b40b0625500c114003208001022160500a022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 872889226 1250 872887976 872887997
    0x114130515070512070923150304080a1205070816050c151e0103150b031c0f1106090c10030b03100903080603070b07120905060d1b0f05040308030601 66
    0x1040034010700351580400200b0004480070911130038001c164221a10b8649110741d0741c500200624080ca44c0741d02c0c1c0b00414080e2038880340f941c0c1c803c2c031042088083c00c4100b81d200c3c0303060b003414560b5401c0541d100020407018104026212510b104071442011203480c1c54205442d0004c0e200202d9240100444c1809010060b039923102c101041806410790b038207100a080d5213854000080e1454000070315000c0c04091b14010303c0003071941d41c0244110781d114080020100340400009250160321424080300070040041196420303806081c0ca03800e603205031102c000e440708414819540d1030701103030040140c1d080a91003009500c0c0c4144030342070028140c40c001c01c07440b408100103401c00d070701944540d02d15a1b032540074808154000c2d5070a030740302000320003810050b8540043c1400a22941100500d40f05400140b0444140079001042c050407001e0009034880c0b901c03c03007501c0201882d2034180d14082600e0b41e91a81c041c492201c3d18131800d45941d40c0c0d030820303113955a00c0e655900040c02050602000e8541c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 872890476 1250 872889226 872889253
    0xd0209040e060603070501030c0816020a12020312060d02060313030203091806090114030d030b1311090301060902190e120a12030c09050a29041e0801141305 69
    0x1070500120400320141490f410070038109031501d034240d40414140342c00c14529092440d003250304554010240000ca5480340c2c03000c2401c0b070511014030001010303901c40b1000e40503040e038000098030340700d19550f07851811070304c980e002c01403401c1d0208002540000d01704001048201c1040b9100251442401120709000d81c1c00d0006420420007866040802c5020082090350318001031060300400007000720600e40030000002c651a81851701d100e405240e1030b4500840c0303e0300d44100d109803914441d0f0f010042d00340381502a201e00d038061400c151080d8200040402c2900c6544201c03180d03001002d409800d480c00b02c0c041610005803030200760350702c861031412664582c0824080d2030003541c420b10f101481403d5000c0301408030b03201e0303102d07040801a118030180050385480442c0001d030380d04074074101450000030040201d00411840c01d44c1501c04003007000204484502c10242d40c4081f01ca40503c1d000343c881750010708a4044c2e10380c902d480705808001c5584003c150104100340b500030815115424003011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 872891726 1250 872890476 872890481
    0x90533100e121e0c0603091504050304080706031a090105010207090b120102210106020d0c0818130b042d0c021c020c010f0f080c031008070e1f1a0d020904 68
    0x2075010340401030040c1e84030b840f0f0401d201c98662510100e80542c00c0d400c026038003c0d915065800790744081c25010002c501407000030010317280241000740441c0d4a0a80301c0e44020058a00180d034000101d41a07000062145020100107041e20410b03802003103468900100c4030054440800065040750060074503100d407a5083c0003e0800e224030108400452415140000c0130301710583c1b282d402c54100000180da1983e208038008403c6420909c2e10380c036038014041102c1c00220700b0419030f03400351078014844407a079620b401050101000701ca00300a40c2e1488025440052400110380c00000043c00c20180c081d510ba902c0a0140515481181c0d1019040b9a111128034810081c5901690010400a400e5a88007103a4069044c252910751082c1c0750407500078010700c01c003800c0c00361400c0707002c0000b680b003c0c4001c9080e00282440070072030b07044950b41e54241134405020759155100c1c48074840821424045040c140c0d048620b40f1050401c5510070951005d19a004180702c8244560200f00141c056911030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 872892976 1250 872891726 872891743
    0x1d061b06060a05030a030906050711100206010512010605010525021801090c1d011211040f08060903040312120f14091e07090510090533100e12 63
    0x600108803074100794040184490241d403007503110394001c84c0c82e000000d5004074120211004d600b491a01e8901e14079200700c04941d0310403c142c0184028441c201819400500c00381200e10030794031958920500200542a503030301e401481e000c2802048000f003100031401018840d80c05600d01c4000d205c50340c1d030000380460459090443c2c042c645000510883c00148510600301005080500101d000d5403c81c01c49030036100c0020341403041c6c1102004413030880f604008003040e035850003150744a0b150213248800085500900381d84c1d02c900d20004000050000494040d00d41090050ec00c000703a00c1c10403602c03c100306449280c038031707199042803c0c1c0900b103000d00c075040b03041c4c1081144c607481c20b0080c0310301c1c00305140220468074080043d41c0141c00d4000c1422020307138a07605004a03043d507440140005c036040765400030540130310785400c000d035242106014080f2119000c580030104090b182400390309403036500810fa88500200300900815000d042d5034020400050b00a00d882c0d02071180b46410b00110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 872894226 1250 872892976 872893027
    0x2090a060309060617100b040c022d010e24010509060f031c270308030408030a020408010204140f0a0e01140d080d02041a070203070b0a020c03100b030d03020c060402011b0501052403010c1d06 84
    0x4ee803254200401c0108504e80514900d0751064200c0d1b24280001c3c15400c0f01030091070040311021301c0314070542c13402e114010400180c19104900a4a411001014803040d80412020b81090003583d0014800042200c81282e8021043e142552280e4903070408070340c4040e141201560382000000b80d04602800600014524591401c0002055605004c00d03903e07071f481814400c2d4600b603402c5c403110350300e4210300341500c42c075402e150a08004203000c00c4404800d9007001c0d000f2500841d01110004860b0000e00540703401c00c20295940b640c1d8000c0b402c5d1806a010001d5245e00101c0060228030321900140900350181c2c411070f4012440c0344040307410049000c0080701400e455401100b02410100140304003142c903803804500d0702c0c110364625a00c0d0007016000034104141b10184111000111800084a54100c80204a5420461400055404110511140007180c01501760480ca41032161201d0b124050725507166014031071030748c14001c1c882501c480e0352141c1c0600901641e640c4030b4040f00b012400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 872895476 1250 872894226 872894233
    0x151503051c0f03330308031f1d0f070e060a0306031106090607080a140c0609011404211b060b031002090a060309060617100b040c022d010e 61
    0x1c005030000c0001c802200c1d403005160500c0c001012002642401d00c280c03074005510005a00300c1e40b510715094440b1070340007400c0715030044248581144145042d00032840d44c841150038403aa0f48014118000b501000340402c001d01c80001210004c482a038035030b0007000c2c0e00d06011114032010005841d60404c07101413000139610081407040003a0142da44920820448081c1d00300108540024107a10444000900100c808609455144e01130000000604604580c0c2900c601040f010b1907a0f4103012242000d86600745290a80e00c0c3c0d1807024818001c80d000326200c000c0f003110180802d802b03002540e180c820000300c04941481602c81e0b03001e4611a5120f94000708021001d241050b141150b0f0310151182640b0400c0301603c0d40d0348800403801100c40e5802c0108024100c1e0804600404041e482002001c445090801355010701003090052003900300d004000c400c1300ea4041c0700403100f810305540c0241c1e00204c4c1071544441c030400030491b564030f004804810074054a141900b0741f14040341d003040b140d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 872896726 1250 872895476 872895523
    0x204090b07021006080f030f0f09090421080c09060c0a02100216050906101103040f0902071a16210c0809070618140102011b051305040915150305 64
    0x303e401540000c005040c001e04000c0b82e0500c030145c03603200d0f490b14881c0940d4001282e2400300b0600e01551000d4400500400c410b1505007403140300e02c0500b5000601e070940c80100740700344a024071070721401940071000c0c06040c507400800740107003a84040030a54040c401d03011220016032f180104525109a10b5000c1c10f0082ca040d0440701c1d14550316040144105103000405c2403903224031a442c0030810543c82e203108880c4004401600318490380e0061402180d40340008034001a6503001410401c2c071031500d14030450500c0d004248481c005544101c4199810300d1482d115030310400380380454201c0240781d40e41c007203200c51240c000c443c0e480840c0070100c0c0c1c11004104119a050110200a109038101500882001005642054054010010020312024200f80b49920035400301440114240c0901107a14800b031000d042d9810941d1018610180102c000c1402e041a000d94660f441d44110b0440080198254000113010094030404a410000d0b4000000c00c60400286088441419000c100c24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 872897976 1250 872896726 872896753
    0xa0b1c03051c1b054e04050706111906050105090606160b180a03110c030106050d020d03030b03030d02122508060402040f0e010f060c0503160204090b0702 68
    0x1c00440c082c0e124003510b0100702c108000244000c1c081a12554900a961840d8045140600300029806944070030030011560300c1803a000441c0c0d2524603146a0111283d11041c65451610041180c0c020b0003900728040c1000b43c3d500820003002d951710b1440545c0c0d01c4400141640c203005c00004000c1e980c054641004000d60b051200203660002c0d81514424940341094014101c00d4400100062044095800040e8802914002d041c08151100c0503219990180e0500400c2d20039800d012a03010b018404007400d4601d0305204860450300e000e0101440b041c0d47c0d4080003094203501000b03074103040c0c552184559580c1c082c0010000040c4001d00180c81e0300e245000d06104181c02042d1441c800c90020714810342003160043d00c50600c440e86054111942c0d6800407802078001c650102c0f01501c21070401096024640e01414180d411206001a84542e10602103d040d401e201f070281c8a500100019500500001010790502d030000d40042108003450355000e514920448055006030020305015400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 872899226 1250 872897976 872898007
    0x8190b010504020f04030f020a0302040915050105030613030e030f030c0d020d0804170a0e0a061709030703140304033005090f061909020a080a02030709140a0b1c0305 73
    0x25103000d0b1411400c160880e0450f403820300c1603000141405c21605003207000c56031550090405540d02401c10b01ca05030503854002080080003010a01540c02c060001c2414100082d1403845490246000c90350114181c40c00e581281081a20682600811100750301500e000c0000b0441408041d00410684000d13020007030611509419550810244009000200721030f000340310710140c5040000703076070351404900076182480101c9960b6009242608000303041e680008400c901003509034060000380d0307200c8038195101e1040300310090118841c684030840034102c01e005103a01a01c03a0030b08900280030790754803100760340914000745090f1f0036600e00c4900107207542c018190000c020703000805039a0a05055191202c0c1c0c000e000d81c071104000d044107404428603400100c8520707005800705c0200b030303203800f00d02d902e92003010801c1e030103485800c100080a2015110300c01010301a80203843c0203480380071030040039008450440354000e4107032040c046014004010750a0040c801e4a40d941e4071442d50040488 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 872900476 1250 872899226 872899229
    0x60102030901031d1c0219080414210303070e01050309071e030b0f0109061e050103051009020c0a1101050a0e060a031d07050a050a050a090b0301021306020318040b0d0f030908190b01 80
    0x5e07c41104031201c0700240c2e40d0030941d416144030401089580180f01c0110b01c4a400c800c81c03c441c104402d01d02e080c22100040019401032503e561808038840c41c400c0151828401603072902202d41c490348013048185a880a082103800b0010b200028140e501d0712548000340d011340380101c220446200400c02d104852103954002c245800703021451108000c41039840040500c0380300c4c149501d8500084403204442ca641c006803c501c8000c40d21000d0780507840f5038441c9403400c21941481042150f80075580030744107a640c202d58954a2100041002c024001036030403080c411024540c641006480c41c000005040a011240c0c200030704210789068100265400140c0c00280146240c01044c441626850340c50300c05e43d07200c103d01207009505000821300903c94000c01c4c84d86010411030119105601000404036403400e90300340b040f440415410041104e0340c040070142d014216400300c2d40040d103141a0794079190b00a00f0154091a03880e010942000c6111140001c1e4581104825041207041d0a00d0750 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 872901726 1250 872900476 872900503
    0x1921050d260402010c2d110906060309060c0c1c030c0e04052406070602190905040b0609040b01020a0c151e08010b071e0303060815060102030901031d1c02 68
    0x140c15042ca07400181500c1450304010345084504100c42c204801200da0113045070602c0b804115420070503003041f48660140f504418840e0060801141c15442c1c10010790307006061300e0003e4406910b0300350700110b6950089405103d01e020301818145100641460038486160301d0b14041401c07103108030018613001d0380000b8203118500c1c110134030100c01000302070400302c4034a6045080340303845c014000560724043d0940080217203000141c12038507003000000030108410240c441840a540743e40802083c2c5002c401941d800000a226101c1680f820b034201520307103c81070041c0c8000c4007042d118912003030072030381010300040710100001800079840807405000520305100c03804410010303d0002c001c1d14044c400c04000c841d0118442042c808201c103010106002024106000481460040c01070110740c03103459010b003d0b04104102005410348060b100c0c00059015525040d9001d006400402c072058000c5281c007a450034411140000f00201c010206449900028001d00860000d24214004a03000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 872902976 1250 872901726 872901797
    0xc03060412030c090e09300f0706021207050a120b090c072d020a14010f030e030c0a060e0115031203020717130303020601051921050d 59
    0x44086640424011401c01d40c9240c086941e00016504071590f01d000e40146140c080c080061000c1c94600140e9010310483c03000501400460802009000300e4606200c020301020411a6414032409500200221441a14018103121240c1920b00058108651a101203440000d83d0901d240e00000b03080e4500d040300400303101054011010034105540600980742005000c1a40c100b005039020390325800307100725000030805424071040100e840c01c0c001400e0380541da80000c08a550149005c5403424000c0c180c561075005165038108400a19010341325925500003032141811100c0144850342c0a503000c0c0c0e1000c00e4212070000c90608440840c1d00380c0c070b42e40b4070200d400c00008004800b0030244509030700b00103840e8141800e000c0500620030f00d0f12641e40b000007c040340c0302084945a0000c0d680290f0880d01c0b16038803202800302b000a90504107a000d080150100844180d01c48610925071940100481e4900c1f1680e5251600d041c05083c14003007807031260446406040b000c408008504007000a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 872904226 1250 872902976 872902981
    0x5010b040b040909110d120f0f0206180c060708130e060a03060221011215060f0b0d0e030f030a0b0a050f01050306151317280c0b040b03090c0306 64
    0x141030303102d1881038801c01c40d22031075007030305201c8800c004180f00c900240418401c16514905456004000b070025001314212079404901d25201b9280d90039400c240ba0000c202e55282c44c22a000305410000000580f8800d42e200090701d074540c3c40141050340d02c9000481d817501803004240702c5042a9410800c81c0d44c20900400c02c042d510403000d001240c0d000800180d07a1b07601c5e046c503111003541e503d019529140c00388000091034004140d0349100c0c3c40c0100c0d204440041040340c0b02d8181c49440c03080c10700b1405010018056a2500c00041030055140640041d4002c0048109070841e040344a5014a255010007000300c04031081c018281d1826048489803a0641454000382d007840d25540c00d20304102012002a856484580c40d800c0c2d2121581c8909441c0d015100c80c01503000390303c2c062050000c108441a80140d800000d040842100345c40203112108070b8045a6600c1c444c001200755080f440c00100056070f04d403d20018000f910f90a407003980d980c545040d1403841d00c138180214034080e9000004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 872905476 1250 872904226 872904239
    0xa06030b040b0303091c0f050a030801030501050a150b0a0903050d1e09120f0503091e010f030509030a0503040c0e07120606020316020f2101050105100809031903110c01060905010b04 80
    0xc41d00b8406968504108106d020303043c1001c2c6403601f07000c020300c28410300c9007020605800c514194102c81c8580001d205e19070322008110700751007801c01100040200c000f002e001c412490b07005041e15660924100007496030700e0703c80c1803400030904008008101c2d0b4400070212515450120b00d10283c031410b1088005103041c031403110503020f48401510581506905000f008814070850b003643c00010b00900407203560383d80003030303c11003007010b4940420355900a080c00c1a000c0e0080e2442204048003450510402c1c02040d65554030090080b0344140842802003030060020700301e035014500c5070b51001050380350000c04408844040c0c01000565005120034001c170040301e412141c091303078191200111a602400864580281300e10007120301c3c082138401d282c03401c10540c08541228030031181394141000c500010396000c03c0540d0400e42e0340c2c000b00b151950010036540c20b4542c2803aa840c00280d1326001002c401501d42180c60b5010340759440c4c0d003040106114901841d409032241640f900d282c20b15060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 872906726 1250 872905476 872905489
    0x5010302090609070906051602031609290405070207080604052a0f01030c02011b11010c031b180f1d060f010f0e06070209100303031413200a06030b040b030309 70
    0x461b80e01008000510f41100009510b540c0003099800303422105000030f0f0070170f941c00b80261801401e0007140741c0344a124444402446084028000c28a400a46802c0ca81071001800b8000c0800080d8400d110000881c5241000742910450040002d051915030b144001c505030740e02c44006449001c0d50030b4808013503590322003d00300c01c1d0809080c0000d000b41c2241050307014000810780d0f88040c00c0b02c41070042c02d140d003000b4412a0058104020480788808160640031584144444401041841010020180240c80103441c0004982410744450b5542030f03c280160001d406c0302d2500c00501d50400440c59144e03411a401000495a10f02c034214a035000a1400e480a04c2900c200801802401220384614045801490700600034140520380070ba00c1092a07009e40c0310880010f45000722002c0030b2000d07441c01c0c0b4015190241c84a003407014a80b210780c48004240083c01030700b1610b40b218050741e0303900c50314140209219100814009000340420084402107040c9034041c0d0820854440a41d4400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 872907976 1250 872906726 872906729
    0x151124070806180c0d06090606050417010609091a1e270304081f0902091b0d05040b0601020c030c0901060302030718080601260c041a040906050103020906090709 71
    0xe160581c00c40d0742d64000191544600850349102049480038020500b80c10300080210b9200117100f4003480365103429180840703005124040c00603105000034408032181d0710035041e2030000d10303001044143e15000050106c842d003400031a004070b40003018035402c851807040071343d00500c0380041c444000101e26501d01d24020042501415140300d21111440326444020015046280c100f04d81e180c640300d81d941a9554180043c079610072000d808a146000a5809104a4607038007038250f1071180c951210707104a1740c00d284035842e5044002d01c8440032005c03030b6110701c40c42035014190015060824000182c145200407180c42d00036000000c000310740e910780051141c11990240b500596075904d07520704540300c5512040c400d441207410880081c20203800510039050f2080e40304001d21169450101103500040706290014070b070801224015285002e500915003030250350291074040c0072540001d001c4402d400d1088807013a5403803005009504186880300e0b4072a0082d00d48032a5420482e101818100c902d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 872909226 1250 872907976 872907991
    0x84602032707060e03012007050f0d0c02133804021e07050f0d080405010c05030115031109120109050c01030e06130f140607030b0f010e0118151124 65
    0x80d0b00c02a43ca64801f58488003501a07003203050140304034014454016544154816900f0b48034004510000d039a0210351600e9545060301e540303906601c20b500340084007900c02e00460703409030703074000840c071801700350714401000160240000001c480d01c078100300400c8007982c0c600780610720501561104c152151490300d0320842058415889451a14146240c01200181c1700c0081c0142d14503001450703002a502401684150002c5c014000c60400c221110b000901c11840c4988601c103880c1401800f039440f295201340c140d8079062400c12004045007201200d15142c1c06160340d01d038980c4042c040c052010840100302481c0500004038180c41e1507680c0d0b1009800031207000c80414030f8508215803d50342e0100b1a6011040c03090b86079014140540f2400125500d40210b41800240043d074a82014a000c060b00161180c42c009080500111540202600e14220807083e0200206101540c07031078010902c0c85540d0303102180c4001426513414488030314036151103069450001228541d1449042da40001c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 872910476 1250 872909226 872909237
    0xc0b091c080702120312010909030905100e030601080f070b0a050403140304120303090b060306060a1406072109061103030a0e0102071a01050f0108460203270706 71
    0x41070502100034490300c0c00007503020001c0400025000d50100213030140025192495885a0741c611000c0242e4000b900010f00294280c1024800c3d0700d080000b003014002c2c1c0c0e00d4540c000d844980701280c43e001d001c0e08418034503404500005844141000710b040035020004085042542c4c010f40517100303000c0d50000a040da107694260050389401002640c00400b0350141d4102c119509050241c028586403400340d0f65800000c0c0001e10070700740060071038011400a0040284036141140340c1f100724020700243d6611620400146000c10700985141c20050240c40c51401842c854100203020304a55900a6040c0005104500409030022055a5001d0001030b804074142210658050086c0302e80c06004000e40c0d0704c103140452040c0c44402c00c0d07058600581d29941070100c100015509500211100107980391030901c01d10031030f85140c503541841c060715140105c00d241e040d4540c41542450041c407900407035010040003120041c12003640c8500030b02844414420002a0301c003030300c8490314010f10040c4103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 872911726 1250 872910476 872910529
    0x1030b0607050105040803010e01080105091c11030409050a141306202a010207050316020d050a0818040c12091403040f05040c02010e061f0b03130c0b09 67
    0x129410101c030006035104008110601d800d103440c208580080c010a182c0280040021401c1c00051084a005200c100014400c034415011000495050301c4501e00422200c1340e60802010010400b40000e00f00f8000b0118007440e2200350b07141103a40c1402580e525041d4403091050681c0c04c0812810640d80000c00131824482c600b844102045002031059002c1100054504074941a490301d500785a400d40e00740c0d410019001c204600781d02414030054829081008030400040000c0f000d00440c0740701030100420701100e5143c075070800640d04003d0b84c421800081000120424403061082084112402c100d0368043c842c00404901d06c00c480340d07000d1992000d1081c140401d94503000101c130098030840c1c1d901d42c0c840f0700302c85503450395200b018044c0703081c10003003842c1380e0041c06a5081090b065004243c0781d52010800030494401c000303101c1100c10a1100405d0031084800110700c40c0c101311640041c84007151400440c0c9188a6024000742d0105005001d8aa5101e03600400c00ca44400c4da45103469 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 872912976 1250 872911726 872911729
    0x507080426040f060f0210050c04140321030406050c040f0b0c010f18020414040209040201050f130608151206180709143408090c0d051f0b030c01030b 66
    0x91095400c40403140350f51100c0051aa5845071580080c03a03129426680e403000d510310074400b035a109441e25060090280002d02141c03030a610742511480009085540007492192400341e4031584070600b00048c04000204400d10465004064100d20070645503489d2134603103241e4501a2035103008903032043c10002000b62504000750040d100c19000801e04001c11100982c0d041c5500c400004102d02450802d8021800300e020300701590300c125005001184c061340c81c2d034011207003640000c40000d02c2010602c07034200e01d80794011023000603041d280c031060180e0800040e0030312522850740200e44500c52014008824010128085801030340e4070b142055111004501203003080101e8100510007842d01c0504610300e08904145809084040c002c6030b014241c0710420001e03440201d44940b0001c00404410108500c01d0000c940e1114844090358288080d17140000c12840d042d0300296800d5004101c882142d072401c2d145000d100300d800ca0304020344141c02001c2504c1ea540d04042a040c540d4585e500c441c3c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 872914226 1250 872912976 872913053
    0x90312071118150604140907090b13180203070c0201030b06120a0213050303070809010e01031103070f0f09030507031403040b041e0e01051804060e07140405070804 72
    0x841400500d16003039a1403030ba01032a0038180440d08411a003030030351442c9040d401d10000315010b884250070041000d0507031005014460f40c0150001040000d107140000b0030344100005000204001c1703080090701c0b89030050815441c281469890000e910402c240301080d5082020b0401d520b0307080c2008121120844006103090042c428014142040ca408000043c1c07541c0d40103110b0710503041c80c20803645803035000b0306a03070f80108100208501c0381004400c1c480d60050700c03808503e100500d0003160090000313108040c150800d4840c0b0001c2240302c602c01007499001002c40c0c0d02d00d00b41d40350510b10507146450700c6654180d02d100160850140c40e03200040c6107018030803200600320075078007a41d0b155900c2d44480c030100c03402030750407103203460042000c80c59000c00741072503040f201d00034154030880e00f1001a0344014513000e40110380042d940d4016030010b440a01c404e100030068103c6c1e10132030300b40341d0040c032040da1402880081049100c0b82003100298407240140038242c010030480380c55191070b4040c2c069 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 872915476 1250 872914226 872914253
    0x70615081917040b1b03041d0f07050406090b0f040f06030203040209010626090f0a1a0f010f172a010908030307171003020315041a0603060a0c05070b0c04170309031207 74
    0x501c0c0d15198815401168030540c08c0340529101a0000e10039920440111200e010764010580001d1b80c0a800700004c0070b00c98003034052a11b411440d00d1405580e608814170310711140c3d000202198010040200f0b501c0e085c1c44e032a0042900d0b043c611442001012030010103140380300d46240c00b00071000451402003082040040658981d012a40c003001d00e418241b80c0341070640912616250800002906011100000f9040319107140c1c1200d22281064400b56400600301d90401c803c2c816a262807144a0072800d0908130711401400824582c40240c000410300c490340c0d00305869560003002070004060703200e0301a40c0c442a029414107102d44030042c048410b200c145d80080d6151280b00ca440402c0c444d0303111020300807842000c1c040c0c0e445011003d01e41280780210740c059459080b107000145010003071380020102004c0303458058a4090240d46981d07c8040c1030741c03042c984050101d024082445481c4a500c45200242c0085041003403031f1000959030348820920f01c5201c0c602007125020000280800c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 872916726 1250 872915476 872915489
    0xf02071e030f0c03050607021621060c080106120209060f0a050c060c030a0507111b0103020f03010b030105180c0304031d0301140f06040908070615081917040b1b0304 73
    0x500b44024240004141641c2c0000d8555004407004a01c0040c00000c0e034141c00513426001c84019071501c4403105122041800b03032050010300c0e02c5500002555403190604480306a11122220f504004005102c3d180402518814074070400213140107585482c10350b0010741442d0a81075580c1215401100e240c01070004802442c82540300340508a64540080c41c0300d000442410041c4d917507800401c0b10f01d002d8124090060f60852003441e4089854419601e2860206040251408019110001850380264083c8004070ba0100040c052403800805050004040c103c84030550305100300c100003a0700c000342004040c400052200402c60403800307220601414002c008002900c884004010f061074201c400c10161040b0340e0001e41c040c5081d10901c130380d250b000a071150620145982c1c00c00249540e40c00c1c69001c5c1c5103070000140451041003100d000038092002040c01c03c42d1440e1284114a00380c03200141d001050005108030300c43c100603a166601c0031b10b6004401c0750300059080c1184103640085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 872917976 1250 872916726 872916743
    0x11803060b010e0103050621010e1914060f0a1e092603012108040e0702030c06010801021206010309030306030501050a091406090a0f0501060e0a0c0f0f02071e03 71
    0xa2103a25400112014020788904009407248001102210000c5451507401071042e50000161074003400440511031380c81000107440d0030840a070b039190011040c070f800f40047c03180840c01d08218103800038103070b113480d054000c4c5140e04000c1c031200c011080003401300001541d03400c0a08010822a010702d0900300707403003204000000290810070900da8001014800c0070410280390010f4060340001c40b8101e5807500281c0b101566405421404c41c602050141c0d0840418440443c2080807401243c0c01400d2980056039100b443c110740324200b1405074410100b5910500032a08151196088150301010901e00020328240f00d10b0190000c120b2904040c002e907103407004029920909074400524103003ea8140d540c40f900d000c101c0c0b507940504460780e00f1650810034000340040ca09400340c80c00d140c4507000100c2e070b07540c46c0c00c4a0b42e85c220f000c94140d03c81a81301e00548400c00e402002314140d200180c64035402c80700b003201029540740014030a220700d1080b003d04200d06101040740741307006140e110894 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 872919226 1250 872917976 872917979
    0xf020c041e18021c02062104150b10050912010608030a02070e0c07060513140a0606060e0315090c06041403120406090b030a09060507080f0112020109090b0118 70
    0x14096000380c440c1051595602e0302c2c0c60404148025440e11014640c0101003069941303034031051290002c88102c0403a000380080c0b0812400350300078080c903018480c6003507201c150f40c40c0c982041100c41d00200340d821155481c1400320040740d103e980c44061813401a00303185503035006900228506c00e41c0412582c0c1c0a500e412808151a040030008220300704940c0c1c2242c00003929400745404c0e20f1000d03180385d00600c07000c0211000056040d005181c0c0b2020074642400c031b100c50f9441d900c0b01049010850441a040080030000308055031151074080d1002d440c0001241d90003002090b41d52007523441c109400044900018140c80b0104800904800d000d040251160f544250030404032003001e400320322a00540d00e1100898013101c081e00d04940302552081e40480c64003840c400d141d8006071811042a03150400c0c100850440c1c060b003400380d2540c3e5641052481c012102c810b0240040c0c1003440312105032a15100540e82c00b01c0ba500940b03400c12000240b40000344010f03030341e03501d01186040d09030303100190 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 872920476 1250 872919226 872919251
    0x60915030a06080c0109063e0709140405031804022104060e061033080f070509030c060904090b010e09060f04020d11040f0e0127030c030f020c04 64
    0x1034080f1100c0c1c0080303540d5003070700c0001034554460602a14000814907600340050145408064024800340100c0003070342540315007103000c40d858a94960130b065000103c200650f48162080c0d40700c05c0c400c01010013050816980c0d045d2207108080c2905902c03003a0424040a0740d44690480b00315946280a1210f418811150a000003908440c2580c066140c034a40714981c0001140d8188641400c0d036981d82e03480d05008404030010410019048142500740001e0340c00d82840300440712040540c2c85002e458509401ca02c50428030003002030041002c03d201c01c9003d40c40000725840555001c030f607410f4550342a071020900403c3c85030000341100d0f04031000011840e5080c18403074040c030003a4099030941e0762041c0f5004264035040d84c0007508001d489000f900403401c14500107046c902c00400102d140c0c41ea92669038140c4080c08481c180303503551042c02803210101c100349010750707000c20707000c10b0000312068801409201ca00d010260a000d01442024400d41c401d0000d002c41d0b410045c0200030720f084601c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 872921726 1250 872920476 872920481
    0xc151c0615030e07062307050304090615030905100e151501020d0e030a20280812030402040e070b030c03010f0806101e030204090f02101805060915030a 67
    0x1e00d0394010a141804420b400000071a0301d005851031074841001c0241c1ca2207000c1d0005801500d840ca4402e0188001e10000b035042c03005000608894901050b071030304280c181e204003007080c08054145450022044001000813424443d403000d69070000824226003020981450390344841c82183c0f0502c0010401c14941e400d12003c0d600c0402c0e070840c0c1d41203d00d440c041d2584100c940b102a4564410000780300060b00620408880b00d960140c0300c4101809a03010402c3c000540c1615540324030151031904200500d107841070300800a100003840148450a0b5180c0e0710301c0040c0020740642e498400c5401018410003540c0c0c014545100d91999900d4409c5954140340c0081c0500d81010079480d000144015000585600500b11622200304070b03860010071403e90701031040c0c051400c84c0440000409039445106951115000d540110309040702e510400c64145a0112541d040c804440b40215010201c40c00a2065072001c0d43c0c4241d0b500b03004000580b500020084410007a01d0000801c10103a043d80c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 872922976 1250 872921726 872921759
    0x18180501090506060301080705100e040504030207060807050f070615050901140405100e060f01091703030906090a1e02010201020d06031505011401230403020307170706020c151c06 79
    0x340701088076440d41d00812030030384420712030882541e012600c28001c0d480c14034803800c802103070ba00f00301200006641c0031805a9804490507800343e00300320010009590400a40c592025142c07278228509032940140700c100d8060300304050070703440d07a0f0721510b001c10f483d621001004e400000c4c0a80c0712980d44140300c4101c3c007628030040340582d0902e404120cd0181a400c1d00081d0703100d84038144512350b00c020034004a141403810660410510302d400203140b110300c1408440c4d400400c40a55928648140010720346000030f0481c031103d82c0311882403808105180c0341d001c00c03441c0102003001001c00c50300040b80640158940300307810340d2a0940002c00c0201105a546540070032410a0020b41c2ea02c1e00c812001a1400302c3c0039002c6110004c803100080400d02422011881180280e420a07899401092038400300e50054009016448211352510303000b00300380b400a000602c014124030b0042e03000b28101001c0da2541d569148004500d00c07820b5441c0c1101641d082412001c100b08030b9170381d01011506103001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 872924226 1250 872922976 872922989
    0x12180e0a090803090f1b090106030506040f0f09020118083310060e0103090206030c0f0c03030408040f0b0703021005090c030d020336091305010f0c1103070c0618180501 74
    0x22015007400310906c40700c0c1045000f000a0244000760310741b078004d03030141100521040d8480c0d0b0307886076074000020900ca406c2c000340144030001203802840c0300150003c030602c1d00c1d11000313044c507001c1080710500010f441043c14080000e5640b00310146001c80244612a100d05101c03010030780304019030710b04110015000c03655140c4d0759200084101d4015011075201400180d08200c2c20030006204545803001070148034940c0c0d803a18585000c000500d070450b0001e80d804c0315122000502084031101810040c2c0103000700c03080e06890114203541c003a41c0c650301c07410302d681f0154984001569440c0103002503200d441001e400d4408600350018001d403690710401d410810380c0350030b200d803000d68074a4217240020040050348000038004000100107000c1801003500c80c04450501d01070000600078002c0e0314070300c1c041543c04504000b083c140a06400c04441c480d204607031041c000c134030100f04584902421140302d8201040d1590480c400e00d083c45002c0d07003002e4401c00c0111241440c0c01459071002c0c0c100c581 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 872925476 1250 872924226 872924233
    0x9080706060e0f0a0c0e21032802030c1902040615030c02010c0906050909040609020a030b060307150509010f0210020403080405100507050a1106040504050a0912180e0a090803090f 79
    0x12603021800840314203030421700c00079103c1c40c40301d07515050a4030302d58134400402c0c40009107440300e0540365107158040010107084d0307410345050840c6201c10b9060760b030070701d0118005103003400b82c00307100d00b070740c80e1140da1503165402d61000c01d040640d15140c1c80480513214590030040060700c0d072000030307010f010ba407050780006600c1c180b681c0a03041d1007003517450306890442d500d00f407500801e1030400c90703e010301800560707220360b036001c01c0d00060b41c40c060311900441c031402220240f4a03080041606005c095803200481c01d100c0e075103003408107a0003800c40f01c0c0b035142402d04151030982100202d180c445a01141c0242520019000c4180000300c8094011118221413411607245102e0b030444090050000060469001018210000324038070941041490040c0501c1e041c25501c1c0300290a494040e10b6812589548000d00c00c140030100d20410b01031045410304404203428040d80045c00031052240e280850340110200790f6021090b0010900d55030452107554036402c0c66a0995107800b00541088064403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 872926726 1250 872925476 872925481
    0x609100f1d010906120e01020c0a03030e01140c2109031806040302010503011716061707141905070b07110f01050f0a05041b09240308090409080706060e0f 68
    0x64500314075074814001a035035a0085031410f04140ca440792603450161131140c07500810b5140003000d10151400e0490300b4002c00200c0020309003c0d007103403650040b4100b2030741460000c90844005070340b6240c01094220950365184d00800440c0d00300f22615204481040c1800240229040004040d11038414820081a40620f00c801005400d1059100007400b0405c1840100f0103030540030f10001c030f510418000d584941c5007800040140c203110f40c000c140800c2c22800c00b840070a4501c0c90160b4055254101031100c210180100e03445406000b080f0314a10310314005c2c0015103031050040d24216070703020540410500b0039031300140c54580c10188a4420340b080d0500c403490035905004040c0618031203d0608010748659034000c7c00743c0740082c0700745d401004504407000b81502030070080009025107603000402200001902d1412105000d40003002c060805091006c94007000441d14904c1c1e0403500001c1010f1f0504d401c402e107000e601d0740036003031920307081d8001001c080900040e440b07010994100c48407176 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 872927976 1250 872926726 872926757
    0x503070b270609100b0111030d09030e01051c05071205090304030501241e0302030a03020d0206060f090105100e0d0305030103170301060f082e05030c0d02090705090609100f 76
    0x30502110f403c82c1540c440c6043e0000c049036a0b104502240b030614000410103a200c8540d07183d176114004000711156607000b41d030240350b4041e414045450091070128940115000c046603e5410109000344e06507845000c0350400780124548c144000144034144480e29102e58050b449030400d20003503500e0b5003820041000c0d00182180051880990340540562a0504070446c500411004403c44541c96283e070203c0940e600700092071186100350300400e05442d07803e030000d040540107000c00b0300508981401c11600d0b56903104007415140b0542d102542440b0454084500c5030302c0b000e030190010381d80c0107c1400d041d4010000c2d41070b42c0c028040c0410340a202140b5280601c824447c10000888820058a200d803050440b0303900100c0702d601c01b0340c0300d641540014a034138482030305d001c0e0010381307246040015060a00c42e2614068080724031483c4800c0c160041030030b20784009d01c3e4004002e40020700c00510381d6448140ca0f4100005401c101035606013000250045107040c2d908030106042e00000c0080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 872929226 1250 872927976 872927983
    0x6080a2f1306090f0e1b120601020f0616210903080f1003080301030f0f05010507020a0213020315060a020f031c0f060b1602030304080109081215060304020d0503070b27 74
    0x464800036136901c00c036450445141030080014101d00c0900d4681104010388810340009411811000c0c07562600504210f00060b18150407200480d1040d00441d0030420b01003030171010886060000e060038081c00f22001d070500d94000c0c1c001d0451004602d4200c0700307002c0c5039210b4074041c0301d5000852056180d4548042c0c50b900c6091612005015039020401400041d103c10056407030244244000741501e240c03640c40fa820f5030022504240164088449141540340c5410300f0b04408107140400c501d941400c14258a0b64210320301040c4c0210313400208c10b0104c0d0b01c02c010500c2880d05041c1a84c1e2030310066000708840c0758a0440590083e0b040c040c10410f030b040203110300000c41c0c5445072030b50300c0c00e5491a040c1c5030100c2d4001050381c0c94041071000088184084c0911001148142c01c082c0d40d507955107031110b40360b0700050854401c100c00e0514103c500c0d04c4840480740c01a0f012100388403420560f01d0602d01e103200f0414000c3c4461514824400b07001900842d0842c06c4200c4072a20740307121f112104050b035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 872930476 1250 872929226 872929229
    0x80f070801080d03020a03021209010203071b02090106032f090108011d041704030507080105072a0f061d0c040b0612150d0803010303080601090f06080a2f130609 71
    0x1894000781c407000f10b8580242c0c001e0101220609001d414054952409100d00340c003161424036594000007088121944140344030194024600481140e18040d00420360a500500901003859034900310072050703503210f03400c0700e002031809051164000080352007a18240c110002150106080c000041001c9103848100c4c4000f0710401003013521965551261150b20610680034078443c2030400001c40803070b41c24080e04018042082c0003180d46c2c1012240100302c1c01480e041e000302000c480040320010396203410007002460300846076806401950030000c008000801040c1145d500500c0c250160307050110b0441c05070801110f0070404041c8101c1448074034880d80b00e9070b9841d01c3c9860300080c0c13200e11408035910300b00d00c081c2c203519002c2c12039a20300c000e0f41c0c8285c1007900410700311410012190381c01204000a001202e40729241140380910143c0120009442d41e4062621b5101000c0c3d040404841c41403840c0c81c1c601e136822a620003040071529940a41d501014042c00e49031702280703080c0110700703040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 872931726 1250 872930476 872930489
    0x31206010e030607030b0406090e030301180203010f270906050708281509022208010209060f090d0c18051b030123060a030b0f0d030f0302070201030605030d080f070801 74
    0x11103680b0070134200c00421640d00001da01958941c3c022a8240513482484030443d0940c0c010f52341c07541800d00002c940c0d188139541c440e24500410040c420100d00408010490b900191075040d8201010380084800c1002410040ca07140380072880424415550007882c018081a156000319454803004407c88900e24580c030345107a186000a800d07905590341c000125900000d40496610381c45109040c2a40e02054201180420700a00700780013502c040400d0008042200007180b80600c9000414100d01035007880502d01d89010035602d03107903158201c4200340386078080b54540c0390648894009102c407402c403280092103450800020182c14a1280700c81a00d05040c3d0072500b50b07071070400840d102c01c17202030319100c0c10200c43c1e001c0300c40c54880344060400030137203460105001c0c43c000d09226800e480280c60300d104040360009003000c00d42003088150081c81900d009a500d4155000503000303802960320035030700342c440c1c400501c8002da03220194600400303090710b802c5425110b180c1c007203c02090030301a44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 872932976 1250 872931726 872931733
    0x110904080901110a020a06031b18060c060f06030b090f060628030503030115031a01090b09040212010923090d050a033903020406080a021317031206010e03 68
    0x103000c1d5601403a108103c1c000044126041da0b140c80e40031911050b99a400b150200340c85403d106550b4801390350740c1851190a00c1c0c01c90f42c080c10412200b8150220703206800c01e0005134440f050501020360800c208080d4503072803d01031541d483c5000b800c102401c0b55002c81501440074403d8540b480481d040b4018a001400d141c418540081009d00d50004109440440f0501250000010350103002a40c02401c031000c0310802c01c0c41c00034006d400c1d5920b910600c145800c810011184581c1c0004420040d20700640003591290005004200248155420500d0401400300001200c2507103801c100c2d003502444034544416011140d299000c14804e603440c1540e03401030408400750134815000b50030740c04201d10b004150110761402c4400b441410280d00343c03824510b40190042d0f1a000b00465001c0303202444c04614052920000605050000d401c444489400003455a411240d0903000c001800801c5030701c8000750b0718604810b58076031101c42c4107050150220001110340d030180205070160800a00607 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 872934226 1250 872932976 872932987
    0x40207020303120c0c1903020606060a170a020f04080c150a0c0b0c0409110c0d140a03180203010507120c0207030803040201180e090a150204030f02190e0c040311090408 74
    0x140410000010040201d013002808014081c1c03004103d014220300c40302500b110f80b0304140c20700a050400c000e10f03e0f030142c2c004203c00c0700501c4e8451180400c00000e10b50311601e58680c405c034040a441007400c44500d43d203000c5004541100c010403001182e05080380d800511105080b03000c103240c090002d540005c9006c0c00552004110b11042c03096221403100700782c1d03180c40d0f103440004080754110400541007503c003262a401d0b81d0400c008410f154401400e2100982c05c20900c01d907014170075402c0000416445561220301c8554110850041d560b00400034022403804190040c0344910300707a1805410ba0400c0c5200c401140040741c00d1003a6500042c41d5880d5981315001036403410300c1c07142031000920f8201c400013400040e0b2811107000701707500c40180c10b151005003048003160145c83d280504240c41040704100160401f03032125001c41c0c1c10380354074800031102c81c1340d8200720f2040c2d4040c0403442004c034104448006040000c10a80344542d5401020385441340520812180885004204801c00c101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 872935476 1250 872934226 872934247
    0x18110603070309061a1c0c15050c06130c09060506180f040e03030a0b0f0321040e0103030201020a080c090d2018070207060f02070b09040204120c14040207020303 71
    0x45500807001e04010880030210303940c00c0200e8a000e0041000d203200500d036001545003003401c104e600101c010403540c411460b51200e19885d441c030f01c1000761116045528000140c0190140d51003a11110142c03406494054128003044040d800101c511402144001c0f440081c284141400c1d10300240480382450307040d0340800786000050f00d105a0050b02c581c1d401051380d840780a0900d1200501014645074106180d2a0041d04c1ca0003540c00e226410340b061100480d00c0004c0d195402003030121407101003c06403180a1000e201f150404509069035600110130b0540540081440c012a035031030b140695070f850442d4030b490080440540d800100c2289020205102da922030448884165040c0950300500c40000c02e640341c034a1003002054403520070410800d4050000c81d00415403401c010900003ca00c03002074850b916800f0b6242048130210300c0360b425031500ea041e80d01901d080b42d110101b00c032603030410b001c2a030070340d100e800a84562800000305030704140c0240d0390034030b038003800550410364600c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 872936726 1250 872935476 872935489
    0xd051207050d1a0a0f03050c0f0607020901081f0c0f0c050309040903111606050f030a060302280503030c15150d080d231807150f02011811 61
    0x500340001c00c4014030505005070310314414444094140041c1404945150f024400000069840008260b000d06410004100081020030010f2012078410f80010202c0000440358004c441001e900f0445410012865440000d43e00712200301c0000d105a07c0c040d580080c0c000e4400070804076001500a10106408900804d500c5d4441da1181c0282c2c1e0802040c0d0003c60215000c00d0300960018103140e02c0d09a12910074000d489000303a09a019841c4e4504203100074059101e2001170440c490000400210000115880340c4003940c0d00900c2e91030400c082810103480846aa01d40f90a012101d03040002e49141c0001101c6c1000255406816031200d03070655034003524002000c2d91100c0707103054142c020039910682981072040c461f000081d140c25141c01c4a10486a040c0b40000080381909a440021504282c0b1594801c4101c032112003944042c0707041c0c5040100592080100c11001e0701c1d40c1150740c1e0441d01c0340301504050b5008000104401c81481d40c500c40f000d42c0135262659507129030109007070a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 872937976 1250 872936726 872936731
    0x2071101080402030a0816030e0307060c1506081c0206150a1205011e090b10060c020405091c1d061c2406030b09180d051e04030c060e030d0512 63
    0x1405c1d511408251b0f29400220303401902e0060300e00d000c4c881c9407010541c01420075003141806070003c24140e0300703155025190046041015000e466a0499921011a42c4e04643c1c0905082000e640c032441502415921185045840002501514001400001a00030002400a030041c07420790020701c0c101654040b0040e0315410380e0255215421820b000310003107160360000541e0303180001c070200182404ea54038100900090b03070900b048032042141c1944071501c2659282c04580000c0d0755294140020b144c915101c10002074619221a40000c141c2c0103040c01000b10340d81c018650001d0101000c100d80d03031081640503050700400c68880781005070a81c0c000940303022410801c0030002050441d0340c4c0200b1255200d000042c0c3c84440c20081401d00183d01608818002d203003440b9960200925174584002c1010a02080004101d0007034840e60074841d043c10900c5210003030740d2561a4102980c00c2d02281c000c060100390041160101400c0008407205c60fa800b90f5251410302c60300000080801801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 872939226 1250 872937976 872937979
    0x91d06091504110910090e0a0b01050412060605040b04020703050f0c2803030c110d141e12010b03060907210e030d0c02071d0604060f06200102071101080402 69
    0x210040309030b81c81d80d104160785102800000c41d242c164500400680c1c01c0325281d01001c021a049040045241c4000707101d030049804000800d42d40381c560012110f034003956114201c4040c421a03820180036181d80600107881d01520140160070340d403010300c0107900c600040100094000c200300354913540e189000c1e200f61980b01c0180c0d0b915074440740581c150800b108500248211001c0c1840e070426806d8070680310703200ea0508102c03008007940861207848560700c0d00580c0500030004002150906600112440342086180c5403c41ca02c032501854015000360303041400405040001203410a004810340b8071503140241000d01c19590303150121880c2d24111441a40ca900003102410200d889001d4640320401010085071541a06180501950f2010b00c0c8070302950044041807107042540304540004c180341a400742c5942e200c03540860000e00141e40115100f000403207003c0f440c1c40e840364400c82e40907400c01420000c1460103194508074450b80000070001d41d0010100e8001d540a060303950b901900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 872940476 1250 872939226 872939251
    0x1020706060608150307050904060507140d06030507050f0d02210307030507021806090a020a021207080307120b10080915090d090603060308090603280c091d0609 71
    0x12503031000181c541c1c0d03030030090110300c58400308403003140b100200c1400d00c04120300a11401c2d181401081c215407014001030813840c0c513203001800d101d0003015401d200c2c900f4042ca5a0382c40b042c004e4040c008081c9800100c855000c1d000000885107809408400201030061444548181c0c65081001c600a5520305007000f0110100d6881035103010300107480042e02945410b0b5403075540340f04200c0c040a00144102e0900851024000345440700d00260354000604000185c0c2e403094020140e203844491540392408640000d1002c1c208480d4a000e94000c404943740c2490482200740c030701e811b0b98071114650760440c52510954444620403000329030040c0c100b07415159400300f8084100c0c01400c040b2000c0344107910000e0214007655000da0b915000b4040c0380380c03c2000a007156100380703075845021380300d502c61780c400300105030040d030042c2035885211860302d0000d02c0310761040e00760300280407060200c101242140f0000210511440f603501084292640000300c6581e514041018002015081d00e00200c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 872941726 1250 872940476 872940487
    0x61b0803071808060f15040905030f0403030f08070f050307090b0d05040201110c1c17040602060a0501091a2b030306092304080f130603020702040c0219080c0102 71
    0x428660085009411a966641c0d03034480b01e24000400a0b4541d0128285074490400c100d0600443e880c60750b00810b039040d0b2016600059400030380900440080584507000002d240c8014100132001402100d02c20388900480ca100d5000c1940d00c002e040340d81001140e81750028001c418420070046034810483d040032140340e03803200c0c6980851340002c1c0040c11a5a030f0307102400190360300000303405600527403403000f0100c0070103038400b00c0c022850840c039800800785803516440c100b0001040201e202c1406600302c1303441d80e07940c510095403a407003075400d448003c2c81d150020072000440e00bd00c0402c907091041d0354940207100780c03d0000b100030841640e0300305d8034044020610000e420b038039085010301a580200390076040017925002c545250240300101840f8541041504112100d401d910582080000351203c049507201c030081d105016141c0d00307a41c0c0c90340c03012860b0740d0541e000d0600036000741c4040248c21750610701640c1e514800021410f142e80c0030f11410700050b0a4000520301c00740070400250420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 872942976 1250 872941726 872941733
    0x9190c0e0405010e2a2e20030f0f03070903020307270501030b060d0305070204050a0603151a10050403021c0b0903030c0d0b190620060c04061b 63
    0xa009a4045403165100c20300769030070300010080f440d80520390025590540080d4540c4d0b550350240710319041d00a40710314480d6200301000398102c030405003686c0e205c21107503004800000c002c4107664000e844090728008450700040310000550b0711031008001d20703d1038107404c1541b01d0210740008120b03904214001d1404030042c1c80030f01088004200150600c4030522080c5072420209040c403a071140f03c2d6140200400100e80d040400b15002101070303a140c03c0e6000300d4182118a44100100a9000f504007400e0010078504c0d42d10030411240100d03000c1d9040700300d050300d001c280c0300804410341c1050140c20124038a4901000789015285160078024540b9a490340814150340c0c400d00940029050750141d0030034410001103030b90340070070104042c5145141c001e6802080740100d020240c9003558401c04192107807100464011400307024840101c1c9181ea03010001d001a80600c00e40c41c20b0b912070b550000785204006004e034000c0714a40c1d40701d418541410401c40340ca280c0320010110903400f249000c40407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 872944226 1250 872942976 872942999
    0x41a0f220f03020d020f190809030a240605030f06010302010e0112050a150f0b07060203070504172b0215281b050702031f11040b0705011409190c 64
    0x8081c425005040307000791141010f8140b521228014510341c000707544c004c0000b002e06150005140e84408803035107461001c0007007403500c03140e2f0304004e051320702e55031841551004c1c00d4403c6c44440c01d85c440501c0469160424103403250030000c03000300c0e290702000041c801580203610000569a045c90300b181d1500406d1a120250390301030741c00045803941c0d080d040c040035180e2040e01000d012008240482035207031000300b48a0303208250740641615030110120380d24038400d000710382c018680410780c0c5080b8803040103165240d03440840c601581d0042581e101c04075420303400095081b0540780d005040c00e1100354030b0037100b070700000f000c1031540600f408414502d40c0c000c00100416082c0e91000151b0072800000c100b102d280c5040100003802410b00c58203005030740010f00e00f021803401c21040004841448414030191024848000d01103201080100d40e030025080034002c054007a2009204a01a001840b0481501940c6510f1950021142861541030320445250b0340e5120341620403080ba03507510307082c50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 872945476 1250 872944226 872944253
    0x9040f0b031b2b08030c07020d051f0e0c0d140d1e020a120f14030106020a02090115020705100e10090914160f0c0f0605041a0f22 57
    0x1211400700010b031241000e0500101882c0741c141c0200392400e43d00407400c01c03600940c0c401442104000300040319406e0b1364050301d1809034081c0051880880074a0200c1d00c800700d9444e02c101e0542c040f6050310310310b4031030302030078400c0f0208201400f9030112020a11050506081041e1100e000c448a0a009a2000c000c403011042c032640e101421004a042102205140460401c2c110350181031810301240208107020b10b10040c0781040181d0341301020040e24031343c401075800b040d01c03035011000003060f41d00461101403442c4203c8280707100b40e807141041001c582166000c40010381c08600107100d6404c01d050020602c0c100c500700070f03c0c215840000645400c54040d46d210000c1c00199040148000ba03005111100c9400c0e0034074461403815650100c100d0307201411550422400348400703901940581d403414078098000407410003001843c00c007a005030100381c9003180c00d020f004143c3c0300601c82d14038150b030140c04100c549009540b1101400ca0f581c007103000c0d0000506000480c018006215050b0015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 872946726 1250 872945476 872945503
    0x1150b030609010b070302190f151506140307030c2304050f01020307032f060a0207020f0303040b0301360c02060601090b041a0c100207051b0609040f0b03 68
    0xc0c0d0324074211080c0720400c00180d008181d100801c0c084900001c2d0003080c2e0002c50050035041c0240702c6903c0c04c0800c014166004007904040254034001d15008140e000304a1a0800810242d8855640c17041112100c031042165110b8100500c042003040d031090b044280e450120703241c8261903405080e0f22184240d580c00601d5403003600090100407505040300030003081042400518201103454034080e1a0181e415000a03028001951995181c1c040314680900541c2442c1102c0d181c0c6400700981c8001d50202c2c070141c1c41004180190f111503d800400c65047d00e0140c88520b0441e40780c00c4515072150040203c11526048030389032030540c01d82e0b040d1401d051019080c0c01241080184101a0a025000d00100d0401440640500450000a04075022200022111407034450545103036065030240c0c0c80c10740541d0181000c0d8100003440c41c0c002d05071150185060341c691200a44c07451402c030318511030369a0403a50a01002c1c2c0903280581c0446411100030b400421180b040d0000203090020600418 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 872947976 1250 872946726 872946749
    0x60c0903050d11150903070303050601020f0f0f06060405040c17070b0c030a0e03121e0d092108150d0201030609060906080717060412020c0603010f090513110d03020115 74
    0x3c804070038040008900e2441040fa00c5841c604040201030348a20400e440a0241611140403e007142d10810140703c50080c0c0f44140c80744401c10646030381d128201854024404d10031080030807200d140c940300f5503004a50001315003421074034202080d45121190f0302e1104140c041e9900008080d55490010074500564002441da035034a016170141c100180800402e01a92000040f004200c011a00326190034486801c551203500d65901c0f04080c9115100b4098040b40c1042144c2040005841d080502c1c000c490765448030942030f440040b81c490304116080180780c100003610900c9814060700c0000c072980180740c00700e00c00361503509103004da4a481d801800c80d1655201d0810101c901401900c015042216a01c419500b400d5a26a603a44000d403015004820b91051081054000c015004000d9000781896403217681d51030011100840d5445010401ca0502e400500c105004000441d1015800f17209011040b40340c2081c0a092100520120152340d030318824150644880d201c0c2000411900028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 872949226 1250 872947976 872947997
    0x604020118032111390a0801020c1516080402010c1a09071e060e0604030507180e0a0203120a020309030604051c0507030c1e02040507030c0305060d0f060c0903050d 72
    0x3000d454003040c034250950440c900d00202584880e0307502c0d036010003584200c5c00018a40040c882ca840a0910041e4407060441000502107419000761900b4145d400a98010b00256401c04004840c200d90b4680c10366075507200070b43c1c046d002e82074154001c1e006144c40e601445a0356a04940c0030b01c03180c0044c0c0041e807041c2c10010400800c11031240a0300b03030a00d101100280b44048c182940d00b150041105002c00d11402201540303613001680c00460b0070008030751036141d45031820030011030500a00604542082100c002c3c80d040000e0055840c0d5014004020420241d5441d56817600684400000c60004100c0f03400296000c000c1c0034000c1c0d01410140002940c005072070185404845504414040240540404203404c14a8014041e0f0000c04600300155065803071420200c84900c002c0d800f5141c1400d0244c1aa0b150340050500f1401e0b44003003025072610f0f01089100010b262004107060f40c01c0000d2400506240c010700341c031064074105003070303003030b0b1a9030b41c0e18109900700c5c01007400141c00006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 872950476 1250 872949226 872949293
    0x2070e01062606030a081908161e03200c0d03060b0412030504090903050306100305130f05010b09010308070b130c2904090c120e060402011803 63
    0x50440c0101041e0804062500c84031007100a2585200301e03540450b2514400120962010b1103800781c0140c0c0460004d41c0c0f0101001d050411300b15207140d1100141e81d1300b0005103603420011401d0101100c94a8118584003000c5211f0864259400808101b503201c07054003003071080c0038418059040c607202d4103d03200d40d60f00c01028902601c04607900c04042c1007040401c1090390010459050781e01d818449850309849007019541446198841c1c0807042c500102c240034190300030f0145000e80e05c2201c000c1d152400b010000c0301600d00a07510b00000f007a0310070780740b000a010a04014495840741d8008500014240005446c46100341c3c000e84e501440051280d007001294685a580030305511206203d01c0f032036484040d403c2d042c5000742c21000d88076082d034001c0c4502e030305941e414803132295030102d0759640c80719001d8014041440d072450214941c49000914903e103402000d1a10300d2074402403407235554075001181d20001011543c010800c2c20031012012070111016075503880002c0e4200288a00c4440c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 872951726 1250 872950476 872950499
    0x150e0708060f010e1603060f061e0801141e0a08030a0809010507021e0114071e0c0f081b0a0308042109032d05070504050106110a2904030207 62
    0x10315584500d040d00b030061109505280e003050b0401c1c009403010350342110b8070780190010312464101448440561400040e0310f90310035042d80c2541c845074190b21000031a50425104440203009490b09440074460107259410180b009440c6039a566035001803440d000d0012519440c6290000c5002e07400c001041002d89402109150708150a600208024030302842c1c0251190882c490410040ca10000c0705806004250000821425284a540381c0350418110250010b0280720800780402030f582404081140a15882a13219400103100b0080013001d46d01d044c15540461600b000403107690b512692001c02c200f24601e5654400e072600c042ca820a403d04000840d007282c01a40e00b100f40c840b0300201d080e071240c241030403213901c2001c0040341b0105a048200340d44418600c41003001c0341c445150180000055200e049407400c4d1070802c00d40c0d8039410112003070344946100301107036845400c02e41c00040e40800c4a120f2003040c00c6851180c070700c01e0452195100c1e4150b0f82030340107a00030b040a00c080d040c03c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 872952976 1250 872951726 872951731
    0x301080604030305010f060509100c02120609010c02030c0606190806070323071227060906200403080a0909060e040c2102010c02030c090103050304060e2407150e070806 74
    0x81c446c51641615005000b000d43c451100600d014500c0f00010702034241c000d140d001c80c5180e009043d2180314401c1100c040e035500003220460255800d11b441903040c2400401299440401d880c083c10b90380c0e54800900030b01c1d61908a070100f500b0048200015015010311880740210140c2c0d80c0800c01502c114903040c028003080504440240709241480308058010b03940c2c40c1030160101000c24a500c0034845100740001011068002c2c290305003000d0308201043d0710030004540300d282c0c1005008149041c0c6042c51030300c0300030ba900d8001c00708414408280b0410192a8090300c40c034091039010344503100501524810fa1020440c00540414442003101050201001d07090f100c40342c4c2d01440e0740801d102280110b001c0068144506040c40354250b440c207116003880c0c0c0d00054500005035942e803424a82c0e0780d009208032400a1303045810480c0324a002034007661148146c0040c41084101e241c0c000344140d004101c11107040504880c2c03080c0200407405102c004426030009800054a408040350601500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 872954226 1250 872952976 872952989
    0xc09140109150608060d0c0806011401110604030c030503090f120c0d171504020408030a050c0f030c07151b051f02041a0f120a0c170405060105040c0201060902030108060403030501 79
    0x481c03d01101e030b480f20100c1e600901c1214120b407131061504140c0880a0240c01c510f6042c0501742c00482c2c403941c0c1003000f2100c0c83c82030b81c4440c900415461951749590080d00d00070002082003e10b44003192285002d5038202c109031069030042280c41c2d081e1032500300c80e0700c0500c2c61000e0100d442c6200d5a4140f103540c8004505080c11000442110407010400400038414251008414002480c0b0344466050794040c0000e0412a40e407040d5094004e03109800c4000000030501c02c0c01040300840c01c000c400d0f40c4038081107600030b26403281092845a070380c540201515080041c0034511943c02d440141807030b054540601c000d000100c800301c0c8070000c007206030144901501c0c0100010400003403c85100b07004001c1481034507440301004011003506100b81d090070300a200038201400481001c81e0320190425a85480e65180610b10100c003c60075442280c0180654100c1c50040004c0d00b402d420502c003e52030b40c40009155a1121000001c82c1c000ba0440340c8658400f004000406801d440781c079000d00b61 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 872955476 1250 872954226 872954261
    0x30727031406090c130f064a04020409050a03080126031b07050a090e190302190c051e0301060b090303040b0906070b0c09030615010f05070c09140109 66
    0xd00503039213541c0b145100e507442e0040600c44540c50340c00005a116208840e480c0740d0a11031203a4958007601350180030350340c00b440c0c051502100018240c2c02c04118141100c901e550007400d6030360611a2041400c014800d9811507220014000054010f00c040c0005e00c0c42501c9000302ca50526107139021040da180c900c003000049280da10051880000180c4031821425600380c0070040e40025150f090504d1a0b01241e001498100b0100c3c40d0b040036080204081000760890b2404152004440750382d0700c00d0400540940c11000c18540d1b0b0100c0c0c405140c1285000710000c194040d03942e40440c14400f0318165080eaa4694100305845600c0d003805200010300c90941c44030b041c00071150003e07842c1d10883c401c0b421684c00028401c0555201d060603140d12035005015001c00c0d15000008520759801404007510a004a800241124004902c14420300c141a0365540c003421181c0c1054425610100d02501c600100450000e07030840103004054011000c10003595041d45006045010799101c0740c000c410707454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 872956726 1250 872955476 872955481
    0xb040b06010815120c0303041212050301060c02190b0c010b01020111030f1f0503010f0c20032719050a1d060409020d0b0406151202030d05030727031406 67
    0x1d00780d0f401000c035004460441d44480341d400780910b0001e211816603014000402c0004110350a400d40420450141d400302018103940f1100329405d200034012080420919050300c809410120000c40d034005068451400c03c0b038940791004020b03040f011000b48113a468854030047d6503420b0242d803d0041001070341509504064001e00c11503030004140850141e10703c001e0165400d02001d02d4070052502900070040c0710030804226014111603040d82c00031910f600c1a02402e4131502241d8056441000c000d5801c05908817082540f00c544120402d084002103408880c0070ba03219500200c40600c3e059080c240c0c246084144034050160380c0c40880801c0705030041211500c0407010190380f00030701703e90001c1e59649a1001400103801d00ca8081c000c1c40188082000b000300a600c030815419280300c2c83e2003d80d40d5142130001c00041214000d400d900500d0160707035143d018a002e103411100a04009401007070388020b0174480e41015120b540e001d10034103420400d0200703c041603800d40d00084041e10740c1c1c3c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 872957976 1250 872956726 872956741
    0xc0c1011090f1507030c0c050f1e030102091207090e0a08070308040f05101d01060501021005100b030f012c1308040b2803090201020d03111201030b040b060108 70
    0x180110010399000b4400c8040d902c6140d52108821401d40140c92140303921110641001801c1780c8020804032011502510f0100301454685103003002c0c01002403140c510480750160307500c8243c5090704c040e0307010364080c041c5040702d0341c03000116154501c07880c00500b03001d485c01c0c0c42d110948641148030101900103141040104034403004482075903805081540e2503441e0751070100310600241502400e01d009038032121044181c10b811081c6038000c02c90250070034074506502c486c200c0304d00740310725800b60f80000d00e070b5a074540301c58100c55480104d0030134801865a0f2111000d4003507104580d210f2041c3c855030010b00010008101990b0707152523101b10400303001038250000200ba40301506082c401300d2030320151070800030f2030f10441c0d000e0002c52080b030340c644e0968030101d243c3c10102000c00781029059491002c0a41c0329200d80100d0a070140c0c0100000e107440c1c0d07020340082104503180c514050081101401c03440071f0302007180c000c5200b0341e210b00d51450141482122200050201810012807205100c1d11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 872959226 1250 872957976 872958011
    0x60209150c07450c030c0906110d030518030a02030c070902070206040528150809030705030a0c0c0306060b070201080a05040201080606090a1d04020901080309060307031d060c0c10 79
    0x1c0060001c06810f0411003c84002c4403600c05400740e80490810070311507440e0341c0c142c21070103a0340040d86808011645074681900c541d122006254903a40c0300d400c5641030b10340b19820068001130f141d031401c444903210115071400d59001655040c0946e00000d5020b004050800007800281202c500450511241c1d0380003903068491361140c40d1040444071025080101c8500620b612123940f508108500c9a40c1c045a580324506440b070303000454045800240055008000c031000254004003851402030000c7c01550481c0301c0e900c0c1170f031700480c1d00040400010600c0c40364501414400035115113440491000508407140244041c000f03509010601c001070360030103566a042081107507401c1d100c1e149640840c0140d00c2c10b6000b5a80310100c019010500020004c001d0301481c0291030320700c4140e8940c41c48641d41d10030620115006603013007001901c2644641d021642d0301c948410700d640e06800000a403490000305031407403100f4040001c0c1940c08540c08005125200d03e85603014400300d0318105c0d41060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 872960476 1250 872959226 872959289
    0xc0609330302030a0f1b110102090d06110d140109050603030a020a03031806090c1d0114010e0a0915050307050f030307080304050a0807030c06050114030a0f060209150c07 75
    0x2410303008004240c2007084c5422080e01050b100b41e0030007443e842d40e210070711503402c001c420801060a15080201900040c0212220040082c0c0120803030115036880b03100504001480c14010207090004000100e903a015914a01104580c500340550509100c08200c4201605481c0320798020451806550f8002c03a05515190f01820001081e1070900f100641c0a0700200c401085a1700d090162410441c600d08040203403a905c141070040700042c0501d0300e4001c2c4007030080b01400006001d0b0300d511503211307400c0b014800f0006820500021740e039030802e030142d850f0b111010300f00080c0b4150910180c2820404c00c0b0040004030342443c00c44104102081e1240705100000d04546c40000001d81840010054031070740a03881044907a4808084c20000c180c1d050b00307002122081e0a040000401c4c0003a90604070045400401400b1222107690f6000d420501d0034404581890b001d020b60902c5503074480b02d07a0110a5130f080c820383d40e6240110001e00b0145103401981603003000b4103046070b8150760040d100c003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 872961726 1250 872960476 872960579
    0x1120210110304181a09090715020307020d0303050411011806030216052d07030c0b0c072102120d05270406090207050c0d0b061c0c0609 60
    0x6524922020724218822508003114002264050f0b00b0600090340c0700f10340f5003c5842601c641401104104200c00c1030581e1040c541d6442204180180d9010307016582e090141401100d103005410f43c04524035038504d00d004d9001c2a0783d801000b043c0b041101003450401c0c0b0920346030745030203424080083d6810a0b4000c0c0800c260340803d1042c0c001190000d0340c000a07030000100d440e1a204800d924030030a0445440c042007117501400400035940000300c800559500403c43d0344014205604940d460f00071907512103591103003a900040003c140000e4010603100a900003655030b0544c0140710140c0031402e0010140d900005071104500c1d80032058490300070416001450369034a04402015034404045a40d42c00307881c291b800181001154028040f10384100103079049881074104200343e000a400300134129503240070001e1041c0c54094008844500c0128207011990800e0b01c89500000180d085100071840c4060240208031070484004000208018040c803400e4800c80001e00103400c0c15111b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 872962976 1250 872961726 872961737
    0xa02211c02210c16081e031e090409060c02010b090f2e09020d06210201120e100b0118030c05090414060901090219031a0c1b011401120210 61
    0x51000782d0441040380d90200c4214100c444516001c00d100d020b0302980e200d02162845020140c0001100707500c40b4181c1c02c0d8074000598242403240310b05c2000319401c000c1c40030000000b0400310341a65100d114070700c0420300441e400030ba41c119005020382103a2500060920404500c0c0030025110b2050300c20941c01064101c810701103001102025401107a0344e00003000300882c40b800403602003030685c098500c0c6102202d06000e0140c1e1107034105103d400903d5100000d80d1030103220b40c0554060300741da6001180d040c100144120300901803d06121200518000258079030303034103604030341e807013415414025886943c0418952640d0b4981061410034420580600702000c005814002e00c0d210502008451206684803882c1c418140d9009000e071344012841812000f00700350201c10301360b0307c08060340d07030010084200030900b00c1624401540284bd0180c0031104100181d48602c00041085800e00c04500105012611000761030021405070442000180c2100f41500581e88840c690300d12031002c0c2c02d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 872964226 1250 872962976 872963023
    0x30203120909011701020f070327060f0c110a080c1905010801151e050304030801060e0102070323030a05040e1b0d020703030605120d02010b0628020a02211c02 70
    0x1445e01a008415814641110224811090503009252440e15401400102034441c602e1007a202c2e501d411805150300050f5012031044106001e0201400074900854060020000290000700d4607c0307141c100032099000b2104414080c113000a40401045c59420800c80d07450504000900e5442d0503c5560009a154035007490610700400c1c003520406080b5110440a1845180c00b81596000351070440008820310000242c03a44a800500c3c94102c0581c0034080d618a95140c0400c6140d4550300041640d4501241c8010644200f00610b40044191203d1341c4881c030300b0204010314180203210102c003003951400c00e1344100e80001114154040d00c00010b8480d01c0c142400c4000704065005190001505420051070682c001074110f00e880c4071b070b8001c0c090a0b40c15400e00803540103100400310008004840d1683c00c51070880c0e8420416081d104444a042d100c2c1c001648c100118031038403011108801c3c041e40517040078404009010785403402c814001d00c1c1120000e5448110030f000400400301e5800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 872965476 1250 872964226 872964269
    0x6021e031e160602031f050a0b13080f010b01020d08010509061203090a140f2e050d11090405070c0308012603030a05090d02070f0e18031303020312090901 68
    0x703590010002ca50160a80c503a18504a4001d41c001d440316204d50001d00c00000e405c0d01114081800e0702e90280240a0083c503040f6a51919004554080e2003440350100204080034204014541040e02c5000070401b07140003000a41004c1c8001c2444c8100729510005120b82c0e00c801110b6a0402019100400485070041312a400d500034880c10a0b84561601c50001e41140c8001805c1d5850f4001c07540f400d200850241001100304c12600c5110701045851002540d54480c503050b054012001d041080c9082c041c1140c1e03904440482c0c3d4551014500820000030701d040501c01d8560000c00750820a80c0d0384500e4030040c10b005814854401c0080d00645054100313526079800040c18948030040340e450703050142d045c01c05450101d4641c0041e10401c7d14401c4803501c0090300e0780442d07100b030070501810b03824480c0b603a0301440d00a22481004803090141b80c0980010001080b0311400c000b685d600f01815441050f00f0200e9103044500704400a010146290352080541070446603d01500030b290045542c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 872966726 1250 872965476 872965537
    0xd09082a040b091314010216020409022701060201050a0203060d0611040f032f130f142404060b0d09020d06090b07090608040b01050f0f1906021e03 65
    0x102454000f007064003404a0907001000d002d140501c5180030315a0b107080b44900500300d004030a101408088410811800740c1003580c402e006081c0098030042c10010142c100d001d40c000c60180c00c140c0207403124010081c4980c203100d07154001e16445400c1d86141000ca0000d0342c16042008041d007401d5a0b089002800c1c0c0c07840701194010940c1f100440c81240d620f00b00001003a84d9548500215112191a9001000221360083c81c426005103038a16412010228a0080c524038000480340c0b5960341d00c0841100601c07000901c00d124499090f2805120307203008480401002d09018010382c20080184003036024081078030901f038080040080d44024a000082c19804080006080030385030500701c070180440340031b850f8401c1030580c68040409a490a0442c3d804504407005850703620080014002407900c07102030b0303412810051904dc0204880e0002070340f8030346038042c40754208000d210100001c80c1c0600044a000d01414440d035058103c0801da1500c0c3d1007003284660b070f01041e480014510311100c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 872967976 1250 872966726 872966741
    0x80402060a032901020f060f011e0914271f060b130302120303040f080c0c191703040e0f180a030e04060918080315060c0d09082a04 58
    0x5002004144810844110f0341c4402641560040c082d02211581e410000900b603809505140a008440da1a106070022000c0c04190070074000c800034000000d140c04103018031152440c4203034550403d03042605540c11030601ca100401580c61a55003200710034000800d0111606003070b2200149404840605403008200300e40040324038400115800c3e903404141652079003564403e03100b502c0d022000c014400e80d6400201c4000b818070401c009500700152054000c2c10f5400c4d28441144c5030142d82c540000d41f03840140e1140c0d4040d00b03c0380400c201001c0b949268040400c40c1c0c40156180c00d0900312003403140c01d4003d10950504000c50085040040c5c00184008010880e0b42911140c0da03481c90024a0312449410b81440781d41003200200d505041d9200b000c0007214590a4901c50085c0750b0f4901d1240d03000108078900c007840c001031440c416101d5600405890b00b080000e0701c07242402220242410304d00790408501d45d0300c10941000480b40d201c1e00907040d48080c1c004045540d00400004010b4200f5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 872969226 1250 872967976 872968001
    0x7081303020c1005161101300b181e010f140f0a0e10030c05100f0f020309040608010501091802010f031e020406030f0531020d0605010b0c0d020a03080402060a03 71
    0xa02c40c1c003805204145d201c480080a003641c40e0b1800c0c0314000030f10509048c08981d07620250714206841240c0c0c1201e940040d04940000d020b69459900c481d1101d28920740c1203910040e024407119842051614114005001d000c4031140c4140a40c00c0c0b6545a4071748041400250050400405827811980c0e10007a44006180b450550160b1745010f54548400071002e100031102c0b0415003801296529000e03102442d103080380e60751b41e9103008500404440301d680300810442517000800c0408c04944903070080b0070280c001d800003c215035141201c0c2030b045036007031074000c6201c50b28804414010707a80301e003080204803140e140c0407582c10802114040182e00121803c90032520024000540c01e0f0160811401e046d00c80c01e003041580d40305480a200c1948102c04003580c4a051224000400112440d080c6602e001801c80c00d2658141e42e5100d045410a80080070724038808079001d610260b041010070040c081c140f029140d511600c1d540605100409007000b88a0724005c90400c1c0c515200340d10440c5004207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 872970476 1250 872969226 872969257
    0xc0904080f0313031d090f0a110c0c01020613110d0602160b0619060f2003130e1305070e0c0903161802120604050601050c03040e07081303020c1005 65
    0x605500789440f03001800c03c1100400d2110701500104600c0c4910401c903540f0140400d60341e65181110304054040051292a41c25520b0000c92100360543d00903011403042c1c80003c1c00c00c2c3c1c283c1e10019140210041040c000ca0910131030000c0010f020b00e0501d1100c003000c3e99035900300015441c105c0081e0003000107110a0700714580a11050108825809001d0b44055410111078401d070b01d444043c880d0180900304c04030710500b103401011032180d80102c807901007000031100350001d412502030440c1d01441403140d00c008151400e00951300355240c10385e04841d11401d9a200800d09a481036220280d41c400d100c0c00310320800004110041400460700010401400d0310300c8110070440c28020b410044c012501e03105040b0010044686851013112100020069071103010782d11801008003401005000380d04200003448041120310f800c0000c0c101810010880441d03e00e008980108201c50040840c41010710489a1a01184d004980001a40006c4d1094128104001416560391107040b088108000c5d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 872971726 1250 872970476 872970481
    0x120f010c0c020a0918080a0903080c160509041104021309021903230604051b0304110907050412060903110d02030c010e0c0306012702031815090c0904080f03 69
    0x3a404441d401d880c610803242058003075154400b14048a200104161003c00b8644010012540120242c014290356142c81200c01c2e84903607490042c1c0e0800c0e00300d1000c41e0700c40c4a0b0700003d9172191a000c3c003d001c0980c3d600310141740a4a07108804106540d103180a0759002541c22810314841107150042d01005000b50364411103d0380007850b4034000210040003030300d80b000d0811100341d9010000c441c00c0d211071150ba425180c0e1020080201710140c103901c520b002d02c24104280900035409540f040340101100400146110180050901c0c0203122008008040205001070f4440c2c5030340b03580203600310701c0000d90000c50b4a03054a4103040104d507003540f440341c0015051a00c0d80000100108401072000b03000c1003040300386c0a55164400402e941d03140e045500184106038025440401e00501d026141e40d810b12001c0e00407049900c1075400100d0301020141801ea00f10f03040002501d94402e80601038501e207007072030401d5212004800302c507120341c0d2850041810700c10000c2c2075405082c1c1c3c000c0099541e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 872972976 1250 872971726 872971751
    0x70f03020910050c010e010c0c0b060d02040e030717070f0b0916080a02040b1c2904120e120607200322270e010f05040c06090f050a0302120f01 63
    0x44d0029000020150b0a0104038036071544180201c40b00d680326070300d40110101440c0d44010b20004c0080c078a980103400c101c1100c025a50780d0203202d04a00d0300d58061640c51405050040034002c04800c89404034804104480c0012101c51000c480d4035004148440280c803120307400c0341482282441e40b02040324078140030070700000201d040e41d4118421982041001c4940301806440380482422150100b001042c030404070b41c0c0580da2540800c6200c41450804412020328064001c0a4131305442c1520301100c00261543c100365007425405045a03120184c3c4d02c40305030b01d0364a250080050041004201510517011000d02160420032125400e480d00c40d075650210980c000090940102c43c3c0c0305a02c1c0009440b4080211581070315150000350701d6040162900c035018040c0005014500d45d40c079600050301c3c20135841994080c1e803103a0500244140b4200000b460b02080d600300d903e1182c0411703c200610b584c0d003e9980c1c100c1794162000b00c240040c01039603d06140b5000c101f0846542000c0f20741000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 872974226 1250 872972976 872972987
    0x4050a0215030709271e050a02070b22141204030506060906011e031a04021902010510061b03030e0d021006120203211603020105041103060c03070f03020910 69
    0x1c3c42c071541e2490343d490395541160074030f4500c5495042c80e030110040c201c8450356041e00052001c038a09003440c0c01c0e08440460001c1243e10072908641000d90110318401000100d07020741d41c2005203000400c7e06a003a040d0860300290310614003c0280000d030148050b204000d0000c00140c00029010f0b9448643e03e08100303446030003c0b07440030b1040b40840700207030540d07004200000080c0000c80031407405109824055000305210300002e000d4082804400b8090303551800100034802c4030900c0f548a4884114020342950009403040001482031a1709103d01a40240f0084041812018800e818541420300b580200f110241012039401000081e1001301d400080d103004c0701441c0c171420000143d56162951345e062410304020340c035800030304048064032a80e0482d0803595204043d4589801030010240c0c14030820f09904a016075120f4007088180800089034003404041500501680c0c074152020100301d100080ca55001c0c0300641d40070003807640c070a5054580400d00503003207800c0c0d110100343c0a080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 872975476 1250 872974226 872974231
    0x80a03021011070507170a020a06030e010c111b30100606050f0a02100612231e0708060408030f0928030309060f0516020102040803090904050a021503 66
    0x524a080101c4005002d01e45012140c0e80c98200300034080c95410060001141c040d100c0310344505200380c9403020007581d14007498070024032668400081c00c01d02c141d156401d403082c2c81d803d201030106a04020f55080340c0852042c200f24141e103080518142440e0014400e4082c9038801d40940b0241b007020610707480d000d0885120304005800311807000300c0244000c8142d030070703900034800019800c1c800108a0780e9500c01078503020f52140103480d04103d005d40504101d801c1a403000300060b08080038a001c0c40302d0b1102c800c10304072201000c1080803030400c0c0c0c03240e591608a0204c0203220a54020080034002c20302425005c1c0c80002c0c2a1501c60629040402c1c41c0d400c165219040a10400f01181d541d24000681c111180c0b030482c0a0b0107400310200209600e412140320a900340340d1074407040b4000440921a0f654800000b0f500090307181000b88880444550a104e0311701568410041802a1603000068405454044403248026515843e2450900c10403460081d0030001c160044004d80c401c54010f91f1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 872976726 1250 872975476 872975503
    0x7030242120c030c090f010c0609150b03010e0309190e0103050a030e0d051213090f020c010b010c0822080307052b053901061d0f0609060a080a0302 65
    0x161280c80382c80c01003409110039a801c01d010007040100710341c035051180032141404014102441451801e4865806840e482d107012240c0c004250303801e0302004821f1141200e0100d007580200200f40341e07154403540d2803044072500c4d4401d9203600022607207604200c081c0c2c4040e2000c4410500c540d60341c0d290141d95a420700c1c908802080195a0b40703001c0e0f080040359259202c3c0c105005181280b4840580f040c25070202c00c0b80d060040903400701140494a07801030408642601800503940e55642001c81c5c01c480d02080710904002c1c2074000a4040356000041e1000340d040d48043c8a251003ea001c1e0044180301a44050641d002c041030000a02c64041886824050080c0310060100b420b44010224055824800404200c0501901c210a84c0350b00c1403a49854014461001700c010b030806980611541e10300d503814980d154841401424034154101059003100b050094407402c003803a03082038035140100503d00950064001807410b6599400300300040c03960300c05403a282c1d0750904009444841000c03410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 872977976 1250 872976726 872976757
    0x9031002210c07020405040204020d0c0206060307080a08030711031902030909010b0f040306050414070e070906020105160c1b06030209031204350706090303020f07030242 75
    0x20303084501400851441109802d00740307031501443d582040000c0401600c03d90b0040d0303080c8041d5588820501c201c01094040c0e070014000d610300003003010700c2c3c01e00341d41160703440b80c201703118590004010b00281d0340c10503c14204115031040c0c4804241c610302695501840030081c07017a640003520b4010006010390202983c8604250b82c903101017845034883c111840707208481c104010000705015910464005203d081140c04103244161214a807001c6a0051102001d01c030040c0441d080e0003a40c01d800418041c0001c5c0403034070700000305010252202000c08203104200d080c00c001c1004114021071418040b2001d500e400c2e8480074014001e4000854a138001d01c21100030280c080340b2182500d0132242e800885031074108102c18034504102c048803241c8600d0006074410000c054051004801a120559410303030000c0c40e40c10000d00d8003030240360003a01a008424280302589a0304070300900d000e450004c884107580d40e0709440a02d03500a462040441041d0300480c0030fa4501a4010001200503a485 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 872979226 1250 872977976 872978017
    0xc0a0510020a23160305060106030b0415091d06060a0b0c150a021c05010803030c0715050a05150405100b1c05040c06080c12190b04020c010b01030c0c02210309031002 73
    0x6255013007207070303010151281e8020b20040110030b200740c0000310024030103000030030041104202d10382a0800d0b6040342d00110345800030910340a0f09011203c2410050000802d000d05018020461381c2c66580142d40492400140f01009000108501120612044000007562810111030402900b108841d10784001440107856400000c9001d03550503036685c80080c51841c0c0f2504a814900d50040c074084502d80f60304c442d0284407000307a1207a0f138402d658111001c40d20340340201050a9084c854030a040c811481c140500a284184510701001d0728030072703912540c0c0c0e00804110315031000c0100c0581c4c850103040c0404c000400038911481c03411160240c8414149446072403d0780d4a50184d0802801c02ca4001c03030001d502031050030340c042c1c21182c20345000034291540b01c0110702a40d0026006502981d181c0f40040540d5a0500c60981111354600d00018440703440d07070005003021200c82c1341901e21004201500100c9800b03008079000110300504030b524203080c0c030708600702a4124000c1910107480300c0c40c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 872980476 1250 872979226 872979253
    0x10311060a170a0e190308060402070b04020f060c0a08070b0115050d09030e0d060b1008060d0311190c0306060b09061b070918140c0a0510020a23 64
    0x2030311105101600c1d99801c0780d4850000b20301c540e100411010a07203403294040b03442000117200780c0740c2e0180725201e18503c00d1031300e060117040a80d002e4601030240d4410080480030071040200e07640c100c1e50449600552862820010f000f034043c5c00365500f16405409203200801040740010426948900c1208103940e980d03550809082e44054241d4020410400542c0c1c00c0c00e403103601001056100f410214440c1c12903334003043e964081400d040744c85e1a91039264a009103020041d00c121070203940341c05005440c00e1004903041c280c1100380102408079034075150000400501075104001000402c840d840e114500706810f0307101140c482035409515100c008a44800315004442c961040940080e1034403102c1c14074a403d0904100826505014600c07002c92502c16a00810f0301c0c850700120402c000707442600702902c82e01103181e8414950351101d402c5030b0071074075030745008011036004403440703103d00386117000c11703030800810141c000c04c007078880203d42e50681001c20004030018180030449070b21448055 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 872981726 1250 872980476 872980489
    0x3020f2709010b012c130204080105070504090b040c0e0d05030c1507090801090f14160f0f050604120b06030f16090b030c01140309010b0a0e0624121e070305010311 72
    0x5d55040041c0310201c102c403068100140f0350741c240d9aa0180041ca00341e5038104d000c0c00c581c41580e030003001a600107410458038419000c0c007a0b841c04112001c0120341450700300500301c004000d01c800d02400610004000b4028140305803440d00c2c0d2103205403218074030101c020822080c2e00321a05400b094521034003162a600500c504042a6407007518011460340a03154894005007540c14681c5034450000d1030f0f50650385405007540280b4607407156805d8a82801071080c20043d4540000b400f800701400100441c0070107640900d40d803030b0001000400740d1070b0f80c800710342864101d08082c072207442110300141814500d280000d0480752240800c000644083c010551244e050481c0c1f14000364620f115011041c600c0c0005541262400c40001040c404600214401203020303072007000030310840802c1045038100080d5409094100c030803211280004215400070034000c0c51004030660500380c00284040d1000c00e00c0c0d0030317841100c207600865440e002d00018007030a400d001c02c031602c0d1a0144001441d0030b282 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 872982976 1250 872981726 872981777
    0x1006170d02070e06060403020d030903020a1719083007080c03070807180b030a05070801080a080d09060e0303190c0e15040302090124020703020f2709010b01 69
    0x56001e803042d5850624070001c40d45010f040240d01000401001005950304000110780d14400d40b18541c101d4614010032071061016480000d400b4080c0c010013900d110003080890200080300f807481594500b9003801d1a440c081c80140245040d0303110300401c0c04440c1040c010710341900c4a09100c0150f518000c04032410301c0107441c3c2801c1c5203404d00218071150701564041d82d204100303282c800050b07541040c0003802582c1607801151560f0001082c414148424050107a104500d8100030507194501540070380e49110080014003129000318844c4805241ca4100c00c04171601701400744184000080c885450350f10a072a10a02c03541d000c02d000c1691241c0d802841040179140d100d810651840380127111200c91105181c44103036000b0000400142c1e500007000340070b48241d074440358081e603102c46801c10341504c20a83c0341c1907600c80380302000140c0d00d642810000f0f10064501c40c0307080014250461100290100180d400401001041107003201544994a0890241d03120085100061041694104071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 872984226 1250 872982976 872983003
    0x150409020f09040510023603060f04060e06100501121514010201110c070608070903080d2a02030307030b0a030206030114030307060c20010c0918020408100617 70
    0x203030701022015241c010503142c0d1203070050b0309442441c45000a554120392040510820604105921040303014108910558544d0800c0160603652005000a90303500f0b0003d00600d051104500050204202500b1901c4924150f1040780c202e03041c500003204403900c0f02d0040358006503d040005d24100030034024441030300c69516000d10404e00b0324200040b00c800c0280c2e260b05542d00c0741070444500c0100002022054841e00140040508021008101c00d0010f00308901308024102c0a0010603103d10840700500854100025400450310140ca40c102d075a00c04500444149401e000009801000852040085940410081060b50204076082c005800041e41000060005008581d0030000014503844000c2c103e9090030015500c0b4000d03940000360364000200d881814100b00c580e6850300e04101e02109000b40403040303c644e40104511118415040080c019001d4001e03100202da045034068600102903848900c803004140c0040d0800d1310502c00c9110542001e41d00c3c50a001ca61755040540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 872985476 1250 872984226 872984239
    0x305070303110d08180a021302030f07050c0613030e03031b060601090f0920211e0f040224090a150804081e0a030e01050a05060121020403061415040902 67
    0x84482d415042a45e40122804070740c4a03080c403c401507a10324104c515088100040980e99152281c0c41c290300350405040c410901c6424403407008605070218a5a501c817003a4441d070703c035125103070504076201c044d01c5003541d8150000065415201d40b00780c4080900d8100441101c26980f130300d200441c0c640a0a128040c00d185044009105451241d04414558646100721400c075a59810442200707500ca013007100b0a9521482c14100f40d0a1001c8695603ca480c0782e50741150004000c80041c0d08400040070309400b001c0400001e402c65960f01010340040c140003542c01540c00381d01c52040c41ca5407000c2c0c9101e105602440c00001e02d10f80d0345144903101240c42e903888040341c40c0ca0341d800c030703041d04510040359094801c04800e10081c484a0f01901c052113076554003159040340e1100c05800c50f000603025401c5642007408008442e608103a481001285c203954045034403180300c40250003030080e40c20080c42c82e03040200c0540d042c1c0c00d8a030150301070202c101c14a400c00060f082000308031411000c1c001d40001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 872986726 1250 872985476 872985481
    0x20a032f0a1103130b0c1b060702040f06181512020d1b180c08101a09120f0d1e080c070201030b0a03030f090504060302060d180c0305070303110d08 65
    0x1e01c20341e1080107a1030500b088904041041040c80301c90082c0d41c210750801c0001288101508104001048080b000b001ca40c0405240400c042807146c401d50034040e010707030b454080a107031030080307540840005c0410080f0070408415028040000c3c6c0000c17100494035450444c1c0100e00251b010b1078413841203500500c40200542503a844207070950810313041958207a90f410000800305e000404514404070005000620009013002c0a051000050000310400c84804410302c80c6038058041c6500b005900d42c82c258651108100041e00d0401104d00c86c4203502921807a9400b82400050f010010051919022030800c2c1c0300b4174400d000c40b5518074801c0003840b0000891054030400c8014910700b8010301d4003280400d01100800e9030781000303900c00c4000800717184410007140d902c90a400080c02c0119000d025081c0755400055060061500304051180d413511008808117005503c0422503034043d440b000103694078213080e80c0f1074119100540c0800c003141d06994040c1c0021440550b00900d0792500701030754 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 872987976 1250 872986726 872986747
    0x606021b21060c0d0c2309040b0613140118060c080705010e100609020702090609130c0314011401081504020328050f060c0403170409020a032f 63
    0x50024410003070842080e02084045081480100d2042d1010744046030b440c40c8002c0400115140300036001c0030003040f4620340d03503135404481503180340049140740c40b5103920000c80014000c184040c54242e0015001a0400282c01160801740444a5800c551440900c80400642d4100704c0b100c9400294543e0b07100c240720080c091492142510b0207040c0c90360a010302680c5003800c403588e0340d90a80702a80010360140b6441000d0042138003510300c40c4020b43c209201c0c3d0340814003103400a4100d910a060080020f0306000c4072600700d5000030780260020101d16680d007050303040c400002018820342e5088c9102e043d04203c00a040c103040342c44240091403030748000c141e40d4a030002c000e00200c0c0c0c0350058102c130f02865000420b0b4000b415410040c191512105c078500a0b18151130b2515090352500301108100301c0c038491006607000c07250406190f50454040d083c0319070881c4140c0d00000d00e854400b20300c0344107041e8142c7c4503001d06046080300340a52030503002ca840702c007040e4080729182c54004010f0701450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 872989226 1250 872987976 872987989
    0x109020a0e04030921050606030309060d051f0e01090605010c021302070624060806150a1107031a150301060807050f0d0501050915070f05030414160f090606021b 71
    0x105002e032500390f203150388541c174410542c00502e0041d0781e40c4040c0680801403200901c68160000c40c00c80003103141203202c60115019006000002d800155500c0018003507148105e9030817800020100803c001644824100c40d9850003030040d4043c003883c06da808502c80d4001c1074607660f9260000d140c8130500c20341004a00c040d500890701264203e440302c840e41d0144400307165240071036460f4a0389001d800e00b00301000709004802020144641601040b6a84e50f0192100700d0b510040188ae00180c422040b600c0d0500d005a00d40c030050034015140807462030201c491001c0d9005070251030362000c81101810406003610031a001360300a40c0c001003030401003480c00595010752070b4406000e002200c80726881d040e08590007190881801c0e00500d094640310444044001e81c41012800c0150702010498401041030100820040004010b1000e00841079070420085958404044030405c41c6915480b81c1414901e007449440b40444c105200400c2a03400810b05030340e44440b07103400c1809084c55a080180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 872990476 1250 872989226 872989231
    0xe0f0d09090209061b07090c140301090b0307030f080a09080109050d05030703090203190627080307050f1317070e0f040609050a03030b091303050306090c0906040602100c020109020a0e 81
    0x10310000400c02c0240460100c074805c1c00c402c10340e07400740507154505440803003628034090940c0e081001d600c8203240d0f599400390690741500c49064001034a180410082071800481e0b410242030300c2c03110290701c403c21020300c0082805908a40e600c0d11182d03a00e140007401d0703907000c000003400d6410000041d504c0501c1240030f0369000c48989004503035440280c001c6800c1400c184010b00c4a082036206010a0040074081c40e141e01581108054950007541c6140d64030307e0783c000d0000c04004000010540312841a02601e00d03a04010340c002f43c1d20745103008902d90040041c81103e10150180e000078510f00f0300410003008481c80380030081d50303507a44c106940c002c2101c001c204407211599a48a00041001000559401440f2f40c500040e864498010032084407001818040304000303807440b6000280c0d0010580e600400144d0701c0c2c41868450324500205401181c400715000f00c00401c0001e20240d0004812851f66903290701000b04030590070089081e106404e078003a421849001003006008101402c059 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 872991726 1250 872990476 872990479
    0x9150810060f050a0506070b07260f0f0c03040f06020d061e05010f020712022e110601050112181221050601080103030f050d0c0804020306130b072601030302010e0f0d09090209 77
    0x60107541011007009000c04ac400b111300020030400308142e0640341c0c02c4894002c803d11565103083e207000d0b03420b201544030040005207800d8060f0001001c012403501603c01411310300d4414480c103902c41f50111480350081290840c0d01c019881e00160079401110105042641640030385040307030800740e084210700c10000080b07800c25200340c09222000c0e6110b140300d80354002d2281c0000c0c1c0c007035500e4005040f003110a003803a1a0360000d400401c0a03a030070200c1c0b000442c2c18401c010405a40e00da1074186004030040010745a403043c0340300340d851654001210084502c800d9044105243e500000e0012240220b501c980843c5410740180701003409076a040c0400c007041d00d44546811209a03010041e25425070803000429441004e100441c50300784403c1d584401c0e04072200030001d850351140110440b015000c2d1051001400d88400e4845100e2980e2210f90002011403043c3d503500d2a00038002e240c2d1805101c6039008002800e82c01040205011078010036036500e01c5102801e00d524071009620000c01103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 872992976 1250 872991726 872991737
    0x5180c0f0109180b0307080705030c2e050c100216021203070804090b1305040f0204021602041803020f0604031e030617070918080409150810060f050a0506070b07 71
    0x814000c004201d084041c3e034401c0201e40c0710b045400f07040c43c00c0d0641c1c0080310107070401d81041c0081e45000a60365600d141c1150858100108066000b0030002d22040220000702c10304401007403160030100501107942e400c0c2c2100d0307260f01000102d600328014010001c2504596051010140c43d18108000712505a1401e40346000e10321780e20481143e03c55800380b480f1948410b0031280e05c1ca03010951462800004406202a02d040d6503940c5164503240b4000384601c0d408034481c5062014540300c488000d6014008004200c900400e003503180c1f2919004400510400c041c0796440000440c00030b00076076058480074050510a904c507c0c2c0d4842c038480036020103a4074140061101c076000c44810030441c0a001034070425090051090542e445001c4944403400384a500a00148080302140d04031011310000160001204504e02c003104019031198645124114080348003140325844442200c8010300c0058070180d40340144140d1a90b588103d6510000c1032103020045510880a180c0c0b0075060300c1c06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 872994226 1250 872992976 872992979
    0x1d10020f071221050d09080d061e05030106030b010603020c10060b0306030d1e0e0604030503040f2309070804052e11090a031b0f09050a05180c0f0109 66
    0x18a10307041903070303124004481a041000c4240454203c04040c3c2d00e0901c2c210450301800c1400203401c40c403400c038000804551750300c064010322030008140c1d084481d40300002c0c020507a5902c10361000445008410b80c440032842d500085600c2d05100b81e0040343c0d40300c4820b184507880d000040e80250030039003468105021350020000b1903800c034030484019250800c0042d490f400d00d80c0900d8030b0b2143d1228170105006080c0301c094410503880c0e00000d024100f0f0725022079416401c0022072024000d95000070041d12002c900031401103a6541554183c8040313030700d07000d01108121040001c03041c642e00c1841d0090b50030b0000c1840d051060041d50380c0240610300702c440090000c0b074001d28964041d110843c00ca40c4c00c545500341603900c0d01510f820b078203540007a2418068000000350360001e50384002041c1d800b501d440070b002c01c8460700c3c50200801d6208100d95815513645501000b0b0030f01201c64083d01860200001e8001740d0703c424407100004030800502d408800001400780c0031101e000352a0500500300c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 872995476 1250 872994226 872994253
    0x60f0e2a06091e040f200915220314100e1c02011d07080d021504020103051503070b0306030c0f031905070e010303030b01110316110f091302010e061c05060a050310090c061d1002 78
    0x107280c004ad482124140b10b07010070254502d080c90100481c4090781070902507450580030340040c0c41e2051b242e40d98115904002142c8040e4010703c6004d00a001d0010754041ca10070f542e0000c10f0090072103e018094031a07900c0d55143c22a00d400414503107418411ba030382c2c003003405540b09a10207580f2000ca04490001c1248000000b480e00c0a0365102d2070000070000704100c20707410148203400081c3c509662040d07607100c104002a442d20601c0b144a8401c0c2d04042c0f144060280c20480c076070041c921840c820f90556180d0074018054100140356a0108600001c1000304403800400c803040345804501000d1240440d40c1c4a002000d01401800e038040c0300d094140c0010b80e226102a800744d088020b013101c094404d072001605a031a12250305100300070901c040c11030007203024071040a00800c0e000c00501c81e640d660000700110159000720750144124501403144200a901206d002d6000c0d642494010355140d504447d000c090481c01d400000600031b000100c0d082444a40b800540f841c0142d803064012680f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 872996726 1250 872995476 872995537
    0xf040203131401020c1b010507020a0e0915090d12020405061309140403120917160b01170a0f060f0e2a06091e040f200915 54
    0x201e504000d200300100541c100520000351050010700d64009508004007042c1094a8410711080d02030602c508460440c0c050703120304200c90304079a0042030001c6150700d6540d118010002140d00e0891403007240241040c075006050f54130b02c54240c4400400401400b000229013200300700c4260791606400344408102c65460001601101c0311408035001d04606e00700d1510255842210b00c0400d111900741400b01090b4054005201c03101c0000020070790421a1820101402c148500c460300c0c031304003041d40c0b111310112505101395140610000312850340c96611649180b03031003060403515503000c2418040080c641c04040d242e12401039000207401d580320a001401d5078500c1c80788807039580010156260042906285002200399040a20a0b00c6294008190280310340d40d44036208a80000d60b56800c481400803007102214050428407441d21401003003000f6003d00810b40b010a41484d40442045007010240c8409050040c10403256a8034031f02e0745192680101c507a9a0f104030600c000e464007002c02c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 872997976 1250 872996726 872996731
    0x5030c0c0d17090d060f02090f100c0b04050f010c030507020c090603030912100c05040e07030c05070b1312030501050a060c080403030807141606050c0304020f040b1908060105011701060f0e0f040203 87
    0xd180036030b9881c00a41080b0341109c2c50100103128150700301100052070ba200c9903040c80c840d07011141099688403420198508980c100002c034096080810758a1041c0d0305030085401001c040d003c0300d401c05000020028401d9085a5550300b5034001d2145e0246403a1108200d1444403894003614803654010444030b00b6902524103200c045280014100910314920b1141a40007017645400c000488541c400203005c1d2251150141c81c25040f000030414494106081c81a1300d03601c19603c04044102d0320300036020301024400e541c4201030f45000000d0307990040782d0000f0380e40c2c0c2c414613040c83d2501307542d01510002c1c0003074504010000d203d400e805004038448000d05017603001050034150900185426010355000a10b203034004002403040c030005841d000340001c440242282e011404c0341050f40130a20404c0c02040180c3d40c02421100026110400f2800c40d040c1c071002e81c1c03070a84100c001781014034100400e00c03c90001880d040a120341841c1301e1009440f80f407800400060010681e480080c0a07604103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 872999226 1250 872997976 872998001
    0x102151306150e070503011505090604180e0105060301020405090f10050a06080423191502070605040b07050304080a2604060c090f060c0b0c0c03030405030c0c0d17090d06 75
    0x42c05003e100c0d03800200d481c0c40d840718403403400c58034541c1080d41040007134044203072040a1103408211815550340d00d505860240c000d020190f09840d100315802e001600740800c003009154603200224080e4203041c001c5070300365000a0200506501d850351303860001c20005201d0400700700d210601103030a90b1180f00d104020181d0b5500d42e1241c0c10141880a0780c10380120f00345100d80704a0352880c1341d0041c080760003c0c41ca20314550b030405041241c00c1920351000c0d00c044080303031148000384900070000f540d440640100e0003050410703541e43c1c410405840510099401900c00c4c6800c1c40f0190b6000e01ca031001000012503c07171042126410710041c1d2c1a21642640c049030000c3c1c070b030607001a841e03034090780c120001c03d041d41d0021078851510001420321030f82502d018003000503241c0000c00e004c01c1d00d411548101d00510850b1b540c0c0c6810700740345031260003510001910f8012034084190303924004101e6903405030444440c00301b010201d80003481c154000000103401c6440051814003249641c803d000503c0b05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 873000476 1250 872999226 872999261
    0x804021207061e0201051003080a021e0a03030e03040f0506180306071215050a090e1204240509100c050f152e0501030e100c02160509060102151306 65
    0x1405045000c14010f042d000c108681c904800c00500d000d1030215501100c0e0014800e07a5600c03003d040807800e00c0d00c0c518041c01c0885030400300c000c4042c000684280b0303041c00707a81d0030010074262440c0c0e6a2030748624420a06034400c8054140709501d072100c0280036000e00d000302011150030141c046030800200b283c00b040030566440f8040b8002200d030045044d448025501e004802d800e21b40002d240000714022200020b0703460102c00d040100420690305482403e141d4a84c403240e1b1410901030708000d4401c40400c0211120001c0c1c0107a00810035100e25000c01000c40380064141c51742203802d09118071040d43d20740b244020211904209218485618607010200e0030b1038900060300d04a0b500103c0e9a00607441c40741c0c080105c0d61070744084030a0a480d401d28002c5480e944e00b0400c01d02e4a40d542840c0c0c03070160700c0d00300d504552540018070f07000f030008400840b00515a03103034100300e0b600c0c6040b0340050260b00030030b140c1d030703805c600002110758002c9501c81107000120250b1070300e404460b100e49501c0c05101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 873001726 1250 873000476 873000497
    0x51603031d06040b040c05040902150c120c1006050616030e0d02120a020418110d050a08030a0b04050a020702091b040803160b1012080304020409080f21010602070501080402120706 79
    0x641b2210340028110543e0b0510034040a640402e025020b440c25110405001107446030b0011000c1c010601507500542c0055124081600010344461031070a0030005a8a02103001444d4217207601601d00041301c0d403503481180220b03074406880040752102169800801d9642c01c1c001a030b01c1520050b51108054014440d021151041c40101c80c3d221100072207010041083c0c2c00003c13035100180e00c2012003a660a192041c0c0c0e45011440c1041b251401029020302004000f000421135100e040c038050704407401d116a886800500c0104d2048490180d001041d0301c00081900d100115040020390018004500c5c0c156191410b50075900278101d04c000c21206a01c2e81130520991905c0da94001110700c180a02d61340c54040b0324602e00e140e460000707104181c00300c0000e0030356480d0b034004000c940c0c200b10265659442c5810b1250b86600004108484000d040a00188401c0c1d00c10402e041c0c40c0030780c004001170f505100054541c0c01d0003c004980c4062201c3c0303001017015040c0704550041c21107403a15044030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 873002976 1250 873001726 873001733
    0x3c0a05190c060b06340b181b06190e0a0605040603050f060d03122301060f020610050d050a0f260708040e04051009081306051603031d06040b04 63
    0x84000e200840d204d40c1e8240854403010303103074000340000181d075003224826080070800300f03481d41002c10001800d400050803c03c051201d212813031074410310241061318103501c0703d04408481d50f100307000550b0300b20b4002d000d5443c4503061180103692036031030f5060a00c1c0500b50103000070030828a03500400000741000c42d04100198260043c4c503003000741c03000c0744111454004086520954601006420000442d03006d00c02000142d000d8074220400e44818200c6d120504c10f103400c108030a1003003400160011082c150068408503040d4000c0144c0404200301c0c510381020400207811b6103000703071481c0c06490000000910381d600700000700c5100310070541603000740900c805141c0c42907002038020301108219060000d051003003100d0540300b0803640982c00b03403aa8240586021002c41c00c074550985081300c040180301c0000003901240f844641c240501d10340b00c0800703d569004042100e00040060508440006e020b50040c0106d0301100003400c01100c142224245082000d0b942a00c10008200900050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 873004226 1250 873002976 873002981
    0x15030c08010b040e0307060b06130f0f1202031b01090e011401020106080304080703061808030411150c190807050303130201090603050112060f0b060c01023c0a05190c06 74
    0x6507004503820002c0d020b80007081e5407070b8450000010146592003122642310b0b6a2842603a910034104035101404030780700c54003500d03161200d0261980160076900c0000d0000b200038481c051169001c2c01902e109034184100144100103502540d050108000c00852038691000469009110a118102800505000280c00c441d41a0400f0101d0f8004010600103031000190200482e980441c0014450401d00c80d15141500001c070300500c04680041440b003801880010411028001c0b10885008840d01103910f4442c411584207e455030002c24640c60400300d0a04825801805100d426141100304e54500341181d0084442c00415212a8241d50655a20840000142c040390404000c02d5041250075080e40300300c41002003c80b5140c000303071000c64053380c001ca8001da0000c2e01060319104980303c0c02d8003035041070f5505450b00090382910802c1c0240030242c0a08140f4003141e00e2a854502070b40024968401030103402441000c110b800c40b0a144180000d40901e1107030fa51441074102071a200e0103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 873005476 1250 873004226 873004241
    0x1e10060f050901171606080f0a1505040515120615010201050f27061e0f04020603060910050a0b03250f110a0602070f0b0a0501030317060415030c0801 66
    0x215140603800740318684403421030074156079441e0040c5004c0c164108140e49000d00001403182800d4400c1c4d4005801604003c0c0d40740034500a80a420003581d4850940c4122002400f200c1c4a40d54042d50800540c20284e104a412125007042c80a41c1707204a0007168902180000c0c03a03001e42c0c4004204541b03503549400b16208000c1c02d2000b0b2245003402c82c039845002a0142040e4080d040f0030303000f2484241034058020320950340f0425101d2900e01100310301582c0c19806441d44010300e88400041c1510181d5650610682d80201400c0c1035480744d5040c01f45c4000000c26000402c400c0c0400480c00ea43c0c0e501da41c0303000b000c40c1d488995407481c0c45282001080303280f498004034420310844085d15160010240a121000303450060849080003907010701c0c10300c03000f1000c0c200c1e43c400140c5109120401505014050158640d00d041e500ca58105504984003440702070000307644048041c180b03246e00038001c0c0c1c2243c0f005001041d160049280507400c50050b40c4100c0b4440124501000714200a0081c0318 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 873006726 1250 873005476 873005489
    0x120312090607020304141f0504180e030d09030908101d0102070c0e1003061503030f020d1d06040312030b1201090305030c07080f07061e0209010e040e1e1006 69
    0x192a00300b40002035542d003c0ca016654216040640e902c0c895203031b49090464080100c04405a10844800080c1ca01d50041c095018201400500500b00c00b80700c0c02020960140c41d00114130b003031101d203210350052502c00c0b17040301000100000000d210744200080284070340501d500040915a001c0c409590758070b02414804a64014061a004030310162401c104036a0707140c1e0f20740740640c3d030a18111081c00003a003004208925110b600d41e41c46a50780c6030712046d240300f0348072070700c0c42c0540800070b0340e85c3e000c039144100c00034510a0802d440c0012165940400c9103001d070540d81400c0d1665184c986000400080c2c00020340d031003d51110b507150030001c4521405000d4000c001480054174010171500c070050540141900000300d11041190700c00c00c4a2104248411268a41145184c5000074008080010302130091041c001d0044032520b1007100c40c454016140c40d1100c0d58042c2c00e00001d8004250308001c81d005101ca29402d141c40000000d5101c060340340a402c1c0d502d03141d80c658049540300e070440c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 873007976 1250 873006726 873006733
    0x60105090603210903010e010b13020c030a030209041d010c090b0415050715050f04031403010e13021210020c01061205060612010e0a03090608060906010203160206040512031209 78
    0x840952800f2855010350400c1c00b094054000e4803118000300c2d4403481c4c0c80302d0340640ca409006a50303a0410360200120200881d040c00940c0701c2666510185d000c2e180480c01c0c0c84c2c10410003000d426010358010108c090300074001049190a4a003c28030b1070081701a13000c9903175150750307035031400690101048014003200e00311a400d080c14450800788141d12646040c06100c0000360100910500e80c1c40311041d1103c0c2c000c148081d1030700700e000420554083d81d048020404d255000d01540700d0329000d407416101100e400f003400341e0351100d06030410741c2d001c4000c0c0d8220242209000540c1018040c4c0405680710710300161740d54104601540c210b400a0381b0000130041030300005000240f001c11050740000c2c00b04c400c601a038042d18051401401d140c0308803000c4e4403030004240c082642005400d0100e6041d5250920035036a60424456520b10840300310b130041e00100b085241e108002c05283c040c16002511890034140c0300c40224002a460035100703440c030360000c14440205c43c400c0c81c406a0003101000507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 873009226 1250 873007976 873007981
    0xc0309030e10050405030d0309021005030f0c160c06020d02101107080306060d0e010b0906041a06180d150b062131030f0e0604031401181406010509 65
    0x4209060000391148101c0d064442c400c0c007a84102c2c140d5018040040a480ea00c10703801101500a00100104a0280b506e0038014608680039509881c03140741046a00ca0301c5944550704072803e50710081a05010740f141c1d446550103d140c0908500181c032441c1c004000000300d9000c00b901e031101225080c000c0901f814100102e44841c8001e84101c1d643c0900140e40b0b907200e010004016000b02c91100041500d032a903a24030480c015000090007203000c1d0740103903058507000240801c1d41c8410315400790700705c0201c0404840c6d04080000b01402c240050020001203124030000d12400c014030800c0c3ea40f8070f105845500c04514500c15103404003800c41d8013519040000801038800001c4402ca1340661480400088503025000082001102c4201c46013119901d5001404000d040f480800d900155127120710382e2890317008080c1000c0545000382032900b0a49503913980e001310f580c400e108002035503c4002900c640309441c01d07100161480307080c1035445460000c034581d1400c50140e202511400c1814103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 873010476 1250 873009226 873009233
    0xf0228091211040b010912060c170609070e0a2106060b0c07140432010807180e0a0b04050f0d081003111503090a0201090801050f010608090a08030a0f0c0309 69
    0x610122840040c2d0f40400c0f00c00085005030780070099940305180308404820454100299a0300c4003000e803280d900e50740c4900403444204001d400e401c451554116001d003011641540c0a407042400d0000c0042c500801581c98040304100307190401d191840c6100717048107441c20084203018441c0a4a81603207450b0404a010080d140c3c1d90021788a1010002c61400b10110f460301d0b150080105140141c0c1c81c1c591102c140c95100441600f4281390a00303520441001164100001c600d01044450004c14050805243c00080c80103004482c038030800c91160040d448000f070b0350082003a104c3d5028401070121144079070912800e200600f101202001030400411043d00f40c40c0d29200182e0303800080e8813040c103150038003099041d1604220801f9400010080003161140000c2036050f0070301c04c3e40c8403507070303244d5940082d4281ca0040c0c50a00d110503001005009071031103503414a602421038401c036081c0040623181c5e496585c2c01901c0d007040c496141d00041d14445400c1c01745502c0d2040b280b0b401c201005451b00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 873011726 1250 873010476 873010493
    0x110a12020a0f120e0d08041b0f090209040609050421030501050a090218041122141c060203040803100510170c0705030f0433030f02280912 61
    0xa45080502c0382c038403249504440c06910600720415520200c407038a81c0004000b40c585c080c2100c0c208c4940219520303610034200d2688910701260703811212500742c0c508211684d80690040c1a015400036650200042c07201028040c0318040d42c043c0f107000d03107040c04842460f150b665040c5000810316042000409c61038958400800440b0040c82e40183c03503410150800190301c1000140340d5006043c40440e02000210740006c0010700010440400c01c0588503881010001a51148003800c4800c0c0130540d42c0c80c105250240c15514610034441c0915500d952410101d8000b640c0542c0c03025000b01c1004000132501c2c4c80031010301400c441034003103004001402041c005600001099014203840411601e004c0d860961701c1c2c1c00e90146c00e0720740362100d9a03010180c076042031140c6455001038010140c0c1d5448508c00704040002008662003103654030b44010b41c06000801082003660350700304010054110507102094603148542c5501510101e0000300501c3c6124a070410300f0556002c8024000152024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 873012976 1250 873011726 873011747
    0x120406030207020a1d0702010e0d0e040b0105090d06020c01060f08060610110f0a06110304030c1e08180f0108071b050c04050702072c010303031e110a12020a 69
    0x6240c007594a16403440407454032045584000e81100500d1100703141050160341c4c16108030020350080200c03070158180d070360f650018042c220010407400f5411460f5401d194005824280c011304000e85000700304c0020400c1040705034801d0ba81070743e001c160030216040a0040c00700034100201e0703644415003088400740d11000003900092180c40000602541c090083c800030542e034081000355400004480190f0381ca440b261401291202d260003d941e04100c003c6003030384e00868040e40c5605142344541e0f5013600520702040601d01d840d43d00c41605000408400007083c52451000d414002c0c0f0302694103002e00035007280e200742e05000b241e60401c40b03029480781c00040300490002104c04502000d040881c1001c03c800d80700c5800034184020800c00303940006802080344c0c246e441160310010f048400c44029070551922084544003d40100b0100c5d2090b0048030038542c12107850103010f4100c8401c6401c0700c0803002004081000810000140b6802500000000b080e4603400d41c980841454000c1088211 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 873014226 1250 873012976 873012989
    0x120906091c0209150103061d19060f12060c0905130906020405090f0f090d0c03120e010915150305061b0c03042301030c12022b0603030305091204 64
    0x300460200c0010020075104003540c02030181d0100d81003085003860b540d03c01294450100b03082c000e00140425080114107110321410518491645501407820240b5429040c040101354864070040765840f618134a01c001490b18080300040400c031403400c601581c403101940000e02100580401094940d14540460600c80d0240011030351049d01d4100c00034003e03608001e40118280c010025600c4c041d00305d040c00b0741440da45800440e6251000b040e40c0707180d14005800002c802034400000079004610745450318018041c04a410740c4a400624212189030728299007840b00c00005409628540c4120071070310705000800d08800341562980ea6035104090070381048003c5480241c400c803040402522a6000400d040c1da035900ea40f450415500d10710051424803850301569030204a46c02440360340c030b10002c00d80701e070828038032898a604001d40140e81000d00c004c002c60984040b070005020107010a506a5100080f202d0440c03c0040c2121070080104200381d11028070150507408800507101110740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 873015476 1250 873014226 873014239
    0x91119030b010e1203070605040f0507050d030e130e1507120603021c020d02090c0d05060904050604030309031107030501050f010f03030c0f02010314151e222c12090609 74
    0x10300503926817652040b1800030717290ba480d00041c0f004002c20165800c403580d0050040b18000c030748410030010071125100000703010590a184c081e0745400c000c40c4401c0088a0614001026001501641d082c1089924044a50b500000400c0071082c0c201503a066102c00030b140400400e03040d079000c2490034404041c2c001010078042c48640440d56022403110712140c2c0a0609007141c1441054111035400055402c24503c2c1000009609401c0c401c2e1403610584c0c03c04010000d80d161510250024a0310390030544c10000d00c005103098894040101d5402580300301d000183d2844c08402d140305210040e000301e1050042c00303004001207a4464055030344180c100da40b0b40f8620380e0398070060700180341c031a12036240e0740c05a0f000c00240280941e460035512900343d43e00f40c101098103414121b08072070801740aa21640d1400355842a42c802c40501120341c00b41140050a90060380c2500e14600c200c900319240381c01020a150740d00034040c4484160401c82c100340c2070401e03c61740c002420720f02401040354014030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 873016726 1250 873015476 873015499
    0x20102070f1d040816150509010c080c0702040e011802150a021c0912030c032d0e0f0d0605011e150f030213060210060e011d040309091119030b010e 65
    0x444401c42c2c000c26981c6029200f8145c251901c41681d0715401e4041408038504400542d1050b010700540780004c00544d42c40700940d0313500600078801d03017001405a0700503a48028140c4c208130700f445071a1400c4648006a8015030291040052654030402e014010b40f405200f08544290002480c04e59480c0314540e0045100034213100300c2d41c01c0107940c4091002400000c0000525400007200d5001500a03581d280142c0e00040085a02d8043d5002c1901280d0581c0e03c0405005d01c20150010711607401004544800684c07000603600c5940364905a40e002c0c0c0da140104808104c00030a030355151303154080a4440b0b442d1000c5004259100b180c01c1003840703245040141118400c6d412200300308103069003220800d86401d002503403203511000c50f502c80c03032034100c0c00300310302c13402d000700604843e242c1d10f61340944100c0c680b010030507190143c8206c003400039103540810b450032140108010b808490006644840d80000e4145144007542000c000741440e00c1c100c1030542e6800603d000f141407003078031156080c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 873017976 1250 873016726 873016733
    0xa080d02070f240b0603070f03050a020f04150e0108090a020d0c0512100507030902090103020f0f0901090c0807030b0319081b0304080c01050f070b0411060307030207020102070f1d04 80
    0x712403041e8000c140f080d9a00074501002241c1000001c03070b10b03041c03004024080c2e240342881780b188000d071361040c00705885c107000380c1c00184031750081507200303c01d800c0250920140c1400c3c480d40b40c00a42215510701180b114110403030342e1100c11102104024a4515020f042c4803140f1070703c1c0c001a00021380100c01d884268400c0c0403612103880000c00c00600225805952903a02e40e03110082c007000c0000c503d0804002c21402032203405001c0c4051703001404599664a583d00300803455180000054102e1401425052260354949003a8000c0690000c00701d2003044600c0018842c01c00104600c0034940342122502d0141c8000031041143d41c2100c1000d01c40d40c00300d080940460046040082c85003003000e003500303000324011000e00101c9203881e084404144c440e00040d60280210148228064030501112002c01e0843d40a1504280a0795005200410b10004100b207680304480c000c01203500007440b2011035a04001441c000c0c9120b84090700038900f804220389074103503c031503c2e4400810801c08181403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 873019226 1250 873017976 873017993
    0x2031905062409041b17130c12050c01050f0f031305010614180121140a03050421020a06030b1f090e010609140d150911040e0a080d0207 60
    0x24181090681e124206004056498960001c1102402a400c0440f0018441725038010380c110b5191545070740100c0c0d10601200e0068000040c42c03001118601c04071000030500d0b43d180070001c2d20540000c0203983c1c5403420003a140c401019001410044200903240030b88501105541c03c0c402144403441e5213031914103a0000d50140b9500c0075005520b0000002408051062070415000003a1070303401d2045070040e603032030b9151000d101e1002d41311907500341024600c52a9014060384c92243c4008483c8c4c0603480045864401510740403808640001001d000002c21415291540910b03512900e0311600e10303134003044d03401e1950312914060684600a07203040b035a031411251003c400310b80c0f142d031070358015010081241120384030304052000e60390000b00348148030b101148182d8041c210100400c2d0402c50622159042c2ca0b0800d4403814070350fa501e80385400d9980502c040080c0641c40030460248280204000c6a0403d4200001c680c00515403d00148204003540c900310000080140c54a0003800c0c2008d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 873020476 1250 873019226 873019249
    0x1f0c0c0f0b0a050928151e0f1b030e0411070c03020928020a11060103050c0d02150d0902040e0d0206040b151503090c090403320a0917010203190506 65
    0x2d03100c8056064050703000d1800315040b00c04441d406c455081c2c160f0803e82c1c10640f8006a1410030a40030700000406024403c3c00b001304805180c0b11103400001070309407400418003081140055005100c0f1503035071901c2d00680c40c1107403000382250302e044d2240d5510401c043d5540710081c010382c4100002034030600c01502c40c2c1c5040d00b2a541c04104109101e180d48020b501201c03846000c500490071101503100d0000303601c0c0c103030707540040203040141c91802004102c41c1600b80817640240382c68002d100b6101e00c00040d1100a00c083c1000c01d8645251041006075001c200342c002c0c0c141e122164855050303138000f4025410580007001840ca07511501c01544103c00910702ca250400341c0d49188500e00c1c2c030030388000c510810340041039a0701121407030200882e810040c2c401400082411600d100344480d105041100d0080041000000700442d0210310f1a0350040402d50300030580307503102000a82140070010440d0399101000b18590300c0c1c1414021804030a9100348243d1030f03038a01c001000354460344407082c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 873021582 1106 873020476 873020509
    0x1b080703080706090204022a032b0b0301150314060c0702040c11250801020903070b0a0203040e0a020c0d020c0102030a030b1f0c0c0f0b0a0509 63
    0x12050340040302c0c00e030307505541c0e01a84001070f5039038070050250250551000398000014151121505170f001c140c41205d81040110f424814242003402401d6049400030481799000d02040100620110507880d03015071800c9040a401c5071240041070880381f1500180031503000c5200160b8843d0740540d50041004030a0000d900140b819400c6030030070f0503103480d0504d580801c0d1060b85280c80715018150101c038840881030542003501108800c09030403040300940c681202500070940d25045849452507000380071a4001e882c0c0d04c248102c41c0240381180c0f04019500b4080c082e1802503202c011010013901c00c0402c031000d00d1340041a605074900d0144c01a50500d5600c102c164041c0c12100701499100d070314012075102c08008a1246860010309545400d41101c442ca0440007141c0ea81d003101c850080740c454100300c40d40811046614076462854480c0d2288003840202c0e0300c2d0f40d814084007 = true := by decide +kernel

theorem cover : BRFrame.Cov 872841726 873021582 := by
  have h0 := BRFrame.cov_init 872841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 872841726 ≤ n) (h2 : n < 873021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
