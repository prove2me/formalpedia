-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4700
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:27:37.363957+00:00
-- url     : https://prove2.me/submissions/6033fc1f-2fcd-403e-be72-bb6948d0dcb2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 845143884 ≤ n < 845323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 845145134 1250 845143884 845143889
    0x200a02040615080f25170901270501110f1206010c15050403110d080f090601030f060b031002031302011116062607050301080601060e0a03030f181805100807 69
    0x68144d80944e034414958114501040c000984180d010080203d1a640030000c20402d46130682c1c1c5c06c40036210008201d01300d40380104850404010300e48040c45c00d154040000c0130140c0141c0002ca03400030b800070600e1103544014044445148001a12010f02c40c00070074550b40280b00b401c1440b80d20341e039034450381c1501a41c5424540302d66507810010b01010301419407010728119503000c58120707a1040c0c10140c615001501c1908201200c0381c0020541600021524141c07580403040315908616541c810010b06480402ea45e4180610481030440000c684040c0d4411441f102100e0605181c41c0005402c0013001e003a810455000b569a0007056124040c0030001c44540385010720b0320007090040c041da00101c04480c8001c800c0c01c001402200c0780e0240155040e9140034055440690743c5a80503a8a8080480119040b01601e44204042401110049030203010f82c1020100c051004e5000d65007007489401091003050300e0380000070100307138611070036038001c0d0042e407114001410700041300d6482c030346803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 845146384 1250 845145134 845145151
    0xe041401060b0f130f06030207230c090903090d060b01031401050a140f10020a03020607110604030f020313091b41030a050411040c090b0a200a0204061508 68
    0x4420301c840c242c0013184002420301e500036002da15150500180070390300c40d0100ba0380c001403050b0100541d60080380c3d0036405085000c014080141c0c1d2500344480d06400911814241c0814401c031b5080345c035800759600700705209041c0083c0301000c200014088581c60800c2000f04440314005220075100e07841e5120594030f40104030b0346005100d500007010302214080072a004076500034a0384102e03400241d60030507a4441d409650390344d540da2504407031503c1d00d200420b2560344084085808a0302405505400d1612403060328509032204450443c07200081c2e1101e021541d90703400000c1c1600f90380710250071511281c80c00c049109096044100509804c0e01012904000940700c0c100c6102d21001c40ca80340d40c103504403146c49140c050551001403004440039901c01c888252070202d107143c80d2040703070700303905440e125510300301c0c14802128543e800454150090003440e250b0700c01503980d00407240c44403100001c0200125080782c4144400d0301e8140c0e010a20416206842594554014200544c0006034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 845147634 1250 845146384 845146387
    0xa1803050d023f0f0d020f0711010c1502030406060312120c0509060715140c0a0e0609010203030a0908090a0b090f01020148020a0303151a030615040e041401060b0f 72
    0x44144001703110307101940045d98030000341804584181e20141c14090b0090030041e1400d000c00b001925190058140102020b54001d16400240d0007680510f070400d001d070800256003034992303440b00022103034024040042a40e80c400c0e102010703002d01524400c03014a1802d00c0c2480e0140c0c002c2001401141401044046404441c862100203580000151240c1c102640300509222140c011540d000d0709a1034002540783c40307071400505050f82140c0309000182d006518643d40c0e8003152004225225040364103000c100140d902903540ca1070410050903004140c1551034800d40f040042c103201001c402d505590605040e101e170943c1142c0304103820200102d805028900c00c818421410010000c8030414004540c4410202d0740d0005003042c11600c039884c02c000284800c1c0c4220191001031140d030354480542c03984512a040c00e400955089240501000d41d030f9810100c0161700313900aa0090f0450313400501c03c1000f405002c0c0741540c000d601c0d00c40200025400d02c04402460303c2010201c407a142c03070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 845148884 1250 845147634 845147647
    0x118030305030a0b090c0a0206010806040b012702030c040f0e04020603040318090615030b010c0803010909020d1e020306070503010b0f07020d0c03061e0608030a1803050d023f 77
    0x1510b0b04044c00703805001308400c0d49441c0240d9146599040202890018820f2200102c0c0408000a8076800384d41c00507a50b0140c1d0b031803c0c0041c0301d0108082d0400c0c0c0d070f40c030384680d03000503400e02c0d400510300664007003114988440c10007440ca81021040c1c3d02081ca0014880240405602c42200700c0740c21641500d0401c03481c80780c00210031003004203588090f618031300d000b400045100d8200e40d070020030602c81c1d40502060220900448000020b050050286541000100428013880d880103880c0d40c40500b60060f030408546a01c901030f1840c07032003440d001180400d40700440c6410300c40030341d0041d44d9086c4582594100003450b09e0342d001c3e0740401c00c400c0e240041c608065503202c0541c1c02001e0791000040c10702c40d440b450408080e2605060407072464021207652072000150f8040c15043c0d5184400031030134029a084102d4a0441a034034910005400ca0800710114200b4003c1c4400000c2640041c00e0b1074401c02034081d00d0620031044488a02004c1e0342c0701f000d0b0010100c01042e4030000380809170b240c00c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 845150134 1250 845148884 845148901
    0x6210506100e120609010c0e030102090f0618040509060403170c03070e010509101d041404020603060414040c06170f070e031c0801090f020f0d050c210f06011803030503 74
    0x10710503480c80b4900c00c013000c10450200541100c480c421403695118051249041410300381d00556010729442b10fa074100782040ca0a011000c1e00d00d06031040c020301c14401c0b800d40864101c600507144048160000000c110515170880302e4001c1402c0c003201103c205242041c003113165804041d241e0805c020051070038490f50380c42007058641c070990043c561008091a04005025001100203000104810464400003481c0501c80e20490003414002420240e8a176806c00c00c82c2d42c401810280c2c080e5488400c801c0c030354210128644900c1c8240800c0e000c0d24140710f0083c1854603001c1c0004510071501c001c00c907000c40c246080c01c0d04207400b0f050190f042800b180c0003031300b049509003495465016030703024502010f48c03001e2118102c44411504110464280c00076109030302c198200504030b10310801590810a00540c0055030000c1d000c1d00035030400a0740c840c02c02da44401c212803150303065503d600740002c08191a0242d034010300c090030402050100d803800344840d0101407202606020300400040c4285 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 845151384 1250 845150134 845150149
    0x9040b100306020f07120f090e0c1603090315020f04060507060902130b121501050d03090509160e041e091e0506040c0807140d140706210506100e 64
    0xc40d4402c10a5403100d01448240700203030025602038840b5003002004054090103403012460048641c1d50340100c2c141400580c88402c0c0014002d0078500314108a6591054440c28000f00b040303100351360b0100321074a141010406440b16908000c40c1d41d00c10424800d40b808400201d4044580c076082194681c201414280d0061000030341c00385d0001c411011003658002c07650710207059200f04490107181c076580b04090556580301d10780e80400ca10383c524014000e900c0c0100595141910a00d04038008944031000315120030402d441400d10351045800816403150000071519007101e090b50300704401501d41b0588481d12200c2140080c2c00369a4070362007030602101e0054620389050700b41d80b90030100e10528160303a5450040b40c094680050444000c9585c0c40f02282c4d4104540940d010001c6071030701c071010400c054064a0045845002c1164080b801d40e009001002c01400700d500c491400300e82006840d0390f00d82d80c0f071200d002c40c6490881000015611203400078101c0301280340218050481c0400308203407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 845152634 1250 845151384 845151389
    0x902190e03190605060a090902032509021201051005070506010b0f070f12020f060f01060842030d171e0408180d03080a091104090f0b0601090509040b10 67
    0x4110040000424002e01c0c0d00450301810040c0c80403140f06c0e55030314881c02200c8035000001c2d4180c106144050b1115406500d5010300003848680000e1240d4411514041f41d222081030b412000320f1600401030340c82c2c050102011840c490404a19045042d5102134031036005010786071030f800340032440360900340054050741e1110b139100000004000c800d080800c03040b40300500601c01481103040c2009424030120f03105008502d80d2a1070861070742000f074292840000100a001c0448001c203240541007042d001040071594121010003860b60840450160006042221406507100c4880941c41d540d11408150401800c44c074500b0068070b410b45140c401e1002d040c0302c801002c801005000c144000c0380001c03c2d602901c80710040310b00080305d05100540c3c1600c44058007181b0940c1c0022007104458000c03d40041c82a104086c0c3c182c02c1c4000501107812644090341c0440c51080c4050400420643c581c3e003140c0242800c5911502d4440000d21158004100400d14007405020400140d48404034901 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 845153884 1250 845152634 845152663
    0x70f030e030a1d010504080a0f0f1e0c0f06020712021f050301180b011205061f0207080f0115150201060504060306470a08160f0902190e03 61
    0x2514010000c00425025080f140e01c18120a0f0103842500c1e0b602803000c031400c03609044041d00e42d140c00d0380c9403e40d000320780d4882691021100b041103c00580082c13590070380c0c00c0301c0c044001590b00c16401c04201084440c1c1052000428804041c802c480d00010b46100b15034140c0769180901300c0c1d80c4042529a400040070a000000c5135130300c0c010700e68108020714166801e6903540c3c801081c1000b030050035135201d400c0c01e60224a4070410501510b46d80c0c0c00c1507030f000e04050070028003041d0000b00d000a000e10381001d0001600f065805101c144400d01c1045040750b0380303000920074445400d042d10a085450b208854810f00c4059244d90028000c0d04680c00400004200700055503882c03c001010b0040d81702c3c1d06850150009a2070b90742c40b000320000d45815000c41c1e0340440d1180b0201f0303503807001d05500d5903681c0c003079681100007030b00020030000454040c030b05e5106003101c81d107031a0a600301102c02d504030003600e500602046150050003201440c00f1441460300798944003258020038140031026a5484 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 845155134 1250 845153884 845153887
    0xf032a10091703040302060a0311132c0412051e0f13050d03080c031003020d0809010f14070807031205130c120206040b0f04080604030c050c0d0803070f030e03 70
    0x221590700840034208440552800b85001000c406003151a0303c158040250702040911507100941d10a60003011401880d10300c0c10314003098200070541d02c45140c0c2c4429040100c070030410300304200ca19104c804031088410952411308055031440c500c54021458107042150100345e51008401841c641540c805000c00781a0362030140b0f0300e80e4546503101c0d03140c2e0780000c41040070010b0b0350704001408406054141d5107248583d21040b4185060398409803181500311a80c28001c800360b07a0301e88a40700c00320310840340b09036590b24540000d01030f51508400c071001c3c011b0007440c0c258200c4101c0100d07003ca9501c80c0c4910b0f950f04140c41c4c1654043ca51f10401100686090100aa501c601038800c660042c01409030b02d60325950707202088018170035504002c2d0801410b1104025503003c03c40a80068000c6481c05403c26840c0c04280d0300c1e00004580590003d210251400306114041c040c407085107209540184000749503072034080c028840684483c04001c03e440032481a684264070107421103150f4001e49 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 845156384 1250 845155134 845155159
    0x90809100c0218090309040f020c070605070c0b07150b06040f15031a0f010c02120a030503040b0a050112020f0f060a0c0c0803070f081c0612060b0f032a 67
    0x3081d01c007031220200d0103405602e8401180c0c0041d8002248600041d000075490700d0b00803000c2c0b0015115046441346015028000c4d001000c5050005001800c156510982c51341c1e59405c106032041e01039441142c0c0980c04222442c0440d00318881d90403401c40300380000c180800e101c03012840074811580284049032030750402248003003203542c105c1c040042aa174240900e580407a450f00c0706030305407a003003544881c0300803081502d03501440000e4600e500040c1441c6170450b1030050b507810200e520000303c0002d00004200700810030440b0751190440e100100401c001d42c1401d11088010014040280c41424078501608036565102005d520b6034801420b495140c803148c440146c0362162221040300d040801120201e00da18000040d41c11098002d6003010b4140c540d901c034140d0651200e401071100e011190343c0c1c5840401d487c0103c40042003150440360b904241800d14104903102e04034001d100d4445403e00c6c001603a00040d808590300c135403040480030941c401042c01c21211085a03d2034200d082100c06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 845157634 1250 845156384 845156387
    0x504050409080c1e0c190305010216020117130803091e0d0e0405061513090204150906021b12010209031f050108031e031302061815130909080910 64
    0x54501e00e68000111a842c400032404009200414140050f05600140940c825442e008240340d00507408800c206c90595140d88441e030980c0c0c0105004140180c64042a90441d41d010190680b07035134489440c2e004505105846840c040c0c0c0004c1c0183c1407410100200319041c9051018011450843e141c60201e9500540b40b0340c1c035808850040c1c8007185d81200c0c0350700641000e0280070b00c6000b001713080d1502c1401c01c111003081500700325001032a040d00781c0000f0881c076a81d4030040024004000b82c0c0070300307544031100c0100310300030790380140085400c2201c402c001c212040035007000c0400d0440ea404100110200b1a42c0240a40c1c01007030f07854801c80082c0040c85442c0c28107a800d00d106042c0034002c40e03803203038015941c0703214840007501c0741e1450075051119501a88060750300b100000d0781505100303600340c0000303901741c11a1000b09030040700707800c42040340c2c81c00000080c0030307541c108141820424440042c150105030351152404441d11481c0c0c000c104611b0008850707905100500d080d51980c00c4940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 845158884 1250 845157634 845157637
    0xd0507051e0603011e0f06080a051005030303071215030b01030b060a080d0503100302090103050f010507030501050a1406070605041520070f1502040821040303080c0a050405040908 79
    0x9468000c0702800801842100303011901900c1550240007103165920b0848802c0000b185031801d000a108003400c0072805c0b041e258040341c001c0c00eaa80d20000542454810181190b4020b001c9280d10440500e0800243d1004004d40b9417204c1d45081c00d250000b41200980041c1542c2c0ea0181c0d80f00340da01e0004410080d686890300c0c1031302c1c0540038010b80743d0341383e400740481c0d411a8040c840b100e900514072106c2e101e104400640c2c1c00015943e0454510783d4030303404591840310a070811180b941014650b500041c400b441100d030300901078a0244100c0d4508004184041c600d80111410b610b51004001e01c20345030101150003065210004101c14901030501d29a0340520864800140f802e00d0841c650301c1180d50810680d00d400014840d141c80c070340d6a140b5442a15203442140c1c5140703c052091605c1109101520040001c2009000f003044240b0200c200c0e9a0f2480340340c1401e1070148010300c08aa0300a56039039001036403904240d990034140000756001d0240c0d40c040f690260905440e4410405040d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 845160134 1250 845158884 845158889
    0x1501050702040608061f0b0f16080408030d0b030c0f06190315090c0909050105130c030b04050a0509070b0c07032607030504030c0b03250309440a1d0d0507 68
    0x4050070301d40b0707403241f08210f42485015101c28203883c0c248108049691401074000f00e251044a40070325181e5100c52041c10740d0001100e150303900d60760704007003046400c0521200c2c00842080768844003407490035000820500841300d0041c0720a43c51010280500c1c00381d4040d180c003d414120310300005541d03040004c00b5040e01400b810005003100390000307110b0002d0003480d0583d0340041405c180e441c80c0c0c044035802040417084031005c16448200f8900c03e43c036207100d494020f01d8080000301303081c42e0400d403e51901c00c0a600800f1070b4007080101580311a400b24010058030f600556a41c68203c842c0b07a4103a0581c0c1c0030300d054a00f2240081c0c03801c20590080700a20840f8415040090416645c2c074010f82d00d40400c5130400f50206100c0643d04032500900d202480d80246030400042410765500e941075030f40401c90b1032001c90445020045208001528030041130040c0c000600443c42d021014403850340203942c600c00510028070a0f051000191030940100024040c200712681c4003c0d040c003940d100f1061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 845161384 1250 845160134 845160181
    0x31005091305010c0f020729161b060503130501060816150302070f02010806152101051c060b0f040c02030a08060307212102060915150105070204060806 67
    0x51400446000707889210301c061146d00908202450080207001e41050300528000007a00807072110050950200501200803411310200304040c014034124845c491480e00f85200800c80500c200081540f0000300c2e07500000507503450304100766510b0498094003843d008680b10703009030b42005045040d01c0c0c121904590740c100c115401100060025405c81c4030300b21020f404100401040b001550084103900c1d001080640041030700d40b0450329500003034119242e4001d1455507140b041961102842e880340c05010100c41806402c0c2a641290700e8043c8448402000c00e5100da1444182c0d549071400c40440000c0a0014840f907126000300035140c2d4481c1400c50045403903400030503140d0400050140c2aa00660140c41c200d6a21500385100780c20b41d10030171a00050b0541090045034101004900303034613001d1b00103110b2030400000b91424151b0000c0c82d6900b58410301c080082c6287d030288540480b40d42804c03c0c0381c0c0c6803141d0001c54003a06040c1c00c03680c00c0d44507840500803503a12940620404000c43c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 845162634 1250 845161384 845161391
    0x1401060b181203040b03040c0e04031b050c040606030606031b0c1403090d0c1e031211030d0c0906021005060907030c03090f1407120c060e06070f0b06040e0c01020a0803100509130501 80
    0x40749c5015100010649020380003800b9044140d031b0b04e40c105414002c126016408584101c2544000078080d902c250300910f0010740c8801d001c0165581500500483c105416000341402d400100010880d1110f8080509002d580200b2401d81c400284110b542154015001103074428090030000c0c0c0c9401681708003500301d00c04500b0404203450310400202660b600900c001c0c0c104400c1841101c91204451000341240400c0009130340281c0984181211f604880d11542c0090740340a10181c18101c02d1818050030754100420030100e40d4030001555407121030fa0a001a2040010000b18000c0280c07483c01803800744806403100500603040c3e6110b02e407000c440102c501c0d10382c0354034039401030004518008151f401d0381c0300c0c14841c050013003000842000001e030009040c0030340c944525583c6614503605030740c820140c60034001c25080c140149010302d414034004000054a80000035901c8406001c05800c03244088080344121960000200040c00004c1454101382415810074442d1f1458403800c0350a50318 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 845163884 1250 845162634 845162639
    0x515090105010c1110090807170607021222171b010e0303160203031215090c07050a0b04060e0d1709061317120109091401060b181203040b03040c 64
    0xc112aa1540d0583c410016070801395420244208601c082140301c05015220b140401c000904025503c0180780d00c0403000080c21071203003098144000504400115004401007820710811141141d802140000e091002d801c1e0b01c1038542c0c2c958020790081a00113901d4030940303544801c001000d9042207030810403a0032045d1100015100341c81384c0c02e581038168109000400062070180b0200b580715001505880c5806680e00d02641488002c40b4000d6540000c4103070341c21242048038851381e11004101080d03203411915250540d58400340c400c0289a81d00c500001010000305800180e2a50f5050b82110100310200601600c19001d09130b400310000d50800000340d0130f00d4009021030280303003808000c403811100d039100c101c401444128891301d00501001840000080d8a83c806d00800003201c0024000c0004c1c60884070360200c0405115280e0704220341440070361a1700040311f6668081211110464014002042c00d001c0d04002402e0075010100d0001030307611222000b036110364413900185203191f4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 845165134 1250 845163884 845163887
    0x403120207090b01090b0c010e0307050d0f0503070903110a050307090c021203101a09090f150307080c01030903020118260a0206070e0d02090903130815040609020d06051509010501 79
    0x9004180c03c9000514003c810002143d410740284034000d062000480c030880611800d51441e44100d4040320598021085580720a501246040404045107441e91441c206008010820041400b001e40108807180003208559034403c1c44400500e40501039400d02640e0308030040052a284548034054080e116202c082200808100d0340f09004083d141c515075410154180d4081440d8481e8001011042090040560751015507900c42e540b0418449990b00d01950000302901c050640742c1c0c0280c1c02602c003444001808111411250403e10f270000790022507040480c0500f00c240a20780c0380700745110350703031080c06100415512291401e11500d050b22006c4003241c041882100060001a0080d801069185105006641035840018a003581050190b0009510f0100588104ca01a4000a00c15131400028070b003100081603904040c00c8d4641800c04090b0700090000e00003040d503540c070584102150758007900480c055420510411003460f10484800d10300e20716070082d51080d0050800020b456 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 845166384 1250 845165134 845165141
    0xc030117070f0303050a050f070f1a070f0e0303040906240504031a060f0415172a030106081b011805061c110c010b130b0d0b0c040b040312020709 64
    0xa800c1100c00880d100c3c0341d500c0803940d64002d45164400c1010411520110b01640c001506010b40607080041d80c007445440c2112141c08034401070354003001c0c000c0401c4061078101419000180d00c03802c1012100307a0840000f400c40c0f103a0741108460a1600d100030506001a2085001c0c1c000d20311074451040c50704601c1540e19024074480100407505d1590101101003450042c6a00804003400310074020644c100042d06480c00860b40101041d01400100160307250802400440c02c040e00180120f01c5c90350b010350170f02d9000e240b9071803403880746119290403940b02580014000c000c0101601e204400b292150b000004111055500284030440301241000c02900c1c0c2504072940100300b1131800011105d01406241105000c82a0694a0300c0301140c1318151002000c01040380c44c0001851042c0030708120580a5001ca034665403440c2c403180d03c1060320385110442c180790308140724440540d01c071071203e0000e00c075a8224010f810300102c1c002040001d4480c0c0d11a286000b90265481c464442100c0c000300d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 845167634 1250 845166384 845166389
    0x3010e0307120903230109060e0f07270513080408071815150c05250b07050c01050309190b0412081b1309180b09060103030f260c03011707 61
    0x102c405c041071100d24490f450702c914000321070b10008174081c109034498008071001c03480d03000340f250468030b0a4407030001c1c240100c1d40a4010000d103030072410112081036072244003042410642594903000715100300364081d04417030303030a0307000290310b99554031091541d859055611845121003550035444001341560b0042c044041100c0c03084c42111482c1c151103000441c80051180148140e40192501103541030050003401c85104107940040c410520480715200715139404440e030620140a40300004401040c8102001c1003441c100d9225100c07440c0d12418003000003070b0a01410b10310480c14041196104186201c0c0e07001d40c900784c880b0640e4030415070ba810707002c40e012091254524150295a1000c501802498040f1000449030075141c2201c64121008103603900c030300e001c2003600c2d40d040004002190380d00c0910030700948029451943e0251111000b00f101c1c3c0e060110000782d40404086007210b0781c0e00030f40c0c80d600a101c1d6040c101c0d0280798540c028082c00034442d042c810750405032100018600308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 845168884 1250 845167634 845167643
    0x150b150c0604060902130c030b011b050d0c03090b040608040209060f031c0306170304050f03030a090b070f020306040b0702010c1403040f1a0406060603060f060509190503010e0307120903 82
    0x1c45540b10b54884004040c030300e03800c99100103408080c200360000380c41503143c41d541075207001400e1003505001500b43c00c052129852407002080740540062004503019803100414103207448074018615041ea601e13529904055601d8101140011383e040c0d2000740a0300450094a500425440c0d200c144000c070802c0b504110b425030300c410240c40301d00d1020004a59240b0261400080c0552034400080c2c0c0c076450074544803055800460244181d04e032a28603810840c070120002d615000c5203680c0a010010a8410481440c0340801c850090114135070784100321a5004041d00c01d80d2800d1719140c80c000030240c070310308019031070244610540c43c060a42280311041e42e1041038156603070381e40c4104404a507144101d81c540a0141a0300d04d06160008143c05240700300310201d040c03401c015008007203c100d40e0003180d0760b0707001010802c4595000b0342294072407001982d00c4504c5038041c3d040020464000c4c2e04c070030f80541c03810021a00110001c00038000061058040050301c01000c18100c0303148460303010142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 845170134 1250 845168884 845168893
    0x803180a06021e0c1c05090d051b0d150908210a0b1002071205030712051b0d0f0c171605010525201641010507150b150c 53
    0x943c2030108202103182580b41c6c9009894801844003150b0502070b00c01049941d0391101890419289084280c495204016181000d80e01030503168620707542c9010340c40d840305d540d50300203441c14031440ca4100d4100c0360840c04890602404442d04100103a0215811024245061852000c9107044c1c105010354543d01d034003c207449030500c4440b10180c6218070084659110400110700010403201032201c00c00c100d9106d05440d070741c0b001e0f03850a1580458400e461903811001e44502619040982408500454a000104e0003828501100e100c6080b440c030100e03038600440c07003800c2c5200c8245404200383c030601c0284010307100c0c01402c1c0100468107205466284031112071003040c900c94149030303410303c480014090511843c41029406e21000c030501d0660182d144030b0034401c50003012844904200240c0204c0c03100303d20508100d007400c9072141204411a104492070300340e6882202503400698000c07000344034014034241c90b10020400c4c0d415a0780207907054150618141c5d00602035840807010300e000741 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 845171384 1250 845170134 845170153
    0x3191b030f0204052106070504031208040510050a06050f0103021204060509031612030b030f0d0503100512011a180406050a020403150b120a0309030803180a06021e0c 73
    0x20360140000c0200760040c0d40d402d01000a0540d07079024a000129001003811030780e6190117403601d0802d00b0040414061200030042080020004402c8607121140391404480301d413218548a1704221608805841c00b90070300d0180110b010190b4481e500b210011030303a60b05840030400c0150260301840e06106019800400000c001ca610364101036802501001580c2c42c0034084900000c5c000d05081c0e090710725004801002c130324a5050302c034903801003038100c0c001c0c00b48100f88070311590785500000b2072004001000c4041106803400b03000c288090003009054150316461050014000c3c2150020741c0c24240c1280f001c0043c80c14401d0446024890032202490203994a44610b005000301070030944120703508000000104054860400800301e8009020417801501410418220300d42446881c054000c451718000003134010401400302c0390f0040c0b48903100e64405841c2c1e00080441038424900e4007648030702a003044055401085041da00540040b103001c020703c120096805580c80101c0d01d5440ba4202 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 845172634 1250 845171384 845171387
    0x1e0f150f030b0f0709050306070512010b040302130b190e2a0711010905040618050114130902041107080c01181211010b310207030e1c080f03191b 64
    0x400d50000017818410034066545021914001003120300e00d00042d408a4900c5842c1114448240140740e9503c200b0b06180c150f80001c3c00300385006d882c0c180800e40e546981502a22096845d040b40044503482440c01540e0f10b203403201e01f070403c440400010034070b03452404000d1000c1c006801a0001d0569160410045548292210200034046818410780d114005a0341d515401811b02407d0f07591841c22022407800031080a90f081030304000d0b018032000148040c40d0f103400d0580c2c4605154580c01080240260010400401d1410322171084007030009088002c0c08020340080c001d90032800002c021941400d82d01241040269800411045c04460761800e024481c007220382465440c0d000001d00e401040340041d000c00c01019468028a508607451041018841c0a0790300000ea010825440c01a9668000700a00035841040d0f2207900b04102c2044081c0c003000604416aa00407046580c40c0080c80101d05a90421240c8001d1121000c850807050003950007038500c4e14405208071074114840000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 845173884 1250 845172634 845172661
    0x50c04120213020d0606091409190f021308012a080402040e1c1d060313062304050309280e0a0f1b021e0c041e0f150f030b 54
    0x81c070741c88040e024004c0b402a01207911031400100a1500e650f0010340c81c0140c544081c4c0305c1d00d841148644e00c100700b0031901003020544860001040c0d80000307019000c03000d2040090150204401c1d0350010301c038001c40c0902055101c0c20501055403c41c0a10000c80e044d20318410440801041c001a0114007080040c100f64003c9250ba034030340400d032120001080058100308400e0011240002d10003005540002180c00f2402402201610010700d5841c2c852800d080c3e0035501751004100a40d6041208070b4907903002c034020b0300c00070541c40a001c0f500301401e049a90790003100c0000c1c420302003020202c15204150203ca0742041940c0700680901e031800c03082c42c03e0900c0040c05000015212000803055440501c81c854920303d000181609260391110700910b481c454507404806000280d658003101c002c0005c4c01c100d031684c220b42c040b40f41c03000a85222a0030300100c40004105041415444080c000d03504450380d81d00c0085210a0020342d0b4200c50b01c1c015500c0e00c0b001e8111503001c808034000d030107080c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 845175134 1250 845173884 845173909
    0x1b050a02040c2015100501051b0c03030f031b0316030c1e091719060c0318050114160c030c0c050a030b010f051005040608070309060618050c041202 65
    0x203102649103c608805601c0250760712581405810007080e0030304640d8440c03402a0401c2c01c490f041c4000500309000038080c2c1c802c00b103165a03402e0009a42d041c4e800001c100d2503803007a0000e0282d0361600d5061081850039003043c0d4a0001314420b0211109131a13681c003054a228000490f40710840f04080f074030a4000b02030150488040003951a82c4520342e015403a082914510719a81e2490224a460b06800510840302020042c1da003005446103110303244441c04019007a00a40006030801101030300350002c1071480d8a2400242d115103e64047c0310041d8480043e0f80c0034801c02d5402540c0e01c00c07506410070500c103030000100f000203403000c01013407040304d0003c0c0b0f00780303d6014888200e4950001038039079803030341d03008450400121006010980c804040b40000700000d032120b1303002c0c4a480801900a0040e4010b00f41007181000004805ca403190300301000d09a003198040102c5030703c07006050940b242c644240700207503051001090070944218100ca040381c0300031654400e6aa40c940c00c020080744d144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 845176384 1250 845175134 845175137
    0x70807022107170f010e1c05044101140c030705120c07060212040e0624030a060e01050607060908070b090a030e010f0207050603100306050103050d1b050a02040c 71
    0x40c1880501a010840000502443d02c4008850403a00754030501c0c046000a03040d10b1a410f01820130710940000540f00444100d5040007803108200413070441d101d00a65000f10510b02d12005508022003418580b00305a01400584c0103041c401180061413403206903003000c0c00500c900421a407502c2c000307400341a1405610055034500700454861a01e084803104400718aa02d00180e404002001008000e00820aa0014000010010101d0091030049100300c041d252028800107020380c0d00c800f80d640302c000720317040c20603c48145002d0488081e0030859454003a10702d080d8000c2505d010202d15035040701c60082c012481e00c00d596039110043d049404048a40400c04c0c0600000510480356070b600ca00301910051801d8042800c00400c50fa2a804145062204c00c036070400950764003140c130700103940c0207032003996980c0c6072145603403907085469001801d020315000c0007104001c800f00d40c0140a6220760384030760800089810f58081c0301c0d041103000303001d580152060401414141c101d040d0040e2103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 845177634 1250 845176384 845176429
    0x1504021c0b010f09061703120a0e16150513090e032515090b130c120b10210308071205010905040201030e010b18041506230607080702 59
    0x103030707455042049082c0c004048142d4181014418079810384165001002401c580c158904031046215840380f041e9a0224a0400d043c0006280085260061042d00c4040f034101c8525041c003400c040d06620050217558041e805110350011079a10810030f441248801c2003a843c0304078030307222082004140421109100c0d000038040c24031082c4010084c45210380365400313a81110a218905981e018440e4102da04440307103051111804501051001940202c1030b8020090000d034030b060a8292103020f620180301131314401300010400650300c44890043d0005280c0300314594a4000c510740c4e243c0700300060040c100400ca00d540106c2e219a4056400008074200445018010505141074070310907001071304815110800d100440d40d06110700c00f09141d003c00200004903103c400502d01100600c02d8003175100c0188040f03001c1c4603042c03200c024204480182088882c0d95250001403072380001c2d81c443d8518901104c0c401c41400d141040720b524a074042500307850081140d0030000d038a28000900400000d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 845178884 1250 845177634 845177689
    0x40504050708031c0e1f0b01030e06090d08100b0a1b1a041a04050d0e03010b1305010503060903030417030705161104200f0702030a0b01060c0c0602150402 68
    0xc244000e110301c40c6043d600320300e009004c00d41c10094400d000f4081003580c0c007103003a01ca6a610800c400040003044040d002c00d2405035480101c3c00b90201b400d00f115517003d4141402403002000840b00a121120717110141542d403910701501c030500d602d126007410f020003080802e20062180440c031824648205030079010074025100d01c03141c140020040c2c130959071900c00384000c2c0100003250092200f240e99a00c0510b280c6641c4440d200e8a00100107810b004104458907816542034101460001000e072240c108140c0e1803080310054078003845030b01d0182c0a0003000c180d01d44000f00440b0710454000e03101030192081820307604110391000b001101004020701041000b541d0081031511218002c06510f00d400d4504002c000803140301152019107054260394160700d8011807416621910024440941c40c0e001070300101341001c0d80e44c480100302d40b80e290b00101d0715540101103003880b9070140d0381001e01c0a440e00e80507a680e007481c10281003400c443c0070003c0e0040c0783c800b0b0f1041c5814001800d0742d44422 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 845180134 1250 845178884 845178899
    0xf020402220602030307350601020109080d091101020a081e09030d18140f0d030c140106061407030c020d15020c0a02040e0604030503150f060403030e010f0305060f0405040507 77
    0x25142d0407000c0140c00010602c40305c59807014041041c515000050b064440140d4420000020008445c103c01c41c1d400c000035600768000c0d07001584440d0002d40380f9645082c1030200e40024184d20404913440005044610155480020840340303250b0701101007480c0160300304080c0c8400e84842d00b076061f064000c1017201c0751394806100038910382d229a2640d1200f901d1499240c510310781d50303406c074500c0c0580c501880303e803507074902100030032609050f00c0300d0b0004d0645041c11501d4800c440b02c06420130440020fa80d0070248150b1107042140c09540e030780700746615000740155041c807800c071010300042c00302031840e400b5207049500b030703140a403084429451440d2400781510603600003000ca00c1164000b8401d100940c18903008180301e4008220180207189440e83d40034040740030240c0700301070b13a502c40202d4490315220716040340840300340202900d8686540f8030300204291450001140002c8017000b0290325039000e40078150007160b0051120001032070100c1400010131001300290341a100d04d45000a804 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 845181384 1250 845180134 845180197
    0x60f18070306171e010917030103030e01260910060f0e0f01030c231807170c04060e030a060e030901090b0a021e0f16090b0d0f020402 59
    0x105200021081a00e0140406011203003281d000340d521480c9040a01000307100496402c4405480303184042e03055207110b07440d070300400150030010300e07405000c0c90503607010850001441c1240d10135503c0c043c13038040c180c2c01129040d1103854001c1540c8841d004201d840c800044175103500803800c204817840740500800945c15240e880c0c0c0b05180e10429420103200c0c000307250748282d6000c0c403007000c9039600c1e51541d80d03000c840c1d614038800c000d110300b807004211181c100000c014094026009003a030b403020032080011042c01300d090b62103c0108640f9030040c5201041c071460300f0f1251001500c241d007468074281c1700b41c3d4010003058090f907043c050026080e00245140c407680150400510080d80c88a031300307400240c02590660010740e100b900900c1440b84051f4005989080f200307001d04269400c01c00c0000d0b0501d090302c4540e41d15091300400c0c4860840d844a0310030841210010a030501958641e40144161f02a030054060a8400c01070715074405420107030000e000a0826100e5181e065074446504a2035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 845182634 1250 845181384 845181409
    0x2106020d060b0a020705180619030606060e01110d0c0305030a0b060f0301051503160e060c0d0804030f0905010e0d0f081204031d03030d090c090905010e15060d0605060f 74
    0x11100803e6410f68268100f01c041e020304010384440c5034007100c0150042d03a0000061445d807203125952070b95080115004040740003036a10a0302800140d40b2100044d05004001c3d0007903000400c60300d248000c001e8006401209802c83e501c1d0b02441c0011914111080d078001403c0480c0c0a07161480e180342c5440d03800003050006170308105a038a03541440c01304005070450700d451111340542030040c800200e013441c4021814018a04106800c1c4102d8000f082640c012404a2070315400f038001010f2056802900b002d104500c02d0342da00300d8082c15590195065501400ba0900080c10381e407180740c490806000c40c06183d4000c50060140c000c0c950b0b00c03004150300c580080d10200302e51405010805030004c050b081c24003524170300700300c2640792000400d0f03407030113030008903107509460300404010700050820000162142100c01c0c4040b1900341071a6004c0c3c4481c0506115510510b03009401c2445840d004901440d4010b0030583e04035480e40743c00b00900f00c003800d115413100f1058034960f1250303a5071002196 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 845183884 1250 845182634 845182649
    0x30b03030c0a05010207021e150d1d06090601050301021905090a0b030408040e010503061308090d02031b031507020c10021006141e030d12090803010b0c12042106020d06 74
    0xb07407078000d48140103502523000c1c040004a04034144603a4241c0c1d86c41c0440c0585011801c2c50307500c4424107000500901080c81d641e829100020136003101105001c1000c0b403061030003e04030382140e43d0714410703d400c0340b090b414a90214402c0391406030703085100340b009240b14540184426a031940320584c1e03803059030040d07404468840001808005003041e00c3d0700b880c014481140074203201e19000940b002010348021000700006000280290701c0d9803094115124260013a08130307155000e090b1040f80307548001c00c0320700d4400d119940b00e54000c1000e1075119449036480d6406004001d20000911040000c05083c0100303601070703c10400d500350214410800140f5020241d55540e0042c581480220b450090810500028080f5181d800b910005042c4201c090700340740c80140c003041f011341680240102c00c0000d11800c000000040c0910900b000390002404000c1560600900041c40000351b100380e2040641103084100e0404104050324604480940500c802500e04140c40da030303601c102c50705600081d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 845185134 1250 845183884 845183887
    0x12102040609050a0602030c03180105210618100e09120310050f09040507271e230109020f120907030308090307030c08030601111608121603030b03030c0a050102 71
    0x20982c40c1044c8140e00600c0c460020b58603101c1d1007103c0c140c481c491500710340c240a500b01010b04c4903034455012541c01703155960501540c8100c41d54080034006055600d50b1281d5100038514042826140c099400350300099103102c2620301c1c0100d030300c400082c000c04203c0036000310141000f504541c00011440f501010b06182107450500017044040c060006000340030f120310008000010b080020040291419443c80800d008850070000c02401c502050320104542400d248400f9a503480340c102104c51405001823094000310042c889081000903155004144020010490381c1d509600614041441c05151450b100d11000c000700541c4041d9444507941e4891b140400070f042d40b0407019a000003460001d1441c109054030003c01000b600b9601600c0c0c03000010218040741e0061290714400001041681d0200d10b44034800740501c4458403c9813050f000d00c0100b070b071451160508071816481c6808004800c2c10345518120700038441064500c0c0c1601c400c10128070701003010000942124407420016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 845186384 1250 845185134 845185139
    0xa020a0c06050403110d08040906060206041a06010f030c050d050708041a09120c01023108060708150a030c1511190f03020718050f070c02030309012102040609 70
    0x31085100d05074000400c2040a0000b400042c91440003448500000c031000300290103030782440c521600c5507501c03001c0100d14001d00010040d401040c0c0910941c0030303c201c108400ca1103464820300c01000c0740c03401e001900000710949514040e0780200e8503911140340c250308000c01810f85000301d600594103200402c01d000c0c00c00040000c440d000c030f159160304901d03020036410f0049606a450130382c00140c10500c1c0d408510604480e00940c142c50519040000001408510f50b03841c0d008080700c10301c155100321105601082c0d0100011350301e401780d01c4566840610b541c03115195400404161803d5501803841400000840c44107510a40a42002070082d82100001c1c000030700300480d01e02c1040807540100c0e0310380e60195400c0c8840081c2942020141048202a2804030704024041d000000314800c18611046601c03503950229201d4450025005202d8841000035211510020700080d0b06030300410500c011540700c1c0c803000d035001c08000004030399010920024410ba8101c0d0300800d00240804808 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 845187634 1250 845186384 845186393
    0x1020f1c09050a051c06020921010e0106030c06111f0915090c061101020714010c090611060414030d051e09160b0a0e130213050603040503071e051006180e06040b1b0a020a 75
    0x4110bc0090300d00001c2282901d035a13105081c1c00014400c01081c000200c030000c240210900c001c102c000042c042d000d00a01c000c0d50880300801d4560b50948060301d480905000041c070511807859140d800c1039110041d03034a012800c0b1070784401c003842d00038555000e101c07c2001413186020300882c44903c10011420b000f081c0f03c01002c03503100381d00000400010200400c0c0501c0040f5205801c99084070002583c4044031240601d140318a010254021386440100949120551100e00c03081c1941d11300404543c48401c0d80ea43d5460140012780000e401d103510410107481580010000d90b013041c1090300c0c04a20550000340380b103415080400301d25400040110601a415080304081c0504480c0a811414a40c0301c0550b01e004501000b0080194207008811400001c1042c240d920340c482c0480e00e00e8500304001101401c003c0c415145035014a0356420440850350041c454000722880050003240d40c1c1381c1f5a00e01c4a603020b80990381c0241c1c0c01e03020011445a29000302404021038005050703900140c0f81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 845188884 1250 845187634 845187641
    0x302060d061404140402060a030b0a0b07120302030124021204031a09210d0b0a12060501090209060a0c171201030317061e01020f1c09050a051c0602092101 68
    0x30b0b0b2920551902561080300b50308040c0340d40c0c200b0340648100b82c461155000039001410003800065005007201000601c03840c000004200f0903104444003010405050801c1d0160300081c00f4505610f21864240d444030002d80b0b15003891a6442d04c1141c2c807441c040d0a0f01804c03941309810641d0480c1083c0301c0c10cc0602603140d1480d410548840c01407143c1d6040030010900303003d03c060800030262000030400034000c295001213099500040284405642e1019500d0760340307035180030480300359060900000c1c60380e205209640c2c04210140a20b0316080003840d0444481480a2048401d001c1000e850380d40c42c104a000340c074107181c0c460081031895055040117003c0c0760780e42005042141c40b00040125070307180e880780036034055078012100388400402030041c1d0500400c6001c040c498803902000d1034540c82c417045c000101103100c0e126540900d4684052180c280c2d00c0e40503590304007003a0820007402282c203141c50311405002d00790060605114000245d240d02c504613125203024020801002c080701c0030310 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 845190134 1250 845188884 845188919
    0x91202030a06052d0c0a08090a02040f0902011b210504080d03061d06061207110d180602030c0a0809030f0f010204030c0b03060d12050c0708061b03041e020a0302060d06 74
    0x501801881c0b920000c110010700c540c2e0000306c1085180c001041250504000941085034010010f12a1a01074140b0078010301c0b031090141d0010b00000300c00c03501d2440c0c076036001340b00d580c01c0400800020080d01d8260306452080495400308802044000303100c0f0000e1214945405c050b0341c02180503850031010786080e80c8901d121101303004400041c401e06541d484111510420b44220910f41c0360b549030400d4802115040d4407022a00074400c0c00f0b0750081c1d00003450044041000c25080d880358543c078040342e49011b880001d00b899844500c4002c0891400c03000340c003d260f0004c04542c0c2810890036114101402c05001038400d03034002c24103000300700d120a90800030305501c4c07525900f580303010340000d050740303c24440c082c054600415800c07900034400e41c01c9a44920b0702800310764045941e1212a030703840d401121002078040880a1802c13083c96130b40100c90007650070003c1d1005141c00701e20040c50203403800030100e03400024690004010b03244c0c0c101600c0c04039415140003c1c802c1c50000e20b40c01c000c0a50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 845191384 1250 845190134 845190211
    0x6010e0c03010605030601120605100905031903050304060e0a02030a0c030b061e19051905040c020f15190507050309101b08100e100311010c03091202030a0605 70
    0x1d10051004a40c02030136a684280c092802c40c0340c1140350200d480023040031f50080c68204140c80011068240c01550103022250103404441d507205824070602880309426100900003201000070030042a60342e0801c2c0118030340034054903814101c2e50f0000c1e240010806c0200c0c4d01d00d030007101c10014002444070f010741c005070503215072010340c0d18000408103481e00025210701c6a0444d000e90a502c015041980c00607100180c503030306402d42c200c42a500d220140c0e2098a100380e05040c016801c0601c0030841d1341c6c564000100400b9102500c2c0c0a11400040060401c21550720348054011418018050f01c1e00421103034548c4c981e02c1c00c258000350300345103002e2400300d011418280e09140066581e800d0740a5001c01e03203000c1c049a22851034498503da03c903800481c1e581c9a16051105840c1c5800000049070302c10710b102e05180946000541702d01300c6d40b1002402042e2004000c1003448035a00d00c4c00d420324402000c1e1121018075a481c0b40803240241c801550100c0d085501c6150f0b4003000d11a040c20441a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 845192634 1250 845191384 845191387
    0x1151209020a060f09050405070e130218060f190306091a0105270604140901120b0f0a090b0f0115090f060f020f070e07081608060616050a0506010e0c 66
    0x1160041402c40405200d02002c01c1114401400158400d02602e000b07400010024011410f001c4001030502c8a4400d19504c00e50300c0c1d01248501021341d208440c03000f544502d6140c09004400c0401455400c800d140541020f003c0000220713402c82550f04504201980c1c074005155814481c03164100c40d2815081821051140d4040950381e03045401c0c6c0342031210004082c0412403805d44548100908408000d41280010901160410a40ca120a041802a41c2402e81a80e0350a0201101d0b42d060601800f00300350390001c2034011120b404190f500070008500410203080550742c885203108200c1e1080070914483c00140020700390443c62410031922403a0410444d418080e40360003001321803098070244001c88900000d214001c2c0910070300d028044050301c1c0f48d280e0b250aa601540e8007144c00b500000d010000290040e035182c1c0400300c408940e965507184d207a507a2001d200d1b9950213a64480105010100d240000940401c07004c201c5d94412400f401a035450008100e40410029181030b050620 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 845193884 1250 845192634 845192651
    0x614060414060f03192607080702060901030908030a051501020c03060f070905030615011202070b07080a110c0f0114010501020616050d0e031b0606030d26011512 71
    0x8810880703903004181110058a00101640024070f028424080b40c8142035424400106111413000d0030b103400c1e02d0003482d10340c510314504540403180c8501d800040c18044203000b003070094240032000d800025018100080c0403502502c660490790070880760361400a482e6000c01c0100c20100b1081a0784040a00042c11000895800282c440340000c24005903d54101c00180c0000d102d00ca02d030005000150175103809003060b00b104540441600305660104050407141a1043e0191080300d103030503003004400e081c6480d010f03030884007800c000e041101c0a6441320030040640002d100204400101e0304010000d41c0d83d01da540609481000d480c002e0265a14001000b00c1d903004600c056001c030f02107000a5a43d008024244d4407405102c108416441c5031070041422000700200038411092102509401e000d10040f0082e40d881d401c82da4140c141c0c1000d0141281d1038022400000d80e0442d1910440c600d00095010501001c801d80c4001851400c4002481c140b540140e02810380d005810810700843c0c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 845195134 1250 845193884 845193911
    0x3110307060207052b060c020a06060b13060f02120a050904110301030c051012050a09050f0f030a1206051008011707030c060e031507090f080106140f01110a06140604 73
    0x803403401701c2c0c0800b01c40c038102002264011040e400507030f64000020810130104140080d03039401d03940e408039400761a043d00400d007052040161002c240b11841c4150100341070034011102040c1542c01c0c6829407158400d03403448040f122002e031040c003401d03540d010b031a00b180d0340402054606041e900240ca8400f0030040c4003044840f0803078802d4410a503651204005410001c484126a002a00c42d0040c6014280516400b050304880c549a00500c1120340c0c0030070001c1c811380c54441d010111030240c4c0c0100922079010b4040c1710070303002d1901280340c0022a150f132030303020030401300c00105214000390300035005110001040380032010381020343d03004080103407c40d941d03094074030024000ca80c2803011440c0103201d10f50301004100228164a0a0075000d42840e04014001c40010700900219140e07461003c03a5240d414403504044414003a100c003036a1350180700b4880b581508006841c108054a220445422070811091511610400700029003a20100e520402c8100240640d0700c1142003415040018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 845196384 1250 845195134 845195149
    0xc0a03061208090609240a030c0e030c01210e010f050c13030f140f0a050f03090a0e0c12011502010c0806010c020f031f09050c0406050a0605071106040311030706020705 74
    0x695064803c183d6680c200e000040e984072130110005005003640105c01d0f0311030f2100c6c010305200885900c0030720409007180300584140505800c001c0d010707402900320041641c480d0031404000310b4503c1d40c800404240804800a481712044000e8290391518034040440009101d0642d011246204617818030b051500743d00075915262001500080c0035a6002c403d001c0014010055001c07404103d03440e1510340c500e00e94547d8613401c0203641da0b0040380c4940c03144c6a004030440b240e5101c000c0c004903045080c501179803100b030406410003803005405d119154810381c81340035003800790007121817141151001c900001d0a43e10340300040c00c10002c0390010320036503980000007000182e60443e014a140444040460701d044d064806800d410500a07115107015503055200032812402131083d1880b000071401480266511480f0f150f40103070701050200409440b030720207050824851040e004041c04e01c040002c0c04c42e04240c0080c0c5550a90f44500307022840c0c10803e200c010407090029203034007403500d40085c0d000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 845197634 1250 845196384 845196397
    0x1210030b0412020c0d060509010c050313140c06030f09060a060e180f030a05070c120507030b130c0608070f080106020c011202040306020a1e030207050316020d02090c0a03061208 78
    0x1110381d01000c0c1450301e4024003d484c00c641d0040c105915840c2c2c02d0414001414056420740c82652a02c102118032900c64002c8130b108551a1210210040c5c141e0340d46950303131861900c000c2c140c0c09170150802c103540d036190045010302d642920b821441c3c10503d920078284500544805400d0786044c20401c02508000081c9601c110809075826880201032030320741c02c10f03020f4024940540400100d1691054004016004132401100204512a15107080c4202100d00380360147c203550103400100002000300c41c42c294400805009420301680d140c1d42c02d03151044030b412a00100d85a80c040000e41c0f0350141a0600c1c1d00310138503058400754900b901c080c1d241d08a4110f018100a50000098041c1c0d0060701103038015680b0500171541c0d0204510300800462520b10099034140402c030740581e0540c80fa00a481f5170a8004024518108000035443e041010300d01e012600451407401040259a0b86841320307200340c4c001c100c2d10350b842540303943c0201151b580750009004005804064404960108180c0d4003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 845198884 1250 845197634 845197643
    0x50610020109020319050f06010b04090c09050906060f0705030a050702040522110307170106061e020303071805030d031b0c0312050a0b0d030905090c1810050c121210030b04 76
    0x40400306e05049007401d28a9513100d24030310a041c0009800388280d00180201c072001c07501001200000101162124110303c1003d40c0100c40c40c0118010b0301e000701c000d082d18152203004502e44645c1e680c540341150888924080490703004100c80c0306508141c050540d004590a5400a400f440717801c8d250403000742210060120300c4019890509a1070800200f4084c2010400742c40346810324000307940c0a040c00307014003400240c0b4400c1d00d000c005159403e400700030005401130340c25a030740c10700200c81c40741d051503554500c1c0203281c80008007a04d041c8080000a021680c010034610000014541c0074115000d0083c01c00880c9140440420b600180b51035022103101004111511400c40d200c01802c80d113120300d648010780f160700c041015040344450040713680c2a0340312281c0d6a00c18032821014010f20388103030612009100d12150f18500000303804403c0200d030802c03600301248094103901d000008000e5a8440100107041481d00301c10300807481d0f101800c80f801c0112035055959090880c10080c20080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 845200134 1250 845198884 845198923
    0x60911030f040314070c0f2916080408100b1203091e0913060c0207050a0b070302071e17070b1c0902030a0f03080a0903051c021c0506100201090203 65
    0x18109803082c4d51105400c0402c001d010380741c0e00a070074805084c500b00c1c0b14202c1c10b48a40c040000f010761082d21800c1e02c000b1700801030030040c640540d44000035800b46010900c40445810a0000180c811010b032003d03000c50343c0144440c500f085494421507010110301441003400001d41e070f5071154000110303010003505440c0d0403034400b02c1e10000c1a01c00b840400321030b4000102010030443c3d5200c5801000800e029260a000d80c0400d904180d840b94180d0048079003210750b101c002d20910007030200030110940b09204407040e145c1c0ea00c244c2d81443c40d4204a210401d920400c0807c00da103540c20841c03c0d03000c3c1c0a006491050b26000f00c0b14001c0c415100c45080c2041d040c200c01c4000780740ea520501e0141d8028040c3c440c26a4607290903010810321142c118042419440811040303d02486025452685a1222031412156608046524805180c90391001e5000c00c000c40307020115800e500500e041c2c10304045418140007040281c0050304283c00811a0300d81000d000c050307070b400240132040504044007034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 845201384 1250 845200134 845200141
    0x150f0102070b1903230405060a0507080403052a0f0c091005091306020f0a11010504030f120b04110a08060d150b0a0b070f020301060f260313030b060103060911030f 72
    0xf5800303080101e40010740c5c083d481038150041040d40e42110700c224403d80580707115a55425501046450030f89031203000410b40d00004001a00940003020300c03014968000d0502c0002803843e00c864a0144000c0c41181c214444010281d5006c001d111000101140c140d481c40c0340c28800800981102d100300e0384181d40b1680800c2c50580f902070084407031600b0903402d5540d42100b5000e4203966200c450b00000107403000d40404c80c0d440062003214065079050343c550386030008000c01100c109039190400c485080e03440860920310780d0b90703101e032000242c03a02e03240903100c401c00c800c06050042c000700307218001c04103d80ca01c0001035440c00500d402254000e0b00080300000c502c04140f011203203411a01002e0381c0040d102c3c040c000e0741d00500307254901c224001d200e84c83d210745030460243d650f03200e4040020070b80b14405081540c1c1114043d084407580b01228141100003180780f14000c200e42c01510354070a0702d030500c080355030301d0f0181001a02d1800024440240006d488014620006103401d00500301c20020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 845202634 1250 845201384 845201387
    0x9060310050901060c1e02010f030515040c0c05011b08040f03031806050615090f041d0304150813030c08090f040e030c0c030c0f012303150f0102070b19 67
    0x14001404002d01508a5076840b10030180c83c6030081c0d03c05407420700000764029007103a40140c20420080c2c0c1a582c80d5142c1090041c00d80140101074403d4030f22600b13401d81688607850341c1c8210395680390076590310821a811401d185086902044000c0007036243c060b055440c80790400e6150b03401980c40b07548040c001d01d0303c2c207007200103150794000e01213980030380c0d0000070510110390850303406424100d845080300c8540b41c0001c0d8552160407051034004030f80074000c0249140c50b41c00304d0b84d2817908202e07543c0d241000101282c1507621a80245e5280c444004070003c0c0a580140c4c40340e030100340300c0003014600b03219440182c002040440000d01110700011079800d503480b6280c08582402000e4818060040728244094480c0c000441c146860301c15888821060300e070020700850074160280600f19070360103907001140d0654051540700c00442d5510607200743c8040542c0114415440d0032440c0654540365400c1003030707002200b07900c0c40c11942b080c1d000703014900c103001c00c46a50b00c035210295a0b007041d88940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 845203884 1250 845202634 845202661
    0x11010501030c0501201b1918091a0a0c0801060f090302040c0215010801230c0405090405030f0a02100501061823030703080d14010f0303030c030212090106032303090603 74
    0x42886844c0502d403980185410100410300c01400101c44c2c05044c0c0c103004034071441c68555423092000070740c04075405020b454495401424541e00800d2140840c916038031030070850300701c1510b4001203c0c0c0d8030024001c03816031200d4500d014103110316180c48900182e400003080c1849500020340b040d59120701c041c00c4c440c020459021215007034604244107603520088180249501e1078030100c1e544004040c7c807600c0c1404250b0a1150b8151900a4102400c05040c0000404014022101e03480708000f68006445440007502c1100d610768000c0c5124480011190203403801a4051003d109007545001080030200c8030f09829540b40c0305c1051958154810b0f10000740c00f55181881c0c240c011301030048148002c440040101c00e006c08014050000142520754071150309210382004003100d441e0910009110342c120700c100c04020f02c4c0140c18020440408010014142c0740440e25a643c2c2e01c003003040010300d22a100200001c502d0b4a8082c0b82c00202a40e02c0b4130829110368481d0318000300151840d031048030b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 845205134 1250 845203884 845203937
    0x402030a0f0c021509150a020a02120d020310050a050f0405040c050d260a050a0302090d171b0303090a29010303053f0403090801050c04030311010501030c0501 70
    0x14090b0240340707480070f5101c41e50060b48620881d0001300081c03e00c0c20029032460401101c08620141b42e40b81042c0c0300094201d010030100314021901c4140070a0900f002074401d030010329400513500d0901d801e000344070a0740c540c45180900102c032010007a540e036100c14100e0103d4103840100d00c680c1c0714501642c5840c15500055070200010358114103000f01c0c039001c003004d40d0b0031004102510400c0c2d14007403094040c80710030b000041c00070003a84403824400c0d000b0303201480000d40b0310003079440301341d4800403058180000d05c3d400c031001180e10a50302510080080080300c009002c0c5186090941640341c8640340d900025102d81409145410b8a4464048950b905600390405092650312460024072580c45a0004e180c075500080790303162040c42e04219241071040166240b4000c000c91642440301240040c030550038450b103d000012460004c1c09594407075134170f014003150b07140d0031890082c208105891010459030b14001c014400140001005005d43d072090030004841c00d00490b0300c1c4001000c89 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 845206384 1250 845205134 845205161
    0x60a031802061c05091b270106051207230a05040905040501060e09160303080604200a021506210316030941030a0f0b01061e09050402030a 61
    0x92402c540041c003c0c0d06610819a80c0c0060290340c4410f00156612240700e80030410244075410614104e00e040c802041070002403c0d454455070401801d000e6103404268051008200300040200c000031018030041d510500d00d0402500e04000d1040118100c90009c645003441d110000d408803055000700151401040004800d0215203410b16041c0d0282c040c0c0d12890304c01204a0303000c10f0003010042003c801602509149224941c40c58400300c59185020f0300359030700503558600c2c07524942c012021000e90060b003030031520340d04d40d0714040013440c1084180a0a08900740f200070701c0400da0b0307003c00065144000e101904003507100c45090b54250b104400701d4400200b10204103004040d0003140340390407150301010300c802c10304041000c0000200f04d81d00c1000700b5082d8007150004c481f04076400c008001c1000e000c9840d00d18851340c81300740207908040c00b40c0350103038000c00410031184d01851040d400b4208050300e610700d00c04054081c05491003405102d00c05d030303000710019240356003540c808003038080d08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 845207634 1250 845206384 845206387
    0x20904060e040f051603210309020d0b07020d09050f060c01110d06090b01050c031e1b010f0b0103090c0306050c1603390f060e06092a060a03180206 65
    0x41c5040d01c1039401540f0112858040c10034044202c038114070090017102e82240080041c904c1d00620107034251100304410013890356582034500940c440da084d014025118110010040c205480f000e481c0110307404041c810440d000b40b0520068584600d619030411080e0b841c01d0f1074400c8401c0c024054a6103c1039034030f0780300000c01d10f2007441e1196040202198034642c02000000c07510401100c43e481140018041a802008850100e5403003198400d0080442c00449007011106c0403640102598900c1c40b440f5607450b001c100042c003c541c41031a0003802e090030108044511951080c061459900c4040c2615a90b0400680b86e000c08408440c10f0000141d02c0e0300d441c881d545005081000142d001e040402c07190700d030490400d250100342500340da55502a450040c2a42d0703680c5000000345082c100d85954860303d01d055850820010b0600900c205009407880b240d01200c0080c515601c2282150003c0341010748075016110320045a0080000d864003260740291600f01d0742000c0801c020007908840c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 845208884 1250 845207634 845207641
    0x41104090c090905060d0f110307051009030b0c09010f050f070c091a0904080301120503130303030b030d052b0e0a030305010f0b04051c03090906030503120109021309020904060e 78
    0x18040700709800c0d5200f281c0d040225440b0901400408203c0030b01c014a0072503d0030b40c00000c15080b60524140c4c00000701110142c41d02d58003c038240040310051340000c224030080c00c0c003c2090380d08445500c641ca03c4903440c2003481c0413000174841c03120103154400388000080c1d86217000d1200d2048580481d00a1840705045544100c01d000501e26119007a0341c00040c80c1e043c04132451305071034050203960400314450559007810703107d151b0060a0502244c1600c420410981c01c01000382d080d01c0150f02a07100002e000e0540c40500d07080000d81c00c001030030480100800901d0510101004003031004031008030464500c050490780041494604c02a494401d12111808255050300002d060f940c02c400120221030351a00c0d8404580501d0290300e90040c504401415042d00356000745042600a140180ca12a0354508042c00c491050300140c5030b5070000291490598100c41005005140844c0114580a002c414640402e0154000c840e5141d80004030980c556030356800140c050007022110191504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 845210134 1250 845208884 845208887
    0x106171b21150703020c0a15060e1003051207080316050408031c06120f020f0117040c0602010c0e090f0402010320030108012004030b06030a06090b060a2102041104090c 74
    0x5104802c0340140c0c40b00d1000007002d56100e40252102c03206628001c0c12040c1c0380d075540b60f40c0820025018100766580b040e0010354000d42c0e11a0074041e80721214803040040c25810000d00b004a2184203c0da410010029440054003250460b035014921220101c0d040914543c200e03030a2059502c440211b110100320b22020f0034050440640500300d5050400000365140c0801136200c1e2a020301500c42c1103605001005070400303c0222000c2c55051400c0749240014000155003050103443c29681203659034800d1010b075409120341018941c440c00d0021f0b452981600041c0398a07030003005080e00c0071282c2c0110b8116402a0800160900020480a955044481441c0e4190001d00c5603144540c01c00c00c07184500304008260007202e0281c59103d40c030380f50441d154002d500d1320203010249c251140442d9800410000d01c515041c4038410344001d000785c00d00004000200380d440e08164800c202041102010312050903d4a42d03143e07055402084a064582a209940c0075a0348013100181c213001c241021103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 845211384 1250 845210134 845210143
    0x170307030b0f010e011409040219210b0f040e010b03030406020d1209170f040803031501030506040b03060105010c080c0105010806190b0603041104091b05030106171b21 74
    0x707000558074800c0440e0500c0046031440d0aa030000c0b030100780404888516606240002c002c0b1440140015282c41043c4042014059252150100107000350503c60f1030120310142208a03052400000c0c0007000c46100050f41411010a0b05032245540c3c01c00c0d400202d000390000c0c0c18482006003541c2c0c803990f0b5000041d4444c00d03003400440004000c0c1440e20b4020b00320384110101c0c5d68018000c000800e075240d6003620f030f96003d0076030410034640920000803d2481000110300c9201d04024114040201000140c1034407409030079584518140340000c4010b840c0010030f241105d200b481c041c0503090003402c01074110303c924681d0301481d50a003030010400e0300000506e240185041d105454030100480070031001c541c41e0040b0030f64402d004101050100c2d054080c24024101c008000045005156403003a042000704483e1140c5a45455001c200c280750a1045000070900d03801260390410001401684484060302c000c1c0030841000311405140d210315045900150348221006640c0fa6220000740d500c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 845212634 1250 845211384 845211401
    0x131109010212030903070b071b03051806070b0a150f08030714191209080d08041202070302060412060b0612040209060d03051b0115031a1b041217030703 67
    0x1521441402c010b03000c81e12412244181e545070041c60030701d03c05585502d05010051714030410405400d1405a0040c0710f1641034a12174400d0706c2d603d603030702e50304414103140b080c02014281c81260300380700240c046100c170360b210b0354003001c030640000c0c2c05103143c070441c1c4012659401010041c4e1401001003003000300000106151030203a41032208100d2841c02450b60382003489524455030422007100800240e01ea10580120710303660501034540b40c1c03245e603c1480d01902a20000001d03c0340f0050105019072a07000c00d01100e031074405008041c0c21600826258803a911641c0d0b05018010700d150244a090780c07003072024080080406650349600901e61281000c00d84040c1c0c800c040e40c00100d40f140c07a100040d96003440d4961261070074020014100e0669500c0310340211a29500d41900140c001c1408054001a6100da01031401c51028000c0301071201c04020140f0005070f07080031080c800c1080341400d81c0c080340d42d1805205488011131410b990000031002000400560101c1801543c0f030b019089210f2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 845213884 1250 845212634 845212637
    0x1020a030b180603100b130903020a1a0106050f070206090a060207300312061e030501061a040b0f1303030c060507020d120902030f0d0f140910030b13110901 69
    0x1040d058007510311150030140d07080d030744c5a07005840e009092821500300f107260810080c04222441e904007a95801ea903000003003100148c0001c03207a4000c012822902c2c00170801400201a425030400901a00c240b140680210503004003056800465503080c00300c0d42e100d44042c181038605540c900001c1d665031418002c180c82038400010030112454651020500101d03950002c8520b0600c540f8152520010300c06020419a12910045055610090201088a0648038803558a860b5007007950860705e46411070f0900c5030241d9043d020020718042603806076550310341d81d00d07a20703e000c4000252038400c0800f60007204641182c0001031507084045902c00602480061011342d603926422a1501e0100355403801141041d42a000361040ca9032094403010310207400c4030003101718240c245103440550280c4d540003c00c20082004c50303075400309076102c1c0d096042d10141d041094440c0003a01c004500c85003041015515a40302840755282c0c42c800e50034603660802001001149184c80e075003680450940760 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 845215134 1250 845213884 845213899
    0x30b0a08010603211803030f170906220507031e0b070e011409031e03070b13020f1f03090602040e2e030b0615070b0a050f010b030610080a0e01020a030b 67
    0x113119500801440b207515402e000005c1c001341c00d50b90140c4924414030884020042c50084248a001c002c0c01000e0007108100d00901d400d290032201d05604880425100c0c80d01103612a1520009000180f00d100ba00c0d8003e554050548221070510042072070080040d00151b501d1091142140e0000c4120a0240c42a0380b0044202c0003241c6032100c40c4646000943c065200f0300c4d00e0048072640c0351501d0100040042500c0c505044c607140d41c100b000c1c040d165080d110009041c81011460540000586810183c0b45040d0480901a401d07d03650004802001450b486100240c01c0004035130444000d000d1a044146850a200c2c060703180441046544040e01006130100c0d003112640d42a00700d080740d030700180c000050b54a8809201c650650a185031800c01410312840b4000f0f4040c4178650b21400c072460001610b0302c1c00304000c5100039010303402001840c41c200107010860300d5500c482a2101c80c50f00380903005840303240d0020000e00000300c1301c4950394800306080c81000d50507002508800c0c003c41c2d941 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 845216384 1250 845215134 845215193
    0x81005070e090414060f0c0d090507050301020d0f051305060a05130c0608040b0c03011203050f070618061506050d020903070806010b072a0501081f0b03042907030b0a08010603 77
    0x101d00c29010361f4103a240e01014440940a0185500301a058034850170507a00d4a40e60340c1c0209003603070060310031075060603181e48500c07504030201d114081d0f105901145002e0511071580394a030f1510030107407002c00025141c00000340c0600c0032903d00d0042e10752003100b613010a9070304c0400914020741590220b800c2803030384010a401030603c4041d24107071075602c003410031804811303502552550b0006180c164502c0061011101140952040003449036002160303259100c40351901d40b007140c0b03205520820111214034140f11080d0321009072080c50b151101300580e81c038009000a840c1080503481081030380304403000440c600a024024107038a61180400b0a01001000790104002d240312110303614484034003070108030540c0f00e40469a0011a43c42e5400c040c400406890082100385400100c6541d0000090204000c44540c2007812080c0f25001140c80d8107c50440c2d6250300d43c05441e9000b0980c490000d018180d0b164501030b0000c7c03511100800c1055034034549424081c45000c1004140b070b1400186 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 845217634 1250 845216384 845216401
    0x50907050102071214010f0203092103070815040516091d130c0f0311090606031b03101d310312020f0a0c1b081005070e09041406 57
    0x5a8080d180160080c010050401d07001d060019200941070760304410300c020811955400380700d80c1d00c54081451f409a52442c150901500c1c09040d056602ca6841d81810101c511000f81402d60390821064604040b094a90b0b40140103040000310705d047c0e015180c00e06005c245510740341c41200c0f0b6611915191050355449111410308112207141d94180130345400007a01c040e41c40032068800310712405100301c1d40c43e1030301c50b0030b9100206904101c0342084800074000551401c0400548d01c90b00490384a803851070034112000c0316070091101540e078080003001048080c001c031042400986259401d01a00c1180b070781c01c1c004010001da8030040d19050401a68a510581345080884086000358080050060750f800702c4040d5160400740ba4115824000c14152120501c0100b80c80780442c0c0c2c40004103611414100d0540c038046441c014441e0308442c0c00c000c1081d011881d07003a00d86903000001359642d10320205032040f2021032003042d13001d040081084200013003002c00d125100342c9081103c14035515002c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 845218884 1250 845217634 845217643
    0x307031e0603050703060903090e070e0102060a29012c041503020637030c02070e1e09010605120304080f030a171302042c01060f150c0b0a09060509 65
    0xb015000e40c0192a00b170010680c00d800c1810b1651007840d20780e80660ba1189040003095069865000040741d02680b060150f90401400b0340010484a04203c5000b10080d200000b0358050540c1140540c01d03000019668001d1203c40c001d40c48020703410186481591250300c1c80202e01d841c2078802d919088503900340e0510f854503070003a00c4c2e01400030341c90407100b05030700c3d503210314103807150640041c44904a00300703080b084115102098103610f011031802e0003007070080e080c240c007a0040d004500d00d03201004100b902005c681016811a0381e04e0740401c0d2030300b10071b03503004d005644c0107a6000b054000207542c100300700100400860300c240c02039413503000206540c1c9071a88903a10201001945c6106101c0b84c9500018400742c02c988030100440d0407640950200d01580c1c41701ca08121942d000020550085100745042c3d0884100c010003008600c3c01e0401d40b00c1100c100d03000f0318641e145c120103490b0804c0c1c0207044004102d9081040c415042c0b6003500300e00080c0074a05412100e40c4e05103004580c43c0d940006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 845220134 1250 845218884 845218889
    0xc09020d0c1b0b0403080c09040f020c010f271103012a0c081e09040c0206061801030221120d2702030a24020c0703020108070206011d18030307031e06 66
    0x1040a6130f890719201120030b40e00207080300c01c240e1020816150785035100c0c4500c40a500e0032500c0540c4500742c4006041c03c42e500d1001c0303240c005040c5810305500128082c014040d5141d40a25640c90f00307694144201c0c02c48071900d41c25010f600e009040a41d40c2ca8542100c030104d194040e5521400c900c0a90442d8000e49690380201644424045003004a10043c1c0c403000441c5c0d00701403a03040151450006d001c1d0744050002001580010060100604191064808001c080c80c9416010f514542c013003403d4244070100004a90901c03594210242d60a001e00c1d0f002c40d0840300e44503100e642c003400210003020641a00c6d903030b409031401c00785100c4440040c01c01480f600140a0030b24002192244061805014800410000c0481c80c241c141c6440d44090405240c03050000d281040c110720025000342006804041954403880040209100c0b21044410000300360001c09425141d07900540740403007510750b0340f0b0340c03900000c003c02080c183e060344803911040c2111b201d40c4404100c035444000311021070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 845221384 1250 845220134 845220143
    0xf06110303150d02060a030603050c01090b030a0c02191a010911070b040809060f120105030c0a090b030a020604090b030c04110a08040f0507030b04060b100e0d0c09020d0c1b 76
    0x6000050034192200c03080450b07403030b0150204200031400c1d4005019640110009000300b035035607005000340401007090040c07502080c20044801c50429040514030300000300400362075034584261050141c403c0c88810030043d105485c0301c0319292180340c041181c5244402d0480c070314880000018081145000b25100c0c00200d040e020f140c010103440d2129010402003092343e800314108404200e0780c84020040030054410490103031507009074500e044100c84181d011912940c000e650084090342c40340b00840440b00740c0c550000348040c3c0d103008681402d40d610006584220046000140320a454104c04440c0004400391030590040c2c6040000702c8200383d02d8000071103014001c02c86500e0040d141182c015000301003004032058a50343d014036050642e00212550020a4140020030a06001300300c6c030650101c441c6555031040d807500804804881003c24421214030f8004400d01940d800340c400900a60070043d540c803d250faa00101034042400c603c00094240c0c568168200c40186411941c4d81d0310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 845222634 1250 845221384 845221387
    0x190915050a02010605100c1a040b06060a0309060504030816020a0803270a05030c0d030506150a03090515060310050f01090504050717070f0b030f1609030c0e010f061103 74
    0x14a00803a519000072440d841507640e40c4074046030f1950340040d4460b0b1007130a5079035218441170310300c0c2100714800b10000b280c013900240b03028400000c2000700001d0380000140c440c540c489458030012405010f08150181000d03150006100274540d004030810701c43d01194030240d480401c440c40807a0b940c070203e10080c01c186014400300d211000c140404110031441140141c0141443c00d1107141003d0a01004884503800001c0c1d542000700f0034442942c0100c0302d410100040c0c030300390010940f0042c41100703074600c07250001000d60006000b5406034150315004012243c004900b8151088001c0c02034030142c0c8130b0b2244190b41003141c6642e01a1600c1410380c8100c030546a440c0000c2d00300a04800ba01c1204c2d1400b036690040b5900f8915132080072080300e104000c1c001980ba100d18035034070500031341086a0070300c410020845140b450309070b400d40010b494084032040801011085690300400c1e04028040c50710080000b0f9252000024a4140d550317002a012840340c2e10710081d18a41c400c14030501c443e400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 845223884 1250 845222634 845222669
    0xd0e150f27011220030a150b0a1407081b0a0605010902091c050307140c010905010309030206070e220b040b010c0507030b060d0c2301030605010e06030a110705031909 73
    0x10703a50410300c8240104c50424507412051003007400325400860301050585e0751003195050807480706c19418000c00c030400a8919001d802003004043c1d85945200c401044030000f001010800018205c070380d00c0e100242000100c0c0004002c1c903854541503c0305480440c204000450b24415610880b60110701c010311010300281100c020510001150b01d0650380d50000340000d0002c1103003144840c017400d00300000740c5001703104d0800150280000d60841da0401d03161031900c0c400280c0000d800c9800615504100c562201c04100141d1000f034420340c00720380e010700025800c0c2e109070260401e120104040b42c0038490355a00000460341420925405021544100400c0000c40d12039010f6541000d40070300030f201d40d0019520f540320500c9442d8402e1030341e03040302100a20505e5000305208c05550302481c081c810760b46448002403500300c2e0459510b10624000022a08100e83c0790f010700301602d08010816103444550070712030340300d400440201c5c0403002c41840008065124180c4a010343c0c1c5c1c1d49071180c50304031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 845225134 1250 845223884 845223917
    0x50105011b050f0f0d0306060944150c030402090f0705070206070f15050c0d020c1f02040e0a060b0403060b03011805060115020606030d0e150f2701 65
    0x74148007a2601d01491000045040c418010340012004007001000c40c0801614014100c1e60181e2154041206d840800c0c444c258501c900100c81d081c01c00d0031402c0ca6516002802122004c05c04c61504031940c11b01034130341c21a40801c100542d40f03039020055846590b05a0312028510003100d00035880720701c500c009401000c40c40b01c0d075900081c1c640740490511100b0741c0468107a9100359819112203424203419010820412142520095804800d01580c00c1068003030301580540424422510340109802d80004000c0041d41481c2c00041d9280c210044400b4151000754001d000c1e03612041e40c3c581c00514914800c1c01520100c07220840c0c954500742c9140c41e1a0300034102c0085060b415501c8003410000c040c10700310030f10601401a0090105940750510320701132039140041d0034095400101c20400f040e0b5021540982400081c2002a41c5801a500240c084d000c204000e900c4440c0100f980f0050355030100c00f51224202040e5480e00b0406034000201d200300e82400402d0005c1c0170500c1c800c0d101c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 845226384 1250 845225134 845225177
    0x31b050310030602030901052203020a0308060102030f040e01090501050d111c0210092619020a21030207061119170d0b030c0114030a1512051f05010501 67
    0x102165a0507501c0341c80c1d6403034006903030050343c07013011580d10b17081030060300400320b1241084480c40c0641c040070049242e4000c3c0d00d03a8420103000d8284101040000c035164000c0c002c0f51400e9035801560343d91940c689401001c044002e004a90032a0714144c008112401d101e10b40c85107064200c0015400790100706c1c10880000ba611003c00001d840b07060780c180058032080d250090140305529030742040c50a1080c203121404040b13055051403480030035054485000071903070f00340781007400b05d03074801034a411b00104154807900c4c6d0041500e14a0b4030400a940d40d0700315181c10a140c46682680c3ca42543c0b808210b032512018001c006041d00b0240010b41406050302410307a1b058443e030600104200404410800c0d50041541d00048645600d08180203285c10702140c0510340003400c00a107202000c0b00448400c1c00000d00b00c80c0e03450b5840010404605443d12a00020489186080c1248425261a9854441c1d05140b1001101c0c040b0680c0d41c1900240034490507217006944001347c0d009012040d500d45d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 845227634 1250 845226384 845226391
    0x2100c0201020d090305070204150b161b0e01030318060e0621090106050a0f0e061030051e0703021b060a09050d020a05031206190806011401031b0503 66
    0x190740d82000140c940f03844a00419403003c0c007a4591549417010750040c0025030705100401404009000000d002d50080401643c09501004002c142191954074100c102185d0b0704214210304581c904001034107858a039401410303603100c0e54640040c80c0c0c00e041d206801b092240111008a1001010710324141007200241c080c0300c500c0e80d0b24050703141041501c1104050140c5018000b65144c08080c80700d8181404518010540340080303401c0036150841c1885808005010f0030310449181410015007032040f10b03903122038124840b01d40524094610000c0c03010182d00489903d250514000076506c01401d0001500c0758a490801c0c40c1a5890105c02c60096226588840b40d18048031111700f262142046214800d0540100000303400156080c0340d403a0881e14400c440841d072041e252400001e00110540b1003031280c0301440c80312134403203500003001c03850b0344580443c0581035040c001908250014403035040701c0c400000c5025495243d00110203a40114112464040c406030f00e0050302841440110303070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 845228884 1250 845227634 845227637
    0x102030915090a03080a0e060c06040201050a2c0f030a03081503030705010513060e06190b0609100e0f03010908030c130e011212090e040609060b030a05010e0d0f02100c 74
    0x40c150402c400200244850b41080e91502c070040340303207007416810100040e07c00400b01c03034107400c19107404c0f0025a0380d640100028100700001c035841c07240c280144450380c4180340c0070603005a0307450409080c07552550000300b400d10440321001885c2260130301050701c6000c02c1d010b90741c01419581d03940e00f072107a8401c412740c0d0540501c4208600320200e03030b0030320585006009420723030210801c1c3c5905202c000e49050b6041003515820420500200c4440d54407280b03034840c152403020500341d0840740011160f0080781c84507508020600050203505038862924a207103181282e0170840d042c10301d400c6c10701303e440707100d0000c0040c40c080000c070788000d040c030b0090500c2c40c0a100c81050203a072950701c4681c2c18602a070082c00428041705100080060161481007808a10b2505011040c40c1400b1640074200c0030b81701618456586003c44107201031600006000d220240c02c03034841410500d4041d000b04001c0281003200e0054016503050207200c2c4420248105003640180001358034414220024500e2801000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 845230134 1250 845228884 845228887
    0x806010e0a210510022703010c050a12092009090106050312030a090c030308090111120601050c010b030d1809020a0f050c0712030c0516180b04140c040501020d0c020102030915 77
    0x1c41c04d1043c00202041d8030000c040c011540301052103403100c2e00032428258806d904014040389440c2d4072500343c41c0460040d1801c240c10303451000c40d030070091850301000307462080d2000004000240c00d900c10313a2000e034103407400d4040f41e0711014450b089803098040c40344c0c19085118a007003503c90754800b564000c1013100f40000d6403952130ba5040b07402c13803c3d80d0086000c030b041c50b4204086003c00380700f14400c2074043d0310b16515001901960620b007060080c8442c2c1481408101951100000d5125a2030414054112010309118040150020115817400b500043c4e1000c070214210076180280e40b07188025894100d420540e01000762035035002003560f1607041c4900000090741007410342d80c07010234901a8907540c4104099003040340c240b1400c1580010001c000000410004110092803440090f00490001e4655a03000014000d0807505150301d904540d50001d21000708083d40c010011207030241c080b5008a00610026100746032030840184c050703042440408030310304280c13140080802c24907135a103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 845231384 1250 845230134 845230153
    0xa0b0f18130b100305040209040312090c140a0b0f090d02031908130e0f0106050307050c0714120a0c05040f0e0114011422020906040f060806010e0a2105 67
    0x201c0d034810001094410544078102514603080140d401e4060054070b1400303000c1482c2503004101040c2d00138100a0070040101a50800c4032803d40c80504555404003895001035078400c0c3c0000c40e0180400901c0c852949c5a10009004000b03504072810540115560707814211000d040010002c0d21f42402e0f60540a040c451030411495048c00b411520711034004a6207032400014030006200c40754108403000001e03a41800040401c0014907070448600c1c0c83d00e103a072913450f200700701c905000300644498280320360341e00413446e80070380c8030041c8a100f01600c0700d290300065115081e0f40d82c1115980034050340800c041c10f000701d09107034000e20100c96028601181d048144c01880f82103501c0b034000841e035002100c005001484410100007648a011100402040700c000c000703141c0151512441300c030056001a0b04244c6440766000e0720001c001d00b1050704901980c426010301001d03821500f06000415035400140c0d2440d00c030300d200040da1116002560300710b401418070600d01c510040240d40302e202c0c00028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 845232634 1250 845231384 845231389
    0x109030c05090601230703030605100512150a031a0f061e0a181d010515040f1112100f03030c1e0b13020f122806090809030c0a0b0f18 59
    0x10b40100c5d00f11012100d035a103180d41401411600c00e41c0100d03205070354400001c1003990344801a501944140d04d0200740d9903c44c001c01c513940d1455441e11302c1d044580210000141304800350141e40d0004441062840c0d5034031500c581c0030f9260203c4031a43c0c411802050b80c490103e5400080d18400c82c0a00b4004425440d412004481030390f408075000009e0b20740c1200080e100740c0310b208090300d110302c0c0028001c47c244a200c00d0a500c000d110900d0040b6501d8189840e14101c2d900700e80084050b210503190789182c961300907039404074100c0c2d00c0d0f02c040451020020b0482518041d544c11241c142e41c511010a8107543e98800c9400032682e01d403405001100c00c1c9000c20308001c106c81c0070308009100209241210301c140b254406150308028401e06070314184031f00c8c00001181e004400e070824007654042c5c0b02c507401008003801e01410040c040529144e480341c10010340d1001890050307011800c4400030b019042c1044002400750040002d011028486100702ca140d40010f407180d042d100b4000592440c24801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 845233884 1250 845232634 845232677
    0x71205100c0c0b101d01051e03071e2c07020c01050a080a0e010f1a09011809031b08040311060c070608060102070803120f0c03040812061c030f0206060109030c05090601 74
    0x100c15500110400410071440e11400c881000d04501ea035000080b01ea032230002e610344900e40700d101c10391386040101c0f48a0148001d4450301529090312000080130f03465802c00c20b10000382d4240c0e5110140b0360003080003140009000144d10005940f9246864100e5400f2a42040098003034880503460f0060240580c401380207001c120744c4040000100f1850840d00580361081ca45000c3c0e004110318401885071003c0b07401c0240f14410304800100d607421051404603100c0090b4454414104071a070084010000104000d0007103d00505400700048020b8003000300d00c5c410302d18000500d5000d00c204108007809540a15481001401511100e950320f510301425a400380d10702d0f00189040000b0408480d5983c05500d41214810701440c0c06c3d858603a403100c90501c50f01c0c0560304540c0603600000d0780f80c0d81d100030600e03444540c51709c0c200c0c49a48614000c1c0954200c5070a0340d01500a0b18000ba00d40c0d407041c1e140c042103d42040c28080c2d25441d100070320001c02d03000b03000103040002540034446c42001c0507a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 845235134 1250 845233884 845233919
    0xf0615181801060915031101140a030609050a050f180705061605070b03160507020f06040902120105030c0f12030d02040806090f071a031305071205100c0c0b10 70
    0x88030640c00000d4031004a084074020741150403034524080446425000e89250030b01625030105c0a14201f4084500588010030000c4a151280c00d0025407000800e030b0541000044030500c1c0002e01090f22005088025914200c411520400b4040001004c082c40f282d0249003550918080d00c03121364071040070031070941c440609a42c01c81000010b240130403504000c04001030079004040350071400c0808603241c161003401404001c0000100313000c010340d41c9080340d4154440d002082e42d540d40780e5582d0f104010f900300d140d42d1400300c46a40000192409c0c00328103807422020040c041c00b1604401030402040448640c103e40803440144010038001403a840104050000c1e80c0040440d440c21002e40b030b03c1c1907000c003400b03d821b80056000b00a0341d14a940168044602c00c00e25589a9a40a000c58842c814908019084e80700b00fa45c00a1030007240180d041c0090300a10607680d40700b03c8980504140c480401c40702000440c084c104001040810400903080000e5507010102203aa400352181c0c49981103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 845236384 1250 845235134 845235151
    0x1107032613050c03010605030a0f0c090501180b010e0123040302030d09051905150c0c030709020a030b01031407141207030c1b150b040902030f060402120f061518 71
    0x807107401c1409010004400f1000045009002c0b1505150100340c90380104500240340d150044440f204100c181c54041000d05040b0310100401e40e92508800d0500b040e10584214080c40d201d0301600d15403180c001d0740520700040e118041c001500202020700002c81c3c1c0b0607030b22415020b000200c0160340502c050750f290302003940c42840030350500301086503034002648001c000200f004410042ca13120500380c003220001e000c014540340e07000e402e01a030900003510a080e9060003080f01c0441c80c06403d901400402800d03135401c010700e103800d00c01901200e00f5604004011810440041e0000d80310300406220400d00c12807090615100801000c0d1600040c5d84c1c442c04291100c200601d41d5501c201c000d501004120408184011107485001d651442008100f01d2203842c2d00c07150015840305c1c1c001d410840d03401b4084440c000000740c2e040ba2140c2d4140c504920903003102241c24100440095640c0c0c140954078043d05098544410703500302c41030311804240d044103148001c0750b1820207081c40b0910484a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 845237634 1250 845236384 845236411
    0x90207080403060501120510022109010914010b0f090402030109080d05091009110906060c07033005160c090906021c150b220f090f11070326 62
    0x4500d00300044d900140c210703510180a0718a00808190000b81d421100103d400006a64241c0e00b681016541442611603050b0032050b003c1c000501015417104282d240205c0c11110740c00e0b40f111855003602c4c80700e00c0b002c1c1d0203c0304071810f0b4903514200444640291000300006400e0f03445503506240d0350091140030704699a10010410590410f2001d150390200301e80c0c1c00c05c4925442e40d1083c480890110341240a440100001003158440204840c003001d0654110b5002c1c070b43d00e20f8649052101a243d285800e003640308038445020b0f15010610704150551940e904000b20300c0541001c1030a40340f03040d160340140740c100280c600003912079044114060328000d41e448514116041c00b0b0001d071650000c85502c0e02d507405c81ca22880c1181d10050343c501491701552032607644500046080e0220050108005204000074134840000c080c81c12034480840c20301c0b43d041c05c10040c40440c0d010211600c207441e82002200b0009204502705a103074208213400003020605000c0c51600d40307008940d4904210340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 845238884 1250 845237634 845237639
    0x405130e06040f12020a020a031401090519031115220813030b06090906070509040209100e0307060507030203120601050c061009060f080d03050702253002060d060902070804 76
    0x132009242503150120300041120507500c0d804100c4580c1c0c1c41c44058480e00100f03600c010180002c0d003100424503008001c90300d16480c803c000d19852140381d041100424801000c6058a00d40402c81d030620000e074084034200c2e0f54070340d60700c44407450401c0407207500448542620701c00140e0354005445d00700c4030b01045800060861400107084d60000c1c203440c5c420f842803020008010300010340540c3c000c000d80381c0725840b076007600d0118020740244502542d000c2c0c0c0204130303500310395031001c000341c0000f008a0440301050740d0f07410145d84911442a0180050704108141004900f059003525080031040c580a0314040b0005100ca041c0002607035605010545801c0c200300c00c10741030048401a1060400b032071a01403400008666425100040300c0600d40c8400005440a00034070454010f41492100380905408086c0207001c000000e00510040c00c0d50002e0350032107811592508444c24444528213120700d601e540800103d90050100f40080030f44445000c5100c0200d0300145c241c49110b070031141e44460 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 845240134 1250 845238884 845238893
    0x7021909060f0905040507050f01031517011103041e020d05010f0c0f020f15041109040503030a05130b070c080d060b190f14090310020415080105090c0405130e06040f 73
    0x30041d5002002044c1003c09000218102007a50300440d1021250f00ca0f1420361400180c014151111010290f4244079100060380344002c4614210b6007407800003040b4240c006860710400e40402c1c0c80c040d100c010524007804414101d00000c2c074880303000800d0044254072983e94542542d141c0c06010003041c0d10b510452210039040380d601e100c171090a00241800a80610a0300d5071195688035035100203818401040030300c03500c2c082582078010060180314440c03030681411640c0342d01c140e8800351a02d2401d40001d0565040c0410302c104264050f00200d407640b00c400341160a20200e000652300c00800300300086202050703116400080842c92002525a0104081e2201386095012480c00780700b00b641c0311a540c0c41d48841f01e201d04501400c2ca0503192329030900843e01d48036501c40c12850482c400036012031620008003200b58141c016a84045040e83c13503c05000083c00266000c0b42ca0b68000d0005119038504000e482100d1090312100003540710341d2019040c43d184041c0c40c15601009440d00d88420301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 845241384 1250 845240134 845240159
    0x70804150207140d0e0913230a05030316031103060103020a1701120b0615040e1012030509130b0306190e0d0e030f0105060901030303180606090b180c0a050702190906 73
    0xd14106ca4900c541e140c5200403000c0c01102c944010035020408a1041c1e8004594400f044503000d100120b03038003c040c2e460030304c0e504d41c42540d40e00d4041e6544503000f03507120b11900544586094510503039045844040056021350006030025040c40340d48403142d1103500308007054900038800200d05e418a21181e081803441c0d42d030044c108030700804112030543c0c0040d101c0411a0100c8a80f081c59803215612070451750611582c1d03070000007270b00c0c01c40580001031681c400e02500c00d01c041280e0400d84401d600c0060301c200c407084000c198054200c0c1000a8a031410410158503294000b1804130f401182c200416003040500e21041c4041030340201e0701c0619040400c64100b0000380d1038000c0143e41065000540c25220502c0001d04150b1510301c0d03208901030600000e04107542c401001c0c064203484d0440701d0064800e80f803026000b20744030100c250141890485050003400c0c940003503031810301200c008440d10b600c40300081c1d8125103e8060385074058400c4038900018200764000241d00c604280000120 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 845242634 1250 845241384 845241407
    0x31b06012d0e0402150c01020a08070309120e0112020c0f0115121b0b030a3c0f09120e180c09040f0b0324010509070804150207140d 58
    0x402010740a90079460701c401610300242c8612031590000d540c0d582c400030321481c022003460241072002045c01c450400c0d05402400e801c81d86134440e07a050740d44501c400c8085590040024041c2d03003001606004041c000d1000e203004400602d0112681ca9003101e080301683d021642d030110940c000da40d40b0488140a10481d0344041643c0081a16186800160102004c4040000e0204664400311074085034080001313400402c03040c1150360b1240780c21a803840c000c0544072250a200041248100441c0b00704103c03504011081010018054a8901c40d04c4001e20342c90641201c11561403501c3c602046558004587c803043d6036581580211a400074002c2295100b165440704410000034840340000321130568010943c19070300041c0d121060005a0081d001100c0500d4050045150b4810407146c07581000c100c2c02c0451102e1083d42e6a01c2051204e0910102c402800080180b408680021005c2c5480449105170140160a00b0041e03140c0c00e61014240502e200241e1010f102c25509030340100d2010707030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 845243884 1250 845242634 845242679
    0x10c08100902090d081c05090d08070201020c0d1107080f0307030e04020403112707020d200c060c280212120313031b0803012321031b0601 61
    0x100440c00012501c810044c00e00202140c4020820383c03500111849402000d500508003441542003000e91681c4400101c280031000071814400074040354014003c0f548038858400040440c004080c404030780d10400c820040e40396005001000072100003c10420300401c2c0354400ac0c544e108280d1901901541400e4a81801240184000c00100c0c0fa8400000b0100c40103950382e0030f20541c0721000d070301c0c0d9403040c400350190004070809020745035034001155401803442c1d4454034128203081801c200340c50058120800194828840c000b400e0404801902d1605150022280310841d02c110700d840e2111070a00401c0180c101401103800d501d4a0341c1080c819003000c40c00303810840385150100c1100d00c8010700c60140c54490880314030030140b042000201c00719016144212500262030840c910342e1003885501290400c40d81e03130000740e59980d50440c100c90401007040208040d242140c400f80c5001012444150006208400d901d0542c0080c180c00caa00340c0700500540d41c14445603240740240040e4455 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 845245134 1250 845243884 845243887
    0x901060e15030a0809040f111b01151214071401090605070b0f06062106040516170c090409030908060a060b071403040b071b060c0510050601050c010c08100902 70
    0x65480201d074154103144c0080540741e9841110b0301080107000011541c40030185014016030a00d40c61101034444c803601407000b84030081400c03040b90709030307045903a00d144c210708100b40402130004010110b1103450b00c0380c0307612429a0352b0945114145401744c0e0101d500d075015413074916603540e0301c107030544060500d6040103410220f05032a150700301500200318a284001440c040b5100b50b80e80780695107020840b40e01040c0210500344801004101690218020350815000ca12603e01107070b24910320f80007a540300070420b80e4a010782c4403440c402800c0b0000700e050411910019881c2d82c0510100d841c065100c91100c6860a248035280c24801401070110700d290540a0000a0151080710f80c403d40020b00081a0340e051905541144110351181d203208100113180304c1040394a00991880717005200b9013041140d668441900c0f00c001c9000024901d41084116003400b050b180d10143d00030106140c014140081308244070b0031168410b422401040000c010001703d804c0045603040688802402035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 845246384 1250 845245134 845245171
    0x106080f1302010201060923090d1704060b100e0909010213030611040b0703170a0b1507050f06070306170a03090b071502072907020c01180e0901060e 66
    0x4103026406003035141e14414040c00704003076a100750040009041c401c0c2d01004044100310b564080501829240380003c0c0c0c5000c0005d00034070000c540d800303030700342982c48980c10000745126060100c0c00040c400c8030302c203603141e2020003240c46004200e00310101a86030702505400e00da00300012250300501c085007da00411480090110300e000100441c0d6014034086152052203002a075540a503403c030000801c4046030440915501c800650044000c042c4200096203480e6605829a024500d03040d4008036404122148d580301c1c2c40060501c54015400e4a101e00740543d00c007402d0020070b40395000081d444030010300401600f41c198044c145841c0e0300a023181003c507a40603040700300e148a03010b2060004100c640902c02401d4800e12000c010aa04558a91051a080003145515021912010030000d8040c1e846181348006500501454008160030002d100045400c10040c0400524400f450980026804840c115550107140c07036a001003000c90030300d5903101e02004e009110700010650b40342c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 845247634 1250 845246384 845246401
    0x809120a110d020d1401091a070e0105070f06051810050f0f0910110a080705090a0513090203060a06090b0d0308160e0612100f03081803120d14010608 66
    0x2071544111090300c21140c07001c000e000048a5210b8120081c00321031203403000d0007003100194130142c24244a01c000018244516801945800303040342d0300c0000c10302075220210150b01070405840c05900c12903015850080c1540c680040d58402d80e00e20030304001b20007030424107071001d000700281c2d00c00aa40030410f614091824016a407800341c01488420904008070b51120824021048240c595140900102040e0310510089a200d00015000182204c021404452040d002c0341c5e80000000c20804100e030500c03040003902c040d01002502c8065840c0c0001c00103803020300025100f4a0042c03c0051614a440d454600303444124211912500d881c0520340006600b118078a0b800440b0f401a582c000d0524040a5511503035601c1130961102d008a503007441c40d501c42103440d01c07601981c07642e01d802603501d8901c0c1e002c0041034000105846014803120140801c80c04915456000080c03c9480c20004402c00e03c8055000c0c1c031b11881c0d0355449040c0d5458120072403449c107004100c42e141240103450109030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 845248884 1250 845247634 845247653
    0x308010512030d05060a1205070f061e0e041503080403050c060403080f030402010c0c0801050a0b10050d020f040509040f0b150f1e06030c0903060108010e070e0a02040306020301030809120a 83
    0xf50000c2e19540d1003c0383c1c0a8031000d0621010740443e580c0c521800040c1d041041c0c1d100381034400d40c070243c084000c0104109218000000808007100d61103040d0304540401034519200d0080c4041c0c005689920000700c1c0c200c02030720080258000d40744c0301e0340c5034107504080d4240800c102c0d00034000c400402c420000101c08500329010711100050341d985a84561004895422102c0f1000d4601d0190100101d984030065004901505c128101080707c201144140402070040c1c000c8000882d505004042c0492a01e0b0020081d402c0c800350078034903041e1140f000902605041c4d4080d60300341034042828040003040000117030002d061551002a8000c4500011504540402140c1c00341100140e1801c409088a10030000f24074001d0007151070f0310740010222510b410480c003c038030034480c000c000039a80c1010320030385c260079103000d01070a02907052450180b000070002e0510f4030340c0c6900300701c00008210940302940c0a544100d0301160748800c484100510000115141d10741c2ea002a181e2a0000380c2a03107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 845250134 1250 845248884 845248897
    0xc04020304032a0c1d0f040c1a0d05070908060a11070f0f02150c0d0c02060304060506010203070c060f090501051303231501060906110d0e060c0316030801051203 71
    0x101040740b2841820a0750990b0760320f00070003000e000e1101080c500d5125590150100c0e440c5451600f030340d42d4902d40d60b400030080d24082c142d500303107410500451150380180d450150740520554a04243e41001c0700c120b0300f045031440001130315100180040581802071503001a1130365014017020040c3c5400d42824450508020184d111640c100003c00c00b08990540030f40f83c00608400c1d00b021150345828117139100790010011806025190800140100300c00c0d904190003500132415a070303466544074020200030b000103040d0310088c0705c40710004154013190800b400080c0d079550381515910a0281c96110306e0703002181408400d105028000d8207084d0700a044903040302c48240f508517031031f4803906190008a41d00c0110f020f01107102c4810560110001e040301c20580c0ca9083c030950310001110154804480840142c001054021203948030f41904000c609000380030f20714040c0081135681c91a80030380c1483c03580a80d03110080c3c050540040c540c2d40108402e0326001224400b20044585a01c2100d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 845251384 1250 845250134 845250167
    0x406030b04060306150311011106060405091203010305100c080c07060c050d09050102250305042d0611061b04290c030d0e011b08040528050c0402030403 67
    0x389805015a9615000b1100850b000b2004102c5241442103981e0030500038001520302510b201c440c485c071944150b00320385000d000c14000d0103a6448010410001e085e015140a0240c4601e488402c25446c0240007035000754443d40080c40c24511400d0054160340c4011690700070b00412004119095589a0480e03c1d09540550001142c401c0641c0c291603e00503100ca02c1046442c00e200082000b5055005044400d11892001c10007080c42a400e081c00301003440080c001403060000f00321345a1140c00707110003061921550205a213032594001807504047c2d00400005a070301034007400e5084240061600030b0843d070070a0485c1c02c40320303141140d1071056101d0380d00012045941e902055084406602400380301c00c0c0c20990f0750140b2009950349801c800e1981201c00d182c483da407981020144507404000c0072a40e024040310720710000c25a03000400030b1080c1c07060f0042080d00303003441a640e82842407940c03881000b50361008003800c0c5585880c1240000d940260b10400510000c00c0d00000d100400b98901d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 845252634 1250 845251384 845251391
    0x30f0f240a05071701061d0a0609030f080405192606011a090d08071709090609061f02280503220807090603170a081b1b0307050105010812040603 64
    0x2c1e8001103a13100d8200308894803182d910000491360701ea12154900300781e103421f4a03d60800e0041d03410005402850b115110208000c0002000020321400030648694000c4618506180e0b0798000309003688004600c0c10410301c3c9411042c001c40c0050040810b040600400e0704032221090b4420701e580e00018061908102c43c030b80764200342d4880d280121043c0220182503a0059201ca1034100844e421a030400c5070b40750100115401054855000c1d91501c40c4000d0540749251103180500c203a400b0080d0bc51504035004da40210300d00180c40b4200c041406596000b000c4440d002c03400d50705031070705560140032030000440105002c11400000c0e65010440308029040910246804510500d8140d010424138040c0d20400115460745500c1003080701d000e07140c8000c80c003400c09950308903881400c0d0700700c000c1034001020900341c0c4a01854940d0a10340032a038a4507099070b880c002c400c000705500b0300c0940d951002540404020080c01518010015600185005140710445840301c7c02207028103820107a8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 845253884 1250 845252634 845252641
    0x2040303030207481d0a0b0102060c070809061209071511061b040302030f030409060b0901020d0e01030605150c120306090f0718081e0f1b03010605030f0f240a05 71
    0xf001a5008020030b1342e107080843c01d4004841e1202c01c1501150310805280c47d180175144076500209040c1d104408400c80245030003010b680f103c88a801c4184402d4010200b800070601061030026041e00030b00d02040180440c80c6002c0c070718481424081104810072807140100c41e01d810b8001903150304405400d0900860003a0391800c100b450081c1c0c0d002946c1031241035466225500040010029141d554205000940d01c812400c4804e02c0381164040c0142d00c400052403006c3d00ca80c84240007040e0514000ca0126502e41c001030182103617244a120079240040c0c10340300511300300822403c00780140340c001d003141340020000b8550b400c01413000d0b102201c1c0c10006402e10b8031542c1028640c0242e8039034000000d4981e00119910700050032680d0500040d000c2020780014000340012a08400c00b00904000d00042c015403440c024143c503403a09507486080206055a0600040440c0084040103280c44080a0000340c0381040000d19140e2a9000d04502543c5400c0482465030014602d80f0104241d103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 845255134 1250 845253884 845254013
    0x170d05180f130213080105010b040e18010f0614011d03071a0c070e04020f0103090809040b04020702060307050901091203200a02180a0c020601140f1302040303030207 73
    0x481440208121600c00680721a85640010404c41540c9000b0020800c1d80e03280e11692429100d02c1c01a0807541c40007200044d020720030700106030b00d030300688030003c56a03518000340841038800350b0304100309c00d5034800100d100ca940d20490328050582c4404e41103406a00300408030303071600720902030000310346a4018050104004941147d503010401411250b50300e40d50646254107074000c3c0c2e0100e1142c980742c07045000320b6219000f031800d0340d50000141c900d800c03082403c0000a120514100e40c20640900201001d42d446502451181506440707441d80c404181d800100b081030305400c607110040c0301001d044082548080403014556601500b8202051400c149034030303201031204000c0d40814504000304801d00000b042c28041d40180740144011140d189040e40c80b40000d0007034410b60140c14660881c58a8030280f180202c0c031000d42240200061a1385510a0743d1258205070007294000415134200444e010009c00000310f80c0308143c1c071480014a000704904d0518140299083e4a4207401045c071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 845256384 1250 845255134 845255149
    0x60a0b0313080706050a06080a0302070603150e161407050d260a060806070c0b130305130f050a0b07080901140d0c0215010503010908040611100501170d05180f 70
    0x141c200c016203454440c1c1e1301d0030401070201110702401c1c060070180e00085201000510802c031a80c160085d2115500f0100d0484c01440d0045503100e014001010004892011242c042c0c00341d850400505480002c42c14003400031004042c4421b40448200044c202040002c9554090f210141c40c204c811250121103c0031030f0700c108a15846412640f005100d0b0451044d4802d10071100618103031384560340c0d942d000366150700500c04d007d401011160005000800e00040d911422442070400c242000000f420b4400c1d1003110790481060f490082c0420301580c82e20010f5031004086045295181c40b80f40e55410480e400b0301030300c5505100c1c10703440c20300c408010301090780c0007142d549030204100000c115000b565988a0303068000c06211480021685080600556011681008038985000c0c600101200c040001001c0b804690003020390360310384810f0900419000b02141c180012981070204c469034105284112100700344a0304000c800c01c0540c00d03c05101c0b017683c0c212a03d00e0a0b0201d8400724140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 845257634 1250 845256384 845256421
    0x7081b010302310b0408030f07051015031103012a1101020d060f0902030c030c0706090c0e0717010501120b010c02130e0f06190b0d020307030606090b010206060a0b03 73
    0xe050101d012200c0100d4080e00d050044075101e811040c3c450b583d40d901101030320450007040c2113034104000c402d0343d10700800d00612180d0f00c2241100d46d800c915070703034400032500c000b02c1c07260351070b007118404000348641010a040710ae034046000301f041c130701c0340842e4a403082102d18242c80481b406440411000d4041c50b000003081c0d562400079940c0b02e108492030b10090125018843c1c1c40304020708041080841032003680c0c481c2c0c03a03907601d007851074588140c2c503a04c507007098000b1540c5980303d003140400255a100004010400100d106025080c015005403101851649084140e4803550040150341ea004410a002440f412000203140074a440101c1d00108480d0740a904010f032204d6110000146a20a00100b6085816200c0c00340c043c1180e503486250540d80052150034111610303180c81c207654411a500c4000900b0000302c1c0d0080c0d400710b41032043c81e40c0709a0350799640300001c02c210781d000c0c051940a11800d00c0038090380e00e40903000400e480389902892446a90110018511501107403804a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 845258884 1250 845257634 845257657
    0xa0f0206070b010806070f0e030a02090c070f050309151206010f0507050f031b212a01050406050703060305030403260c0321070c1101030b040e100c0207081b010302 72
    0x900d0340c0c44d90f442c00d5031440180c5082000900d11030b40c000c40d6921440115800341c10003005001c00007260380030480c5031030000e040810b181201700703c0c850000d000e00c02c2d03814150f07104002442e02c6e01c2e99002084020200b8200040140d003081080041f94003103ca840381d440311007400d024121042185080b00c1c14090450300400a08c82d00e601521504400800780c00c0c410040c11822040540c0c1040180d2104100003800111040030600400d1601c200000751148d0032050007000d110b107030b42000304207d5540112075541165980c41c03e00080c003495014050b403091a608003800807904d196281d076903174843d501c000742890840d0650f01e00ca010040c0090141001c0c0154130989810f052410a80c5a510030001d1002c1e0348820341031407150038100c2007040d10441a0f40c5840d0030a9409840b810781c2003e452100504040c0da8944421803683c9038442c42e80803441e1a401402c1d00f01182011100b2506005810819036000d0301c4100640c180000d080b00d500c8484086100030207102000590190180c0010b600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 845260134 1250 845258884 845258903
    0x2240f07050106080c040e2a0d23010b060d0b0307030b040b0106020d030606090605280e030c0604050d03050a030b0303070609110a0506042d09091202030a020a0f020607 74
    0x3000d11038150445070544240000b41c038900d80201c4208030841b600c0c448817174095046000701118103030803950180c4154000781c02c900a0083d90f0710010b29130301b19040044418214203241001d40d041900701038980d86401030300800c64840044002034090050080d8618910788443c802b9950391018050900155400044002d090401d032800b101d89001c2409400d00510903d4115060729100303000f03003402c44126480e2560100e081250031a02d5a00c0400e80038000d00340d5203070a0844a500b00011038907545682d5603181c00c44484410103044c0001c1e140094410501880284450394407040c507100c40ca41d1505106941d24204841a00035010b4060080d0b803500002c07034540d00b8410390b5003150840d940300f189040884024201007081e203044501555400010603c41801001010303140045100c14404081071104096500c00d00340034065004803440300d403220310004c2008a41d01c0b40152460035030010b136080c00940c00c00259148032410340a4100030b0100c0f1402c0a64a6181c00c4074a004d4000744646e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 845261384 1250 845260134 845260147
    0x603020d050102091306060c0f0201111005091204051324120303140f0420060c030405120303041110110607030e07060e0a031101091e050f0d02240f 65
    0x41e0003504259842406050980d80c0c121854640e8802c5905447c90750b11900300000e4a51a00420804218001ca05129001c070380440c121104110441c0c0325111110007060f9464855940703030800e54054181104d49200340024800303030359482ca4103e26103040300d074000782c2e1a403081c02c19004050406c40328040c52a49040110740500c00961910b00e8a000351801c2c0552004541e002004c414103c80340e0390b441295001203400501e08461410064080c5081c05100c0745280001070b240e0340c06900440707001d03400001c080000b400e00340440c24204a07007001560451a041d1140d542c000e1646c0383d081c0c0306c0c440680f048640d8034002e11800c800301d00300701d0880348640b610380800b80080c03800e41c2c1c0ea1000d80c030645100007030240c411164052010b002400011748a45103554445813004884100360600c21808804200c9d240407071030f10814000f08a1074003e1203032814040c001d0703441908401d00c0c082d44982e01c4e500050b1701c920401000400ca58042c1d1403c841408120710400c5c003c414600408020000701c2c4c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 845262634 1250 845261384 845261393
    0xa0c020c06040806010518041e112e0e0112020c030712110c0411070318120f0b010806010f0e070e21060a0504120f05040806181e1c030603020d 63
    0x101410381b00107643c0200401c660015401802a0441d801404820386145440c60100b0411031445800d11038501030182d00c074000c0c0041c080c10552101c8180a40e8003104115100c4105195504959900d081014841c020340c0c0000342480146443c4082442d0000340e04007800d1400c008460b44540c100b0180c00b44070041040041c11000035a5406409100d076100800c03240ca05480f908603c0150104500d1811040c0d0b42d0648141c0e00000a40720f00902991002442001007075003190f46911038480b0300b900d84107610700401d440c032068014820650003c0e005003d0100440e50140c2a2001d0440c0c8ca22161307a00314040b43ca070703500040c601e50000328007029203010010000001444600da08266009581c40f00000011200111806401000d581b05000c1c0341500801c45006181705624007989881e84803441c2a14156042c0d8045444955482d00400c0c682da040c410b034014000c1c0000318210311039040300740555624030b40000d61046580d0344041865103000c1e911410046902070322008001401d41030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 845263884 1250 845262634 845262643
    0x2410120c030c0f1403010501030e0c0904050a020a0602160b0c0319030b15030c0d091515050f0904020d140102130b070506310206090607050d091505030a0c020c060408 73
    0x1a62011483ca401000c03111806151090030700c803000000c06065a2030400110003503e00e0482103111801000703c06902d42c1c440f03da10903c200d0160004103511041441400400d80075a4404002c40d003007141c5aa0008050003040350484a14000d40354503844203c412600350310621501720700b4090404d4170804c175107405070808600c40c40300703c034200881390a0201a11030761000311000c1d015131030b0800107a1410152035110100450203182242c1d001a0300c514108200c522500601d0301c41a500e6804220a150002910001c1041510324150034201680400c03030000703042038010400090400b01b081608000d60581c0d000803584200503040c143c3d01d0b8a0031030304c1d038056441a2081d008071000a280e042d001d105010348204441070703800205010303a0034a0541801003400300c2c0d010320104201c10032959031401070581a4002c9002e0700d204c0c21071102c080d260110a601510403008002920f8090039001400c0d2507202407085800b01d2034821450080b8100480c0c485401da20040c04940400e44000018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 845265134 1250 845263884 845263901
    0x310080a0c0503070609060507020d05070e0106051c0c081519030c14041b08070c2a06141e0903062701060f12020112020c0a05062410120c03 62
    0x102500d85040d1101c4d42106c10112502807400428002c01c44503005040c42810030030b0460096007555821364a408164004170020b0740054001100410400103c1c4059080d0310310700030540408215694500c1009410300c040103020b100fa5852602c200340080d1551031000d510361300d41ea50f003103900e03d40f2881c040c4c8a1040c90702510581550540d920036980c2008e00c079681d081044620481444035000c0e100712a5080000c11080401400e84000c00003d28400b2544404410300c1c00c41d140c0b445805288440c02d00c0441d03101d01d04011141d0043c1046403204c40031203058180c0d0740904880b9600b0803c0c449034078850000015010307c80c00e0f081001d80103080e0700c8210308280c404103481014008901041c207880581c0140600c070300c22100108134410001d08894000d500c1030414880700e03150280d20f0b6040340c000c0c01824089403c091411420401d083c00b406a004141100008403031007406445480441082e0099028410358030781072406a019100c00076204100d40800d200714009200010b000d0b14980 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 845266384 1250 845265134 845265139
    0xf1202030a110706050324040207030c2f06090109030209041109130320240106030c0302211b0c070e06370503030c062d0c0310080a0c05 60
    0xa0003074441c0602c0420602c08031030680e51840c0c15038403099a56855079110034005180480c2504000ca407544481c0040c10005000352900002800340341800e201c8181c40350140b40e81204030481c02d4001c0e9804000d502c0c0c1c61001039075000d40312090000144d0303410b10541c00c045e40c4046c0c45c1c42040204030f400354049080100c2a140e000850301e070705c605a8030b0858a202d0003004030311011100c0c0303104074a1039143c40e0640b040508594404050440030b9101e4a91143c007400814036000c0140a09600b50155071807042079841c0c110318000036041440040b4034402d80100c40b101c0c1c61000b1490680d44c040c1005940d084260440f9900c0001504040e83d4942e50b100c2d2028200709480014403e10781140c2c0090754081034145040c4a0420b04e80e8907209403801c044e0b0141075144250b01040c562020400fa00d404580040240303190700b48980540d8008480d85001038050084100b40d03400f050403454032580040088004c1502c907110031000310304c8900260440c10152181c1800304040c007c40d400060115a000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 845267634 1250 845266384 845266397
    0x11090310090c05120309041517010f0b06041d04050a02090109060e072a17040305010e1c0c0605040623070e010f0e0108041407060f031a090a090f1202030a 68
    0xc500501c41074030f041c0510140c13203820070700090f06582132640221482c2c8000ca000180712984a4200c0e202c0c4c6044151603050903950341000c610042d00d03512818482407421203159081c2850244080d0b4411901d14007000102c51001c0843c0070044100901841076500130b14201541d0b865191810003003246110b100141c0d1414004a41c81c14020003910070402c0180c283d0308000c4208901e40f01d01c0c040429002c4402d01440924a031070356100502070b2001d14400c1c00041140505684014030301140743c01030030b04a0b2030212509005582000e443c42c14294002000b090aa50754101080241402410032082c501c0c01105c140c030b481084050644512015214081048418001183c092024001140c00310b404024841e66560140216941c06482036101e20440709041c03c0741d50402080360311013000300e010500303003004d2907070107025240d032903c0d884a1504080c0040d070000340d070044000d0000c01c19155142048401e01041498921070070b03800600c3d003030954000000c000d55942c8007a5107100002c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 845268884 1250 845267634 845267639
    0xa0309230f01050606130b0a0c0206180916090e0a0b03011109030d080c030a200a091a070b070c03172a071104051f1212030b0d030311090310090c 64
    0x401e003086e6084181d00c0c28040c9819410025648245c1d0b02c45a030820034000194140c8005076180030003401902000f00c4034135540c2c044141800b1402d10302a0101126001c0c00792107280083d4031800e4942161001b40f0400300640392003a80d50300030140d02c000d154240d4240745542015903401d00007050070301019402c980c41c0044040381114000700a07200c885040c0d40800100e2030404260300071980b000b4009c1d406580f0f01c503102c01011681c0d801140000042807880408108050318112083c2e000607550003d04d1070306500b60f0750204001c1e00203100b1802c1c000c04418060074540710b80501d20f01ca007034088a2159a05107422a105240100342078104031401618403c0341000c0e0349420303900070341e5001411408144184080101400005280d004600d41c42c0519200798500c04604000900f16020f149249107032505026107200f80126000c01818100000e4a0050b203900720150340c025010300d000104620028492070b100d101e03034046164503101d801070406a840b926444948040d106072030101186030b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845270134 1250 845268884 845268889
    0x190803210714031b03040c050405060d0f170f0d0f0c02030f0904090f290711060f04050102130602160501090612020c150a05160809030a0309230f010506 67
    0x303000c440c20800140c44268450764410100c01031600400d039803851003500012403a18039410f03001154140c440c1c08402c0f8040000742030038426180c01039003c0d80c0004508010352981c0c4504c0001c210001c2c620300c503144030703030032400800c00c00e0b40c008210b10040b03c2d950300407061080018048200100804520780510700e5109030000048888100700c0e1020707a42022006400c010080628550507102914030340130203000075590100d8425154081c81100403005008107408150b4503000700300805000102007221410b400c001640340d88203803034954940399503890b4030f08a800790081c2030070900c00c07001111003c15025000b02d56011f82d07d50b816261044107039181d00440311503c0611a03040403070011424020003403c95001401800308000c101c400c684645076421400c42130448414003116659800d102c00c5050031613410300c035a40c0c0351506070114100b688010f0f41f24030444c80a6014581d54080300002c0000410790582064045100c1c0c136040d840d43c205003038075002c2c508000b9801e5441c0000044d96403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 845271384 1250 845270134 845270197
    0x3030706180b090d1409120102040b1804021c09171318110301151707050a0e041401091d060f06091f06031a130b0a05030c06090906190803 61
    0x9440d0381e60406841345d40307000c090310341c4461401504205d804807031400c84542400107100524800414a0f52443c402d82c000c2c603804964013a06110724010004c0260303100e043c90708a0744001d0207401c002250465890503540e50402c120800c0890307400030500b039a005d50410600c800b1a110b000e21103901060a941280031240c0b4070f042d82c0b505c040c051005201030b2160030214001a159403c20102000d039480f4001c842c804100c0c0d02c0f03000502c000034076078015540300c0181a81e260083d6428441004071800154401a050160a00081e51000c81403c4e1405140c41c000a611609003a2030850070700345540402000129403060280c0103503804034000c004551034003440c8964051a2201c0c141c1840021000b400c025200c03c001150856440742c01070707460340f00b2769000d847d00c40400114003549505014607004658040d80c425084055941010744801c07048800c0362404540d8000c00d55107080010300821030740c80603480c00e4600300e240890100c4000005111303801042802516003a001c2c0300304280c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 845272634 1250 845271384 845271403
    0x1051c0209100e03150907032027041b093605120703030e01020a02010b030c030a0807060207170307030f0f2a031d0703120302070305120603030706180b09 68
    0x50340c00b101d1056040c007000001541c0180d251820350308500e036079440d2003071506403401c515400320032080d101c1c0090b444c00440d44004c55001c2c003422b2a600c80b900007006452900144081e010424003242048440c54110340003014059818080203045400074100c0303100c00540e0541c0c5900400c07015060411080600300e000c89561120061440e441540030b041d0517a0010341e81203003850740314120b01c031100380b080c00504150f00e0160b000045101022007010300d00081003100c18001e401c60400000403d21440440b00500e03085400540e644503d8a042d030049144154089500702010040c00340c401c2d4140c01c07000041000da441481f82d02c0381e40d510003040300c90111642214128207010451a071141001a691002c0c1c0360500048020007108400d0a40c01345400500007a000b5440c20f00030440c4810402c46440d80c40d02c0c045060000302c2c1c2d4080c00c9442442d0f004400340c001c80d8005009540d00b0030840f02034651052051180203a60a90068a21206c2c08202c500d880070000040d603094000034000207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 845273884 1250 845272634 845272639
    0x50306070804020310020d140717060109060f0302070f0b0f07110606010c060c020a061d100c0c0816060c05040914070203030a240e070816020307060b01051c0209100e 73
    0x85c40f5420340c44070025440320b0310081030b02d6102d1004903506460ba0b51800c4c820310558072a0845034110640c019070000c4000c05c8141406801c01040c88403a9118180c2100c8110608006a44150320f041101d000712948074000e0488080400700800c0340114010340e80688256110358070a00f240600b03064a841080700c0040c0001c030101b00d0a0040b421581007114903005a0060b5030040740c168558400340c2e00909100050303031404245190400d84100168180c08042d45800c02240a0b4070600400c620303100040900001c03008078481c14115000300f60031003000d90100040040c8001c0010160007900280300d41340c0a81d1419943c016580c1800c42c0d141d201d1003003a07001c0c62440d50b604903000c0040c0451002e0181c48520500e91005c513580d020407181c042d1130203800c034803101e140400c0f00401004004041d40484409102142c0c0020b400100355440103a11000200e00c1c090350500488071400780791000b0200c3e00311a2075510005000c0e40c0100580c20f019184104040e080341029102203150400b8143c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 845275134 1250 845273884 845273893
    0x2090102060601050918012c091b120303090d1214010512010608030d05150102071203080c090306250e06030c03070507080a18060804051e0c10090503060708040203 72
    0x400662041340284094200201100c107a400c481d8940c044289098021540b0606c0c91085000059503640d0011110310030711a200d055441d00e140296120000aa1800d45400b08018400510740c2d6034041076a180e4007080850f904e80c505090840c1d56907a40c0324203c030104000f02d5080e00b1030303105401880c207000300c0c0c90300b104120391a20040c4441246800c000e2a074555880c0da0215049130305000602c0b209586000205460500c020781402200f001030802e410f541c4800001c11a03c400200c0c501489030300760401c800760365203202c0820580d1194180041d414004d41040009921010310701502d03040c000480a501c44404940984007400000b032065407021083c40000c0c21241c4000055a00c0740082c035016007000300c10342d10100150010742e0750740082203007900400420340c410103040000701602e2030281c42c00d041c5034880545034280240800e4403142491992030030b10f00100001d1158843c06021120100076511005100b807455004583c4a806001d0105401610034915940540d800402a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 845276384 1250 845275134 845275141
    0xf21040209390c15060a1d070518040608030c0111250204020702030d08011a04060c02100c0209090d0206061905060703031e09031b030801060315050a03240209010206 73
    0x103103900c00d60041c0b0103000036810000103038900024012015908200004021380f0300f481810025040c0e01030b0042e0603039000d8a410040700000c180c40d032580001642c01c243e5550300d00c5406c103ca01812292006030410b0404100141c0d2040010061024030310000c02040b0403601c1c9440c22078244900c003844c1110000c8030941d08000039080e6900c1c0c1929100803c01403428a050307001ca03052100341004000824507180c010071600c94078100311280c081107400d0081c905414048003810705d0301c0007600a400f42c101c00c0804584903002c2e40f9000c03101500200340f250b880c58881501a86c410b0841e21070001400f602010580c1824084a05800c41c880344510061850400092140c242c01400c010b800705629068018202011300c400d0f02c007400300d400703c049280c0f045410040d0071080e20840a852800c24031340d004010035445005141511428500403481c1d90141a0280a011880e04099800400d141c0e00100708420070300c41c05124810b85852041810348000408100c1c0260100c143c0540c0104000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 845277634 1250 845276384 845276461
    0x20d0c03091418010902030108070f0308042714100501021507030522030302040e010b0a090315110c06010312020d09090b060403050a050c010210060f0504020f21040209 74
    0x40c400c450201600f80d44201d110b901020003200000c1c1d0002000d143e0020040c055214107000e488042c111301e05c0c0c0008060f1a50f80c5031076043c800d80c03041812001071900b801c2c0d1000f0201443c21a1507001c6082400180e600b83e1004180b480242c90400d82150070000004242d4000f180710401411010380c0b003011503451100c02c3d00a040014040c000440440c41000302000c03c080c0c9498200d07009940040c0c48504100c40011264010780084003480030902c1000119944402c11906803644040c400c200d0366400002103002e02184040c4d02c000200128803c0711040001440ba8103e80c01900c00558000c0c4042003662504031907014400010090301381440294182e401584c8440070180c20203141580d251580b0f424507901104c22906074005241d10400b075a4100308000061050b2441041007130314165510704c20380c00760720945010b40d80109144981d000800b09446290740100031510f03a40c544038005c08900d60007214124803c1d404e10022642818058081842e5945800010002145480d01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 845278884 1250 845277634 845277659
    0x109020f0d1109090c010815090402012304030f0605010501080103050d030b03070515030901051b120907030b04050a0309120822030203010c050c060c090d15021315020d0c0309 77
    0x5054a0700c045250b42e58866896a03c0c0e0948500c0e000b01c0a020000b41e5800014181d41c000740c400d401e00c0c0c1c0c844026080aa9884a805070402d0342420181c400ca104459000b4068040d404031203c9071038081000403d01217400300c029441c0b846814200302d240e80354801550141d8080c0009003041d80015103000904d07010f5401294070348401022501c00b60750b80d10000789415000c0900401180010051280c6141c0074017501d03030803c840d40d84a0302c658000090500d61405a9445484440510b002040141c40e0a11210b0055070304241001e940d8609030906691310700300008201c000507011030000480840c0c0d011a1580d840d4040101450300d48071045260a0180440310307034010010007280000180c0d8244034425196034251200341d2100c000d00c030050308125005184440741e060800442c0e4266480104401d41d00e98005480c0b081c3c803800540c03e40090091690041e50025115070110314a0a6070803043c00e000c043d80e003102d80c000300c049022220307880b0707a21005000c076102e082c052000c070145a8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 845280134 1250 845278884 845278909
    0x411040501051e030103110102010c1106060103020a09080708031b011a10021e07090b0105390d08220209040b13061a011103040803030a18050607200109020f 69
    0x4003c12801c4140b0100340c4140d0720a130b10440e28000003a1b04001c040d602800385461070700301d500700902c000c440c01400c01d846a1000742070714101a80002c0c1441d0050003603050710b000e4401c2504603240c1546510362195698408812000e20301c0990013424415001401000b4000c1903034a454240c075031040003801100e06d51902171754194021541202c0442003000b2046030004901f000826a492a18103e00c04803580c01400354100070701000181010b00c440040540024607801c00401201c507411880300241c5403046180200740210825444840c1c2d200ea05640030b416407084030350011519070202d000030710a0310402504002a4000903012641c0221802e50040c0b61502c44160b1034400e603607040480340c00000c0c010511035800c2c2e00142c9940e100500d8140804003000031031400b41425007440d580d000090a0250403521080680402c00242642050955102e401c441740e60800d410054a101101942035480d0303464039611100d09130050044d415041d801404401820350880c0a0004402000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 845281384 1250 845280134 845280157
    0x70f180b1206190e121206010c021005070501051005030a110316080601080c0d020916051c0507030b0f0d020d0f02030d08010305060a23090a1704060e041104050105 72
    0xc8000c0c04190a20000f44a10742507114400b840342902d038460708070b52058131030500581c0040054002d404001c0100c0b0702d21842c0d000c080100da5220001200c040d54940b000a4200c6c002243c502c6e19203411402030708540b486070000703000c50341d2200d08159030500c2c1c40c40340d07503850390040040d038001c260080141400d2480c05170030382c2c1c0007070f20500c801140b10f09031381e1283c4111f07880302d00104800324081c400700c0d64500040701d840c090444580c0014000c1c5102901c6440c01016015034074040038080c5c002c4404000603444040094080104800300409003143d01c1404030f41880c00060943c03500442e071014182005084520220701602070107400700d6034207001c407182c0d40385004e50405680c080042c040300007525030b2414815815454101d051a00240103460001c1c203120305c5207a48203170b1160000008400990650701a66000c82d204d241c146140c0e0094441c1e00074800f000300042010700204140c030600d880301000100c040d030a000840f13410740a42e0000c42d4061205000070362198008003000d1034903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 845282634 1250 845281384 845281399
    0xc03050f04060c1e0914240c0a0203010c05090f0906011e090f03081312080301051005091305011703030103121103040b030f0a0e010b0f01050a0302160f05070f180b 72
    0x1c013a03ca0100b03aa0540c0c071000480c1e400034040100c0b1100014078641c2d40b80c10f070390600c411904544076014040703a0820300f1002c124046207a9407512801c011624100341c00130000c0c84003020168010789150300006c103140c010318201e840c852440c141180f600d801040180d413039000c0d51601d129078410f55034074903440d40100407088800107070070b4020442140255020303540080e514002451117100c5850240e0190b20700c40000d0007042c0118002c007050300c0c1158026034512111680c1c03100e08131014030075498001d40c040c07085141942019120760005042e41c4403240400380341d030b00580307039165680000d1100030001c40380c60510070680c1d441500342501002403541100e0509403214801001074104449101c1c0e2000e40208000c0e00511a028003100d01e04400c000300619140440481e000b410746241550500000107051207100d480ba904803501c5200c17024400a880000345810901c0e1900c80300706403020701c59000301090455840c40494111413a40d02c01d0901019400e00490103045490a45175100c0d12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 845283884 1250 845282634 845282657
    0x5071106090f0d090f0509040c090905060403080601050c0c040b03031902011b0e13050c090402040306020301240c1103030409050c090a150e010e04180f060c03050f04060c 75
    0x1080103034500403214540030344800d0504040051030001401d40540801059034010440c8203542c44011003603a4065800c91107551710750920f111712080c3c940c03041060300c0c038140c01481800700120748940918481d5596801c030751124001128a0301440032501080d0704244000111032500790b112100c20807018040e20700f48054a00390b85d4000c4400751440015075101d049141c641c41f851844182c0f01219402c1001a50f01e190700400c0300c80815245010b070441c0e80d00080b62011481c1c5c000d849005074010810b5503070326120b2510802035002845201c0010510f007201e504507490a80b00c41102c200f1070703662003c0200780d94983d800003006403550660035000410010541d20707180e0082e907100744419450345940e1100d0800f800403850302d42e803014044880a4000c10043c0e944070041c031244080902e0078400d007003620400640244400c1e25040071121350300c1042010090400c848030103d6025000c2040f0750403000320140c041e6a400c4500703401c581c030b0031030000780082c040740e00c8103410081d1860402102d07907 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 845285134 1250 845283884 845283917
    0x28090618120606052707050307090608090f0f0a06061703070b040f021003061707080705060d020c01150303112b1827021e0708251203090b07030507 65
    0x1c50b005d003280c3d04442d8140703513900d4406080c1c44907802014a184c40b514601d0310240090184465008004c1080358420214402060400c00b5004440100c4181d8071645406074075950b0f245181d44003205c480c3c0c14060700090340c6552007044001c1a12101c05140362009aa82e1082c04410092084480718007100740e0f81d0143c1c40d01000660303a050b06031000140030713040c045000301071588805458400e41c00004207210000021419004603032080d43d0b0540c0340c13045006030030003038026420605265841c014111984484481041040368000e4850414101c1080721564880c0000e00c0400040c2030381e08440043d00c615103044d98140e581328a4800e210021007040e03000c00030300c2c952000c06110500702400b24000a0203613461100c600030f05e41145003543e00c2c68000500c03000070f00a282c4c41c10010411805001c801001c5803c400009140b4102842e0181c1c5109680c003000d440664146009840d0011118024480c501043c0c6d045940b202282c0d0b10181c00320f002e018000c05640070000042480f4600d00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 845286384 1250 845285134 845285149
    0xf0d08030a050a0605120a1b0e0405010204170f030a051305060a0818010e0a0b0627070e060901020a020d0c1503050a0c020a02010503010314032809061812060605 71
    0x5406200700455141810604481610582d4100d5417140c80782082e5a80c00c101c000440221141d803140d030582660f254580c00141810f01540060003482c00c1d10104810028194018070a5030b540d1000d5200710416222460b0b1b5a1941d40120038483c0e100300032030140d890145020f4600d4100d0703004003001d60b5444002040182d000b00d20502c01040c1910244090402541a0424034030240402000b40ca501070f4035141d40c0b01101c0c4000f4042e110b240010038035648071021100c6041c0340040c814480d03007074440f01440203008225001c00000c0c039006180285461b1510071141c0041050f4000c0c00014142d400700040901c01e84004c540c00001080005180c51440003070300300164403510009064a405a50310040e1400440c152085410a07002240140e80248c1a203040d250030000c44441500f100f00f01500d144102104a0001181c5098400c2c0003800d43c500c2d006644099611075800300e80d540d2040d41e2030541d00503c010003250011041c00801010704148194074002d00b00450904c2e6a1008910760 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 845287634 1250 845286384 845286391
    0x8030106081306230c250f05060711150106080c030a06090608031b07050d03050d06093207020d0c0206120c090a12122006090d020d0309020a050f0d0803 67
    0x5007445516081c089a0041e02d00d40d07408509003c04915080800f1b01c8400100e051252011743c02c900680800180324003d0940001543c5c0a400c68980c0d09001d500034048500c1e28202e0300c3c80d40300d001900160400002c98175412070390700e62248100f68685102502c41c0b13810003410600c009a03248400500c10b03401e8082d6034000e0458002641c0d60b038090f04030405100c641004008a00e60140700304001da519800303001e0902c140c040c50400d40799030b0400c2007100901a25440900c5150030080c4545082221911046000e0000c0c000381c0b025044100041d821844100c81070009a009860000034450180c280c40c0507aa1004024615060720304c8c8280042c400140e0b20840aa0340210b5548040c0c20061180700181c180c28003005d443d120a81d5800b22400da24132035160801c010086580d07148032598819109404000c0180c8100d40307400301c12a41d0b148aa08542d40c014841c0030049034031760f400f922820545503006000003103001e04000c18450301081c480007064000d00e0a6209001160080028500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 845288884 1250 845287634 845287661
    0x6010516080301055127040b031e010e07230108041e0f080d0b030c0a0602070911040b0406170c031e0703021c0207051908030106081306 60
    0x4403541003209000704484034258900f41c070010485e0000c12070121844a4465520100d0102c641c00e21814800ea03200c02d080302c04014206001c21144904140000748201d440701c2e03a2400140100e80300100025503000c3c0740e800f60960400c00ca811044409490810b40368400c840001c03642140d00440c0602e001c9055103c080c4408603807400102c0c40c641110201c050710340c00d2038014554101520b0b14290641c5c001c001306000c452200c04101041040301c1e03080d80c0349030004502911000c41e186c0e1b860142c62084441e501c240900c07a80c9401d01c0c9010700700881078a034107074010500b2500340701e079400050104000d10305840105020008070040e440c0000d2024043c5a0b032510341148540301100c09071a809442080d00d07110074000c21480c840000410b8021012180c4204899184e81c41e060b4000d1041501c030307142050094484c50003580c01500100780c102e116400f11051129194529100841c44120041591604000401040d0f01c107800240d044101034070700d012558881c0c0e43c0c00742114000d004058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 845290134 1250 845288884 845288887
    0xe0f1002010b0a091b091a031f06020a060f0c02030f090a03050d200d0e190509100e0603070506340c15021b2202130305190b040b0601051608 62
    0x5402c0304010380e058694001c0380c10f1880310b140c00c10340c1d9065462044540c803807801c0e001000140c51515801018150743d00c0000d40c150a05442cad1500030b40300c0110304800d490041c100340540d960b03100144103040c1c0745c500c0c99001c1c6090100815110724240d000c84080c1d54051082c07140030011480920060103000c8503038442d0301c40201d140700c030001860010103088407140c00c200000b014280d00100003404c1c00c107007110020041656082007800018260700103503040110035040201c03080c1e43c21265815581c8034407050500d40e9038003007016541c0c0041e0040981000083c850242d24a005040e01200c0c000c100c420b1101c584062500741c00c101d0300281c03081d1003004660200308840010640e0703031600440c041c07010300260068454569400c200030302d007040c020540340030420201280c00814084842a10200f595511030360428a407400348240030a44003409500d02c82e0807041c4000a81400c0598018801056030391662951001c104e0010040b03410301c4000c1110010345009204580043c5114402c05c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 845291384 1250 845290134 845290151
    0x2010e0d020705040b061902010915020a1d031f0b0f0409080703080402060d23090615151c0204030605010b070f0611070b092d102a020304050f010e0f1002010b0a09 72
    0x18545c007400b0507034210200d40f0400c0001d84dc1540325058009040c09649106030806000020a16048440304032030482a202d045000000c131550301b040c510268100e9508080c00d1840040104482d0480c00080c44114104440e00000340503402c6a0703441400100124242284001c102007a251600785005050282c490200f580705800620960000f0842004140724680800c0908201d03132045182c910640706c2d01028582008290100d5400ca0640c1440c10f0031f4400a2617440080e400c0380c08100c4145041100200fa06040541a03400680d004511850044000c0c6c4800009100201201001090800c502d8002c01c41491700140034030000307401480000c0b0304080c80301181e91509004080300110038084040320100148000000e18601c10014840400e00d103001070341c100300540e403241c0010200c00c0400450b00070000e80100c1e207040e60300190400f80714004441084101c0b401c00e43c80140fa9042c00b0300d038140316641200da61318500000031000300c00e0b0b00080303e90000c0d50003403003061340ba001e49 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 845292634 1250 845291384 845291393
    0x41508012009030a030e04180b06090f130611040306020f0c0f0303130305091c0b22020a030602070f061509060b09030d0c05070f03080a02010e0d020705040b0619020109 74
    0x2a1540103000e030440d400d0042160000381c844204c52070207000c10548441c0c4155030354a039404480d4004605814541e04901454000c088800c100c4c0c0c000d00c0b458540b4001030401112103070b0a8460710381403504450300d0b01c5c00e42d24580100300707010303d13100b008500f4480070000410f284010101c2009000f1403544405100c42241c1c544034041c00039a00e503030020300a0007242602004034110f12985401c02036150444c40b40400e540c00c500251400c465091859210240103217101e8050084d064880d0400c080d5001e601c1c008ca8486030030350003e4204407014010400300380300d40e01074041c0354400c50901e418084e0300d0b01c86105842164850120006460300204605104c900c04c4000801d0040055410100035000190b2a010411440400e2111804040d410000c00340b103c01e0281140b02e00561003070303449003020b8855030410740340b02025610340320070340c42c000ea0000341034101030312541d0040c0301150901050101808001c0c4d544c64001d1000e1080c1805e0141102040508400325400002c0b0117005042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 845293884 1250 845292634 845292671
    0x1e0c060a030f060b0304051b1e040e0d03140f04050304181b0216060e06120c210403030e1623030f1b010c1a07171018060806130204150801 61
    0x40b50035034466151030a2400340c07038804024689c044c0544080340807403070722404540a000714080e0b200560290303c01000c549030b01a4032490203140441c01d5114155107540c68030386d9408040d0780240199205200410908038034009600319003400850125800710740d41005006540c1d00495440940c000050346604403040907800d10052650703161413183c8a403c90045401407045e5541c2c509040c0f1080c00150480366210704032690b50000e071420340694a260f008004040c98240c5045000a003400c4c1801100c110010f40c410294680803c0c0315015450004c03100340000d10306801c0101a0311074620b0000c030f654203114003c0c1000704400078000c4201c1d200003510303079104070004ea5410300c13040304a40d40114182c010300d00d0842c61b002c40c422032941c0314590291400588400f42d1034041c2c2200040103040b0301a243d03003038100c0380480c7c00425081c0c42d02d080c220580304180120f8800d030b030007400000c5d038200c81040340b114080e00280001842c0701d141c4411115852098115005682d100c06012110210943c13 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 845295134 1250 845293884 845293903
    0x2030d020714040e210409110909060f030f0703033615020316080c12030c0904050615040f140307050904063b1e0c060a030f060b030405 60
    0x301070310200707041c4014400184515030700d203400750f55030300c600340313040101002003551880100c44d000141e00d00780c441c0000c1551090040d06803180c1001903040008138188207a50603028001c00d180c0060359075000303204400f0910f8807255818070441c1e01c08404034405121941c051802607807003442c603410310201c010b80303c08095485100180380048162a8803843c584001c03d980e00010740c0182d050080c401289540900c0da04d1580c0c2e5800407983c1d10802c00c1c0078004040c49002402521081c00c00076001070780a0200303d445c0800c1040401030000d03240707001d0744010742c0000c00805284030640710075038005840d003040c3c00c10051510128424848001c08040071510040114001e1807510700b00310200d50141e0000e4401401a52140c030a04640201e140c003ca0b1510188582d1902c0650b4520301078000c4080040c048089006012004020f00d45c054201d90340406940b0050060410800621103694461600b05e0201561660040c44886150080d10000c03c020381d241512810070b82002420030700402d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 845296384 1250 845295134 845295137
    0x70303050f07050403080f1201090608060a2a030608160f0e041a06040f1b090b040f0b09060c03040312080c071703060105070b0f0a0b0613030f140a050a02030d 70
    0x1070040128156200c001c807015280c1c0060103d8965100494140440c0900190f0b01c0c440030a040011401840d6070707200d0b07400c44204908560568a030b4000360002c0342c480360ba80200b00500910180d05100e4606086080a40380740f41c000342d420b40d0303140358a0a0915282c0e04044290400204008a4180d0850a009005961000392550515035100080001c3c04c5440c4015a118400068042d80d1182d0202901c02c400c19400d01024141c1e0f801d443c26a80301824007004a04844c101240068408007510151103805201508403418540c0989603a0441b100050b40060b081142d500803440900140009611400f80320410040341107025008420091081c80000f00070720450001c076001d04c50004a195101607042c3da40e4440a0040350140310320200a4020b03040034040c071a0340791a400515100e24401c060400055a00d00c040040910850403d81c9581d60500010301c045441a1544402144a10f00c0c0039401481402c045040450020341541c198010044890a505050002241c500d05a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 845297634 1250 845296384 845296411
    0x14040e2401020d02030306042d0e011b1b0507050613050112051312110a050c0406060e03070e060d17091905182a04140603040201120509120f07030305 66
    0xc96000071740d81e0000a203458030590712440ca011000340d807240d40000c954180704041d030718140d515030400003034a40e41907000055031901084420607644582200515407660b0b550300640d00d5040c03180006001e130345009071014042d641000400ba03880c20001c1900720103044004041516000c0003400c40c1c0080c9000501150420b420002100030601c55114010790095100110b04801281200c1c2c5620551800242c2d110341180e28040c40b100054912080c1c0d012541440025110401203a200c6403840015816512a0b071041c042400a20f1709158420005814884424456103c003451080444001c4030581c4001860409034144250102c80055201a13206602450000460401103514250800b8401940003040c01601d0110300c2c0900c01c041c1d080803076911145040b86050300ea10600c20821800d40a40e020400c44c2852003d8078800c0390141c60b00502c25400c0c0e00118040d00008211088078051248503202b40950b50300603016024030300b5400744d2150203a00c0c0180c1201d1001d40141e034950070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 845298884 1250 845297634 845297653
    0x1213051b06190e04020d0b09010506040501021e0c15040501080a200706020d021b10060b0904022b0b1219110303071223091014040e240102 61
    0x100d00044500d068951120b445058841c40400c41d890300300344010079070041c0009417100881300700e5002144051000c451400c0c0a913614410021184500d12641c0c0c05078202002440700003030107241d2a850040d2903810f9500810720340000640040e042c0b0300d209800c680100381400f03c0d503802000aa440821544d007000052580c4445043c00d10741d0071f894110910001400304200a11601600c1e1024020726041d0f40310180002c05c11194907180301c0307080f0a03100700c00721002c1740540c0f40140400c68a104550503d440344440c1404003940c4000d10001c6040c00081919080c1e404c403400003a510b50038100001421603010082200300c01c480c15405240b40d10851030a201006400e095040181d03102c505032403032040550201382540500c140c0a800d95030040d1085c4000c64002e030300801300180c50f411362282100030807d4503102e80a41040c40e90070458803403d40001a00458960364a05001c840c1a41031555606443d00c6860342101c40e080200041c5644203154101e50361250307c0d01c9800d0014224001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 845300134 1250 845298884 845298889
    0x5060409150f020f031515281106090706020709060308030a090f21020610141003060f140a08070506071b05060a0e030c03010507050412081213051b 65
    0x28108a407120540d50341d00460200301c00300c1d60481c0c215450003040c0d2070716468100c0c3c6c801111352005110b58040d0540294002c0040164000c03500f82036400c482c1c0c1082d115440540d94112031040d2400300c180300024072a003100e0712080124521400365007004040f05401c0040c024280005039000803061401c000040c030016035072505403544414820000251207140303051400d0070300e5035124040e0841504070780a181c0c0310500c100b0070080307401503004c69250741c5510b10b580c0c403141c04138481c0840311240d074030010009181c001e1544101c0d150314940815481e40b00d6411002d540e103140d03c0f525054601ca0110135441c2400c5401e01c00801000001d050402d00d01004507446103c1c6200042500e100c44030404602082059408050480640403076105c440f1060302915402d42d440080b842403054107144122440c0502a0034424051540e0f420304241c0750841101030a150040d003150620b60600c05281e03801c0c080500710703214401040803c0c441c90814140941030020003481000405018841c5090b2034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 845301384 1250 845300134 845300153
    0xd020310121b0b0a091404020403061401060207050a12020409060905010e010b150a0e15040902040332071e1a19050313020f0f0306070302040510020c37030f0605060409 74
    0x20b400c044558181d1031385200001f07000384681c0d04000c00340c0385000408501e0030010a03860381621415001c6848d41c82d03c85040241c0402ca034801e0240b0070320100200310050901d0703003281699500c145000701d4030001550702c031400e4507090000c644d01c60b90f403050281c0741d030b05e08002050450860603407420300e4407144190051846a20486282c0140702400c1c01c0010030381440704646c003d0101c464119216500ca1030310804141004c0c108074144210f526542c1c26800c1e0b0710703809002100c3e400000f000110324001d1003103941ca80344590050000880c54001a050b1b400b5400380c1e04030752440c407089588102001410360303107071114240c0c2020000d06004020490001848180c0e98a8044800c4c14145410b40300140703110044080c0a605401030a0a0102180d015006807041c0c480482310460307030140070074080703aa44461901465002500012505c0c08201440c0074001d40143c407003005041009007202400c03444410b42c000c0300c1a00d141c0902009020041c8140346e00034108950500120380c042e115425034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 845302634 1250 845301384 845301389
    0x90203030301050d140d05090108091b13230601031811090c0f1803010f150509040c0305030a05190804110909071e05090901110d020310121b0b0a09 65
    0x903900b04130446052004944009071051100c4080750710038920b08600400780d03001510303d40d011625440100750300796008181521403000440020590f02c6e90407003080003034038100701850b0f5403541e50004401d2072421205030b12400d105000c4a4800c909040000500b25092080d119150714102011035001425050480b00000b004445005881d141c0305503041103803080e000c01142541d000558003840c1262a10b455110042c200e008100d10000142d00b0300c1551040304c02005075002c4604188594981458402d40080c014030084410300d85076510185154091795407071021841c08a01d1000c0f031190303800402c01c00b004d94501b03e041810316035960f10481d02510400c42c840d20040002a08444080004030010300c142450500c0340f403040580910b1013040c0b80115400b4041c10380000b0140001401034240341041070114910300481a800c0d1402508090300c00c0314010041003000903454a00164160703c140030f513150300c00400d2842c0c0703828010720190b030000344283d400b03010460700380780c006000004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 845303884 1250 845302634 845302639
    0x210051213030e18090f011a040e0304030602120f0603160b1804110c0f07270204080a031116080d030e0f0703050d14094c03060909020303030105 64
    0x4403003280e00d8180e40034102e0f16119504920003d580000c1811610300850281e560207050b40d403104502c44a0300c0c262a402e5580c49159100c08013040110301f800e80c809800d40300310307006881c00e080d2240e4508051380d018441003114860000e0034080e40010b40c0c06010b80000040340203081d20b00102090142d084450721400380241000301e0b0801c9000340300c420f4000e00c054028000c104100e801003103524941c0084c00022071034440d82401407203072040024070310140e440242302d01c5d28000000e04261aa2681000b81c0703044c01c0d80030b000c0024014020084081444e1290b2120392000b030300507811a241c540030104284205c0e20b080820444110041140c440f03a0000785400725203569188003082c90000740c0301d0420046c1c8218500007080c85400b1039016000c01d2940c0c2c400300340d5868040704000f10300401c060543e20812412501d1031075a0003494080d401d81141c22a552140c44c02d0100000e4082c0c0d43c5c41c9044c9003010002c41444495251185001a10391f80c002003006003420f4012907030f01c0c00140180c60 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 845305134 1250 845303884 845303911
    0x27060406021602040f06061805030606061b0d0804031706090c03060f1315050a14061c0c09060f09060c1e08031e01050a0303021b0a2102100512 63
    0x160002da002c801402d40140003030041e600128a890300500301803094000050001900c0d2a2415940083c0002c5a0004008102c503032210410011650b00403460001300c21603650f80c1c0f02d108d280034408541000c01c1c07615114014600340c100900b400141c01d03140c1104015820412000c3e5603501001380e0490507a043e416201c0e07542c030303001c00d45210f06e4400d0140d01c0210760003140300c42e032441d8000e03085e098626000200d07032590300c2061110100d05030054003103240c2e00c00c0414030141440ca0141c100b2400880c0b03000d00c2555a07604000480300d041a140000681c1400c080c0541500061920480b4a80b4982110401d29040008083c1100c40318000c0014402c044000300d90b100483c2a071101035006001d05a890800120b00f1003101d5413506940606950700d0000191854003800d1101140c1d00358014200b00722880030040d08840700650165400b01800b08040740d00b242e01c2150810341103007650350306907007411030041000b01e51568100c0b600b0010100f01844124031020071181d0401c03000d86911 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 845306384 1250 845305134 845305147
    0xb0109170607110c1806040e0105040b0403050903070e0114041d0c120c040612050d05040311010e031c0903061b0c0b0406020409290306071e0504030611032706040602 73
    0xf50030320340c032807141076030000f0f000c00511164103004403c94000c5a0849040145454038142365003030760f00031103001c3d01011b0321600140110340640003c000f0b00d078008050b02d11403074403440b03441b000000a8200824042c0b0450700d246071400d0a114012680e6413100d4002001076280d103040f070b079a10102e010702c4e01038072509209800c093740800182c000003000600c14880c036512000300791030408140806483c0c03032040a15010b64035010340200c0d400d8076003004000041c94003403401528940700b00618140c144c821010200000820346084101d011955a01c2001d141d20390b003407003800e45844002c119202c0410f0301e03511000c61781180003480c171140c0c000d900428507a150708043c0020300959001c88030003810710b00580c17161124441900c094a1000681d0100f440d0381c2014540d0301c500840d010300104510300d03442c09000d498580102d4080c49649019458661290380b40070941d0851228841080c2e808000d01810950942080c4031400542d02000001441116041d40e82c8501500290880740d00003801c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 845307634 1250 845306384 845306417
    0x2a090a08060a09020109060311250501241a030403082a04050a0b070c030230030a020c010f0c03080a29040b0a0803072003100b0109170607 61
    0x44801482580255200d0345009055040508000007049000a550b10f9003c100c1c0b9000e0f1180b494480700c0d014815040a03000234048841d40c2c98100d0f00c07006038070f585004600162090003004004d07200c4511010120745140c02045c40424241c0040b15440109070103a00e6141c015020b80f81d0150301440c1c10034907030322010401c0358158103480840941c0750102c0e00004690b0030460040040701c0041c0d40ca02880740d0740b448160200d0082d500010601c0f0b0144c44200b0251811543c41042d4001d60388003041c80781b1034100003c5001d1140800030149420120300b44480355018054000940c0c001e0801c1d901c03600c16403000600052031002d0041c00d001080300855420f40c1d103a80444195540072584039055242411100c00000801e000c0c0740c425802c01410041c5404d00317120303101c211104c000c000c42c200f050369a20070b444c410030420080401030480c65180300b9039904001401505405010008805014000040c001030958010480007400c204041b459002c00180c400e50054039450180011140e0459 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 845308884 1250 845307634 845307649
    0x41404110d0b0103301b060b0d0c05040b031906020a03110a031e0c020a030503043306240e0f0310140a0c090b031003080d020307082a09 60
    0x3400200360b060011080040e919031641000f52040c01e22030341c518183c0c50340b044030110310007110000b40c0d018802c060f4000c05a21001c51030740c450034012400c0d0001c200403a0400c01c0c2e205003910b00b5160004100101c1c1818459114081c8083d0050011403044002c1c000040d524403034010a44d6900250064505200b0350101c40c1d81540d5109a035581c03100c20384001d02915070704240400c42c080140f00c04c034040d05188142d400f8a00303182c01915003599141c4040d01d49810041c8161620f80da1040c01040d00101c0b000e26950508a01300b100300035121040d0354604076a03003178101c164059080c0070b10004410060020702c240b03040a03d0207020904000c0080340d0240254200c07560107100c1ca00034803024a60340d4000c15403181da8080032040c6941c0d015010000e4402c0b040c409004100040001c0c000c80180f9401154000314080042c4446552640c4011440c2d2141c144c0c4005140d0120030b1140d03040e03010160719000844100300c580c0c001a07580705840300c8400c0f0513441502007000140a07200e61079461 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 845310134 1250 845308884 845308909
    0x15050607081e03130b25051308030301060c150207080403060c0c0f060509010e0613080a020f07030515070c0c050f03120d050603151e04030306080d0c0b010504140411 73
    0x4845603d905200e46006508494044111120584000061000110b0000402541d00940017000a4903410241902c190340702451480c1d00402108000c11055010401140200050390b6180c1c0e580b080340c14850303461007100a503284443d00400000012504010a841c10303a504928005110b246d031010a46105034002d000034030160001c0c00e03000601019500c01441003158000038003e08680390381181e200e80048580b54804000600504007064499000d4803031288503004481c81e8003400800c842c0b0f006266401260298000c1074456000e0004c0106a60805003a06040300642c034140c1e1140a03c02150164a0003903003d200f0382c0380300d0354003009400310f101981c480d55031356170b07500c0c03100b0f5409841e040702c40c140039124220303000390505034455103a44940d00c00c031503000d40003050b0001c030681040301030402da0401d5110f410115009105100d140c4a404140e01e840c0c40e040d8080c0348c543d90350071050344141e01c22460465050f050004541380c3e141d000f03501c019000407290074000010012a001c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 845311384 1250 845310134 845310187
    0x30f032d18060a0b091303090b071202070909030e040e0c0402070f0b0f0618060105070804091409120a140c0601060f02061321020a05030c01020d1505060708 69
    0x110a001103000880300c0c0d900740c0c2450a0a440c0c0c0707035076a921000160703528542035903042244500003035407444d0100210864240b00b0700d40186400c5da100c02c0150b2a812155013a1036042082c400e0015054040045400501010f0414800c4500640300900112000c000b4107020300d855a8a500c0034142c11b2091100007440244115280c80003401d211400c5484000112200c51540d0302160314501c074101c602e0710951006202d030026600c0c4100052042001801c0181804402e00204000946550241012f000c1550b00000c414500c2114104c4942c2c000d020503240f03401803858110170f00340e98402c4541124207401c1c99105c0c00c000003c03404c054030980d9403c6003240500b200208802c3d80c041400f0030000c0e0301381c3c00c80f81181c607400c1040500c03061041c0d006004c03414213900d120b5101c40c00002907290000b0303070045c3c400111043e2102800c1da80031160740b1081f40d41c002039807852802e071441359403282c2c081c4114074030398141044082541d83c03180082c05044000302180c030713524034420000c41c18140b40d02ca = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 845312634 1250 845311384 845311471
    0x5031e061807120606020d020c0d0b041e0b0c07050c010f080a020c0307060e0c01081506180315070207081e070b030606040f0902042d050f190b03060102010509030f03 73
    0x85e11002901c9800c01d02c200001802202c0010f422840e0424004090329045954603045403030f217640300c2d1030340360501d0800304a1007005d0b5000d10110f02d2614501e44108880e0b00d41c1d568030f0107140381050134221000040c50510000c02c0f00792038401c0d4018a0303103602203210b0200680e24607140310902c1c80d40c0a130080c002d06150170031040803a0a00041042404d100f020789500c109501c412003440084020109036503040740342800141c82c9111034030724015081402800352070f00032108002114122104483d2280941e20047c000c0140307440811100c04140140c40c01d099180030445a07040d2625403a101c1c95600c190040701144107561a101201e000b002615003401c0c0c0681d4511004007c3e40240c45101c102d5070200340c2180016100d100c0210600480c00000407505040c001080908111001e0311070300306051195030300c10183c50400400180524060303054407494250002420f4450050441500e6041400001c504880d50f4003600e070046008607e4100085034222404180007000200c145c48184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 845313884 1250 845312634 845312639
    0x307050310060806060604150305060d0821160518010509030f011a0d0b0703050a0b04140402031006051807140a05070210081306090609080a05031e0618071206 70
    0x1066000d1400c5030748950640b0307107039076034138040103d03c3c0694401c44614280d11203044100709c0c86030344950b61000300140f020004541ca038448000390340004890802c1c100b81805c00c4241e120110403420713446207501070003c4003c0c10720b00d002010b0740030f01c0c40700c1c2c4004010b15410940e01e80c0030f03405540f82000c010701140d040106046ea0302c1c3c041e0218141449000000c40b44543ca2805d003a4040c0c000070b07412001100003915200c008800600c001010380c0c52103a80e038075419103681e8641c0602c0030307000d610785004181424580109820060302c040e000248520340b6104014a8172019150205040e55803541c2503590f4440d5416911400b82e1900c004c0e14110001d86d6130710442d00320300071704142802651205020380d02030b4010780b000c51050300c00341040c164400d10400011044d13000604018812403000c682c880b015500d105090b001286114049240401080410786110080d96074000c0752110b140c00b00e00345400404c58449912122060150fa01c000041525008491101008170400b804000e541d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 845315134 1250 845313884 845313913
    0x2070503040b0c0d1d0d15060f08100f0e06010e04060207082a160504091109070807080901060510030203180f0304050a170303060111150a09062a0e03070503 69
    0x25200b1160038040791003a030b8828818040390a0005c0030034000b800e00400740310039450384490842000c07940b500d0b4a85541e000b00d03d0007942415040107003002e000416043c288031403500107403010000040c5015141200c440c107185000281e0604484020711241c541d5161428a42c01034803511034054001c0c14000307807102441804809480c9607500e0b01800b10314000c01640310640b9000c640c41d2003e42403820320400c3c440b91410703910182089208810b484185040e03070010441c00b100071650030012074002c000708203120342c1018105074414003e0001b008640d0174a80020100c5280400c1c500401da400700002c2e1100c1003c410101818220b40103c03424400060400d951f01d60107401441c0c0940d50f000000103605c500b945030f00c40301201c442c01450440e55500011211903528101194070340c840c504c5040102802480324a0042c000d42d107021400d100c40c0d05050064038400030440444500d1844221100030b1460601e000a0601e45456085804202c0000e841c104140d0450b030f501d03000c1c406002c120031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 845316384 1250 845315134 845315143
    0x70606030f0b01120c0311010203160b15060a091203170f061516110409080a020604050d05040b12100b12270706050a12230109051902070503040b0c 65
    0x750702c11140064140c0c2c0b0390000c0da40c026103406008000c1c0d42c8090003800000c0041d450a8000d0070b042c4102d908000c040e1014140980308208250784102c0c1702024408600020900403496910a40300070380ba1402c800301c018107035041486080703002c5010300008010584154258103288000c80890b0001c1e05042c120f9001c248020384800e03124101e044807000c05201d2000940e90045c11005801c200c4c103604d92215030302d0400d00340302c0303a40c05541c412008c0b000503401009403456a01a074000c0080e89400e00d4480c0c50070600e04204018031034140030810202420b4000c0f90a02c00c8091822039071501d458010300c2070dd0784142c0003603181d410042400e82460240301d8546114003107010358950000c4074000075200100c0300d04110141d581064405101242c0200001d0a40c00e0b1141f401a0401019220120803101c0c80c140f108848520b01c40001102d001440d482e5014000d585c20800180c148142d215004400008112400139008a204000d211080c01070310020400002019910030940e428182c95 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 845317634 1250 845316384 845316413
    0x60602010c020c19030b15090414190b0c0901091a2709010e040c0e0709060201050711031b01021e120c18060706180501020301170309030a03080c07060603 68
    0x52040c064036410030b14000c9801340c8000d444026820940c0d00b540c9600007041c1004013114030440c02c0c0030b9500e4154441400c543d200f82c0c011001055007111882e8183e003800300300d50750b0061820354070b079290000c14810f80e0519004600301602d5036a4565400050b11080741c0340d8020100c0244001521050442e1140200900000280070020100103100d541d80b00c400e6a2100c90380040080d001408825101050990050300075265004003c0c0d07184245040c0407001c40c0c6d0700c40000d8803041d082100c5502402919002800307404c20781140050000b145950303000d64040500c03c8180000690681002913044a5450070205030700c108078001e490740c200c0264000140382c941f00d86502d00040e050b04100c0305a4168501d800c48a000c0c030385500040101030380000c0b8054905650b500d04d034482040f40d03081c2c00010340f4031510001d0784961400714110b43d02070000c86100c1d401cee0810002e07005580e40c0410381101030f0f541400c1580391a211a1189095030146c848000d1041345015004403d004010905108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 845318884 1250 845317634 845317637
    0x2704091104060f030b04020f150d1b0e03120d1e0207020f1206010b070c0512010506011e021207061803091a0403031b11030a0b01140306060d06021804060602010c 71
    0x2d6503824107011407103900c0c400070703043c203a00038003150040c900750a043c0002c010003032401c41e420384507085040c9550321201e0b2404400c0d580d158641d40741c03c1d803040c0c24120346409082c2001094841400b0075203448031107004c41c1100d80c000640c4003014440d580007084003290500c407004005845022600250b001c0b880a0703109002c0c4ccc1d10254603910305981c01c44074031910030029019692030701c03001c0c0045802c2150704807040c802041d13000c00c5644aa0707041c04002020840040f58904111002402030075000307100418809800065a43d40c40d00000c4601c0740701e442c0b0034115030f6070069040c02c40c0200780700c100da0700b03803080028030b808281940280c0c00c02c1559540441600300c64010003e15200303201d148001808100240c240c0500305603c044410030300d6015103201540504280c00090070030b00e680c0c078211600800d80c1300511081c0944440603803aa401503000f0000c034200500081c4800c1c20140740240007580000c2c2082489050304085140e150001d80207128590b1076940c064085c101c000840380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 845320134 1250 845318884 845318891
    0x11805060906010323150a020d050903030606090603040c1d160201020310060c02030c152d032d0f0f09070b0d020903070b0f0408060901112704091104 66
    0x25150341c40482d00c02e04a0344e0200000d004d045031000e0484110603102954641e1780106094054200c0d41c69012500c030304e102c3c0c1401130395004c2540000c811200c0c09020499954028010090142c582c1c0c0c040742c003002800c84039280c0380d55840c5424040717011280c20500140000f9886511904880d01c1301d00d024450341c48801d010195952400c03802c0b0700040360240d900010700d90003040a28000d850310032132140081c040da10350044601c08140d00c01000c4041c036540703180004000b44428074034028200c50041d2400c0c3c4c0c04540e0200c0c3c1c885942800081c040020404452465008c0032144c03080c60301405543c031801003400d2425200c0c2c42d440d40f130101c0380039142c4084000062500c07030000c128401078504845420b8141000300c80464001d4208101264242c81501c4c1c020a803844c022002d40001280e0301013240d650303403c01420340e09200b4054610425603041030060a801000341301034070f040503059240b08081c0c0c56141c1e050400b81d0b15018625400074a4003502c0e00c00d11401740004d4900034400e56051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 845321384 1250 845320134 845320141
    0x8070e130519031107150306090203010b09010e1804050a02010f0806090a1e02040308070303060b120c0a0c0f03020f07080f060a0b0102010b190618030f06050405030c01180506 77
    0x4862640015000502640101414041459054051800c2d107402407804e07400d141c4880c0c4a151030a102c0360000102c0071a40030b070300101d03a6414050440508198070041d411545006a000310740d00603c0c5130141405140411500d1076120400e6803a80c42c00e020b042180d0307a091034101036813100c0340080281d0018511458020886001d551400e0003521301405080540ea20006400001c101200980d041ea51912018010881050020307101450148070095551105464080c0460b441603200c041841c0003806441b00c5d8442040301030303501403040c450a03595a280d5110440b04c181e4105c01c001d1400910b0a07604083c1039000699200083d8100d0485800c0c03512115810350b200d00c44840d0707100c142d01410009811004581011549c004103000104002c1c21036000100080d025190b00b00b054014501d0400c00686d016196041d104406200a0b00361410368a813000e180c0c040680280640341c61318082820000200201c031850300a0000821042800c3c1d811060f2803400b500c03060342c41e803003910b010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 845322634 1250 845321384 845321401
    0xc1518261524010c0308070320130f0503060a020d060e0c0c0f011125120c0314040b160213240504020a020304260a030906021b100e0a050a08070e 64
    0x4002c0c542c405843e1207284101c2a60201d0f400c920060149040540b152200034043ca01c010f594040322104d02c4101d5200d0900089880c40c0410b82d0748080348480c1e90388810000c40d140070858640114640d00f000d03035109400c4898401078070440d442003038100200c0081200b11100600500207000c00c440a0303620165080c5e840d2401d80e920287c150500c480100495000c1c00d809417049420000c00c103916a00201003a182c40414001e01802203020903603581120080690051000e400002c640b46420f0030981030031302c032403d00d004011000c0750720520324200c90107541e5801d00210002400703600c1400f54a4501d95001040d65820100b07009041104001240a14190090381e0507a0402d40c000e6080a15099081c8900700b5a0700c2e91100c200c11402c4031440d8a9400d02c4201a03150080e1108000b052410030020701e0594515800140004103000c001d801d0fa0b100c40a001c2e1502c6c00d407170403950000030000000d00c0c2004d1948100ea10640c00840041c0aa03004601d003c01c84030a404c8400751039071134026 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 845323741 1107 845322634 845322691
    0x5070215030c0901170103050703060f02120c0d0e210703050d1406181003080c10090c14061801050d020d05040c15182615 54
    0x150081465800210290800403c1c1c185c071100b542c515200c898440c1c1c2140801040d1a8841e080307040460880d8041c1c1c0c50008034009440820700723001c1140725080e8000518000094201203a1015090002c610b400b902d2700790300c0096004500d404200c0141e903000b00811004e0000030b218000c1c9804552040d124220100b440450319410301c041003005c058003584200c11540000020044600c44420350304045036480071001d911081118203042c01c002030440011581454000b004050051700301744e80086039900c1c402213408000729000d2010318407541f484a19814404800c0340c4031540700310001d03c8041c480c3e080044c100104007030a0410b071807050780c050761103071240c074402d000350a4000151000210b05040040e0911091344a00309080c0e511f1280e2240505d084104118a981c2c200312103000506903c00e49800b81003101d10454020300942d04000008280003840b6200f41c1e1511 = true := by decide +kernel

theorem cover : BRFrame.Cov 845143884 845323741 := by
  have h0 := BRFrame.cov_init 845143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 845143884 ≤ n) (h2 : n < 845323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
