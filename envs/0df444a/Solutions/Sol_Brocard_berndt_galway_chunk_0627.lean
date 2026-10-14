-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0627
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:48:43.75018+00:00
-- url     : https://prove2.me/submissions/1c14c95c-7c0d-4aa6-947c-932b41aabf27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 112589928 ≤ n < 112769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 112591178 1250 112589928 112589933
    0xe040f030815130b0310020c030901080730020c0a0b1f1d0702010e12070218042003031e130e07020717010f050c0c0c1002030706021b060711010b03070303090b0304 72
    0x200764400d02c2d804901b42c40003503c8a89000d022000e04102e4800762981c1c6450fa44081007641c0d403100680745103d01c051079410002028460100104801108407401401d09143d901100d10381900d4010944401d02c000040188001c00c2d030001e54003401c00b0014032001c46141404003068801401c0707405400380420400100d20500c03d500208510001000b100c07103060140c03d054640d988981c00c00d03402522881ca10303220b6582943c0966024645c400c802540b4001c400b20041d9021000b0214140c0c1400108482092080e00c91403a1202000e80140e49969152a81d400700c86481700d980600101c0010340108245a60040b9030780b070444440c64159401c10176200013076401040c480e6001400da5162100b441080c032451809030042c2585c000440329018018004c205c0407082181503000164400c00042c4001a40c0d0303005072540e40102d002164603070f441d125919062000c1120a5800944806041d00c8181c50900403102d0001013a4081e00400d401c680b401401d1400901030700ea046400000031808 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 112592428 1250 112591178 112591183
    0x140105182a062703011406041d0d03020912010b0307030221100506030f070e01210f03020114011505030402060315031b12061003020f06040e040f030815130b03 70
    0x3440302005111a80e1911100b214003450000f01d000c14508411681e1200d0440c1014803e4005100340e030041280c6a80d144800c01c0f01400d104c003803503040328039007204200c6620020000c1d0760408101e602c0150f183d00030706050003d022402d24600c40070360f06000074180ca0303440100741d103016250160303035411500010b603070507103041e03030b0205d04002d420701c6564103150400310740754441400f401013142a10760350203007a1162a69040140501c40850320100b004000b10074800044601c3e40070744266017604a03a15840e80001d503000c076082500585d450f07106100300000e103210110301400c030b581c000e803552592007007009240c0c1c08000c0000340a0040040440c02141e183c81e00b0f0000300800034200e6095007042190b88031040500c0c40d21034010403d6500070080f80d2000f02d40c0324803411100c52245c58070703481d603001c10117500c4400c00301c0e030781202c1d00700000b04042160a10851291340581c00b0080b0018444c81c004000ca0001407600480301030f400d01900d4140c2d42c0b10003280061400043c042065444000082e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 112593678 1250 112592428 112592503
    0x20306060c0706030b0a15080f0702010b03060c0403020a05060c0c1009031e02150c060406020901050712080f060103020a1b020a180f060f05150703050409060314010518 74
    0x10781840b418200080da281d0540041c40003200554002c8034240c1d43d92624079012403c020081c0210340e0480000c2c0c1d2030710344d21401952080f520301c004241110100c01103801c1034000e80359146003c4d0001018802e6080c00d01044004040c10382c3c000340f034078043ca8100e41d242d100c100303001c0e8890300c4115101c0b92420b02c25821a070243d43c202e1a110403801d132104000d4103c1c00c01e0750040340210519070b80c0c0c03041902080161070f0600101c2000d00030079500c642d82c200084d80070581c1181480024442400410101030200e50480100d8070390080394200b2111002440304002c11143c10103004021a0715a258440d00f43c5191039040d4911880175000c40c400124a0302d125003042ca04c07022800d8928107211201d4201081913110310504100f46500d03480f205503c90114000c107600100c20011804220790060000d00344140203241c42c1742000e840d039680100380c4040398000e444822030349040c010000002c0c0318080e00084070303480c07645081005030a0140c4030b0559617044490f0b180c100b800c0400c8103036014440c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 112594928 1250 112593678 112593697
    0x70b07030c0f1406070f030b030703020613171006080705010f03050604060b0c010b0a0905100b03040606090207060b1905130e01021b060f090d0203031603090c0603020a030b090408070602030606 85
    0x12040140740680959a44c404c403800c0c00000c001007480c410300e501a22a0070138aa4000c0d0146c0344160854003480425400103200c52600e80350b4100004602c821038025030404c41d80080908420000c60b001c0c881030320919002200300360071881e001c20890780c020701c1522001034107090204407640c441001034001c1005500c039083c100c1c000100d044103110190301800d1202002c6403040580c80d00d43c40058101c0f40d08598824294410460034403400b07160350f000d554003900c00c440100d901c80d1900c0380b10040c4e070441c020445d0403644a021101d1a8030b003101c400c0040382500141810050f29160001d0081558421100141c50341c0300500c4001440039011140044203001c80341c004e0001c40c0e0340d0255103140883e1881500040203012a44140c408180f000141034503a0041d410342e21507030b02a00e600b82042c50004103250352101c0e44400140c8806100c03004082c15280182c81e106c3c00340c00502562041e8a959110f400311100b0000052401c0003a1005580c101c04016141d42d160341c04160b42c0e1040c0c205a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 112596178 1250 112594928 112594943
    0x50d02010e030a0302031b0309031518071202011e0206010918060501030b040b070504031728030501030b090c2115010314010b0f0f01030b0303090a0306060e09070b07030c0f 76
    0xb50281900000103068400101d08070451403881c18070f1f00b40e00c070300801041c1940740e0004155040040f04000712180c0004413050004030503e498140b00d40b6060166000e001da0719045d212a105668000a10021866080d10614040300644d407009480300c0c0705008200c03801d60740d0076040320003480107010001c116602000030401940c50b03042c0060401c0e03044a007164008030140c00107903407520800c151400c49a12503840c00c2c484d803d540c030702c0d1410340000405129882c000220130030104004001103102641940300040d195055040500c50f000d002000d40c0a0b035031102014101d10780f9021460882c84441020034800d14506000f0076083c007043c414542403400c180070012040c014104148041140c42c1d4008000c1c4c80700c802d083c8a030003403044035003550100503400300b0000395003c0d410403c01510000c05680c135000030400003440f15132840c1c1003038840301e0341d401e420300108000400c1660050f035044002c00d0202c0c5441c009030018400d5950040402c252100c0c03400c01c02c01041c18040545034007030712 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 112597428 1250 112596178 112596193
    0x1215110a0305040c17061315061403010c08060634080c060105091302040b150d090204240317040f0905090c0f03030a0f1b0c030506010b0c0304050d02010e03 69
    0x30080c0c0b4007600d081c3d51450503d640012804440c80c03548616030360840c05401c03503075100d81d020004100030741d034183c03211105100c400f000d41c481d038407414010f03042c1036035456400c03070402043c9401c50302c00a0402d01444407000900180d41e40f040b098685220b025045d4030103800d00b81d4140040301c0038100c050105c1000c0918007904000203c4068141909481d00b00c42c0786030f98620401c901404140c800c01d1402100c008018050300705034011445c14038000e001381e100c100c0f854403040100d511981150f8012a615403003542103290a01070b440500c120002240c0301d00b9000700540d4410342d5103200041582240001600540d10110152401081202c80c01c2e800f00365100b400b040900001c8410500354004c0f00d8061843c2e2410043d40703000c00b40058001c60801200e0403041d601c0c80300e40140342e000d100717004103a541881601d240580700184154a200d401a1451404c24544041030f088144054400c5c0516103440000006070780850324100c44d003030b1104000e400142d54900d908402c09030103009404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 112598678 1250 112597428 112597447
    0x506090c07050c040e0d0f020d0c02010c02030307020a061d090103050622080a0207030b070507050a02120109060501080c0108070c1110050408100e06010b0a082703030106080115050301121511 84
    0x503109404007481c0c90310361f07591120b00c1c412070702c038400310040401003240c0640c00d0340594810824041c4a07440902201c3c50407404d500001c5240b0380c0c9600842c0082c0c0c00d1100e0403413101c002141c803000c46d0700a0392001170780c1d410341c5e440380d4a8140081c0b5840703240d004140360a00c0d4100c2c0c010654115608290010354904030404001d44802284c00103580030140c55000c0354005102d00200c40b540d40c0c010010b49541c00ca65820804803c3c08180e20304069900c462441c0701203a41d903c00e03a402070960b400100315400080c0000b42845600070501014420301e0031401000c180b0510701084818000c0701d804001403c2c0d001d0070b5419000d19081b07802940f10344202c00b400366240382c1c0080284503c840440398aa0f0b81c6103c0a2000d21404c6069000102c41070302040b210f02140c1980154221405401d01c4814203100c1c0044c61600241e00407070004014000401880c80e240c120088042400e00e0402c1ca17540c101545403549621248005000400da914100400d042c5030f84007081c1c004503a1456669500c006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 112599928 1250 112598678 112598683
    0x20303041a0c0d0e030c090702030d180b01060801061704020d0b0a150506090604140a0515070605011e061d04050a0c09050306040302060118140a1e0506090c07050c040e 74
    0x2000c2c95180d40b203045464600c160060b01c1480710100700030010b100c0c003080d000038016546005842101944420300415805024034000c8503413060500001ca6030242490038501908201030340180c040c855610018001d26602c0006012015690207152940752114408181d516420200c05003c0e07510b0310080c4404c0c4584c0c6d8201003c0540b071401c82c4190710b03484804000940c49107501030f130b50001d001c11003040004d001b044540810600205215030b49961080464440d000071000d20751080030014547c3c0800000e0301c22070340036100c403258a96840400038504202032840c2d019603005c5c408800d8041000360554102c042d05018060414840f6003450045003003e00440e101da000850719420010503942400514103204507050b1740100340c5a4a00255500d0f0500e4071080c03410007907110340b01c22811441c100ba1039805840c02150001c0c29000c0300b41e4074800d80c10754001101c201800c020a01401c2d1351040866a00845000c10007595000710340ba1940c90403181a0141e500681000111840c20502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 112601178 1250 112599928 112599937
    0xc03030408031608060f120106080304080f070b03062409190f06020102090a0e0c1306080106030e0307025b08042114030a050912040f12020303041a 65
    0x203e44500414804508280c07101502290200c2e00000301c0e50f100e50607450509440301586150348000124a03031500b094900750b074410341009002e5401401ca0a0050310100103100003041c0840c001c030b0031400d00340c000810040001070003216019102c0041d810b511a039070101e07400e6003001408401c9001d51074101c1209410305110790b086101948a001600358010b0080b60f0700c2c40030044c51251003d05104124082107405480c08800e030710240002ca01c10703510801100d002d031610340c490740c103030350324140004091707904012200e0140e400038865980140c540d8480403040c5480c80070542100088604015a6402052050010504103038007100041100c5001440c1c012441e844c10024000070700c1c2c00340c928010030b850003040303603095070031a0401e8110824003c2022005140c0380004499085010070300d0342050720740281156440e028443c510742c04014100d518424000c00d14285440c2c10021700c0111600e100b10b0802e07005901c11041195403e2040718081c01c030034190514140c102411400c1d01d03411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 112602428 1250 112601178 112601191
    0xc03030501231005040312020304031205040815090f0a030c0b070302070b070c0204090804061d010906050a110109050312070e1e04090c030b070203120f071b0302030c0303040803 78
    0x1400e000401d0035a1030408000e0400c8a200c680d0018a9030308040c000c03c83d9040d005542081418040800010300c00d02c0360312450200c41e0300864403181541003015000902013051414002c1c2004208200e440100b602910f200d10201052150740e544c5031078a05060303540d000c0ca88907020b810310240c2015005050027500500403074080d00c240d40d40030001e50403440303602000b1b004803015100148800c0c1c480e18490349403600c00307080802c00d003a89075107042d081d81290b0072080c04117a44445000c41500340d040d2070041c0400c2443c10500c120700c4d00b44060418801e06200904000350782040c1e40e64502c094120004481e40001200d5440800d0b000503001d010341a90300f0710001d01c031142d011405140030040c0328401c5541000c03204040e0203440800004104100707045804407211400040885c3d030030300d40303588100100d4003e10740c1c03946c90300300010140c1001410550004078103414480c001d944000904445810019002412005400c0030b910f540115001c2c80c00c648000420082000140743c0034500031071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 112603678 1250 112602428 112602431
    0xc070f0b1312030c140102040e041101081f06140906040306020405030f0102040b1c1e1a0d0f020105031e150f060306130f0b0306090a0b07093209070c0303 68
    0x342c840c4016403440031054030280c005480d003103183c008074940c0120200400010400186001d54071706e0381030390402084130700740c0c0d0703030078802c0b80c0c41c0804d5800001565001d05c0314880695000303011204120390f074055010368000c11000d10f0910b12a502004112101404020820740e03e172582c0389040f8010f58464020603020313026050030390150110500035503040e00c07961203806007401003991a03142c4030b00315034040b95592500c0b6882001c150360341d441680b501190240300401c2c0c0f40054020040c0e00059420b401d4003442100d01a0804903805a100461540c0e091a000fa80d030348942c550004128801e149010490700d01c0d6082c4442545c2014113074030740d48010b0351144510130501c1e04010701d50008a807081e030001d1010540c00007900ca40d50102000e05401a0300141181c0440082840c1c1a02143c401101d0360216001c0d07001c0c00b22020034168418100d00c0c0519102c1d0404039020b103c81c610a004013442c9001124801880030645509085008082c3c802500c62034805402415052900030980200303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 112604928 1250 112603678 112603717
    0x30221011d100b0f1c05010e07090e040b060d14010b15072103020409020708091e01050a05030a021e03040210090b0a0513050d0b25080601050c070f0b 66
    0x44100c40c600d02c602001000140c8062034915904515440000010b03030720360042041e4210801240440103c0d10845c5400088541c1002042c48091101074001000d105180504100f4005020f624641c05980601e840d6840d880c0d034030104100300403070032000300f0401d1b10f20a070444100056011411003042158490804012501c5d84c0c0580d100d01540a820300c2164216254030244100340009001320628006140c15a5024041d0490708a40402c880324000006e00610030328003244400d039007011a04003480ca480c880b000281581c03141007074010502101000090208403298181c900ea402810905038441100b68070240390381d0301c00c0318224800c1a41d4103c4240f4144550050b01c103803110001114078007804804180c60fa82c0000451f100385421084003c40d050312421031400c8a03501c581d510007501c2c1082d00c403200000d012503186d46d00030501c0c03021041c545980200500c1c5c01010a09199a41e030074881080350411825401140408054140c0007860340c40d488010f02ba004403d034054081c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 112606178 1250 112604928 112604969
    0x81305061809070e030d020705040b27040602090307150225050609060d0c0c03110c030d030207060f050403020606040f09050607140c011a010f030513060b0103022101 73
    0xe40c040c1502080300c20000d200ca0751050b080a048840c0c2080e01070800d003100310f08207000245000308114020006030002c3c0f204100074249400307000c240c0c08045880b2034065a6201c0064064045c0317000801c04401d5800116041c0419541100c440354070107410390300100d403281545260b81e0b119001d07400051140b100c00100600440c80400000048005081c5405180004101c4a81c101d0301075a60300c442c080000b60300607030103031259402124440d1241404003505d8203000d802d41124448645243d00400280420f075039000c2141680c00e402820016150a807900f0a20000c2211400c1512400e15002c01d0206041d00020800c1c4600c100f103809000c40310f05000aa4152a52030400901c0b9900100201d1845405448200203020000060606006200710b0041c2510440d01e04440c08800e41e00620f0045d583c0b01243c880040d0403402c040c002c50034450344207110061745030006804180d03120786028943e803103901201c07401040310f094481c041080c0c0544161124082c4038001c40780c807128010481 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 112607428 1250 112606178 112606189
    0x12050304020f01030b13180b07020703210c15060302040501080309032d070b0403060507030b1e060f0a0909061a03070e0102011401090203040b010b3c07081305 70
    0x11a40c0e0180090b601402c2c41d500540103001c8081d81a58007090f0076180d0104a0120300c00c44034000011030301071110044609026924241c00780c0700340115045003500b030000c15608003401d130403151301c86090440c03c1034030a0115640740c000e190081007521720742c1492210300600d4100d0001c2d2402210200200d903030311350003030303940344100d0400c0b90309900308032000d500701c8400d40c014074020b101d02105c007030f1522280200c80f410400c954014204000e0082001d100b4050b85104403503000c102c60034100f0050220308000f6001c1c06190194440c06c0c0c0303207880c001c1100d8840303034140e8400900c800700c15600c07103d4a01026102001f076000d00346810b860301d500018450800d40045400d036050b03210107031079900c422100b00d410711076070104a4155900c8100d03224441812000e81402040504001030b120b050614104074681c07410791008804000601a00c1001031801001e0590a40081940212045114a0510040c0c0c243d440b0403541c580104500c0b0034401124001c21003880e80d1034007a90120f888008224 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 112608678 1250 112607428 112607431
    0x40306050a0b100e01171305010207030203180904020108010521011d0f0312010b0310080a080705100c0e04020d06050301050916060203040f051507140319090e1506070f060603120503 80
    0x117001600b940ba008104412520460760004146802e0052440181c0c0303405003a6440b0702d50840042c0c0c000102060b40040700080c60031040d40881d9111800e04058000038500c1c001070140621030b8080b105801c00c03466408468407540e0840300002d0140381446520104040c2c0b96401c141514040c880020f0780b40d03d000b00454092900800d1a4100c60f424009403030140d820042510103800307400140403a94070420450510040c1c0714040e4103540c0d4200b0f28000e82400003114081900504003200300b41d1f195000007503180030403001e950047e19504a0b40f2690f003c3c101075801103405500c0d01c001c1c050b90040c04035001c01e0246505868070740e02541c0b510101c0c0e5a00c1617102e40101d0050002d000d002a00d40842011080540b1281140c14014036845031140210b0545030f448242e4000541900d503180160003031510030415080c2503a0843c900304410103404401422800010a88002443c0079900e081c161588650050004442d07070700c80346015801040c80c0d0200742c40e010f50310805084050300c41c03003c59 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 112609928 1250 112608678 112608707
    0x2030c0f070c0b0f0403031d03060105060d0f0603110321090f010e060a0c0204050c0403110d1a040807030305060406260102091302131707030308060303040306050a0b10 74
    0x680c68480c10040c100d0041c1c0000c0d008540c2500951000600800900702500300c0e5a00c00c16210b0fa668a9407030054065840340c2c03560200d48100590949903680c2c08580320f411600c003a500141d4656110302540014001c040d450f032403491500d0008010700c04041658440410b0640403101500c6502018141c9640b070034941654040040260050f1820314a19140004406050200c0d03115200340000b0800cae04100ca01c000014000e00ba90403c0d413405002d41c0d41c0081e20380041c1e618040c29078031605006512042d1144c098880e626603442004184000a4044220309864001c00c1c241440d0005495000e000d040c0c000038100000310380c5a103054460781e002c42e0304505c0801c0400b61500d103841038003110340b42c030a60f1556081c07121484a8850703101022409068043c0180da5147c80c4810051560644c1c100d00000103085801050341e550020300b82003034035003500b085e1a13aa82e6040009155118079000245400d080c81c045c04201c2030b458000c024507003011242020300e003e248100311017686551406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 112611178 1250 112609928 112609951
    0x90a0f0e0c070b13020409060e030702010905040203090c010302070f050f0d02060901060b0703210203100807091a0d0f150902030616091a04120302151803070b0a140114030f010203 79
    0x7051301600c00d6481c0e80961440900045900e04c0c0d02d856034412105400102241ea4200044c40011503911052050140100311011411810a041c0d0f0310baa41980d5036100b410302d41e0001d004000d010103d8801030540e9400412035480b4240c100e101c07502d07004003980344005441000c0105502c810180544000e596090b140c807030404040b910b0460345012100380001e11255410007116a203500d80c001940700d8403550f150400680e280403030b29841c4c1442980070415952900950798400c25030007a00c200642400c890920030076210303042a11660384a1030008220100bc0c00c001c50604c6269000b85d12000c0c0201c0c107491850fa2194001307d1100c40c1112907600088801c0c41c103211202142440840e100c444d2888a03003440d40701c1c1119201403461080a801580c003001c1e0850511528480060380140d901d0f803040c2d03001c0034411006959016041c002840007507480c00140d01001c065002d640450204484e03882179503034920312550100c0c00642020301a014142c01c0f09800306050084038043c0059041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 112612428 1250 112611178 112611181
    0x1a04030201021c050d05070809150c030406151e0504051602060610030b15041a0f090d0201030906090b060a0b0a0801140d08040b090a0512060a050c090a0f0e0c070b 72
    0x2011204202410007003810f00c803051000c1c07000f4180391b100b00342c4600000e0312255070905016207418030713001d02c9411361014443d608042148a2002c0019280c01541c08480030452680b10415002c11a5240c0c10062442a850016045107040c5400c00c004840094a042004e51a1010b204020410b0460004007583c00326000c9029801d0100c0451120744491400141d20580080051100003000b00f004421040c00306040c003090354101031805030741000c05000391804040188100150107201010f9100303a210303803980c0c801d59010340c201c0700070f280d44501c1c108925511403520001003842030716128021408004003003601c8402c94101d030050700468035080c01036868424900042c6220203090ba0308404c0208a160000324a00058000b40084c0281c0c117885000c440c1c2408030644841d40128840d003502c7c612910ba5040c041741090f0410318407030380480d440d034452104000602c9601c615030b0308003040e01c000045000358100d000c0103131928a5811041c83e2115041e204440c00fa8802c003401c0c0b10f01100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 112613678 1250 112612428 112612453
    0x31409011d060c0118050c010305060112050403030b09090d1818020306060c0312040501150b0301030602130f06110c06030915190f09050607020a050d05070f020604080102041a0403020102 82
    0x42001c003101802071440d490840d034001c52600b034403003208201d242113460006590400c10203000b0541030820038a010002c03840c14030002040c0e41841d00401c139020380e8400104040c148a17401034400248064041000d5003410504950355030004850304e0000340028600103070303c0700300011300340868820103a0060715240c00310310240213510103130080d0390220040040214581042c03014048424990010907428030701403d100b070075140091a02460460030110a016159003207041c0e0b4150ba40084006890b580348603d280300301c0b2590b40003e80c0485d4650000102c8982c84800110303042900c20907140c4541c100c40c1449840e000550320302c0c60329004030148078401d000000005500607a420034005181d0110386600040380d11401318440095240d0b5074010034800300f000401d420140e14030082144001d281c613555160b03241400c0020800900040040902013103070b00c214407850f002003c1c2030b951076403880c0c02c82c001c1d40207200c0c60038a80e48020b03030030610501303000c1030b00c1c1200d8042e0064402c100094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 112614928 1250 112613678 112613717
    0x71815081e010e06100509010e0c0d0207030c150501140d11010c03021005090102040905010509040f1b0b0f0c07050d0809060901110607030c0201050603210a0507080a020a03140901 79
    0x81c00341035075031a07a034200940d8003007210358000c0c2007444428429070b003003505200d41200160090598145503106004e080052001280c88802896000580ba102d242c075003181c0c052102d0b8006000c44002070700d0710b001905160310140c1242c2101c41104421b1280e0f4060000440c10810302402c901505444030f5915405143c0c009681c520910640c2c95111188112108035601591011034580d4046410300002e085441080d000d4042140d45041c14600355031030b0118880702001c0100b441010405541c1d0350404441d02c1005031014042d01038884a451400c050280c100d48801d168911034030034005003509140b0b03400040075400c0010286040760140620550b64001030380726040042031000c502c03841605114860140a40b950080b841c0d008043e002400d4400c050003081c466006400d455140b65000d1507190b40c00100c10150f40d803601618441600e032030060381005810705800140c030107003080d808500c3c1070381c00d803082e19404030947d030007200c5021a005901f4000d0200c0e0805050b0400035424 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 112616178 1250 112614928 112614973
    0x150f0702010e0709241206050c0403020d02040b01050f0f09030c0a0e1b0d060303120f11070215120709080d0206041709150c010f06080a05031c020c07181508 69
    0xf4401201080700349136051103801a17a4011703850a51416035980402000b1301403250800382d276210f07060905086400060b500360304040300911031f640d80ca08640300750740510700307503242a00144881c603100d00b06441c00d40625844074050364440e020740c0e40020203d1034600c80030020b45541c0e20780b600c400d80e142c000d40741903100804201c40d42980e0a00103031301800d40e18080c03d40690b1090b6905056001350303021010a40701c4007805203000138240f07940c01c01d1003840e00d8162102e690701103a910385035136520220080d2910400200c0280d89040004011040c0d40104000c001c4602031000c8a03440d41441508985920003580c00510313100490342c401501c032601c03002611610100800c92900c0b800104540c1980364010070302100f40e0303510b9040106000740607120300d000a282c65006002e40e0000390342d0381d540f0707441032911321007000051202c06140b6001a80c10f41c2c1d2030010480c1201c0b815a290508243d803002a5605403d426013404c3d903504442c0614100802220282e0004064000004100c18041c008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 112617428 1250 112616178 112616201
    0x620060c030c0c2508300a030f050c04061205040507030f02030f011401051513051c0602030f040204050603010209240c031c0b0319060914150f0702010e0709 69
    0x1d03a50503c458002210045018076a4902411000900d015400b80c14007070803c3d02c02c84100e4080b080d02460480c640f00c080e4042c4043c2d1b5216580e1061210305500429036502a501014644003c00c080381000788001c2040e02d01c41d4441603900c982c008454000c2d210101c4009026030004001080000c0c0070403032142d1800e10040940d41e40c0b0720240c4a49003102e0524450918171044180104036a05021840100c4d44811601e4241703048400c0f030030804042c06c68070031180101113001c042c1d40c1044101241c03c10f601d500040c195078034101840352380c00766403090714107030310480c40e000102d0b110749014030881e103204c04050304948070230f05000c01c41c059003074004808800c050402c20085550500a100a05810407803c10310880150300b0301c1010116441c0101a9002c4d60100e041d0807a61000a000618201d9020a001c25052001e00c1d02a20000d00b081180700103200c5c0b040c0043d440061800f0491040c0c403030b920300d449240d503221000c80c09c1e80c43c1c41c4c00004507074105050034850390b5000e8004030345940 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 112618678 1250 112617428 112617433
    0x60f090f0109030501050703060501030e0c01022a1206041104140402090a1116170a050409020913020c210a0e010c020604050909160f0b0319060f0620060c030c0c 71
    0x30303684d4945500b55501121400c0c0013965420b418086036070140700703001c4208000c40061111341c1c10709001075551a9102420034484100e80080244031381c10000082c06041d02030b01060310340344040b88503a5070740e6043d2000c48040782040f86d00102400c203480f403119203881240c9a8500354449400f444060701d00503040e41001074580081f1404800c8031001002c0a182800551030b5000d0740d410000352441ea50300002200040802199135242d5028049e10141d03081410010b80c0c4045500c00240380a0303c1c90140c200140c0045001304100002041311110420030400e0051b4a007862080a00301c3e2040b04200008035074a0418691503520404550103540d1000e8000d038505604c450024424070400c44060402d64055a0385404031a1032046240060901100c2c030803541d8104030000b1080d0000800030090364480559440320705071960000c90042100703222841a4903203903d4002e1030300445083d040007002c4400c1400c48480c8000030328a1017a5500c4000500395102c07058681710b00e0348040d0300f56400b403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 112619928 1250 112618678 112618697
    0x1d0d0209010b040602010b03030c0607080c0702090103080903011a011d12010501030c05010f02010605090c03091e01020c1605030a020d02130c0203030613050402030d081803040b0703020606060f090f01 88
    0x16140e41800d58040c1c000e0030300040d22503290410080c02d55981900c803602030303081881505106c1100150640e009141420450030035580e20351004854008e43c0d201a50000200e800003050083d04070003421a0a001d900910041244ca00d512483c0001c1004560000e00304035038500082140d02518120000010006036096a520704580d00b542d8080c1c00c1030300e25100b417100c10041981c01c00c85059400348103000030b100040c0f500d400180d018030020000100f0320800000561700c140d0610900310180c641ca9144c4d50149807201c0c1c414000d4015640c009447e115640f14000541000d011120031034100400500c06054076500b4000350a070302c000c040341c03c5940300c500700d4130320407180c06805c402040c40e0340150b0722440d10408000040003a0482e06002c1841c1400307103c003585000c40c08103252982030030485c98036100e485907240f40ba1a28944550f550001090200304480707031000500216010750708451054031200c040006501c504554804155820400e00d4407500b421000400184014101418035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 112621178 1250 112619928 112619933
    0x10603050f0c21060c0d09020d03080f07031e090c030c031a0a050601020a0609110a030302030904140f010603090201020115030b06040f1a090402040612030207150305071d0d 76
    0x380400d40d40386100c0c5801400100202e8100806440744240e02082d1803040101d02c20509030725540d0241445c045150001203461002e00e098000081c0290b001d030040602052506000741090000d4882c0040ca001701c0000c568150300c00e001b1401c082c3d4029a0b81c001c0e8130302c1c03480240c0060071451401c40383d00440c100c0000200b4082001c55004600655000e00d4a08224481e4400352100410491103180b0745414800340780d0380090105001a40300600141d184128200307001480700660941c0d501c070100d580040308266020016060300b83d000d071010311100c0d80240202a260404490078082c04003c8401000064440e03044034202c24018000012a0400804000100d08031900192017442000061124600746480b880b41c0206004004020fa00e80500c2c00840b402006141c0b20b11400c5408042001d4fd03503154411401003043c1070b500d00c00a43d8501d40a9184c411034442e03041070411703c40d240c1071f40754002d001d0b80c5d1080401d56607404013680701001413201000410038181e000f04074034041800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 112622428 1250 112621178 112621183
    0x6060a0c0c0e071205090a0b01030b0402040b03010606030204140a140105030c0c01020406081501210e030d02030a05041202151303030e0607030218013905060f0604050f16030c0201060305 82
    0x8148581d69041c2201101c004c0405590015103a02682c0c2e00040802c03000c42c0901030081e041d00d0b07100c0f910015984841c00001c018090500069a0552900600054140d010750042c000c0341d44800700b0745201100c0034200400011903118081141c0100c2d4511401c070742c4a40001c55100a220454a04201e42200305500b2a00207030071517404600084244400c000c0a40c0707005a111009280420340044501e401481d06400a081148241d840300403a10401c0d20a00565041140044c400c644038a88042000d01400040c1c0d81912003140d00c040652040d4030205118901c0d210301d10340b5240c1602d1300039440d54180100601502003540d03900041e041e000d81400100d026246598000d80c5644000ba030f8000340c44030421030310707061142488200c8940c105841a01c0e0381a0f00111220200105188290541c030303120764001082405800200140321104100040c00307150203a40401c010341e0307400c20200ca0801c094600c000591485192250114070942020040850754400400e150b070341c9564403071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 112623678 1250 112622428 112622431
    0x1c0207051f2d020606011202071205030c04030b0c0a0e15070b060a26100c120c02151e01050108150d110d03030501030611070206040b030705130905060306010e06060a0c0c0e 76
    0x42c0140c00881c10300009680c480f0390b50301d0f54805404110702e44860380c0e40d07210070140082044400d01902000145180d240300d81950021034200440b844240360042c4160401d6009030404004500d10840100b41800c10f50b1511801d841d8034071400786021070944980002c1c0d10010981e07076210541c1c8101040c4808400d1251030320381c50f0a0070444020203440002412e00c0b070714860500100e0703d030090f40c10b18241c0c02035030300c10343c900740c80000034a9140f141c1c000c034104258010610082810303501031142c1d8481c2d08583c160700718901d0a441c95540d07221001124000c00a460300c0300c0d00c00a80f14000354524020540d080003c0c07142c08004201c818407400b103a0340703203500441540407941d80c030010401e010b5103004114044640145d05460f080d4140d001900714000da011f180044400030000401d00b074011030441d01065030309103084204c0b90780d505550007d8603080354403600a004120000030380c01c07070b000e100034001c11005203076504160303000d401150702401c1c824080d82c6c081c518000020b1116080010a1f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 112624928 1250 112623678 112623767
    0x71707020d0302010507030e0615010c1502031f060905090f090a050d020a0b131e050312010906080f06041e0201030b040906020712020a0b070e01020c031c0207051f 72
    0x1040340d146c0164040d08403102e20039a0405504000100039417a41103143c00c038501035003402d0030074080c030305420210740d010060351504107031520010521100b01044e4004950301400f561142a03074a0701d6540c1151001c0c1c03039110300b0707420428104c0071680740c22030b40c801564882e04034804c4800b07454081d2580c5140040410300c540141c0c00c842d0988040c0908040196408000300160f6070303480d0342c541d0315003658010903040c03c4c1ca540b01010026081010920480d00001c0059404050650b10354a4090040100c0c0c400c4e00e50340e1054a01d056002000480c03154440d94103d042c8030f0702480787d845174001d50f06c0300c12030481c105075580c5200607944d6154401e146519000c0d03a40161500840c1c58a49810441d24084105560111819000184a10400701c4c1e100005143c480000313400074005078900800d13080c803168940200d282814144175064296141c80300c8a03821242016076984c00c0c0a0200c1c0b9024001038281500d00e00d4021103400f40000e046036801207038001c20440c91000c81100d6050403507104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 112626178 1250 112624928 112624931
    0xa030909060b0405060414011232070e1306080a0b0a0b0d0506071d100804050705010e1503090c1201020d060b0a0509150d0e0304090509070506071707020d030201 71
    0x60040030414030400c0003816030861030501e807a0801c0300080940c011803207025180000000022103907403041c48070400394030600d42e05010b50b542d03018181c054501e81c07000c81c101880000808403c000d200e0070105000d40541d4640f06011084030013402a5a030f000c016000c04a91078580000e9040401c015045420f8090841907a0390f051140280c01501e0026040510820318071000f000490b1b00411195044191420465203c002e8108404007141a01c80080c2c0c0c0803403c41c141140158010b54910320031480344060f902510784410041d111101c48001e02e907001802084d280031b40d04403c4000316040f0705e140080341c12504000000440020b18111a0145650089450075907034841c1d00400c0090404084028105004400010280c0c02503001c00c81c824440c0007002030240501d1001c5420352420382400744815568101843d503254800d215000c0700d1391800e0000359580034042a00c006842c1d004000900e0700606031038001c40b80f0308000d50340c058040100700700b00040ea50f12050b02d03986403180c4c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 112627428 1250 112626178 112626197
    0xb0d2906010e0d030320090a051005030c030405011104091505090106020a03110f070b0a14070213020304060b131a0d0b0c0a0315090e15040b0703021608030106020a120507080301150201020c0a03 85
    0x180941d01c02355a100d9030003408031050b0000001c0e040780903243d001c6116402c250312a5164204240500303952180d4042d040ca0000300403440f800d030340e00540d0001203050080e02400d03a48106000f1489824421800160010507580c8006485060420a03080c0d0360720844c7e0b030040000c030101d428058203920140d004000001c41303a906640051411050341d256080707039814410359402040000f0200032412112550002c0000e0070000264040e901061001c1d10742e611030310741802c42d80020314165400d1507281e040d503e0003034242d113801c428048100e50300140e00005a00c9820b90242c107a04942c0c82c40e0103050f111000418040f1003c40900024280310b103020030201202ca00241c10000264a81040440300c1020400811940b00c82e450b044403c602c0c005031748004100e0389541000c046080248101000000040ea06d503000800603a028022032122181c100703100d5059409200b004402400300105000411000145c01d03d040c1c180c1d0300c030340000752808041c41c42c06400c1c0b07080340c101103021500259 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 112628678 1250 112627428 112627447
    0x106060f02100219140d09110307050402070f02040b120303070906081617060109050915181005150403051615020102040503071203030b0d2906010e0d030320 69
    0x48561800002ca1100f14606415610898000640311019200344509480b242c551401c0d5682110f02d0b482c02c0c00020480c022140c908400d10040c4c10610310302c03d1150708808a41c601e020b02c21170b480150301c520304444500392030b070a10004d088450303e4281e0041240c0300e818010003090004501c9610035039500310895052010103411100050503141115441c4c00c162000107410090f980c56402042d900782162741c0d40c20740100da42c20700300d411882d0080300c144140080c1020140d901c0100010440c1d11408840000b440c6030b10f1007008899811035941d605070100618145000d0070540201400c0180741380036141d0319510315140741d4100c03a52410192400c100400d0201c19110006000c0c01c3c0b009500d407a00d403100081d03030f40d121030203490865802c0103041c0342014000d6106200620740641000d1000310300341000d00b006c0c2032110b2000794010f4030f00003207130f81c00034408401841440d0584078051207007442018080005040d00044050580d951401c0003462500403c404c500c180700da040c55503a02020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 112629928 1250 112628678 112628683
    0x4060b10090e0417090301021b060f060108040f030c0b0403020d02010605121b0a03020d030c03020d03020403120f1403090f070510020c06070f0206040f090e0703020306011a0c0106060f02 82
    0x151010401c010303180c982840380d4004503031516000741c1c0048120b900000c10038501c40c0644100105264590b100042d020381450000e205501c884034201d040d18456034034184131200448007100d81d0340c0029500000070740095061461140140c0c024a0f14502803d010307910501102d009071001d5015a0000d070601c12141c0e424000d50014080c260340d1003a07000c40381182d00390b94214000d10500d941742c058841011300c6e15000280c000664000300018203442d01070402405880d107600c01a4014011a54803041642c024001c032004c072039100d4038000c00d950340c0c07d0b412140d03407686860700f104019a8040c502001c20000c0c003c3d41c055219800642503080c1502c00140c60071005c0e40c000d0740200100c1c0507842e502078003c00c1984034400259201983c80d8541d10b811551600d083c1002944000045004202548044c030b044080d50405202082000740d00e90540d6581c4a651100940c50351200005100043e8802c0010045078400061035092400f00702925094071001d40000d800200710040c41c0c54240e604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 112631178 1250 112629928 112629949
    0x100507020f030f0c040f0e030a0504170a02010903030f021f0501080d0804050a02040e0a0506010603050105040b030a0f02040f0b040e010506010f0906080705030c0f16020f01030c120e0c030604060b 86
    0x110014000290041186a02c0d9004059480c4c400c1da40c4498603591881b107a0400003c0b0084081505e5a46020080140442c1c2290280b0b6071090000a406c101ca001300190071000399030140c40e00c160041c510b65044072898581480c050443c0100ba036213041c015020514030408060750040414158104003800d0301d001e03502143c100030000c1c03250600004c900042920301060b5016680400d00f400b5101c0704c1c520345440e02c0801400b5204100001800039819400281038600843d01441020000320402d9683d10040c400902101c0f80b0f90200d100500e4258005e180d42c0c81304001c0071403c0200700c4000b8044980c2580b20710b8031030b5141c1040040039a0b02c544e425110386000d083c2024801c0c28010010402800202004d040c440000013068801e0461001d8420781300850003000c0c1d960303441d0304d0000e81c0710001130400c07405511301c91180d2203207600902400c00310700171076a101a0014802040c10019044c0044840d2450080344407244a40d00c003480040d200c4c5000303540c0410030450000500c11040c40703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 112632428 1250 112631178 112631209
    0x1e151215060f01050301050d140d020f060c070302030d0b0a08010c050403060c0c08030f0702030f0c010e061006120b06040e01060206181204030201080402030c0405010f03031205060d15020910050702 87
    0x1c0d02e0340580b07480c0e13044000c0c1c0e4107644081d12100380c003401502c0d000c100110361030109001c41c4103100180c2c84484c0c0c009900c4410840900a64103a5100d80e0703a402d0080c0200780300100960001d102038400c0070903543c0000c480c0d41340100140b000307981e04d0074990b003154419005500004c0f4001814424031106000b50201101340b45414000c00e0701c26111851240009446011420a0b26001c10016442007054030446082c0c4607085903100040000280201120200040d25019490000300f0002011a11000300c50903911002240c01405640c50018800c8078003a59200c64180008503015a00711007841c060151340d0014085810220718410243c054000303a031041d980034444407140305400c801aa021254282042141a110fa02c0000c1c02c20704160011500b01e4a058000610281e00c17000f100d044034000c2d160600c11031601c034910020fa034001c8030496001507500004d02c2c0018a040181098100400390060406001000041c150000300c1500400510003103034200c158945a826035910fa00d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 112633678 1250 112632428 112632439
    0x10e060f0108070303050304030207030219031a06010206160c0b040302010b0a090b01051206120a080d150e0f0c0408030406120b04051b0d18080d05010e1e15121506 72
    0x10b01d480300c041c1c0c0c2c0c0e01080c00000c0801030017101040401d8000c100780c8002e143c0c020500c04014401c200301c0300c1d003c5581d10040d5050800390700315014030500c001c03e140c091441a030140c100c9aa900c2e45a0001401c24a100c8080040182d0a600801d48107041c40380510321030760000c1803100f500b104110840d802ca82000d080c00d072038050013220580e000800c507201c0c2c40900410402c6603548c0c5001980b10202c019401440f0f0113800d441e130003042001c1e0018600106038580401c40d04512405000d034007103190284050032103030078001c22007500c800780c1d0b030325800240301c40142d00e01030326001032074150740280d070120b03011401c2c4d580103900c4a01980035040bc03100c0255000c0205141010700e09903a01d520b5080a5080b5100055041008a064020596036080b0b100030a200c1041032a00340b0701b0b41e00c5106811102443c3c4000818065100e035000c90080504206804441900171008020400040d00c01c900001401100c550b00c3c2d119a070340810150182c40c098400303a100540c482000c248000c16951040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 112634928 1250 112633678 112633681
    0x80d02030609060a1d0a022101081204081002070602092706040c0e010807021204080705040f020c0601030308060f041103040213020f041403011503140c01050414061303080c010e060f 80
    0x61200412501c0d94419a0340d4144e0113071180346e8203100034402c0004500c09840e00340807101c81e0001e034080080c100c4201008071030782102c5010501205018600515410b9080b0181101680c0802d0300078180e1785010b2800180f800d042480064003075002c14005908181e003c400c14920404074161081d800042a034040c06513103a0204005e021445110f0118140308141010404492003040701248054200682ca40d5450300d4007001d6139220341ca8424180329500704942c0c00e9140c41d490003a280c105000380004e100d541d0039540d0640311604000c16150300284500d020010595450090b0000c2031a50801c40343d803400c050040c44a0326119003030164005004200c2254800545401c580854940303204566690389410000b90143c048980d080a12102414020081c1f00c80c0c0c3c41c1040340241000d0032030b50240018001551580114440c0c030700e403440e01907542e0090b03040850092800c054840c000c1000315442c0c5e59a8842500110510340b56a90b4030288103516102c2040501d8100c20002528000e5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 112636178 1250 112634928 112634939
    0xf010b0301020304030f0f0e09011d01080d140a0e18010603180519060207061103091b0f0f0d0b04080901110f030d20040612060509070c0209060d080d02030609060a 72
    0x2041b000d60b41d000030400c148101566851041c0c42e000035002c0010182c060707030759440040310b444038920b841400c1c070090312200020b40c1020020f003116089081c2d4a41001040e00341c1f03003004144e008022054140469001c55600070343d600030b0500c0040301418007000b082e50408000504442a04090070104510b505107100132800c0002c144202c0c08018580c00c840001610b00b40010707004c0c260000308114104007071450503150410195108002c120700f22520148100ea07040e00c000340c1d80d0300c1d07141c200f0900b000e054024101000b1804150310060048003880459590f0510241000c4505a648650102d104a0381d907030b000300400a01e4956100411a01c1d002d8140151284202507500140582c1c070300481e510036095814030390030304807203207201a1515038071680070302a090700c80302c2540c3c8145428008102c9240c0303080c8003170040c102035450405030112542400400800a440d1903445000f03c1f180800080c010002030202c8080c0f0340d03000d0f841e41400d1050041680c00074000c644100650841840f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 112637428 1250 112636178 112636187
    0x120b0a0302060901121a010807090f0b0304020109080a0b06190305030301050607020406080a030503010905010609120f0501061511010b0319110f060f0703020c06040f12080f07050f010b030102030403 87
    0x180c0781c040320070036654184000140c88102020022040f81c0782014011a01905845111004040280c03213484603a0b8940808403a2484140a02e21116032069820301402c0c0c40c0e04051350f8480d1060401c82a0135440e018074900d001c0d1996012a490003c0c6400c012032410130b15200000205118048860541555182078503800140200d40c040c40b80851042c00b07569407a042040144208802e9803107050180c00d00030003075030090165410300340c03c0000001e2054072401440040322800114400311440d2a65210b600d80c0940d10151400d40d265980440c4800110b210449e16000585900d0214a0074a44c09801c0d102c0744541d4a1094000b041510780711915082c2c01c00d80f450348186103502000d00940081c540c107440322030140d04542c01180146a01e40c0c84402440c155019800b12521000240d04015051289001c0e203128048080c03003c100356201a6540000c143c410000b01c0d0811103091500c0c0404e40022200f40c482e640000f107044040c1d2400c0c4500440300009400035403a520b02904c0141 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 112638678 1250 112637428 112637449
    0x3110a080c0a0302011b0c060c0b070f20100606020a1103150609220807060b030a0210030213080d09031703040308060f010e0409030f0e1903061104180c120b 69
    0x906010b242c20484503540f43e09040300018a0b07100710b035490f00644508c801080c1c81c1c4141c1084500081c8034000c5001c50340202c141e4550a00c0360354400d52074066030b140d07040e04006581441c4003a8440c00c0a864070032130844c060030024043d6030b0300a204041d402d0524002406400100c180207420145d454180c82d03405400c070b02e41c00001640d1a0205803540d451041850201d92000d003981422040404108498040100078150085009006d08001c440070551156080c40d8025480200c041c5004091070103500500310329502e0640f45050555034030605404e140e100003001c000030707101031028010000b41c1c1c2e0a030f401c0e00e18401486401c501e480d9070041c00c240000f404052046010704000313049684101c010100e2980c01500c1480b40c11250314024006485c5101c50314007150307a05007004150b05003d90141452030180102060036071070b40c1c0301c800040000101d071070240b11040102191109006031550b0504c1c4aa43c4000707558002814000d00742007071220b4403c1500d040c0340e03101e10310780d0328100d411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 112639928 1250 112638678 112638683
    0x21050915070215040b040330050618090303040b07080c031b09060d050114040e0307060f1116030e061c054201030b06030a0c0905060403110a080c0a03 66
    0x480c03064662040a03071400703d524840f884004100800c01081190700011240950302c2070b11402183c050940c000d1300e45210340c4c2c5030201042c0202440310035161281d0040d540001e00545400e0906450004c3c130b58440304200c41c200d10702c0d0300000a100030024410107042c1d012800e458045201d0601d035040228a00c405401015000c80c25003103000900d03a088101d0340100c1000309000d43c6c410006200300d026000900c075815060500006401060406005107030275000414080c500e0010340395104002481460b0300303100b010b80c2d15111034401d003107440b004000e800611000305110f18540e24004000c0e00c10403a4043c043e890502030040d001080000b00c4150a40c11b0741c0100c0d4941c0c0d42c01a00303074003410f0101d941c2d641880c11005904119074030f407108000e001480f460251100b4142005406036031100980742d070004410800505521016070000701c80300007500e01050034695503000580e003500950000d0354000c81200145010703107010750038070300144075060180c0491119580091000541844007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 112641178 1250 112639928 112639963
    0x20913050304090204080d030b1c2301060e0f07020c0a26030406030207020405100e010e07050408030d061d01150f020705130b030d0503190902010507050607210509 72
    0x42400c00c0300c10300990300940008401151290340c0c4403c142d66800690403c1341c00302e440c01945008500301000031002505e0790540c2524005007960b1007502600c2c40c0e02d031190070002045018007000c0002c1c00364400804860780e140c1b12500700042c40850710003010380759030295482818580d070540c40c3c6407101e1048801d2a101e01071700208010104a1901c0204607001035030000150104030740d5010740c094200d280c000d8408001507902c190004030300700c115001c4e01030504a11001040096010765503594003030000e00d4000d0502d507446d05c030240795810034440725004649803502400040700c4a0050208034a0441c00304900e945400800c02c2543c6035105000100001050081c0c00d490080003070000034100605030034000d4015800410081c00751480c0c5070720902614031803c02880c4180141c0c0d015001200e80c1001d442320f142d86140043c1800d00e402c0b810302c60b0034043d00004c9181071020520450782d07602c1e120750340034040004200c0110300c102c0f80c58410b071400051020300140022409040880b000c1c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 112642428 1250 112641178 112641211
    0x2060a020d0b09010807060f0201020f041e08010903050304060e030304030c030315080601030b0f06120d23070b250905090903090607050309030106090c02030a1808010f1b0c0209 78
    0xc801d00600b0080400541060188000007201e200000f18002240c001c0da41d9a106007a82d0761049080c2c3c82103844008008908bc0000c1c042d0b64402d0002220005c54412895002a501e448441c00e441d55844182d022800100c104018410b4030300031300d4206e05006016524601d0656805440e001c41c002c6c019042582d5140740820310721444041c00050b020b031000316085903035246031441e0710072411240c0c05041070000020034803e05000c86000d18408040d170241200040d1740314100c1e41e050481d482c0200c11100d0724400110201c0003c0244100303802500500e41c50319000c0d910308600888142a501d03d040400741c10800b89030301840c40d1003928011140102151038140501d031a41c0543d03902180c0c03103400019a04200034001000b400760b010306030020b01000b90b84136000350071600f40c0390075940542c00c03c0102c000d1644c428205240d000e6605002c10000341d4460790aa8211816060310715240b50303681801880501034038289501d140494900a19a40b0709540401c1ca48800500f035000701c40751201e07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 112643678 1250 112642428 112642447
    0x80604120c1e060b0a0306050907240c030302040b031806010e070c02041a040e030706110403122001060b0409110405030d0c060e060a0501051003060b040b0d0204050406120308150102060a02 83
    0x401c41d004040c401172400364651b8070390401c14003d0200756a25920f0b441050400100b40d44a8032041d1008444103810b000001c48200c0c0c05d552070102c0f0802101056802c11010070703401a610040c40c000c041c107039598440f0a1a5213280c0d4a880410382022407403034452000c000300543e1002c141000c0503419540824040421880105035542d210f1406034481c0c00c005a101210f400000a0007049005120601014581407001d800501c200c0c00081c00b07151074a01c10034a414028440d81146511110303c10030032540d0340a0081c210f8010b40c209424814000400300002039442c0610b0f0307910390780c100b40e03e813805140200080c2d640001e8542e000520040c6d2900605110550b030000c0c402461940a80360301e45810082d84009060901420348103900d82d03020641741078443c1c0f241400342c03007182d00c80503e0603082c040f40a00503008002104440c40c0c00b0000402c1c69102c41c01014000e0284038200307500b039030b0b1074500a45038070030041c940101000030003010740c4540c0e8009a1150000c00d607040040e582d00400c0d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 112644928 1250 112643678 112643681
    0xc07020a030f08091c0209240a060503070f140415021603050106030c15020d0e0303041d06030105010b0a0806010804020a0503030304050706020118020108010e1f080604120c1e06 78
    0x640c40544001d007004100c900f40f0080780c000700440705044940300f0b45c3e0302e0901da001d5644103900d00040d40281d580e80c009224000c840c607540381c20111003452024100d828000042c1d0110a542201c1d001a4021060101d2030b5000f034030400c1c402c0340d01c1c1040c4541c0c6a0054204c01140030f140300e101c24007113500c00c540303400303900078082e1320010350300d401d6009415512810294041e2605100490305c4c40d460f5040055441102c010901c0945030a0340501590020f100c0d0488007501590480c941c1400104000101064047d901c0d600c100c00c158132050141c9801404c050031581e05078041c101d552000c00604909a60014003503a01000034241107081d91a1400410481c81440d0000c40d01440000244028008001040c80403110740c0c1e40213101c500e40d5001013240004101c100203001c100200014000e02010b410075503408000b41100701c0c03100381d00c81107510080c825540546100d4024900344414042229104041c0b460b2a09280f082c1d00070503074903400f40440d0f804401031400d03048070700c440401509 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 112646178 1250 112644928 112644949
    0x7120b0403030e1207020f090c1c020c0f0703050f030f1b010207020409030513050118060804020609030703031806080f0a020306030c0405070201020a08012309090106081f0518060c0702 81
    0x3c010844224030191902e890752940b180d1302c02d0f4814895034039590168904100aa03128403541c014090501d07135040d9052030401c40046c0d9880c0f2042e024402000c5018080009c1c88a0782c064100401d20545142022170400d403012808001641003040700b00d84c1c5411107c02c80341588454540810b041c400c0c00c4515009004d503c800944c01402c003c00c04084c10380c014094180031815141c01c0036101e41e20710054820205030104040c140c80412020440b40713010700d550030b602600240c003251420004c076000908007959608114082502c0307651420400000d0403907040a01103501707107040941000403506a03a400010900c920160700000080c0403038400703010382260350344c0160041c005400d040e82d000c0c3c045e400c21211000041c180c28000100e81c11480781d90309614030310400f888000b42c18441030109131030004000042c0c641d220940015504010460b12007901011512144905010b48481c419500050542c04010710701e294510640c0d44e010800716040254400301035039641c49072002c00e803840170 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 112647428 1250 112646178 112646201
    0x31704052d16051c0c090608010204080d080c031b0c06040302100e0307110607030917010b01031a150c0106031a04060e070e0f06061c0e0f07120b040303 67
    0x2041241c0c1480718200010301501c0340400c05540900300c400e007001c2c0c014a141e02c00c242c2d003c0451034440394044686105128014003ca80c2031507482e40b41c0305240c0c2911038503400210569400102046889403d025a05c403140862030f1600a1b428044e42d008480d000180a0524400e803080302c0e100d800103242c084540b4490300000360365803840c041c01d029440341c0c003d407000700c096420300606620284010080703c20007644003120200842400c8203224603504228412001d10090040205030030002001803442081d0b00d800100d00940002d0005060301e403a102c101864003056941c81c03d4503580c2031b18200200611008403078890110300d84850242901d94405012006e406681009441c85002301a120354010300341444104071103003616540c7e5483e0300c6901400301a110100c0d000b04000001d0541041000341094106030264040a036440c160501e03082541d503030360402200c60042030020030040b810311806840000d14141c103c100c8600d81240003050080002c0016082600070fa010300741011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 112648678 1250 112647428 112647463
    0xb06010c050d0909051305100515030a050714090c0a111c0c020306010602030f0414060715050609011a0d050a020d0e070801110f04210203010f0f110703170405 70
    0x14514078090301d07403a504c2c001c8800150801c4005201c44080211406041c3d038410003c068801421a500340106030107401c1280c40340c4844911102035804200d00304440380540301412616180c420368411141140f0301180c004c80d1b0346000c003d00f2155402c2669041191420101c4444501c0c040c031909201044030200c03d40501d6440000030310390310000301c0307000d18401c2c0c0440b4943d0340c0702e240c2070382d5900990008104d0200c04110034000ca131048020240541400740c442801d240080d51480640c120807070502d5510342e52241000220f01d4030030350490040503030600d050024010381c10801440d10440150580d401d485402143c45240194101d907881e0301c8001d010880d00340d01007100c0303444100c0c0d40304104566003443e03009025507034407804a0380c1c440d5101918a142929099100d00c110a580340106c00002401d00d00070051b86080c003030151124003207100000c142c0b00891015085a444081c8903078034407418030010300041d800800400c595910070b54007030415520351800500c2c0c0b504c04070700e011810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 112649928 1250 112648678 112648693
    0x20c04020c0c010e09060619090f180c0f02030a0e060f0408010501060f1106040f021f03020306010320040b09130c0c0209070f0c0204020c030d020f0405030124030b06010c05 76
    0x712004208908040000daa807070315007012010800404800940f2100c0c0e01490800091520b8503030820002c0c0002e07050b04080c02802c0e0b4801d40d049240000b58003071841d00b003000485005500042c415141d1140c203504142c104c1c0c0d090710900070340c0da000d07041e44c0c132051240d800680c0f61246d03a40d03815240181c85841d182580c85031944000341c040c00c0e0030310808d804a400000303901c492a025071081642011410000d0030541d071075803030703040080c88902d00998200406030040b24010061b500c0304603d0214a0301d001d41c1d64103014000404443c1d041d500b00991480d03010b400085000741004550417626541d4038284c81c0d40307818001400026481c10720f00c101c00d2602039031840058104041c061400e008881454840c0e035070726016200d0400c0b00003590001240701d00100b005203800d90103004c1014400040b039040c00881a1494200c0e44200c0162100d820045410015443d0900510314200b04002d81a2151507001110282400450100070a082c80d1100040c00d07a912596500800540010444205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 112651178 1250 112649928 112649947
    0x1020705010c02071208090d030e12010c0909020717070c050901230405010503060f04051011030901060f060c1103150a05060a0f06020c010c05011506260408041401020c0402 76
    0x90070040c160b00d0141c02036510000d082d0140b41d94115107141c01040f054503141104040180d0b600a4150803414094200b0741d0022030f8481618002ca044980e90000415048601014207420f001c1d070320144020380104070290000b10300324040c11072002d0402070345465a01038a00200030300c4050b00156000200c00c0c00004500c0c0c1440c224054014030f0720301081da04e0380d0800500045d220709000b4a90964454030105e803824103880d80103a40a401501070f61004030324030003c101138501d524920141c00ca40070041c081d006600384183c200504039150032901542c03800d507014005054841d0046c10030841e84c9111401a00c041c0201034222190000d808030500e458034600004000030381e80c0c140510f5402c040807400d4130b0600545030540d842a0020003190780b0640c011a601501840101c800f552280d0301d440600c4d81400491000d41600c2e00c4620782d25140411501a114041000840e10b0110400f030001003180d641c12a810b40740001d400017001d0240a0040c0c2c5045002c5911030b40080c80090502d20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 112652428 1250 112651178 112651181
    0xf02030d0503100b040f053304080c0613050108040804260f0109080412020a05040e03090319023706051809041a09071505032e061805030102070501 65
    0x11420890740c00c3c2c4009920751400810501980c05903461103110310000303120b9890302c401c80c0040c20300b801c0c0c14a5041800300c007101400308c1c0380344542d00703c03014086424003090209115400620324292202420b00401e1120301d01e800400d4820340e414864210007060500c181e490841d00580f1611024481100b030205007070b4110211000070480038003138039004003810314041c014020020f4210600c1030800c1d04140f0501122400441b04a0b4006a10388000445407528018410305001c01005180c6440007001030504140080c01c83c03210b000044d01402d0010b07074502c85207900c2410b03802c40404a022800510946940f800d1010880d01c1c1c0b029080003c0d201d9106009040d461807801250100340442130a011035800d0076140201a400004044d480d0214081c0040e50301100c004100e5041c4d0355248882c0e5002c0701c502010500041340081041100004215079000001031440c40c04141c41c50465810303054001e0740698400c00491a1940703120f00b81403680a005094001e008544d0760701c15150490 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 112653678 1250 112652428 112652431
    0x302040b060d0c1d01020615010f05040e160905030316030f030f05040c0801060902040f03170421050705091302040507020f0709020c010b0f01020d05031e010e04020405090d0207120f02030d0503 85
    0x14540d101360781110b00c0c0b0354800316189024034030442e00c002000803550b00546031030080712a6030040000034400081c0e0b01c3c2d1a1018036018900201c0101201c420a44000f4078440d000c2e08458040c0d44104031083d22002e1044581451300c0d01407400e00941c00c2d41034003c6001d00000701c01283d40c14104001d01042c0000032070740004481c100c100070040550303603141a80c1039010754032500d40840c10200301000800e441d810742c10810100301c01c0f940c0c81c2075150f11034030009240440031131806429901c43c040402c5001c00009000e00422602032610f0f03c1d040070a004020746e05078000340210740300c0000c40c2e0524020814804020000310a0b680c01648900301c41000350031641d2060495070804039011400d04110003400c101d0305069000c0c1c601e511401105a546620203070221074005480b6403040700115030f0f030110074084d148404401185041a00410081d80c00180c5441c845400901d54002943c0d00040c006040b80c00943d500a9044140d042024010101c00d8002c1d425026410501d000d00c0c0d404002103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 112654928 1250 112653678 112653707
    0x40f0204020d0c050d0f0e07050d050307050609060a0c0804020a18110a0c020102060a1112070504050d080417010c0819020403080f120f01080a11031006290f03010302040b060d0c 78
    0x4001b4001c1c1100c80e103044e500b00d0006800c043d00a503006004e6814812220441103000d44102ca240448582d101481c01c2d90031104121a50414014002100c1c002c0c007581410704150714000800d130a007600091454062403058641024080100015000c559040000c4040c1e0320718065490f40011900640b1035505000124018010300c00014035458081c415008200703182243c1a04000c00044200703c40301000c2d0141c1d0074080103200008681e5140303200807a4442c800c0a02c59225890320007004681002e60584901c03070790600105000042d4045849540480c2074440303951400c3c1d40c1c0004038001d02c61600050550701c1e00003414030420180c00020b1100d070345400e83ca01d01e580d80f05000d460110b1028004c03415070344c00c164150b4010840807003801500f20b500500713881c81010b50746101c0f011136010768231507564100760403c00321030509003a802d0a44035000e012118a4400561500e0a07548814000248180d60780d203003000140c3c5516041e10b4000009000c00c210341681030700050801c1c030010080c1d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 112656178 1250 112654928 112654931
    0x60d0e1006140315062205070203040302090a0b090c0901050c0307060b0306010f030b0a23071101051b070206030a020702060c0609070504090b0f061306030309050a080a020108040f0204020d0c050d 86
    0x30a8650f050000d07103200041ca05010300e1050307858001c20080002e29000c40b811030300070b04c50076036200c112440c498180076805e0f540085607664a14814044400c04c01090a940319180098042c110703202d50b498640c2c858080070b492955070070b044005841078003e808900c001c510001ca002c008106613503100380f034089821011100e1a03a683c110032a440c48a601006254220080115405a201e50400741d514400950b01c2400d01910111000014900b10351000c0010140ea207186a03c600030701c03442d6084090341c04105000c81002141d8001751040600080c0505400800540d0f12846541500d0450f903000b40015900d1840714901581c0386002c0d2102c1041d4060414005130901c0e0512850380300320303840701800301280e03100301ba42c060580d40100200c1e00107140c405500d08084881c813515010754425110301540c24103003000d00c51120210f400c50803a0b030307000303011510150381c214200c1d80d4810303406903000b51450740900c0401c0107400b44a4803074107603d08100340c40000c19041809486840c001090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 112657428 1250 112656178 112656209
    0x1050604060902090625020616030305010905060102070302010c060e0f0d0809031c020901091517010b0307080c160206040e01092d0b01170411031606020309060d0e1006 74
    0x21402c040b0700c00d4840850f880002000789805501e0b9415003100c0e1681810380d1a81050b100d038003c503003141e000040c252071001350341600f03c0816815200d00c40c09045001400c0007180341c0540040c0d6034051a00010b03040c0580641c0080400a041d00189031b01c1980340261075a21010030740e101c1d50f03042101c1101c0082108080042e50810001054403400102c5202149513070006040d070b94000d50006415138104071459002040070044100ea510700d24000c0d582d0381d0031211080c04007070140c0c20306070429841502c080060103021944505110340050720b0041c410b9440398402907a400050503a00c0c029007110010400007114014442e06a04031111104180003503c01c030340e84032141c21100814080700755940d0303030744100e0f42425911900c2803060605061aaa8040300208619100103d50448049940d4100041d01d818140800900305135004004e0390304034180100652a8004c0c20b0340d40d40034040100b40341a402c0d1054000f07440150344c110076103003c1c1c010240544040c204a01032500100042d14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 112658678 1250 112657428 112657439
    0x1b0712050d1d0616060c0905040609050105060f0a181805011e030b060102070b03090109050c1c060c0507080309071502070501080a0507051e1216080601080406020c07080105060406 79
    0x1600038880c60b07100d07800994003080d01020408150083c03000c240401102c010a000000c0c020303c181c000181003a1070303044e031003803800c0200030940e0391580040c1c0b5424106030040159031a44400c1d00c4000d11070402c05d80c2c60b5030340c0041c101d0b401b042030f00010402c801210400902d1003a90042c100c410031458000740403a80c0c0b209100b802c07814a41030950014030f1520010030100b9580c40810b50810b20510641d00015510408286650806d90b40845c440c2d540d5048001000300401c11120142000ea892078501e007016800c84440c4400c000d000f134001c0e9207070711901c110948a00111640c01d40d010801d5500c9040946d1020340e1000d840c0100b008a810100483c0540c0d8000034100040719016500c00d80c10365a002c901d00040e220180c005030034840305000e203002e1660140a0594040405092503890b2034002e1503a03166182c01a00c2095020a80700c3c021104580c480341c2c0b43d500c00d00078200340da080e4407686801c0009110321107100c0340724001c201011030300b06c03010340100380550000c0301e0a001c11500c1c0c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 112659928 1250 112658678 112658687
    0x509060106113007050304090605010906090e130b0f0402030705092703090d050a0b10120201050325090e0604062603071203050403030510030b0109021b0712050d 71
    0x2445000030940c00f66074040b003000c40003000d403c40c8120141d40d000c240e030002c0e8040071954105031000ca80d130740c00c0410188050b110600c54000108001d190001e01c42c0c0c6401c2010b040d410640c05190001601034001401d003070742c040d0400c1003955104070008058a8000b410080600c0c058a08910034011640001000d140a103611401105c2d83c05100e0034030000c05e90400d00424070462000410300040c0f021010503550300303008000c42e50080e006403a00400c10300c1c045419041c020b2130141c4030300b4240d0040c009588100c0410310b1156081c20401d03900c1d228400f29034040c0715030a0081c030f503402c503800100d48481d034051a50300c00c441d05080490f4450f01c4803c100b006848581c0181c41c0410350054824100c8181c030007240307101e0400c0000756031030034000340c455240c1c0100c0f404a03040407a403201d041c001015410f102d15070384080303041e9004215500f03540d03600c21080410302c81c60040c16008900d42c07008048105142410a4901c4100e48000c1d80d180d0200986151b0090151070a02528602c102443d026 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 112661178 1250 112659928 112659947
    0x5040c1e030c03110403051c140711210f07120f060917030408040e01080f070605030c09030106080106060e060a0c030c23010b03100c02030706111306030509060106 72
    0x820098044080d40e28400710018910400c0e028201900da0b10350104411190000304040d5026201816280e00c03a024216505424000f00c0810003680d08800720302d910403802070b02c04466021104080443c24003002074842d0b108601c1c000c075950800100c0c94201040044e085144c0345c0701c0c50603a103515650341c00c110070012002c203016101c1c0741520141d40010310260b000c080410705c120301c00c005203004420808007940084504450640d00050b0a01c11080d10412250042101c6401131090404c01c940701600c2d41c1d40741c4104c50904c2804808a0340d50401001500d0703211070098020031440da641c0700e01c14068512407007103c002c50203880b81c42d00c0c182448011600111072b40e44400c0344000300c0f40c0c0c0032211849062429280001030f0903291100f49141d04149110003803107000480c8550907601014100004013003010003d61a0000d540c00341500031041c0c641d00d9800030000169131185011201e014800c8c424a400e842d031812101150f8182c060703101e940112500822548141e03260701d000c0c3c40502c2d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 112662428 1250 112661178 112661207
    0x5090d0915050906030601030204030b0c071a0103050a030e15070804031e080a11010207060204030b06130608120d0e010501081015030305090d110a0b07050f03030601050417010b06031005040c 84
    0xf040800070908012004580008061500502d49656070300c1e81d0000741c0082c0c1380d441c80c1074000540d80041c021242410240c401012140186651540e92525070b0303480d100e1b50040520151000588040e030303c6070001200c0c0201140c0c3c0a0380c80754546007280080d40640400c82c0c0c000b0300b2540b404030520030182210310710b50b03000104078038000c40000d05440c1c5940504201c4101d64003004080000746081c0040e10055100760181d045c82c2c2400030411094900a00917010b0382d600d000303400c20190200081d10340c0c108000614150fa207003504001c00300038018494201d19203600300000011008400551940a1b001c440410003200202000c02c10307807229588409000214184500020703842c0c0340c05140500362060307580664038503450000c03d410503600c0c0d019072901000418114180003090152034103501d5100c02940c9540340110002c1e189005a0245055840220b101d20880500035406202003040052103280c880c43e116106041c000c03554040e46000c4c3e07082c8418820b01601400480c0a01c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 112663678 1250 112662428 112662437
    0x20703020306130c1406040512210c0f010504020109050f010e120d08091b0402090d0606141203070c1401020a060e03030106140703080f0c210a0506030f030f030a0f05090d0915 77
    0x8e1600040082440c2c6280302c0451a02800c1001c8503284801d070076000d64026180026a20f40421246060070a0f042848144851f4101810400140c0e4800801000d44404032070191454910800480c1c180400c0d1100c50340205224ec0c00143d030308070024004400110030307a103081650707846000e11910342403036200050304a5606606111300740b61580292003021400380c80c49201c22080d441d60030942e00c1c10383c410ba18035060a11654524108402190311000786480110302d001865520207160f103600b48552a070006000c80010380981c400c1c065006000d400580078407207450036890080c0c0303944c4284980c20100345020200040c00342c0090a84050342d8150311050b07015910703601030702c00c6001d005091a240001c00c2003000312a0160012200c0610000061040c1a1900502c5001250b20207824180b0036404600031060500d000000c803065038400984198072911307044040009051b0000360240410309180401c107940100250311846080541c0d03038810782c80d40d54080840c006080d04225030015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 112664928 1250 112663678 112663687
    0xb0a02070b0a12020a17060d1a090c0604141003060303050d1e020a0309060b0306010b1902070e04030c0b0a05060d0206091302040f0305010c080105060a030507020703020306130c1406 80
    0xc00d6414040d140b040501c0c10043c01105000c54200200c1c0d01407030340071010a041d44540c1c0a2481903a480e00c0d4003460943d90f640f0791044030723142d5000f40250b6010086001c0c0031140040e549030001c1c4864440c0b80c01c060301c4540c445844d251000e511000c80300c4480c0c000c01c002c41c0c040312640d00c24082c510842e501034485601d0321500340c1e1844080c0100850420400c403d007888030f111f2001920003004011015540068006581d01e440c80540d280081c6041c882d40c02035005000c174184503011079041568014507040758860494017a804c1c5951580813500c0030014100300800e140e0000c1c4003618480c400c094115807662100c0c8640101c9000307039a45500311284c84d06007030042c107080380204401e000041655032520340e91401c00040e640290050010000000700400411409000c1d240036070043c3e081031101c940c10100800d203a80141e8200f04205078451021585003402070040c134000c0c1d90042c0c00d49070a4507040303864803840c8903107540464061804450014440c1440007019501100040c0140d141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 112666178 1250 112664928 112664939
    0x30d09060809070512011e02040321030e010207061d1c0f0c0b01060309170403030206071218081309060503070b07050f01020313061109010909021c1a03070b0a0207 72
    0x21120002c155106912440f0300108a0360b460500d0740421400060000ca07080520440c0321a0000c0070402c0e0300d50b0140140814400203c0e040f04d00d00003034421009601c110710700044110042c1120030b541e50615403001030706c1001c6c0030181d000741611442132182424203507130a01816a481440c1300c1010442002d1504098029100d44021402002d80307160034800b0705200c0d15400c0d101c00080c0d00c21404603555000c0300c17081103442c1d80302600c03620102504505052558401a480380c20080250f020844079000849041c074055210802c070843c1400c00d01c004402515008440d07038400c0711055044140c204e0b001441c0079050040c0402c1e05d03000740241c030020385015010540d40d01f10b010304a030309001d085400b000c00f420900c0654414a4054403402020b44e090800e0800c41d1002b011171118180e00b00051a422b0760404c00c490200e90760202c0069840b00560303060492000c2c0180c100c0515410314400f40c1c1444030804c944002c0c884d00302d0990341000d65420f14140540320710703d0307100007680000c00100007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 112667428 1250 112666178 112666187
    0xc1303052103280b06040e040308010608101202220605090a0e07170312070801030204051e06131806060503012d090c05131506020d170c0409090507090506030d0906 72
    0x100f10781c070350380701080c0100008002506030f00b06030010300c01c09040708100014550320604903401070009007440c0c880d42c145461040c64406a03400341907406a080c480c1c0000b1901c4074101ca00c10800320012840c04808000d4100b005410701c3d210b003921911a080115103011101d00c515540700904c070008041c01498000213885649c2e100c001105240008c2c481d02a1210212824600c2511242c0d036003c169030447c0304000803603a014095290320003642401844219203c3c2505800540803503000c4290243c0c1d00d00a0040e155000600c5448807411000c1c0303081201c4e6810120a42e8402c0b0004d210807010080e0800d694140f5402e00103050854000c58071914400b17a00c10007846000e60100c941c50b07611400410301c1a40d1652340851459075411089041000d0085400050030341c901c01741c40604500b40c001481015100c0103005410088008100d01074610fa040f03900419240e441441900010304150f07491700440e02c94121a9410301e80000c04910700030559411210080e240d0000507030503e01d0454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 112668678 1250 112667428 112667491
    0xd0f0b030c090a0204030204090f031103090120071a070203150c1608040b03010b071101030b0108072006100303080703020301030804090c02101505102102030c1303052103 75
    0x8604d07400c2001002581380d902807002042d002d04912a034035182494002c00400e160b450140700c40d08140100341345681d0004079400740400054003002c517215103c0c17000b4103100150340080443c010740f070400040b20f02d03103101812060303000700c05440e08030302040101d614a0b282100d1183c180d4000f00314003811140b1006034044280e001d086c3c41401c194503004500281e80c401c1c0c0000200500101d802d408205682e00d9007984c1d000286001c3c050f59210328001780800002400c10740501500208002c0b05440c261940341c0e920044404070749481c105141d0251a41c0080c0c00140c0010740c005000401c854042d008482c100ea500040c02d92515140c04100b00c002c0c030034002c041046000d10004228182c1e85d03405688505420a0946a0200d00d8282000140d542e850302038030603c8500c60403850010340d1a40c2480c1d04da03070030b00c01c0961341755242c1d80c290001e84141010300e02004941c200c0030040c001c00103003082c407002003071000e4440420b00d030100b002c2c503000c200c605d0081c1d81c0c00c81d140700502c4040c082444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 112669928 1250 112668678 112668691
    0xc01050a1e020a0209060d030906031e09080403120f080105040f0905060a1a120303060d020a120605011a0c0a030311041a030a0f0c0c0f020f040609020d0f0b030c09 72
    0xc89444003889000280d00005454000140c1c0144280300079072621008040e00010207c8646c46440700340c0c1e4014120008900c07482003070581d1258099880000c0701009140c404a200d003c022940c0e071480c04029540180c0030550ba442c4401d041c45005901441c0580e07981c05081e12102c4440c2c0c030b480c0800000c4e01e0001951000d1a4442001c1c2000400c10490a4002d030400030300445e00d8075041103a184c80c49004240310703100d03d1140041c0075521074044201c0e600500d056980c03e660140324000f042d4645919802440d481c82905030600500480c0c0c1d0246069495684240311401144190801e0f03138080ca0b8100321305030b0000709620001038043c2d4001280845400041c904150b030741c400c0302110502d1a01c03000030030540082041808a82e0303200e1201d0b4841000300400c803111091900600100c102500245550103000481c0c003555a030b0405503004d6034004209000040e241d0802401a4100e60281d160083c188110040c0d0008140210319011101800500c0c2c001954410003507181c8014005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 112671178 1250 112669928 112669937
    0x9061804060f0509010e10180308060301090209071707030506010906080403170a0c020c0a260f011d15010e07051602040603050303010303140f07150213170705030109050c01050a 78
    0x41c44003280c401e00803113100f40181400000d504409041d420709111500f0640a02c1c2464540c082807418119442500358582500d010ad40c681e4036640820300400246001035030214845040001c81c80c0d100390041404038000560b1480e070740315070501341c050703400a484007400719000c40303030a014a40c0314070b0341a41d03c00d009280c001420303c02041d1720006a80c040e10245122030301c40651030060b507010410001660425603490103042c0c503054000da2921500741295032105824800c07005100c10400010a105400a00800c580e4403543e1040b0501e0302c00420400e041e01841403100c052414242d00b00c2c0c1295035107400d03544250ba0705402140c45a2091140710241c5400c088403d0143e01c60b440394201840c030410045903a5411418080c1c4141080c481185505000f00042c03812011b0303800c140c07042d1036442031102c0b4141c000418060081d02860000008206aa20000a10b000c0b0001d0000a44454006440f8019242e00506003a10070940c0e02a00c0c9501c0480c102845501c2074000b060b510710030303140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 112672428 1250 112671178 112671191
    0x80705182203081b39010f0506040b010c03080c03070c140f0f0601180506150d05040b06153007050307080a0212040303090c12030203180906180406 65
    0x2078851154150560540c00158030104100a05108000450446801c040350504128001680c40215042281c030171200800303a046a81d01c0900f040c0400d000c03031403c80d000388441000e080b4400d0017410116240d9115505103041d4205c0c81d401007e0094259803d995203414030350720800d40c001c03281e001405980412030314058880100d040508000c40480700c030340c003174034528207241d240602d0104814128040d6801c0400100300d001e010b81d04c08907440b940b14001141595a96000400d900303009800e280500320001208500d040f842c3c0d1101c4e206610030322039210203454140070302108250f84503070b40b01d240ca000c00100045041d8103440711840111500604504080d001c01645d030000192404008190040f003131005064000b02d20b00d0b44154141c004509000060000c01c9035100301501c0035080c5a55846001e0501014078406000b40024650025240280346030082d5a98403c000303889102d0300718203c0c0d10052400d41461405164020000342c00c0c0144500b400740040b07030241c402c849003070352003a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 112673678 1250 112672428 112672471
    0x2010e0409051e03030f060108090d030c09210201030c0e0604030b0919051b0d080a0e0102100c050c060114030303010302100e0a14031005010f150207030b04060203070908070518 78
    0x39280f070540380186000e95200c0c208021162880803000c2d1001c0d0500c0300100410209003800150841c40e00b141c1e25000c5801c0d40440c04c2543c1e403105030b8212040a000703c2d58030761407092045002c03101251003a6410490010340c4007003110b004045501c51a0304c601d04200401c00305022016060b00180620f007034842505990f99039110916021600b1642d98001b81c0c61400c000030007481d204401e0302d042c1e501e14000c8000e1703a910b604501c9544602c0f418002c2c040200f0000b40d00c03c01c41ca009100c5c2801c010480c091107401c0c00b400e180c02c500000003c0d0712500c0c00205260080d01e0100300b100320f000d4001c50442e400c6a08202e070711094610f0800420002400c59106ea688180c5a00001d0003a004440c0b0000742d030701c0505041c11160000325540c1401c0000400142c803004120030121000e00b9654051b4101c46541281040d155900160502005030b0a100600205038020760240721181c44040e43e607a80c80740141e407905803500c68180d0040a044c1c688000421001100d648410000e20b0500f0b50074514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 112674928 1250 112673678 112673713
    0x809030303040b16030e120d091416060207080d030506150313030e04090b040201140708040308040608070207030f03050f0f0c010605030105090c030a110117010608070311030402010e040905 83
    0x44030b0aa6403044440240300b0718450344240c007001c038822840c00303000c4954408035a5943d1200c3d82c0e40112049000129107006040581c004000907a110745008480e10000c02002d64074641030305c9020500b0038607403000448a0000a40d1350031190448082d01c6d500341d0202d0290000c2c4401041d56410011200007001480000d40045100700403240c4008188022400c0081c5541c40ea2581c02e8002d0303291501c000c02040b140d015655000b030342480e095210f00c1c11140701c68400e0046c4100101601c030b0104000c400c001110000c2c00640d07100d691101500c0e618540308990790b60a501c009410f001c0f508040c00c0110744100021321000c4903c034089441c006100b1850340c565030000c22204940d0355151070900140ca001c3c0a400d40040c8848000c040100c0381000007030b1204107801e4018080000c500b03514250717034040e03080002c41d400c141000000075a52480c000d440c4201c00c4454030000b924000c442c0180c0200c82068134000d507010b941705e042a046801c188802003542031801d8509100d00c20140c407000012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 112676178 1250 112674928 112674931
    0x10303020d0305072a06060503030f190503070c082a010911061806180901030308070e040903140c01090203010f091403030103030206062e050406081807120809030303 73
    0xd50082401d0000d0075801021118090504000c0000d40c890050101014418948500580d032240d0406011146004002030840c1e500c01a054000403809003007007080200a0039854102c03200c19108169100e000305c541d840304a8030040403c2540310540c0224080c400903041c0c081d0014034002040c95484a100c9016103546202032190b9166000313038042102c04006c40303034480030a841e5075040615040f81c2c1c000c1e030044950014050000459a150754060280d110040158003400e80c01895841781401030007400300313f5440c1d001c0b40c400b4020404500341807003a10101501581c0b0301c042c50700c4801c50700b8420742c00088180c58039034854074100c0143c1c0c1e0a10881ca9600424040000c4c00d203103518088403002440102400c8c43d400610040000c80c0e00422425449507040300c214109402c140030001d40d20514607542412200811000128207070428010015109140c5800031240e840d48025001c041444000c001642c004010400540168100b15169107104440350360403c00c41c5408245980c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 112677428 1250 112676178 112676183
    0x30b0403020c030106050f1c02130506240301030605040f060606020d140c03030f0619060305070e10140a090305030d062c040305070c030f0f0b10080a081803060103 72
    0x41450902003059010860500c080c04160002d0001c185440f00288802c00a151a02d004016058244c00c5034200b805e158041e0325070003800d2144860721420003000416046030700c280036540b002000c6483c40145225219071002c422405842e580c2140e82e031300f015000280081301c50814103c0b00c4000168a0300810002c2d042c1d03070f03004180e200071040008101e01c0e06001907001110f010420030520980100440768440c001d0481d40c240707910f0f40c002289109100700001c2488000c408804915250300d9000640142c0040c1d1300d014000c20080c040080c40038960482170041140950060452086d40020305110310803401c1120320943d0b65142c079400c40d0301c0b01e080d460515664100c00e01a810f440030000700600d0b80c105040000b1003e03c0c1014886500c040d002500340080030416204000314403039808007540c0e0000a5005800d03281c9040d04040d01c0c018022035102c1d180d0b000146101c0820111123084598090081ca80c0e60505d4580d00503030307845064622030850074000300e030b0840e441c1008058001e51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 112678678 1250 112677428 112677443
    0xd06050306130501110c070e060f060c010608060a060e0708092d06010f0b0a0c210804060e01020a09180b0a120605160507150605090703021209070e19090c03 69
    0x1150f80b0300700342140c181000e8031140c49400e0024141440001030100165411005040026110307100050500509401404e40c08000040e40750820034042d00100201e4004100b01d411a444805003481a03414038007401708560541c40c00078920714400c0723401d41c0c1c2003a4003400f40c07a001040340c3d80301080c03640c072803500c900b2814040700c54000d4014200520350050540441466896080c64000800317840341c55000c8040016014085d414001b4400301180700501014451000d1003403000080c044100c2110280c80b0140b1f4140d00d0000c4d1a418001c4608040441d4380e01d02e455400d04200701c0b0621081c03a0300c03070036041e5521060b01041d00c5420710040609482551700000d84200d00c3d0950550b44c00a040c3c01d61a822003800340b0035103810000f40c80c559070b40f001c2c01c1002c410032212407800420042c0c2c4900d83c031001500074492481d4141e80103000841c107a541a503110350300c11500c0f682c3e0b08407034481c0191210480001aa61300d001012140818180410100304506240c07107407009900d0f1030f0415200c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 112679928 1250 112678678 112678711
    0x1030b060310210305090d0c05031b030609010603020303091c060603210207050d0b0a09170306030705010908031608040305030a120509150604050a021303080706050c040f03080d06050306 82
    0x1540301e01101490300d040100c026042d90f1181c3e0020010b0003a20011405001e6980c1c652040160700907000d000b0300405000c840031040140348204000c004043c10038000c0c00380c1408210307012018002c01c0d06490700507004600d41040f440070b0040c2c640720710804c080e21075145130103500018824000c40e4025406100c4402e200d01d0f403800701b021100101d00c62901554440c003030400c00744d2100f00860741d02c5600048080f0f960398402c010b9002030301c2c20040c01040300300f50a210503414140c00016500803c002ea0032220959268401034400070158010102280e10034080169004558044010700502c91003e203800d20356642d980d41d2942e001043d919000c929009407008802c40c40d0321913181d1011001c801000b0300c05d8882e988440e820741c00f61641d40155100d00003d840180644c0490b44820104461808003590b0703401d107082c4036001450112080e50510020898620640d0296002d80d40030852085c4460b1941e80c801e00d582e03205060b5203400584031080003846a4060080c1440340055950f6030700d25 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 112681178 1250 112679928 112679939
    0x70306120b0f06060c0715051b060106110d08010e07090b0a0504180507120e03160b0610030b030d03150506040905040203100c140c0f0303011d0f06100302030601030b060310 76
    0xb207060041480d806030302c09100a9a050200151110880d50403400c1d9440710b440003c000c40782c52003007520a000d500c0c003400100e01e40500011316281241e91542d2480800350014681903103e5030030841c500c000030421001440950b0102c004603401c00c034a824245442d6660f080440346c1500f000040c003001c2840030800304140003a41002a03000c181110040020340340083c4050315400c501d02ca0380d8156a130340c0303103124a0108204116098200a904445074252240c0307002400900110380190061a08035409110a8000d01401c0c0300840d00030060f0850b0101c0500442c0100704462140c00b001c02494400240b41d10703440000c2001d4101d0742008a55881c00380103151401501c501c0145405151403003040c1401c4d8400103014070b030b00035109a280d0b41c002c5040c1e110300d0321040d803d044030203000c0080001340d030034850210b15104038985e0828001c643d4940094103c000710480e070250700302d0303c418a0615040c1c0b0030750085074450b10506000a0100030316003c1560358008441014160090389400c0c080c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 112682428 1250 112681178 112681201
    0x1507030506042a030b04020c010204060e12060117031c0b280522020a030e10140705071a040c3002060a090306050406022a07060503070306120b 63
    0xd008070241c9081c040340107022121850804052810308964141055005a640c800c1e0000400148014020340d115000700d0310444c000c5d4014810301d800700d8078240618206041c032441c49031a40348040003518861b882c1c0702e90038030f5030307400140ca0306080c0c0001c11031011030026582d140100c0c4030001c071001902d410340c407040c06030181c50014661445000c00b80070000300400c620700c44003501c0086d10002e401e0310080e180310712090340441d0040030040c000b180341001590b266002015034440d1b402141c0741c0d80d0b018805070044445596480415126440001d00303010300a80c020502c5e03510403000c5502c510202d000c4100c078604240e404403461103100d80d00708115048080145015403000080c3c21211591000c0c01040340201e0701c00a0081d4004a0500501c40c09280c0d034000854002d50f0600040ca442c3c80c20800941c8517001e424181c40803028602843c02a8456110030841c0030700c02041042d003840c0701170b105134000500403010980c4580001c00c40c1d44840011201513881441046070a051014030303480d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 112683678 1250 112682428 112682431
    0x1050906011d011407020d0f060b1503040303020715050f160207050319020a0b03010617010b0421170d0203010f0501030507140d060b03010e060f030309032107020315070305 76
    0x80c104a42520980d100e061840051000c0742c0703090030000c0e045140c04d4203d40b5103000c3d125002c2d6000c0703081d03983d0400b4000042e1110400c1c510401c004c01010311042c0800c216000b104881c101031071014400140028017030b40c010030026006000e09542c0c05030b000300040645a049595190100c03284040c41051001e50010b600700b52020300280462904000101e41d580e160480d6103068031480309080c0096446200c008009442e41044041d40d030340e110740340544070f84411020740d2602c1c1c604100024901c8504070560701035900f064410051010078114500080c460030800b40c03a0481c0801090150318289801002200c0e8510405071700d039032400c2c01d2006021078a52199048c91300706001c226269a0054241c005402030751010350b1241d541c00c580200800484d000721100840000002c1410035000122611410044400e000c29039500ba085c1516030107552142e035010780c80341e03640240b03c41800b41c664000407585031800703003445940c0d000285030510050501089604141c00d12010b01e0780340c007806 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 112684928 1250 112683678 112683691
    0x3120305060a05030a020906040e1218010206040201080402010305190f0e01050a09020108010303110319120509010908030a020901020c040c0519020d090e15040911030709060b03010501080702030d0f05010509 91
    0xb0303100545003030003098403032140d014000d10510001d400a546030b6a80c0d400000c0c07001100084030300098403507042090645c84907450355040c810803100b0110384d40c400a8058826a8107079a41d030000c2d2602c0d8010750107848050303c4611084030124484140b08504d1107283c00801140e9004203191400e02c00b441d08403080941140501ca00744048140580d8202c06618112541407800c3c0040c820211412070a40c01003860321042100422101070350240d0200783d12841f1099880100308030303140c9001803170881e62400c0000300f01c03480c180001101c0c0e00880d4007800d020041030059400682111000804480c850544078010031004940c118800b10b400165840403141c0380000c080e035070030180020304501103a1041000b000c58800c00140f140119008421120002600612500304549001800485e9108185019101e18a000107200505e8000c480032a02041d0040c1c2c03540e400c010044900030401881030040d803004000b07c020840461203603074002030002d00d00007119411b0500300001c080f1702404e40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 112686178 1250 112684928 112684939
    0x11030a140c0712050d050124030209030d031104091514180a180b090604030e010c0c0308090a12110321030a0b01090b0c0114130512090414010312030506 67
    0x4202884200c641200d0102c0d400c24000031a0002d641c40454040c400c0c01024691182803a000040c021201ca904032504007541c3d00c1a400002c1c0c1e990110100d000f044c41559155003c102180307611800ba500c40242c0c545202d440074a06500c8520850035a00f01c900f404180c140c2c0b5040410541108007c0c04424130002c4486a41c61701001d21035184040c4050b00440e00141c0e03038160a1013602d0070548200031140e011188030710034a8845049030715008101c0701600031610a52050391b8941c8103416000702c00c0ea000404546040c110f07240d00885400458980ea0818240180461203a400450a00d1800e210f1403420542e50140030605060544036001e0394103450b24140c203d0054084c2d4007c0e00d41c090000c0d84002410404480121500300181d406440030f07a41c0001e1035007000e103042d00080d5800c04a00040c06094a42507640c501e03402140d0006442034120906e0212010720880041208030b0740207201180044088883c400040e0082c2d10480e4443e40860340b0f040340b0f41d0503000c2c141c4e00c50001c030769 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 112687428 1250 112686178 112686181
    0x50d02010207030f0e03100606050703021005130b0a0b0415030c05010504050f1e040c030c090f030803040b0a15060806040f05240d0507260601031509051011030a14 72
    0x300508040106080c000510040600b40c1782280c070108078008541c51000818029070340e60b03000180071503104200980042c002c14200c0321701e03900c0c1401140d00a12056040b099282c0803034032080d001400180c50719a41c0750300e07680c07802802c0d80d44c0e0088002024144020150f080d28620f00f8441c10701642c3c2c811030500109000810882da5240210380d94008165000401c070b900380c1c10140d4446555101c4150702919040c4185a00d83d456441460803c01613100c01c880262101000711040c0c48911000f40b840c00304100040c00204c00c210741c42d821043d401c0000c142e4550710040d15420038016000700b40080c40340c0d0f00300032952800340140300307441c103500a08009904041004e8191459140e44001c003401c0c1c000140b075520b4a07144550a8655001416140e199031035003140400b21401059a00304622480f0880410503804116281201d6210782221400c916070304580000c0c00700f4101c284c895018a03440c454821a83c0d0041d41d8000c1d0030b9040b81d99a03440c0084908003140c9191420070101482c440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 112688678 1250 112687428 112687433
    0x80c0109091a0d06090606090b1c02030d0f0216030303290109060e0f0901092a050306010804080405030109050c0a060512150d050708060103050c100206060d0c21050d02010207 77
    0xe5120b800041960082001000c40c10410050610a140140a1403900301c00058681b1550700011492000f280c00464440c0302d0200340b210141c4000010307500d6084061020055400b0720040139041e0024015a00813440d400b484100111450380103802080d103c0c801c81c1c441d0440220448550204804800c6100c880d00000904103541c1d80550b01c184001140003142607551210b001d03028002c003c114100568460441740090100514841c1214408038025518034404401c249a07805060b500e10b8110359980b0011118014082d105880e20002088081280d4400b800f410903118014401041103150f072030180403140c070711a84410304122082c884d80e6040c0c0400c5007144e4104c405c3c00400041c3c0102400000c103442d01801001340248144440050b5180300800c07280e040ba8010815200300350030010a0060f50701c141090b030b50040e080400041c003540303403003041100d1150180c429143c03680d8035a940c041010100c107030307410080700d220b100c40c00400108012803d50b01029100960901c00c06d82d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 112689928 1250 112688678 112688711
    0x4060e04081b031614010506150d0207060b060c011a030d3c110d03060b030103030f030b030f01060305160308040b0a02120304030f11012c0f07080c010909 68
    0x181c00c4041d030032801c0c010300042190104191689aa054410003c1000f400d03e041c0c5c00f01c18500c03603051443c1d4207250024002e841c0c02080900c10040051000c1d2400762401c0f8a00c001b90b001a0301121155903800601280381c980d04041c0003000103010002500980c0b41c00040a0b80c100325411030312a902c01c15030750341002d902084c644d507403030501009000341c280601004444c0000080c04e045241710034014002000c0e83c006000030801c88001c09541019400700000c4058900500402054080820042001030300c02c0d0340a1022001603d4000b0f040d82502000034109075024000100d580c0d102c40050092200c14400c031001007405c05000e00056146584400300c40c022441901e0503104c010424030b0986000b0b009840070a424070b140107a1f40e00d000c0c03071b0142c414001d480042000030043c698602e24001d0510840c404091a025040340640e400c0d9040000840850700c003460701d020b51a0011030401c001c1010700b014100071009098900740c0c81000610360191035111900c00e6042105c007266000c0390 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 112691178 1250 112689928 112689937
    0x1303020c0d061803030207030801090c020d08060301021b160905040f02040507110f16050f0a1401050f0310080f060417070309031a0a0b01170105060d060302030d0e04060e0408 77
    0x20780d08480c0003032160401d88020042c0c00342c084403603507001c070500c01056496401048094446d4407825010390321841040221514600b0030405079008822358640140102c90081d80860300400140c501803031202034407000111038040345d00710b07400001c1c2182003c150300b510f00058081382d00108241e1400e51500040b1040e4000081e0055684401281e011403003400703100c0c00b00c11450120380f1418101c017601c075a10f000004121902c9890f002c00403e491804241601c00510000d010601c2d081c180981140042d4005c40030505020007000030080a074103403805140700340700301c400e24601c0a2074281030608100b4070b84218841500325608010004503540541c007010251440c4003511843c01d0b11b0192200030701f0b500301130081101e000300d0040944d6080d006500c00d003c8650b084c02a40c0c00e070720040d180c2a420086d40002862158014440b60a05d04094030341d025000074040750302075494011a0070008022544c0d40000c0c160381206206080c03e0142c1c20090403155840a4075145c02d4480d0400341c001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 112692428 1250 112691178 112691203
    0x30c0105120a0504080f03040c0f0e060303030411120a0606050a0e06031002030c1c200a0e04020d1401030c030b0c1801030902030106051507050106080105010b030c1b01050c090306130302 82
    0x2e443c4086420303c80c01200740c40d500c000c01484182c0d00e04050500075100e0b00240b19110b004041600040380782c0007500c000314021480070b4000c40c195102c80e6607100080e580c880110f50025540e62038061030900c01c0100d204094007550001038554100300074440740c698203820011052920505100743d584000070300c4084041c00400068903611000200d40051180a10141c5254080d241a5000509561000054800a22922007503184030403a02c035990058560042c0812080543d1504a0520350010b10101c11084400110401080000c41b507a40302a0030070f54105840740b4050080007200750040390030a92034402c2c0ca0602c501c220a01c55012515000f050425440c1c0d2041002c5480035000103016000040404401e580e4407841110107070403910f4262850742c03c0075070004143c6018810a41a00c001d412074034a19a5401c4140b80180c0c00207090180750183c110501000030020f05ca04c078094059650015603070110241003515200001d0103412010540a5442000a80008240f0640c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 112693678 1250 112692428 112692431
    0x20c0a02061606021209011b021c0509060f03061e0310020904090f150f050609011502070806010f090b03030306030a0b060f120c030f0f06040201120e031305030c0105120a 75
    0x20000042c1080b0029114020011400843d0f506040c0d00b4106006103e078100703400030488110b40ca040c400b440c048000c0802e015812801003500c08941c05540701101400300d0030100e203401100790210391654441c1204403441d040100c00d0117140e04c2c0c141156a6020003480010003040c8164002940301c10701108000c0103903038000f514400a85442d00507100e00c94100386035824080c000d08142c0b1ba01000303020080890341ca003201081c00440c0e548240c1d40200c4002d007054840307030b0a0480040d800c02000c0300d01010f42c0f00e101000181c0302c1040100501800c42039925203101807600c0a07000941b600406290720980090040240548001554004c0c03e9001190498a0784812011901500903000116000000050038440c240800580480c01001c182c04680b10b0a420b190382a445403a0300d05004c4a5400050110740590311030010008185002000003461106a030f0307040386541e0040300704e847d200c1c0d42050200454075003840300562100c0c080c20406d10b048600c00e400d02011030b005014241e090f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 112694928 1250 112693678 112693687
    0x60f021506010c1b051005120103020904051507030b01020c01050f0d0c050c070e10080609030d05090102130e06100302030106050f070602190504080105010603020403030e0936010e01020c0a0206 85
    0x203a100d101900c02c40c035007006401c4c01e014108800b68031207480314080c090080e4403c81071881218880c0c8121030b11409000b0080c8140c0e421942001140301c1c02074002d84080c4280351050002000800d5664010000781e00c000804550100c00a03050040b201809814481c0138000c5000440706c010454007584003043c07001a0f9a07804200030703900c40c080e0320a00e41407440707402d13408510a80304104050142441600b6200e10a0780c48010360742c5c0d0101218440c600c0d40040c840c080f04496950810ba0b0800c485a001609000007461030302440e29655001c1c0c08651002002c0c0026806c1220002010b8101c0b860150724541c1001400b070711901c1400110481030400042060a00c250b0358162406503000d02c0c44400e1060218600034000d41050050110355440d0200001d40c4034042c1c4201c404496154581c2c0c4003054800c4108401d1060007440c04540c411409180b01848440500c04c1d0b0451706a0450084000032540d442802c4034850b401003103d45c2e00c1008100112386000800706505513040701c150b90345 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 112696178 1250 112694928 112694941
    0xd031113060f12020c011517070b0d090f06290f010c1713060908070501120f020c011409010b0d0b040602031e04060b1305040308010306050c070f08040303030501060f0215 75
    0x80c00040d18101c2c80f00e10114070544102c0c0103421016060134085000101a030301d8102c1d201d103407a4404014007081c0d10a6000300041440310303000c0d080d41604003030002002c0ea00d0340c9800207159500a801c8502d66980c1c440f4148080c7d404e5000c44481c80d0b401c20100f4100132890200d62a0113250802a062014101200702000710128440744048010f600030b43d2100311054001c0b4001c43d141c00781c40082480030ba07001c59030500000d00172040381d105039030f4202d00e0100c4c03114280040c400c0101d0358480b26002c2095100455090144200840b12010003808a00c3e09805d200d0858a113007406510842e01e00c10b0b56000b0a04400da03030364000340c210704d005035a40c80d8981c1c800c030119510312100c2c00b00b002400400042c444240d0003510b4821050701c1c01600107a0392074a100c2100c804660040c04a940c2030014804035603d54080369004450f04105071400c9000c0d100e144081c44c400700c0456142c100028280200756050051500400040c207000d10645c0c0b11480294592561070145a8104090400140c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 112697428 1250 112696178 112696187
    0x150b070c06050313140d020c090907090c0e03030324060405090f10080601080a020a151e050d09060f0e01090506040809010e0a09050a0b0306010602030a0c020a170d031113060f 77
    0x201e245e402004113012007090380c6250389a050310fa40341c070302502078002031111908202e040300b4450440440a040900d080440d000c00524401c0440e10410003103d4030001d541d20100000c5005940a000400008001010800602c85001c83c5c06001d1a0140420021510b4200c81d45421203440040c001c6142d4070446442d0030388046031300222080c8200800011090404100c00d6203044c004e841710380d419070301c0f40d90000800e2081001900010208900381d01c0c1103100015180c507101f0185441480e151a41c0d5560040d62242e8030207441c51556000304424500441c414401b050100300024000072480d51207650312044000e0000d8801c10002456201680c1719001102e100c2c08003d01d000c54840d200e0703089100905003190621501403810a44108034900004c001d41200c0e0103074019860042d003484201e03980f807117601c800ca800140c144400302d4200d042c900d01440c2d0744500d40040107043c0d8051001000e580111111a00101c01000104004031500c8911000d580b454103028200c010701c05421103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 112698678 1250 112697428 112697461
    0x10f080a110a08090d090e0412120f0605120a030f080907050409200d081905040f0305030c0d0c02060702040518151605030f041e15150b070c060503 65
    0x5081c0400140c0c042c21180c0020105018000b8101291480d8042d41c500780d807400114000d6140125064001070000b4030300f400310051442d107030728004d484c2d508164110400c2d0340c103402ea424801500ca140a101034280002051031800e5000010a240541510301520040e107804443d0100190500007035100f010402011005001c0904200700d0100d680c10003480e40c0717030012005031500050820003001450600c0109112503001210113280030b400d110001d00d8a8981000749051043c00e01000500c141c140f42000001d501400c051a614180340048904040d1000b05020510042100140150f21400281d88803036506480001e00c2e034881d410060880100651003011034856003098031a080201c032041e40c02480325aa5156402d8001c100a5440e4041240d80030b0003051414005404252040c0312042c000c1d9200000104003041c50f124006007483c404505448151108182c2d0300b0704d00340309240d0004112004003207051880b0b5640307182409015104440802c80040042030f5481180c04201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 112699928 1250 112698678 112698701
    0xe150c0405042309010f11070b0105130b09040c090e0706141809070e0301060b0a050d0c0903080a03051b0412030e03010b1908010614031009050a06090501020d0b0f010f080a 76
    0x3c0001d4a050b003c4030340a0a006450802071904140f042c615540c0a081174401ca43e5100d4805e00060f820041070101c02c40d050b402c0c1702801911401c40142c961039030180207004034041c2e02d1503075240c1c3c20045210300f40d440104d410b09043d4054a010030981d035014140c2405074a079003440f9641c0d290140916004d1481454050398041440b10522220341d80003d160315400c2c9059009020265035800001020300801c6190303c0820030404c0170314651101c2d03500040b500005410824034154680e12800000d4006000c851b011a81e580140300300f5a10410f0700c0229143d081c2107040c03030a402c0511120980170310b014024188000039171424801d0380c00f90459560711030050000c2001c1c0c441c407404594825070740d101e00340c031552a2000c00b0483c0140c0489030400071002500400040d61040c4002d070003401200400d45080c02504c242c074000401d540607104889024000251f143d100540c488011036540d0721540b449007411640281050f600801e2014250600d420411400c2d541c04928201904040c24035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 112701178 1250 112699928 112699991
    0x8040c03062a0302030709050906030109050a050303040c09050c0921012c0106061e0302070512030711070302100f020a0f0b04170301080a060207060b090a0e150c040504 74
    0x25407000740d02c81c000c5111414064040c1902c00c0001e86070560880c40103640c0d500c00620243c070305002c03078103240c1081c0ba08240301900005001c445a04d40c80c2c140700e01d621080b21307150030020070301c424481600400006072840d40810000c40c140000c0040c060700c030384c109050090069802d10000340001c01500d641c8420910000c0c0240051480a214100c00b186842c40c815070004003c98402c0300148280410303600c4944480141401c0d0150704910f0b9158000d010301090f40800680002031814807102c404d1171050700110f0780300d05003007401170160301c240e00590440b076100000810240e540c1030b00d0008810382e1801e003d0324140010004a05240c04058040c0c42682004100c404020f454194584503a02038000407406824602025000340310a1044482542c003c1c0751500c0410340c0c6038002d00c8003a01c103800000d0004803a1010400307404080f0740c103149560b688d603144401601d081c03010b03042800c00c116041005e850960411415402070b809420f02482d81c0b00c070308561030300c00c1506455145800304c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 112702428 1250 112701178 112701191
    0xf030e1206010f0807050f0d1b06030f05010909170a0c020d08071403160b0a021606050702060702011e1d07170c0a080a15060f030305091504050102060708040c0306 72
    0x15003991081d0070700c20710420f440410400118003802040d0305d0141c40c4000d000905000c5030400b00214048015025100c1038003040d250500d004000c1c41308001004182c07004940c1c141c1d4580715808490050380150101801c00307503410001000354030102d030040710003c2c0481d100c0c4650101100c1c2e03008000002500030309405440c0d41031042000213007611600c00c0d0068a08a17a1131100103849000b840d9075100104a025060000198107a020b9079006503181c100500780348450500414101403400180c0300642e03544140081c1d83d0703060002d5644140d10340024811402100c41450146614081640200b907031282150002d608406405000c0c040100031240116200d40121451101c1c605032001184038800f81c903e494104066803400300d40020010f01140034040d2504610b0780d1419102003002c942c0c0703207000b041c0030100718404005940a56902500d41902e44140700c4104140d5140d006002c0d410301c420041c5070b80c001501c9d030348400d080c542003e07241c5031442c11040341141da41004103131030308012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 112703678 1250 112702428 112702459
    0xb030304090207060c0f02030a210c0507020a0509060d02040e030702040e030406110601060801090e0a330b090402011d06040608060117100b0f040506041e0e10030f030e 74
    0x3005003e010740522010041a44036401c29076900b042144d0210140c4c001340070306904103001e20858000000110038010401d038614a68a044460703280c082d101050001c54070005504051100708090403080d02c82c2461420315500081400d400c07c64005e210300d86560074041d02000070b0080c0d50441c1d601130400d100300003058141c00d45035001030090b500041d020660002c0c80c8140040c030781c0c1c1202c8054803180348690911401001030b01500c10100010711030080390b40c0005000d5030051040407141c10b69481110000400304250b0b5a0000d0408146410300c0040200c4c3c0d5180403044c0d401640c2420500c002c002145413400041d010102001d40c01072000c580007034142c1c0c0000107180700740002d0769661602002812414a8140d017030b2124400390480410a0100c90702c204020450780c0e03004c0c4045428180d03110001081c642c00f54224180c3c00c00902d10700241013410304a000c0103400301c15154a03a503d800d4038140d542202c68030000d0208411050444d0606000e101d072041d0002000c0d000309500308211 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 112704928 1250 112703678 112703681
    0xb0406030503030c0c060c0a05030a05061906020601170303160503100b030103060903120504150534030b030a030e061b0a0308070806040e1506041d0a021905010f11010b03030409 78
    0x4242d11600c46c0100030008100046403021100c0d00520b41c0c45860464895482d10001024000d00d02600a0301d02803000704601c4101820000600c404c0c2d0080501c0d41c1000d6105052010124a82e02507038400d0040c00968184100365018001e124500035449546a10036184800303020340c4000d12022002001100380310b03440c3c0082141034002d0b2030b000c4c0101001d40d9403e084681c22100905121884035641040e03400d103811035500450215009101c0192503100306049966150740c410281003070000c580340c1c0c0358060140161050088015140366442c42d00e001d003105c2e0b076000341c051140f0000202a040c00700b49075010600c08009008607110101c452401412040040d00c41c0c43c04141c0d180c0004407246409c3c040c00800c150f10502601a58900c02d1002c101301c0000340000d903116445e00b0380c0c03100f254181188a20100c00f40c1004145580050050107001000001042d0104405400510280c1d0300002c030110110150315225024a1144c0c130590300615130f8101c0c4a51501001074000f90380502ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 112706178 1250 112704928 112704937
    0x180603100302011b1a0403031e0b030f0604031d0105040b0d0902040b04021908090f0109050d08060904330e100b030304060905100915050301080d0e030c040b0406030503030c 76
    0x3030702d50f80840b134408000848091040c55000b0141e070742101d410840f03101075061042c0c0151083c02c002c030b4844c804c1e111581150951043c0001005e9545003030480381e02c0d00b0045009210036400c003404107400d107904c00900415040707410050300207a50556440c50f0b44103208960060a0203602c0d6500d880281640300060310300ca0034164403460510005100034502842111514041001c2d051481100ca28069510000080003600c1900804229041c5410207000f02200107200718050840e0078035641026062820203040c090089a5000c01c010000ea00100f09400c04004a400400450080741c042c0040141c0d405000c012142810f145080b407132800500064030340c00c0c00c02c0c280000003d940a040c1d880c01244240030020340501010031003800c2c0004695031521092811900064640f0485c900f85140e01c140c50002800000040060032800c0c40248611261443d02801c915074000c0000d03965401200d21a200325a1071904000030366070341d40104001c661000c240c0c0e850b443d21400c0145144c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 112707428 1250 112706178 112706183
    0x605070f020601050105090d0c0e0c04080f01020c03040509220302030c0f0309032107050102070c0e070f0c030f0201150807030302190c06030b040905150a0606020a080702061806031003 81
    0x280e0480d415040e00102e4000e0589070180e41e51030034640d650f02003103c001c40900003034400310f41000010030711024030840e5904c80e10103168200c5e601d91918200c14070f131030441144000c1a910501907100754031004000c44044440c112038269545d2104810219103c0403880480000140d4608102c101a00800171b00040c0c120354003610300003031200c1200c548034482c4900c015850707000000700002c102c184074901c541000481076610f0034800304c1d0303841d20300320b90142c0300c04e490701012680100f20307404030640e0075a407000c994500450704d4804030344084c005024058008003840f1100d038804854503c05d520400000b03d00e1030019010075640c0745010380320036403400150010701500240f5440c01e0015082c04a07243e9002203061320503854040100c00034100c2d0104503912540740d10b41480460800c201d425000b00450040401608102d401d500c00c40741158441815900107614640c0480c5800c0140c4407047c0d01650001d68940100d121044504119075183c1d50011020080c08900c1c0398042c01041540d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 112708678 1250 112707428 112707437
    0x30905030610030c03081e070b0105040b0105070803040f080d091a0901020a0207141c03020610051e06070f02030105190e0111030106030c0908070b07050c040902030c010f1803060507 80
    0x1102e08008107035158040c08054201d556038981000054032400c014104442c480001201c0c5103d903000101540d8809101035a01c68402401400607140c1032040304803c40007400c145140a055a0b11b008035400f00401c040d01641000076030f81c0c207000501044604003c0e07220820001107105281449111104500782c0340a000c51200181c0b014105100300c40c3c01600d6600140720503071524450034000c1c10019003040e04250030861401ca1101c0041401d9051482500030304001d2a14113000c50b0700c00c480380c0c0094450401802c0c0301c884451131050700c5070510025200e50340c1c1c0d20700c00c1c10955402d40040d4002505503290108014880c0c4440c80211003d81c4d00ca039042c40010136214416080e501c3c26107540c03c50702004c000410000b400703540100344803210380c2813031000f4690320a4800e040040380d078400c014072040092142c04100e410302803420441c000300c1e001c10a0300302c0b40d008a55140f04111030305041c400099044c0c0c002a00580c0000e4820040106a102c616121700c3d148018003400c3e9030000106 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 112709928 1250 112708678 112708681
    0x2160b12010b0726090907120c0c030801060c06090203030a0801170325230102040f0e0108031b1c1715180c040b0408030c07080a08031603180309050306 67
    0x1142e0b044074103c41d00718618541c412082000390400c0c0b54401060104040200001d42c3c80741c461480a0b8403c84c01d98840c1201b00100001746c6040d9011809203000f045580700c81c52001075040407821703046d181507181c401c018401500d040c9008065010011b5803603c40440d07070303120322544100030505130f6840c5407004074002d028642c219540e02941c1141903040344884000f92802ca412000721104a0041a080490780341d46200c50341051400030b800c0640380d4000a0a10010810045c04001002f1440124446624041d0ba0315203a024220084100c000306c122a00035030030040000f901c0d0301254202c200b07081d480341c41c80640202c009034450409400c946000850440558031101c03060200684510301e012550468045500d40041403010351200034000400c440c90a00d020740b01500000e402182d0b286508004140313480e6490f030144185070f02204400c0300250515068a400a200300c40d082907061094406034098110b82d4411404926002004024158410a0002125425010741e10301e03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 112711178 1250 112709928 112709939
    0x150a030603061122080309090c0714010c0e0105180d02010201020c030409061e032103180b060a081c1101060b0a051305030606030307031107051009060801080105040f0305030702160b1201 82
    0xa200c41c42c840c0c0105030708140840087c0c1e0401418465104200f014401d1400d9030b26a00c055000b090705445881c580e40d90107070300c4011508080f00d40810102401c1c894104100d0705007407031852144000080c092400c1c0130350801164002d4042d1802c80c24820b040d00e44580d15168403800821940c82800241070102a440101040480c1080190b0b90010b00e049114440b82d001c0102c6180c25a1101003055999020307000101b180c0c00071208840e210f00181d8186003000c40812942060a800030440e80e0042042c00c1004072600002d81129081c2d03003172074982c1c0070500d48090b005106a40c41700d0701caa40001403550b00c00e50f01c14020800340380c5500b40c0f070410300d45410505a07541821190aa090b5004114103030201c0d006d201c5001401205004a44069445801003000645084070a2001c550303010340034030585070021186809459400e00800c49450309448400b030f05a40d914001e418400c000003c00d101030720a0084079461034440e60324104265507a00b00001e1503003d069207504116900001280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 112712428 1250 112711178 112711237
    0xb0f070509090106051e0a02070303120b1011120a080a140709180603020607060b030607020a03170702010e0714010207050105091503190905030318030702150a0306030611 75
    0x2841071001c0c003420003680c00c200b000d0302c903680115440211010200c1115240081c4040203224030421640030700a002e1841c030340a804180300350fa803819158240641025145c6415003c0e034003014043c0340c6440340501581072142014480c1c54958180240000c800c003c2e603411261140c0a0249010704102e62445502910590641640c4031400071f54240d80070410340645105951040d4610440040e05075681e40c0041c100d548410001c40d0b0880e00d42407540380918050002950011290019192040c4a50f4004001c0c00034101c200d00c01c840e0700d001080d1018800d51103285042e80c501d08581d20b858481520007204d1001c400c0d65801031144071004070312540315100395599000040c0910768000d9805016030242d400003000b00c0da03034041004a2012044050003044411130003500a165030342040d003030204841c00c0f2464401d41e15030080000d0340050f1a01d0100c4001a00400303406034960360010411405041d072948040e0038241000084901040400010055800e111307081d050000340f210017000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 112713678 1250 112712428 112712437
    0x20a140109050c0f01050f130608160c030309081207080901150513020903121b011407050307080a1130041a060307050d060f05091b0d0203030403080301030b0f0705 72
    0x74020f420a840040250074101881049103505041c018201001c80441d41c00c2500054030300003e45448020070805a6007102e032164010511408500c090243d0101c0980845000b000c01010160b80c0d040034030522500300c013910811420040f040c401da060150006010003025103d281d200d52a002015a0503500c01c4285070132a2805095962244038401d003110081d00940b186035050b00980460031790700e0401c140200100c0d0026a583c038540c00c8680b40c039074216912140300f008001d4858007403011054200303041c0da9002c0350302c0ca058042e55445100c240c01074004542c3e460410305001c91200008403042d103c5c01d40e02c084c401d404001d03908907104411284ac006a401030142c40040c00c0341880011820307015a844107010301281c510300d940b01c003c1880c010019074256945a80d6030903520840c10316000d02500801e109008284011080541e00037624450540030300c181d0751000100304644041c425900111b40103d10103840b9a0b681c14143c9800204803032031034220f140c01c3d0002e49854014020759 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 112714928 1250 112713678 112713683
    0x8070615080d080c0d050f070f020a03050319060305120702010314040b01051011100608010506030a08090d05010f090302010903270b1803070b0d06050906030a030e1c03020a140109 79
    0x501c02c20020000640707008034040c0080f6505242085200c0e0311080e42d002d924040c4107942c2c204501490400002000c036080e8507144800c5400c8000d4071070220b071b40801035a0300040304110070a010a10140681e000304a82da000411a001c1c0041c0e901007800380e1000f416442d8000c8e01d05112100f42c100030345000074800c4500500b00c00342a00140128207001c5042c2480e500e242c2051200a0410b41d1400d2400d0035106c0c066007403646401040c407a1000038041d1a400c81d006034010507149040350fa4013081400740c42001c42c010303a103901c07130402440f00942000c5607145001d00c04100c0c2c807042d810300074080c14034490290302081c0c21071443c9803202c03100400c0d030784a82040c0200703d61450903c82c0c100d42d10382c86255000114103562400300b9003540c050010400a2064241180d40e9a04181d410703004d59072250f01c4944500304100812005440c0846c0c1c42c41d201d603262810307030325268030500001c80e21140481c62020402c0300388080010180c0002d544e8040c02d000e100e0080790050035083c40c909803507061400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 112716178 1250 112714928 112714933
    0xf030601030c120203070e0f0610020d0c0201050a03090b010f0f15050702091b0318011a0609040203060301140405010c080c091e0a1505130501020106051c020406050d0807061508 78
    0x20841003803e201001185803000301951011640c071442d4149010094a44506140b401c03810f1107024035002a207903030941500d001400c40d5003181900548038101c0c0341c2000c1e0500000042d4040715a200c1d520400159a000284010700d5031266001a400c2e03800c0d009030180d02c004c0010102d800032034040c404076800c1040d9a000e10340841a42801005d04020b070100044030104c05c0f40a0520118102561103030043e4030400b0f01240f034800450b800e55076105401031290190003002c82540d1070322021200c07811070036600940d80e40c070383c940031038010300f00c210410500341c0e5540d080c0402c12206402010b80c501199139815805c0d2101c030b039800181d21944024690004045120b481c0541040c1b0504405070402070042004036510f155400c01c0300c0038501c3c44000910000b55501c0050315540d50078029000a2000b00b00e29030070040800d00c622000081c600d100040c2c8030b80c41003150386a030041380103888041c2115201030820300c0c228825030003501c0101c2d46c0e0303428901345c14880855603804c3c0f02244c1d4410300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 112717428 1250 112716178 112716203
    0x60b090901061d09010e060109230118210302010605010513031101030e1e06090606090f0a0e011a330a02010b0a120209010803040b040603020307051b06060f03060103 73
    0x60f2101c400c1007030503581c0c80060b011540916521108882e00030100d01c90100c050746016000101250b242d07403c6480340ca98040013296021000c085994071090003820b10040046000b034109018080a84c010f903881209043c001c000c01040d60300c04500c151184c0c009011441d1103600540c4e481c05880e00300c11511400c11800c001164a4001d904a032050605000400810340080142805800710b05010072004921075940104010040300340e100409901610307650800b01e0000d8001d8401a125440600c0b00e1000709481000359800401401868002080301c01c05101c01d180c02e00c06401a42440303514094540c903001d0740070141c2c0c00f0300b4030f440102020408003200c61003041c03038100c00c404100b10340d65400018855102c00f00c80401030705050400d6041015240304201c401201604036901c40c3d0020702040202034552420354003a01c11904016071a5581e01070304a4190041c10728000e030b080c0b1181c544001e103102c0451598050041550b08050015200051540da000280f0008061250402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 112718678 1250 112717428 112717439
    0x30f0306080c0d03050702030a03051902030702090c0c071706040c0e04210c02150405040606020f1b060d021209160f030209070c08070309080114041112010e030406020f01060b090901 80
    0x1000003c03c1d100342400c506080650f00440c1c9401c4d001c890807008108002120321400359034400200074082a48015807802d0f0b40c540c085200035a0150040082d4000031500003900f40090000d80054540032805c1584070040000c19691081c0070780d0b0583d414400c8440220368080001005482240c1201081c08907000031280040c01c00e070628a80c1081164020b40100141d803940050982e015402c50000d40700c41c20802004111001584068159071003c158128000d03004034440310100c9150081d02d48240c840e002040051140310f185200b103d1000130f15404241d560400c0a00561040701103440100302e805108039203010b28096480c4409130703a5010401890113800190b840122807412144d201c04664402030590050003084000c54600c0302e042c80141000d00c070f000380c03030149a02d014401e4105615105800140401040e006004103031980403c02406d400902080700008100c035038a40d500c1070000d448801d400102c200c0707035003001e900040743d003044002c2d1410920010040c1c10142d1901 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 112719928 1250 112718678 112718689
    0xc0503040b0c0904090303021b0106180504020d02061207020106050a0605040b0309030d0c0c0506070905060904020c15130213060e070503040c0506031501030f06080c13090f03020307030f0306080c 86
    0x2090b0000c980002c224505454860b4014021098402e80700541c6452103414200001100c5440b000c0d0303903030b141070030804c144500d00404108541240038006856282c500208503034005641000c0d400c8080010184e05484072038a98500c628078584c000c0000300e0f200c0003040750b80b940c039101c1d1100041d030601080c400184944015900208080c1c00c580c80c00c0b84111805051302c6540c90f2500124114a10042c10300c0014000568010107a1030041301359414400041c00f180540310725075014540c01f0842e03101907801001040005e02d946034051540f45002c1c40c81c0b6441100041c130882c00340b95040b003099016912400f81c1c1050b40d010318150f84466845a200b02c2d060b4000030301c10fa4801c00102e10000d010749951000354080c8000500041010407558009001e403550105142050741c5032880070001410302090051804000301e42940122607803140c0103002c3d205140c8040c01c0d21364220708541c10150008001c00c0c006111351140d01020580040070f4040f9a4680b00345040e5400900c806107045c5041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 112721178 1250 112719928 112719931
    0x30d03050130020d0303060f0e01061e0c1a0a06080a231002070606060306050f0d0201030213090f05010512060907030323030702070f090b0a050d0c0b0a050703120c0503040b 76
    0x49418000300d40d0342c0c0d0300060442c1c6200030b0190f000c660345000c24440c002c125030b104405000a000310b880c1c15494920000d0000c903848032003e140c28075030200b200d00c2e03501c640d101c0c1121542114110054000d54400740c00440e9041d1b552511140c980301300040c1c2c408000c10289610b54210302c80b65080d000f501e180d580c0600b03162020a205000c3c503044826035071081e10207080c4070b0703006110004415052035405021a18550010307071144000c0c081c01d20441e07070b5a4400d0703182c2d06c0c0c1c2881d0250310b41d5401c0a020340134240d550000460141000c03041e400345891680014100c036005c07140140b003011a030500c9a02c95001340c60421032908031b6201800800e000c1d02c0340039000c0e8010100815010828112007803d5041501c001c80140c011583c1004160610320810014120510003040107081320000280035454a1280e9402103003d0700900081c4150450440700800741e1100781941d07050200c8006085034010617049001c21000c400b51150480c0b14403802c420000c25840c3d0510b035032996200c2c007118010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 112722428 1250 112721178 112721249
    0x60c020d140c100e09070801050303031f17061506130e0c0904020406080612010507020d0e031e10110a08150f04150f0b120612010b15030402030d030501 67
    0x30b41c1d40c591450340b507040344035180440a0341c41c03402c0e08603100c0400c00398203806418041005a4a0014802c2d0740c1c0100c2100d0704500203000c41d50300d00b61350328880d4070200b01d10360141c03070320b030801291040814001044451203070a0700050b240710588048200141c3d4055002000440e208040d810320100e114041e0705500091480711071802d04840c4400a01603a01c0364200500041c40601030100d942020740010358030088080090000d8030b000000207684654442ca614100b02104024802c0340c1c0f0141705440a804005140103036101542020f2903a03500d2000c90040e05c2440c1020f05c10120344002d007900c8010100c1e0791036004030f49580420684005144003440d501459540d00400a0740e203e00c0344002840c0e1001c401c500051800c2008003181c06240d010040c070403c01c1040c2180d1507821942141e0200c0103d4004080c0c1381103048190050080c019500c7e01b082e8580c6058088000c543c0c09980b00e50b00c00c80031903110f0142010708500780d41d020b11620b00c0320f802940f8003000f43c0400282804841c0d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 112723678 1250 112722428 112722433
    0x5070302010603060f02040e07110c011409041a090c0a0f12020d060f06020d0c050627191202010b01080403111f090b1608160e0303030709080106060c020d14 69
    0x50f00e986504e822038001d455059070307065001030200f290070f00303402203183e000c040c90401140c0c00e003022800b56100d40c1000303000d81c10000130709254a48800c4000907a405004094420440d040101c40c8030401ca44e00380c1500c40c4651420800140030078100c40c00c503000e825165030f644102c1600e020084c1c0300c0641510354404407035000e101c0300300f00251703d120700300050655130540d205843c50301c40040d042c0418181844c0030400c05854040100c1e600082e010780025101003103e1020f0b00c1040300c000000900d4a8860b42e50040c410000c0c031003082140e45124141c0034503110003690081b00003c1c1d08840c59485124040b4000000060201c0e01450600c1054519075050f03030326000c41030380c1c02d8803013010800c02032403041e40d105014420b00c9140407503d0362103512103051041045515101801c101d0700204080040c41c40ca210124105109004034841e148020f01280d07124100040051311054490182c0d200541c680079002401e9486000d0340d0700c800f034000e000b11210090381d484041c403459030700c0c00601c07031403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 112724928 1250 112723678 112723691
    0x607030203040e0c0f120a06051503010e070201021b0d1707080a0f06050a06080a0506042a020309100e092a071b0e010f050603060f0f0f0306161704080a0507030201 72
    0x282c00800141850840c2c2c580e50b41b058a480c0e031490080320314a81103103000d42075011903150518000411241074480e11070000d0615a220201203000e0700c9002500740041401c040308840f501c9000031004400303285a150180c1c20b999038441d4007102401158a080010700c4080403070204412940202c03510380d8800340c0403400c03548503004150080c05607404200044c86075000c11020012502c1890f0308083c081b98103004d22110b01d04001041190610301e100b142c580021181e850500800c102c07051908044d002111015500d82c011340170034150860700d40600f401400103491003540d00d204504001d642111584c1c180808065441c00d0b80004c082100d10302c40000c08030002a005100c8000100318030824281a981400c01e88040c1d071410340d201c0d078000d08040c4180102c55a4076848000881c00c10303070710103c142c5000b030001a0424020800140c141c014002800300368007440e0300c4c211215000791124400c802d4801000140000100c034090809282405040e03c0140b05000a08403907000e4400400c02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 112726178 1250 112724928 112724947
    0xd0f050c071e2301150605030402060307030603061d0105130507140a030605090a15020405060d0207050a022d010804020d0b04050f1006060314130809030a08030a05070e0607030203040e0c 82
    0x841d40d40c0346803c80c00540403440c00440c0c4024000c1c000500700355030100329120b14108000d0000d00008d00001e1080c41d000c030010700c5a40c442d901800040d50030280c01d010490704250303140d2a04c645903402072129403c082c005289000d0702200c0e1060f00307901c000140600c601d0240058541c03001e079011150300002d404400004240d443c007449025070b510402a01d401359a51400440d0f00c1c050f48403042d05070b401480700300402e07601c030300c142c0303840102001c40565108105e24082e8102a8400002076018441e42211310460000031248607227524008004d010b210496001520b500711300711402548103540740780600024003544442508603100728210740140b80400b41460800354a281546051982c4800410000340c1c180a8130002142000b060200741c1002c4241d11a20f05a000024145103000540741950b502c0412240054542054005841b820600c20b500042c1c202a51088002188000030510074a02001118400c584c990015817600340360500600c0b0ac84401040c0748240d279024080c4a44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 112727428 1250 112726178 112726193
    0x806120d0f121b081308040e0402010903020402070c03020906121e0307021e010f030209010206150319240c05030a270f050709060f0524040b0d0f050c071e 68
    0x4008020b4039035580c0c440c83d80001304000d030700a03c100c56002940c400e510202e541002150706035202309508016075501c50005942d450b40b80c2c0d00094120344005240c4082c040d0511500080d00e02c21a60b119068403032208000c807a120201c000710340c5403c04644604911450b29001e154102514160790500f0429000604510201c100f458404c082284001e5030759a40850a01b40f1020b29041c00c504109900d40007d41c1c55200414000c0108104007400d0001d0703400308648410005080352a00d140e1185181118503850381011080c03642d00e444400800d018103e0007003d69081455a4860031540c0380302d170340c401600c5d00841003001d61400029800c0111024416100e2090241041c60041d880a240552400d100e560107644d01c60b20b05841800003000d801044001c0751f4041fa0303520038001851941c0b00680f0201407103035070b240074001000241500000090710241400c40070030070030b49001e8004802903c4046980d0000c46400700300545c0080c1d807440d10310301c600148001881c40ba51a9996090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 112728678 1250 112727428 112727441
    0x51e0318070501121a062109060103030905090901091b0303120204080604030503040c05030109032c0303030a0c030204081e060a05070c02091e07030209030f0f0d111f0204060806120d0f12 82
    0x10301c180d50b20701407501c40d440d00c202801c8d000200e04005142030f62560300d004214020500805200700d1010011501103a425002501c6090700150800c000740e01d040e10007038025a0600c022400301e01d504080f0060310155100365001c071402007000e48025500d40c1d50464665200034022540c900460801181b961000d01c80c100030f061103038854180c8d807590b2051010b46000c0708000325000781100b01d060146501c2c0801a00e0b0040d120090104411140000a50107030045802021140c030540c009550148109403213555043c60403030a4072441d4660714074400507150100c0e54200402c64a041020041c100591840d6102e05103007200c84682c240402180b1000c0e03001e80742c2c800040d8010a1065080c5070030b100b0f114503400950000d18242e101d0580b85512884210800c800f400050008821403000600010781d6102030200c03030403014107095407018025002401050001180000058040e060580000d1440707010680207203040343c960002110f5800c103c4a84004011201400e103a00c140c0c1070103180c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 112729928 1250 112728678 112728697
    0x30b06010e0105312309090a02040e101103070207140f180a151a0711100c0606060e0616030320030402130207081801051e0318070501121a06 62
    0x888100c10082996581940d00b0181004141090b8a1800000500014207001c030544540000d40e1f1a03140d414104100c1c000d000e50028208440c080c9400008240a40c1d40b17aa544020401c0d514540c00030380c41800b048a001c00507a000ca40180b10350b01410500e581400001441341c0d03c18101600460040310b0400c010b9903400f0340b29428424000c03074a0059920008010950580070f42c078002c0c21880c81d1100303092100c1e84000000d403071414408a60401c7c0030011029001421811024800804c034100e0100150b4825107000e00200703881d40300d040a2203078040002e00d12030800d400c1407415606680508412801d169170303003044512040f2050800044400070625580d00e134a03290050051001c00560350341061881006428006900c41c0c0c10795010000e49280c911100d444040140c0341842034a80da500320450381202070102c244007600541c0310340303840040030310101500340342640c2c1c42e141ca00840e80424901451141c5034a52640040c2c02c900d107407140f03214072a002c030021030201d91100a44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 112731178 1250 112729928 112729987
    0x91606050a020d0810061101020f030c120a1802130b0a081e070614030c07050a0606060e01080103080a050904060506040f0501201e01090b070e1306030b06010e0105 72
    0x5801c1580d0103000044010703000341001101d40c540039403403004e1203840f80640000d00c01c0300800c8192080007541500c100b84104003640740d590802015011560300841080075220001400040707058156000b09400d4828580080707038a081550f00700218103604030040c8100503510011801141c0e180001c180050515101500407216620340ca207843c0d4001d10403010440c0d200c680c0401c0f445501000d14003400032498200c1d5240d440703090000c69144101c3c3c0740a0b0035807060711200000c3c000300f40d100c1401c0303030802d840d803640000f0b5050054420000034800a49030782402e00503030906a000b6001404003e6004100042d519221000200d040d007240e0000b6101d00c908201c14050755070025100340610248168125041504160603652940488202c0c08001d103454180082400700350440f00c0c002d5030085d07401c001860038003002440506844840b03840740d000301641d84110303555031045c60143e036085640300c60f50f561900c1c01540d140c40c070055114100041000ba4804880082140c1c074614107d030b880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 112732428 1250 112731178 112731187
    0xa0e0601090605041a07081323120a060b040e0f0604050c06070f0602090105040314010c0815010207091104030506040b0a0501090c0203030f04060609060306091407061709160605 78
    0x10a6111140c00000c1031040404c028440401048a4002c41810408000d039641005103402c02143c017400d0210082101c00d080d0100740c181e0108050800c2040603070007400c2d02109001002a9180070184042c615042803000d2004600d064111165100c40540003007142c2e907000c01c2d0107140008564541441d608808180820007405004806100c503049451600349082511030401c102c0032034100425042d0300056004c8540d01905c180c900030764010819038050725420308054040c18030907080c800021036000000d84880001e0f0410a04035406034011301e44103080066900003041289105020038005000c0080012420040300348568451b1006810505101603008103647d01a0060154641003540e4403036407581c004242c0b46c1c4544480e0541d40d0944490401400400b01c5400204405081280200a0001c2c503005240f2883c404c0c0c0c04c2d202e9030071304200300c251514040c2c024100024806080c60507084583c102c0035400c03d50140c00e4034181c0700307040500d00c0030303265640c850408102d0105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 112733678 1250 112732428 112732441
    0xd03110f1b1003090206190215010305100b060a090b030a020c01020a11070b04051f120c05090906060405030304122a03030f020d050417100c020c130b01080708060402090a0e 76
    0xc2d900d2618066070030207002e8070b191680050542d00076180f40c000c00c64030700d441c83e0188a01c07c000071030a140404800f010556140e003002c0351250030511080e28618286405030459003441002c407501480207917524907041e403d001c0440c508c1e90010304050b086a80070310044005540a10040441c4c580d079480d201c1c040302c00401e100f401c20000344e03c07542c0420000d210400068035803030680301c40b24244e034018010101080c0c0c4241d8502e011202c4000b82a841c11803503609049c0c0100c0104000c03c0102d504407125a580020444644220f000e080e4060b08240410015110020b4421f09090312403241ca10380003012060902504541c6031820050060112080041c19080620b59141e094544082c080b0501d020501905030702c1a4456078051182280d00f0a840c40414040901100c010700018010b08d0b060740b400035540c02c1c4110020744038440e074014402103103103d131090000604040e1241c0c50f4968441d07000b03440c007800c000c0090390800d030200005011607460040010280484030717001361060820b078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 112734928 1250 112733678 112733689
    0x417070801020f0a0e0102010e07030305040906050a080a060e031e070b0a0920011101020414010306050a0e060d0804030b130611070b01050f0613080703060c0c020d03110f1b 76
    0x1540100ca140c2d104102d020034041c40c000864000c4019814090046005140100d00404c01e40d0243c0c4100c2c00b40d89400310800d41e110307000b00212000f07594103100c80d6455000f000200202840b0baa1215401642013100041c100d401003103800b410001540d040079038502e03c1c1c4d03400256a101290742a0f90004049007001255242c043d00328001c4c017010000c42c0400c0d070b60640500008a648245441100c4454001d0303880f8100203100c00603420003d40d20307640c0d10030715120f01d948035a2200c0d020a041010103e00750500e86a00302c1102c0355505008070300d440d10010303c4407800c64402e041d6041e00e07003044080041030000c90198013458170514651840441800e000003242d0f41d603085100960020000310000c1002c00070101e0540d1403c6990108070242040040e20904c1921166810b000a0450000380203c0108620046a010390300600840c0d5201c103007202e0344480341d00001d6000d20110b0b510404030b4800d01c0e000c0420016841111604007400c0201b41c90700c160080c810700d50101d04034510a03d804d18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 112736178 1250 112734928 112734943
    0x7090905150d0f050c03030c160b12040303110f0f0a0206011e0608271b01090308030a02070c05040e0102070303060807050a031b03020d0b06011d0609010507050703080417 75
    0x219801e40c004507821000007007070ba00e4801400781c4403840882142050090502103040c440700300408407661100b4040802d9190408217404030b00e402d41c6010002001c10003113045910f00405042101107564a07035500380e00524810080301d552400900241c4101841400200942000d40c0c4041c0d4444410341c100a1070048141c010450044d00b03480c0d40401908011040d005a0341107051010840c2c1d01c2002469001c20b6010a204c0b20300e164070b080908900020481440c00041016240c17007030001344d0015100c2c0d866a200c001d0400c2e4013000021403661566001c1d0022a11078a5000031056a0340c0003e015510341e141c842506035400510041095094401d03c801000d0b960044c248092400c0001040c8224501c8003030b041804102e254403501c81d843c0002800b42d40c0c001c02441c4407486070300784a070401c1400c0f0384c010f0114180c1841c001d812480b031010000c0349100140760514010280c40115050303045480221540d200320304000c40040c200301d01810283c60048070f00301030f901001500914101e003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 112737428 1250 112736178 112736191
    0x2181201091712061009090e031303080712020f19020319030324080606010305040c03120807080702030702030703020f0a1a0a090b03090714150d05070f02010b0a090c0e03030307090905 81
    0x3c51166100280c6d8109500c6012243c80f00000910301c3e00b00b04c0700d41d082d03200702d1000409440e211031002c0200032011000e011400d000340d00004004401040503680c0c0c4c42c0c82a038403d441d502810841c001d0301e941001f5605000c1c405000d8610544000c1140c0000c420741e40b50450110361107084444100e068001d50500c4400c400550540103860a02019120b09001d44144e0406480b04000b0301802848c0b11844001e5500002c2c5008a0f4403070314000780407c4091340c20900191050000c1080d16100005460805400401a21803140303168200500441c16481d0550800c80141c00001c446c1a00448032542c03c100c10029a0b903540e0705000102000481e07000b030412014103205200962500041c440d050307031000d0b00e144440100381c2c40041d001f1440030703407201002000025840300c43e41c2c55802c482d00601c0300740c8440a4000600e001682a01c02e51161680c00110a402c00c01103441a41c0040c4800041418041e02c003601c028040380c1168001c484102c00303d4030020081040c1046803142560008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 112738678 1250 112737428 112737439
    0x60501030c02030f040e07020106030c0f080118051e10020a1d010c050615041103010303020c040501150e0607060b150c1606050a030c020f1608010b03010218120109171206 75
    0x1c513403001e028180664007454100002c80b100180165000750700c41005550000c540c40620b030750701ca0f4001c511303135560302490100b942080540105c07102505905280158040701604500100c5000d08801c080d0300301c0240c08900c1040181d010b8019644010f15079200c05a68407141e54100e50002080051040c060074100625401713034801098002c60b030075821600d50300c1d5500581000e840050080c120a48104002c00400000001017540018456292700410355092196030b98882140180c802c43d6041c00300890b581480030381481c5000001808540e01c1508001540014400491900307e45441c4205520000285130b202c1e80b4030400c83c0449c20891403070f4045002d414500300920a01403214000241512200c02507140c41c0248004c2c10381d000f8680440d0a1803040090400488003548542000e42d46805400402800c040c022076011220500b2000d0031004144280324500f84044c4204103155a40c00b02d0f500000c04003050129481d030b09100700750302d9681e412000072450740c001e81007500c510f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 112739928 1250 112738678 112738687
    0x60218280e0915180303280c0503061c0b040b0103031404080705010f0507050607120b0910030f14010203040501052e0306020c03040506070c1d0c042606040303060501030c0203 77
    0x1500020303e030740c10084403820700000b58640120829486452182610050001104010010705000d4840005072050060800901030814211007151911214000014010800642c00b81804038412a400c6c0d4130601c0e2a0b10102c507a1182403515409071011590350140000400505502c144a07078803500d10041007918080c5401d402540d24229445102d05001c0c81089a8400314002c1c404e98100e07680100a6a42c07074902448020312040c8a040040c0a081c50840b030f0383c019080401c0c1c080d10568118070340510042c00d5454a0041c0c404201c0c0445001c40000803401e2002028005540924440c40001c601030420056013480146400d003030030021142d904808207540c5110258100b142d4002000695a00003c00c006085200e9a000183c0181002034103000704800381c012042244ca80411040305444210815014890709aa40e00300e039400c180014040612030a011a00c5000100c84085120030900c2e06a4141802210150040303540c522041010f96018054001c0341181440a5441e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 112741178 1250 112739928 112739941
    0x20c0114030109091e0c03020310090302070902030603073605040510050402030c0301060b040f090501050d1103010609060605030f07020705030307080702120f0a050106090504030c060218280e 84
    0x11800305229500a8a855011080030f00c10311742100e6140c0c0001c1c0031070710070241903800c008503030000d1403100720b009220b2920010f80101543c03281d00b160369415805400c4852810800c0b002075040500b0f4982e043c080d25500044006001c950540449031800c45400c51040780705505080124a01110080c2c45c11b00c03040000044011500c198072515080000a89854032700100b454240c3ca40342042d059860b000c80821040c0c4000c001e4800c4410315220640a01d45521602e826501d0a12605400035030081840d00041c07821907078015055400307000041c48613a10703801c01d0140c450a9000802081c000014081c1e1841d42e5082c1e030341d021884dc00100030311072524000c01d64034400e20307a01800389140030480c45c003156a0704403202e205c600d012088482d9448d1084640b5120207082c0c10440700d940c41d0482c001a1001240580f034800c1d509034a807150010b21030f4a569020b98840300007a0200800400c6510380c1790b03510182100b4075000d6018041d0403d280a00710440c2d82900d4110a8030070044404000c80c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 112742428 1250 112741178 112741217
    0x1b190807030b10030207030c0b07120b041a01140d050708010503011407020c060c0c0301060305010509070e06010c0201050f0c0d020c18010e1b070614040c1d0a0c11010912020c01 78
    0xa00f1030302450300682e504c5540c1021644400b20044c02001440c588083c0020241e0040c491440c8103d0902d082003001c2d8600100411908001c1c415647d80500c2458a115517000349110540f400000040500c0c1c4103000e8461000c80e80219042070210751078400602c6103040c240314401c0e40508a010b0444c050821110103503540c2c03084c5424610480b80090400a00e8005000841c40d100c4081d000b4840c942e00c031315155000c3c01c411070380000c6a102d003840c000b807102010245075000d0441a19031100100c003d0b00111181e0340025840303c800681082401008070f8108003030441c0b240c05030f000c1c10802401c0c1e420420310b582400e55201030320300850014801282c0d41c215641c0c00440c3c2e00c030007980c46800c042540e2828010108042d110701c0c50b001c980441445c0b0b0608203849680700301004040e258680c10740d02c240702c08550030111580f01a41c00500c41b00d189600c14980a901414041d0b000e0a5609001d401d4400200b401c44542c1070641030101f5183e010801e4203c0c001d0242420781d20741104d440d41c400c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 112743678 1250 112742428 112742449
    0xc0905090a020705070b03072705010309030c23120a1b020102010605030a06020403110901060f0c020a080706021c0203030c0d090f060f09140102030606040e1b190807030b 75
    0x380315061040c00300c0c0a44205034119600c0e41d501400b95000c141d656008640aa002251090086000143d98a81c1c41c081c41c2103015000c208060343e00221418640114010f20001004a050003c0c0c9200c03800400d0780703103201c0e0083d0b0b13003415000546204000700460600011005c4401c6400091011100454000401c1c2c131988442e860001d410504500040380905034030b601064150161640a10500046400420590780941101d04103000703403400340402240c091186000203031003c0b8a14001512401201c0034043c0010140f41107a615040190700301419603100381c025a112407014429503140c801d081c480ca840340d0002d1400c52405002446082c411113170100f109076a01c024100c100079500c0a01d24046400410410116180619280080140c11000c0e100b24040642484c00c110050080368898040504040c0c1054030307103d00c3d6440c601e000b4181c1103048a41c49550003500003240c0240103038501019403080108481d23140a00100f07005013055080500b40b650604040c0c40e03244000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 112744928 1250 112743678 112743689
    0x20f04150b0c100c08090c0307030b0606090d020a060f0e030109020a0e07020f03030a0c020f060408250512030609010b070b1602010b0a06081006110705061c020d1b02010c09 76
    0x80356101441c2203420300f00b059200080c921180360990420401e9070140310203120b143c000084480c02c40c0c1980406540319030f2840010174240b80500021900e041c148040c0603401405030034501049017943c00160b18005c60b812000001c0c80710b500240c00140c0c401004c03a103949082e40200031110241d0003084418420b405100c5009040c507000c1a0180e00c02c00c207010402000703400703076510390900d1100b0300c001e0042c1851410062007901d0007540505400702d4080d0080364007240d40d52400c070b03010b89460780e030300c00b1801451603104400e12803001082052190320081035200c210345a40745000740c2040700d00101138001c49001e940912400380080c22007400e01703030444030316031340800d07260f48030780049001d8107003002010380200b201d076000030711030f43c000e0301641c0a660301c5854101126180d000031640d9820004a49110754801c80341007086082c0f20000300707040f14440c406010311560250030441030b41d1299401c090490740e14950454a40c1c0c82c3e401c040381c4001148000c0c00941e40d0140c0041001c2076a000c1c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 112746178 1250 112744928 112744949
    0x50c070f0c170c0103050703380303040906050405010806070c0209061c03090905070507030e0f01180305060106142703030c10061404020a080103030f0c081204020f0415 74
    0x41418031104150007402042d20b000b4040c02d20350503001081d20340c481c04020b01d000c2030816011440180c000d020311402211900ca410100e4813400d440c840307046030f50840c88010211950b0360405a9101813000380040c0208820201d50127142009000c03c03141c059000c56a01d8020109100c06e55a0003030b80140101d804442d2222140c640a00107203080c14803004010780003c1080c804002c00d908a0b080c40100c440d2140100b10a81c0c07040e400b580c1c1849081d000500144076092144614540383d200c0403004007040c50822140044184041070b0355607da00281d03441d50000004000300b581c055040d483c04482c0c0d1029a050110f214555544503a488011a82c941c6051420091a4504000740d90203c1224811500c6146101203840010b03c0d02e03000700703410305e03225040082c45030510b07000b22554159940d84030003940e0701e992800c0766603500c0c40c04260100b0161358640b10200d4410005001420101881d41090342080d1040003892001166594042c5003060928070b142c140700d00300d420448410981 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 112747428 1250 112746178 112746203
    0x909010e06041401060815030d0e041a0a03050703050d090e060909010e1902040b090105090708070e1905010320030705160507080a05120304080414040905010e010f0f050c07 76
    0x1030054607076a07401811984003c000010555405032003240200c0714504541c0410b0004010303d6129500c0d0500f00f0082041c4641c110001d09080c0c1c0030018542d040f00210140303040403c00a102c04a65038800c2c5e40680c8019014000e000d414880324401042905180c0301041c54403036a031010040042c07a09200c0d0549000280d20854290080009440e05106851020000c0d03c02c4004d6400801d01c1a401186000c0c035503126800e0010400e8142c80d8028a031001c680c1c2d50b0740701280d51400c0140410108410030141600340d481d654500d48410704002241080c042c10b02d0001030445e06d00e2100030850640c1950020b61001070201169000718492406a0f0769201d1030851900156054800402034411a4000147c151010950042207072103481603c441110340249003070140820344000e0541807081104001205d101806404030410103007001c00c1c25549a1506070844000100c0d0b100b05944401001c50154051708c91b02c04d01d80d511550070069400c00440041c4640140507000b00260315a85 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 112748678 1250 112747428 112747441
    0x13090501090204090309080106090e1018050a03050a0e01021603030e0d02090c040501020123150a1707080c01170103061a03030711040c030212040210050d15080d0201020909010e 78
    0x401000d031481c2c0240040c00000da86240c014610919480391051552a02034082803030a80c6001d0300c40d5503c0c9200c0241a010341502d1890024140407119046606140c0d10f080700058082c000803010301c1c02510380d5521255014400b4200886c40800d041c11500228130350003160000708002029650107152203014010300d04c002c13030740340c242d04800031703600554150801450100d13142c020300a544083c2d0082c0528030b170382e4074840a413001c071031f00f840f01d2400740e4000078108440ba00c0d009a01c0c240e0050442c241c007907850f161a0f41141c070a1059000d2134202d0307a0309000c4410b0821440400360743c20f1038100b25108054403e00c06101d018040104003546641210140510000c0d2114030b030000141580d0b611260791500f00d41070600a510a4015400c2520030030724113010b0710a5624240d0b0499030000c0d6940c4036400c21203140841601d4005101d414402d01c803140740325204000408502001c15209030381040c1c041c0e841c1c084c91013912021a0f0040112181c40c0d101c214465045a1400d0a900125203841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 112749928 1250 112748678 112748681
    0x1151d040b07050904020d06080c032e02040905040f03110d0f03020f04030816030815060a030203060102120d0c0207240804170307030501211709061605070608100513090501 76
    0x130741c0c1303240d0180c0082071700e12038100194000030031104030400700c80c0000395040a041d11a2501c20000031920301076569820b64903a96025120020b81c0392000515264456076580700310385003598240c030905c91140c551010550040304802d41d020807034009201da070b040c2c40c00050008480069030001c00d40c02241c00c2094040c0c1c0f4003941c0155034001226070b00c0382d400c1e01004617007441138502039001980c3e0a01241e010044503200681c45103001e0445890402c0100d010360107948040c221038110f126107500c90404600b03030300261184034074807040450400c2d114440245424820307007220510100c0c4e1140d44035400700080710894105001e08051403507039103d0414220625408a420040b03410010800c004a035169001c01c3c1660210020801c1c01000e00d0711000000c0c0ea1403070014452109400030700c0351254001d024019118000b4000b524041d05007140324828031200b0005c590701e9110000500c0282d4215000701e900200e00da600d00601c40c9400002410001c10181c52000566074008010602c14203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 112751178 1250 112749928 112749937
    0x609010302280320030103020d02010c1506090f0609020c0303060f0105130305100c05190503100f120311031204020108070908030c0c0f0114091201060e01060201151d040b0705 77
    0x500c2c1080c044400300d00041d0141c075441d05000c030224075080401c02200c40d4441628140ca4000e8001d119004645c2d0040d03070070045680054980c0945800b41d1a91014140035200141c008a03801040705c00141107500251015038200703030380140c014070280c1c520500000035030380c0c403000c110303048030500304c1c8500160b50300e01c5a00d20100f440b11451700080140100014442089180c80d501007003071286c141030440703250044200600054195520f20001644548003660b04a000d0850104419542c0d24010307003000c011340d00440740a400100b00d0310901d500200650461101440910300c0c080c41641e850040800003800203060085440c0403da03094481d48400010740509402c8070b64648141480d42d945820140780b4910805c08001e414a9079442003082941b45809080024145a60001001003428080385141583e6507143e50003e035512084103028000c4c000741e00005600d21030b00c1030040f04c01c950307504008441c52020410001c4809035045040d800368000d400b034885a201c02900701e480e44075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 112752428 1250 112751178 112751227
    0x1009051e010c02030a0b0609100b07031409120c03010506040629160609050f1b06071a0403080106030e0102130302060313052416021c020a020a091e0603020609010302 73
    0x14a080007010071070084042c0b1f0007004100d03244610395450510100c3d180465000d596030700b05042c05001c3c00240940b6199001c540705a504a06001c96040492a221585804246154426103c5403001e003800e200322500400c0c195424017159041051104007203c41850021076408040c8065903000f040105135028118441c10102880c401ca0620001074000c0010607034441c092246034003a00c2c00005030403003c4140c1e044030608125562000c0055a4000481c2030303580e032038183c085505042c2045503591140744030f81c0b203d40c11941001c200a00b12000700000340c030644e104010400600c110102140c1c1100da0484465550383e8a060071601403482e41880244648507002e40340156241032180e004140d000411120003941d42c801e200c812490705d007060b10000d60001900c01078084010183c0c010307280281d0040380c03984216a4003241e04000243c2c00b0f00c41e5203581c0e80d501b019a05032003140364006495400240402c6080d900064101c0c45920308076414550300003041c01075060038500b12840c40c40c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 112753678 1250 112752428 112752433
    0x2303070602040e16030b0102190507030204090503030f010b07080301050609060903010e010204050301110915070c0b0c01060f0603051e090109063603020c041512050c1009051e010c0203 81
    0x5070b0b6500b0407542c00344180d031304500407600700055054107031103031191407400c060580c0141502407010901003030300700703c9100640d458000c4400c00301c00340e2128040c40300064820b02c001c60340d92500b001d000c030540e403068200c190340004c1040740c4000708820b001503d056900c01c40c1c003d6a02d0348100001380d500d118411410b40c0550038004030030368210b419030160080f05c6081e070084c04548201182070f0060b216500d050b80e805242c200c2c3c428180d14800001d040281d100e02c50010010340ca40d8802030594005600d280216916000705102c40c0061005072401400d45080038400b5091000c600300d5240810100c01c201d800c2c02d0400035a01031002d403c5000c0382d40c0c100104219240301075041003049040d012115500344407410081854050b480e04000729581c040c0d029101c6c0181041c00c10002d08100c5203505484d0046c8000825950120740710001e038984908001e0030022030079414032400c050301d40d44450901420f46010009602c0b1500300340c01200b0352a103136032006524180140d94040f120340c4044d4161 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 112754928 1250 112753678 112753687
    0x905100609050a0209060d09060e030d0b01090b0a0509010c0606120b040c0806040b0c0307030f0c0c05070603050105060d02070c0308030708040519120503060102010608100603060b0402072303070602 87
    0x41449034410001e54481c0c0ca0180495911202d081e0160303c280071200390007141c10000f00040080300c1c2d012400c031034407070340340801c1e96580710101034a035801c45130b15802055a00d803241141d942e00050760350014107424001700d00303042e00c106003d0654013800c90300c00c0c1409240600302040011a43c040c0010b03119906404d0309030001400c0800e01c0101c1101c0444000400c1d043c04220b80d64000f4006101e181c4c442990b02c0141c3d1100b201545a8002412400505403180c0014a11030fa1a000b900d4a401d50307590f641803040c1d81c0e41440d500e0130366941d0100044c9407420005115944960081f1400c034019007001607683c00141c909061904210b91015000703450100070b100800703502c400114000d03801802118500c91030074448400d40070341c0c15001000018585014883c4500031400f460348090b05000006180356118541c600380f1000c01256131803140d540303000f8001c00a06220b0140101c40640d000c40c03e140305940c0c3c0640d0746008805000c5007100d800b00c20042a43d00300122290150b000e9015500d9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 112756178 1250 112754928 112754953
    0x606020708060c070203191a130b0f04020108011406070512070c08010204060f03050408070b01030602030916030c060503250c0605070c020a05100203040b0c030301030c0f03030f080a0905 82
    0x3205441d0203034402500556010070000529501a074000c250020003074010400300070800c4803185100d05084410380c50751407210500d0b00c08903504034032413010385042c4080c0240c175142011304800001d107640d01c48034052040c000941d074404041410344101400c500014804040020780380e0040c000000c0080c42110340d00d900070788003072001d0040c080c45041c0c98410745454590320f9081c2d00bd2030080c0800a0064120481c8803807080e0001078000b4056a1050f00d081d040c0e89421001d078a09030010389541d9000414081d00d040d040101c1888033030384074250144107003141d440c11400350304c92060204120b404000314010b010300a0001080078130f6400b032405a402e1104010f010894180c07403d03501d0a1401001402e0240181e41c08001c450b8001c016403061402d001c10825540301c0049000304610080c8004900040014000d0201207002c03401507440358035605e40b030315124407142c00444400c0c2c2c03801d0082000981008000b0460b0107107007404c09290f0307039000008004101900c0702914501c0b441c15400e50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 112757428 1250 112756178 112756183
    0xe060109060e01060f050901051303050d08040c14031510080a0c030302070605041412120a090e010803041a0a020a020607030f11010509120c1219110a020607061a04060602 75
    0x1110302c07452060503160703030302c00c1c0588196101e00068000300b002000181c010758400c000a114a8940d545000603c42c0c403901c8a6203048103188201d004118030034180024032280c5e40150000b8075403024044030007280040800d484200450b840c1c2c10780082100424040541c5810031405070000300d003192160082d5041032400c8845900c01580540039140012aa0501c12412101a200c0700c1c59001d036840c0d0311406100082d03280c44400b01c52400340c41a1945505004001410140c96a503288805503040044494000c034069000c402c1075071080100700a108051040312600b4038003d042c060302c403004604141e0420602c11002940450001411030415401c540707401e201703582942d04d42c642081036562443c202c82c81601c40e8182c542c0700010b400c1d11240f1042c010540140d4960a50704801d03a60300f018400e5802c5451809089450003010741c112541c402104d40030216814010152407040741c020404503c1503440c094122a03c3d001140d00c5541c0000113403052940180041002d00e660b094001e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 112758678 1250 112757428 112757441
    0xf020703050a0e09060f060c07030b07030b03070e090a02091b0301090c030e012703020c06030112030810210609050d020106140303072a0b0a080105041103040f060507030e060109 78
    0xd010078840001882d00d804d00c1203074148100b0740034103c03000d007956510030081c50b42c1100c00442317082e21440c0c20120000e201c8442c800e00600c01501c1c0440e04807818820141001502e4102140601407401004600c184c00104480f541760180da89844588031280f640d080c019010041d028201c40010000604140582c0202c407420b6059408212040075090210700340c401c940880d102419440081055802011a1034800c051180c011607034034041d04000b003029900246c0c8954980340b0f0a46120b010326030010388255000c41c000c4408600c05080805031880e240b4040100400078070081c942200b005026448525003d030420700300d961801d960300c4003d0180c80540140d0b031118904413280781c114203000003529040d0398004504000140880e07030310042c255603180c0086060228180003e00011040c006050303d00e45941c516803290f0401741031005440701c902d401d9002c500304104100c0031811011a10754144d50003100032440d6118600e049002c3c1c0346070100703405680201d03000090740280550006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 112759928 1250 112758678 112758697
    0xa0b07080a1d030a0303020d0e06040c0e01080d020a0f03030209042d020403080d051f09020c060f010308090409030e0a0b03091504080d0905030f04060509010816020c0f040f02070305 80
    0x303002c50b14480e0020141c400003002e141e0182d0001d496000024040c4d00a40304441380a8000074401e08042c003c0c602d81501030303505032540f0074903403018882c1c0480c12000c18050308180e0010005000c48002c000d503503d8400d180036207200014070000303040510075011581c030783c10000e1083c8020407a90446001e201c140e00c6a8110415040c07200d502000c1c014000e48085030340005400d070801c85542508000b802c0001c1c009090380030261515004c0241c1e01e00b00c0e101030030100b0401038407411401c00e201c0c0b4000c0090102c4040a0101c00100002a01503048504910040c5c0c0c3c04620b4000d1442c06070ae008880b20290381e4010740c8210081a622400d5000d184103549940c100ca14130329034032121031800e110a69014000c000100010740058070a900944100f0b880b034800c40f86131103a0b4010a03105a0095005400007413800900e441140d80d11000454204c4c2c80030048400d00d040902003e03582e501071005150003010703105056141070755907510480b01c90302442c00035541c80c501407400415581c0280801c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 112761178 1250 112759928 112759937
    0x5070e09100b0a060f0e0307090921030b0a12050f070602030d060e0403051b100f02030114031615090902070f02030618060103030503042901081e1b0a0b07080a 70
    0x4901d00b51810020100403039407180c840c94500b80c0800c0044403100019a81e03650148500400025544283e2040340304880c09481c3c445102d840101c038954205021246135070405080940c035000607030701d4500b202c1c100c5842100310515641603203007582c103040c4080724034802c44c018881d0000f4469008001003100f440b040004003d03d584820f9881004041558040c0c0001c03030a00100d0500101d0900304c2c1c252100c039004555400d82c40e40d910300300303858120034540322850300800108414617281c81c043c0c5402c0341c1100a024020b0100e4032500c0c814004d4420000f10043c1c61001d8031683e0f008040d00005407007103c0046d5518113450910882c02c81a140b4100c2c06403049000103003080e540d81280700c108000d00760103022103910750f440032906500040c000b5034080103168440701134402d40250581003001102091030381585001d04041c100228080c90010070898102d00c600188400326641e0751403060b80e907441c036582c8001804954580307103680200c94a4100012080180f01c4c6282c043c01d4a82c5c0e20f80d44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 112762428 1250 112761178 112761191
    0xc0909060901110f0306060a050706051e010e0402010206040b071403040609050c06040f050607170732030702091005030703140c2b03030e010914010c0906090605030405070e0910 78
    0x480c5119842038091302d5415400038004155549006030040000300b041f4607106080401c0c0b51203210440c0c1e41520f07c02e04402030302200198800411100034014403d1544041003441c01da00013075201c0000500c000c140c0e01d4034800140c003542c01400424442c2400c0340d841500c0b4649407514000420300c061007540c0c3e51181321a0380d502807a020f0200d80681c0c40c8641c4406105107032805001c400e4002c16404c50300403100561516801e40c80c6c002902049000c1c0c40c08809603800089520020280f00d44080d40c0b0007400180c1c0a1400000170840d041681c0c140c6035500d03541d603030064408134002603030411a494080d4100000c03d1110301c070f8100980603c103c09031010000014104038199580c0c0c1015800c0c03003042400c1c000341070b80c005001c4603050b000c3e04010400d44048030702c0c1401c441d9071160480e0140e040040806444400341f1850100d00e90340e0500340c10090601c2d40c05850019244200020000000006000c1000500410001f400c90307810090107810808019601d0704084c10340c8041103031900c1c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 112763678 1250 112762428 112762451
    0xc0a02030106120309060c0501061a1c0b0604050d060e0f060703060e0618150303040801090c050607020d0807051c030606020f15012c040503030106080f010302090c0c0c0909060901 79
    0x444109440d40e05071039035175009140c16070980d80582d0240082d6040d550700c110004515503503400e08408044003455003990f07082008081200c0f501040c030740b140740c107107850880301043d107811003150240c800461300d0031401c1d002840e01344064107020942290502941611180c4444c0000340a4011052910140003081d252540144040c1007101c510f0740c0415405440a801c1065030360070b60704400360f00d4001c00f00b00c0309440441d144d0b5003d41e004406907951344841c0c100340aa00d0700c144014002c1203492916100181c0c0009600c1900800080c003100d1001510764108030041101000009510540c942c3e40112201e002e001020301d03100d0300c0050301030b00b108a04198001304501008552180d284441ca07400c0c1318040600c1c42600c3d0130085180b62040f102c01c00091181946031103184104000e664075030510030000c085040182003109105103150060005903500c000c82548060b040c06815210403c0c0c08040e03240050200b4000d030051028002e224400d040416001e10842401009001940c000c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 112764928 1250 112763678 112763699
    0xf052506360206030610170405061501020613060b0102190506061f0815030f100c0e01020319031a090a0c02010b0a080601120501060f0f0305100209010c1b0b0c0a02030106 75
    0x542000f94000003c0000901c40c2c500580d183c80ca26000d8540310400303451411010b840c10500baa01915991300000c2003100d0700e240503c8446c810007080c4042e00150030040f50b046000740070550010441e45c0c90701d840813030591007000103c0d0041040040d8402a1185050058883c2e00645070240900d80c13800d903080b60003084600b103070380d481203560f0380c0704c059542c9a10b081800c070510b086003a03040c090340700d14900c01c140801000b814840040f0000821002d07500014101401d00b02101e4150b420600003071250f200000c01c0104c1c0000103050204804590020b940000b04c3c0003c03066a101007804140702c0c03038240c1a03100980f03540c6107030003c1105d190f154040110700e6a80d44540d2900c1d500100044c00700f51b040298002025101d10f00124101d52582d012503000c1c036440c0c10014800c0e424440030002d2000400c1283c088208030013085203801b0031f58000030046286284040c10004440011400180c2c1c00d112900041507485012a240e1400502050b101c4202c018281d101c1c3d82001e40202d110500b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 112766178 1250 112764928 112765031
    0xc12050402010c0605060402041502070509060102121207050d0e0c030c0405090c010e0607050102161205030103150c020a0602040b041d090712030e04060311030d0f052506 75
    0x50f100c0b2032491091369200c1001d4140281616003141d000c0c04001000d40c2a00c500c03045175112038024001745400c1005100c10880000c000ba411980720002540880c11844120788041c203c4500035060381d40e9681007658035100d02c007040798420b858446e201448442c0450560512003088054452110016040000341c1c0c43c02d9503040c00079003200101c40c4456010b03410303d90244201900482c1000d5554070b842e42281c01666101068207174200d1014100220303c000b00e5203a41003030500500319415a15440710388c4070342c050040308150751582004000780c000c0208081003544204155981c51b10307480861020340040c032030700608240d018688880310000c44203162107541040000c01c180c0307140c12003190403110303007801c1034040c8228507024104a0f2120700444006d0b6008801c0c007842400c00c1403d00d850440c14800200400c0f510745220040c056000d070883e0040f1001c04142c040034141350f521846d61441c00d4400501c150300d000084280341c0035080aa03551517030072540300f00707800c510801d00701c1d400400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 112767428 1250 112766178 112766183
    0x120605060415021905010c0915050a0c020f09100501110a080d1e0504080403120f0801051302280314010f030215090d050604020906040908030f15090a0c120504 70
    0x4144400d01c815400314120105150300303031040380d03451301080c4a00c007103070540007000b0b40300780e51202911500c1c181c004d03418400612040c5010344c410317030550030010501d01641680038100040c0030500019552541c8259800e000002c0010880d4104034904861982c154850136001c28102800b4442c0e01304003180c202c20598101102d0f82c03800300024212002008140103415a50030b2900d0081e010560510130f1070b00c12441075060f44d07038590960400c0751401360080405001c0040042180b18141d6010f00c0f807a04450017a14109190580501408081d0252541c0b00d001d0015107d411051078035136500c0c144018210391020408080c00791504411501c00b409014142e03400e090b020401800c0451148210b4000551500e00f030058030300000701b24250321582600c26070312039000d000c2945455800c2a0704000708550401c5428429600e40d280c80c0030007450020410015400101d4a0103980399603404810f004102404a1820079145c1004284520700c403c0001c1c00c01075400c165800314421140520f4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 112768678 1250 112767428 112767439
    0x60601090305061f03050717012d0903140a09030c06030c020615030c0612060406050a05031207020414010602100e03030c1c0608010203100518060f060a0201140412120605 75
    0xd90f0052401c0c102000899104c03074482c036120380003020500510514000d0040c03034510709402c040b4035042c1800c1d502e4a09201003d0301d14100420481044400004014040480d000c00c58141904040e203030380d124484002c0c03a842e000a20b4580c55a401025201075070720882c0302c1c503180e5864090807001c81f0310505003500542d100901040480745d1419074580888401001c80b03808100000c04103900fa0064108941c00d00c00c0360b8284020b41c641401024090b01003641c20450251038807000a46c2d03505441c80e50b902074000010280299241c64011041c01010080180700950b07544500960b030382d881d040303a0104240340c1503e1814003540071040340d0041200400484c10102c0e000280400304511041075181d01c0c0e503440b00099041c0082c000f0b584a0640c680e82d624280c2d02c3c0ca001d108020303544078400010060380f00208242591440f403a40c0b0103e906841a985503d1542c0007039004007600b4441010307010f030000802c4108107004034100041d0f4459a201e03540079110f21041c8050b00c645001d841d900c01d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 112769784 1106 112768678 112768681
    0x90301092d150b0402090d0302060115020106150806010309060c090f0e010b120408040314010b0f090702070b0a0909020f0a08011d01050d03121a0306060109030506 72
    0x740d000c41c4a0604890456540c1d0000c00401207038200c00baa0750b4011115252160350544030400009040480301901505020356510003d21401061820840d00c0504051060195408a03100401c0c05521408000c0701600e01c0308008103154109550b41400c8008030301c50340180b40b030144013034503003003142400c091007400c2c4144140c0200117061a454010840000c01c40b08038cc0d03214524040c611100d441314541000240b0503a4005043d50f204202003140028040d4031030200700400322200c0c5121201041400080041211400c0c0076802600040000e44450002420741e141c8901c0c0014085031241507800c1240c020b00c5104004050205a24480365086001c20380035100d44034544c03038501c0e0680410381c8554014080d16006209811510040501031f070404115244281024482d039140401c640081c8100d00744030074070900c145030110343c10b1b5000d4003001007a43e4211011b01000d = true := by decide +kernel

theorem cover : BRFrame.Cov 112589928 112769784 := by
  have h0 := BRFrame.cov_init 112589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 112589928 ≤ n) (h2 : n < 112769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
