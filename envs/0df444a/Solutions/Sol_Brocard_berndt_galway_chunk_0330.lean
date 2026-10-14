-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:15:13.482622+00:00
-- url     : https://prove2.me/submissions/3aff0af3-6729-4215-8902-f299c42ddda7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 59172665 ≤ n < 59352521 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 59173915 1250 59172665 59172667
    0x2001080f09030f0304080a08100605041211040908070b09030301030b0406020901021f0207050f030307020a03050f040f0303030204030308150307050112021605010b0901120c0501110a0c030501050a0b060403020303040308 96
    0xc140740700c2e16503c03400b040c1c460b0060001c4200000c202c0e00c03900410413111150348080c0143c403000c42749200900c680c0148000325500340018000d010111902e000c0043c040c0040c880f07480c1c44a40801d0440f0704582c000d5556040c0041c071542489016989550044031010046180d5891616039290340d41c000390000b000b4279000a00c02440d0f81c4200290b060300400c282102c0402001d007020035000b588020307000ca51030b0082041543c400f0302d0120960340b040301d00d6000b40c400c6ca201503030115010792200c04100b0f49000140404900c030080c00121501951203500c0069a450641c1400352102c040127015500c00d044000b4040800d841c0400c103a4215502800c20480e0494514000c2d8040e0142c411a566400980810300b03003404015081000015825904255180d885108038581010000c0d8050080c500c100810044c80d40301c0c0401600c902010816507078004510765407040d1050306641b007075178580c2d1142c2c24062914060b2103203640e07a000c12031324203251a207144d0102c0d807a8011448050461a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 59175165 1250 59173915 59173921
    0x606041107050d050301090e03090f040e1c020102030a050a0218040e010902040504080a0906020328050903060405061909020102120a0905100305040312020901020a1b0803040603092001080f 83
    0x2030031030150752545901c00140c2c0c0069100400082558001344240c0307403030030704140144607030100c00720403201c41c0303000600078146500280c0c00740030142ca01105a285544600c00c0003440003600400d5680342c7c03128590000d6076a040041c50503080d14006003580484510400030740410143c480300590305a542500d012074480c0c0ea808c00603004103140200a5002030a103001c0000f0000320740300500308c16076103032602c0e600552549000c0382d0301c0c080d2080e89019104000390f0110303025942c20701200d0803c003500d001403510b2050b002190501d40706403411529070780404148080301c02481c05a0f1001607001100f081100c0741600000d54070071044900e1144102c0008114400310f2248820501900e005400c680c20351074820001402072204039070036400a1100d950420034000e8034000c54029810580c0102031820054844c03811400c1010f4035800c1a04020b60b001803195420b001400040405481c002009102d50401c1d2230828500710b5411504917841c1c1003460107a17005200c1b10f410402207062301c8000c0d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 59176415 1250 59175165 59175191
    0x7081605011b0219090f0e1204060504030b060a180509070e070c14070b0c15070806090606180a06020d1806050f0f0403050a081b0d08060d02010306051f0f0e0102060604 74
    0x21a40c001c0417003a420710445524410b550b42103490341018110841d60140341c8100d07084c00c240550302440d40000c0c030800081000c0f41144200d02d40044008054200e40c40d603824039500344c0402541042d400c50b480b2810024105028007684000b0b02046542d10308034a4410802420800400801803085117003450040b5442d400300040e001412020041d10368441d01a21195a15403050b200c500c203450781d0400061a2601c5040c81e1402821b000c2c03c600d0842d2246410041c25411a02220001d42d144041c03116007aa900311202c00100125000390407504503841008001200303600102030103002042003000008d50003001c884540b461041d52984030080e02d400320304203120b10350000e090b61048003800d45c184540003000b014205403040c3d0074240150740c001c5542d00d0310940c50707211000c9107201002400c03c2c2003003c80c00048501c14540017541585500000e0340480d0b42c40401030b07045508990819055400c2915800a03102505081510b0520b000c0000d5031400d005105900035920750171192220 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 59177665 1250 59176415 59176459
    0x41506030210031a0d050114071803020402030402010c06050f090c0d152a1d030109050a200d05070302010f020601030c03032f010c0210020f0405061b07081605011b02 73
    0x7850003005c0040e0b540341c50405030b0180c40140e400e120b00f51282c101040ca042c1c014268a500a100e90702100300c442c2c07841d02040001e400c010400d0b41800741d900461000580c5074800c0c03e21603803d0b40c040401c075042407004207280a0401c0925401008000045008174112051510310b0300703071115012070b08194000c4a0402004c4640c001c46c01d0565005c0e16500c1960400c0c5016124421094030210401081d0100360a98442c10000750481d048082204003081d4841d0342e0b030815032480300c148405000c0c2c10011455030940c10505513415040311006004540e4841c41c000b204e00500d01c024411035045890314000082c16100080911480440b520f0131501c002106120fa68001000a20300713543d000c1d6170700c2c060101000c031400140101103040705149800d00c29640c0c40d483c3c10100714140f50401051012a50000c0010700b4003d01401c61411071903002c200d07500152101700042e11080340d02c0f10085480300b989400c03890510104840100032a42e0b050f10420b00650100da01400101848150300c3ca0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 59178915 1250 59177665 59177711
    0xa170406090215120c040312030b01050405060406030509010f0608071403100c0201050403020f030309070b21011211030312040305160209090d080a110a0507060212040b04150603021003 81
    0x540d001c0316424030042c0b901c050134528410b020198020b50303811032000c0f0303688100d000080c2810000e20307000d50501c0c803da1000e0303846c0c030060404924150f160000150075070410391040d40082e49840070010788503801e01a10381c51480e540002d11140b810032000039220813080c00f400007600c0c400c0c8000c0c0704550f4100440da500b9494001c04110b80164000d000b806400704440540240c80f440c010001d540a00104692044010700d0103820901d080c0340443e0529400110109a029010365180c2820500000c1c441c5c001c10b40d040c4110b112002d10b283c4200848a108031591094105018908902c13041001169000354146845a40d41ea601203015001c0d5a0124000c1d4020b081c81c0f0400085c40c0c80040c03000c040120315100d0200a0352001303400010369129282c0507640c0d500a110482c007040c002c8014155080c030400e005414039040c0c140540100c90119026074400006009100a0000208001c603540384450414070000341150045480c42c081d108054040580d1250882c0f6409030700804089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 59180165 1250 59178915 59178919
    0xa0207030c0902070b1305031e070b0106091503021201060309020103090b04080417031305090423060402100302180618040216050d0801080601090906020c0a030c03090b0a1704060902 80
    0x10314907190381011000350004e83c03044422100000204480e036031501c0283d00c1b0345901000551814844140c812401c2c01c0ca070882040c68076003407154074002146070607001d0107044982e580c0032039035250071880d000001c1c10504c10b00034948104610b0125524031581a8159406810301194010301c1f44012002003240c200050f02e40780b442418402000440c000a008a42c07401c0941401c0c40c1d5580c0c24503407a849862a04800904400002c005504104896541c40740c0103643c030b801c1d400800480340c00c4110803503400c441c4a0b00003000708003c41c5810b1908000d06c1a45180840c00c200c23081d21801400421040801d00c100c002003061462150718030185c00380001c1c054415034450000d6410145c02c01803100040b01c20380185540d4103078491260f034115040f1b51134400200116407a0645250050110359000d840d42034080140e0042100100b046c00340280c4a0b5444003030074500d500303006141c58442c0d000001c04030810481280c515500c1144c0c40c0c01c0501c0030801d0881c54813a40303400401890507070741c025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 59181415 1250 59180165 59180183
    0xd2c0f060d090c0f140f060f040305070f0609140919020a02010501031e0305040303030e01022701030e0313030201030e030c01060b04080606090c07060207110603100602010b030f030405060a020703 86
    0x448521016001904060f20524150000750740341c0d501c4c000c0c00c003203900a00d11014810780314200c00740713000c0040c550700100140c0018a050500c00c070b5424580d1181d0000d8031650310040003008a400c0c080109001440b491605600d65820b2050204001020b01c25481c401e14400c404103028000c0341c101d40c08400780b415003c555442c26054003034080e2400744000d841c40030760b498410000740300c102d0311200a0b0781d266862900d018110754042d401044036640c4500c2542d424000000e418144040d401a90003c51f8201e007602c080b441c00050548188078401d90386504207020300c25910716054001d8040e42c0e42406c001c00c0351a00000320f00c0c46d41c05645c40b0800c082d820110005418a8508024000c2d42e0840b005c1e1070241e5914414405075400a455040705070008214140214000e5400341c86220311800e425101030b12508001080c45d002a00c60700c00c0c03a003441200f000119024441c0e003172512800c0e00a00740c20700c2807000b40ea80701d003c1c4c0d11030140610800600d02d40c290344244030b80000355038414540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 59182665 1250 59181415 59181427
    0xc0e0711071508090c09160e03060406060302090a15051002100c08040c060302030402090f0406021207050919050307050103150b03010b12062d0609031c020d2c0f06 72
    0xc1d0b2a85a100c450840030440304000716151500104424100d0400940011a5611800c01c1201c0700100c2000322010044010154030484d0303028850310340a03c3c040d120203d05c550840c010001c064001805205031542303010107070004101340b00240000c5542c100c0d00b455000b40b8a40e000e03410452010541d032005880c1040f06003e20713800502040c0207500551074003c0f615100c0c442035080f4813094802a6104014a000988a4003107000681d40725105a50150801d840d030034114420340410b41c1c110340401c20101d142101d40c03d100021100c100c1c00c001c00400650321702400300f504c0d040603000e10340c109911200ca050064102100040003440d0216401d6600e603951321421441d5006079480b200e41940e420042111841d1041d01508101015041403841d00e6504002c900c030940345102480e00074500340305144c10b0342d0b401d011804900c0500001c116900040180c000c3c00c001203401c40070305221605500c2c0f40e401c0c240c0c03c01d030b0051601c103040407218010307030380001482d04050f00d10b0780390b02140000b40307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 59183915 1250 59182665 59182679
    0xd020904062f030c09040f02070605150a0308090405070e030a0c05190608061002070503010207060f05010b1612090f080a0302010b0102011a090a090f080406020c040203040c0e071107 80
    0x812003030440369941081c005040ca0402c48070a089001402c00c030385400340701040003503840100800d0115801000012107401740036240d0241d0b040b10006941d51692102000100131100e4058414250b08039103a01c034450440d52062094062295024003840e981c10004211034003501101400d030000904841c8100568981003d0f104d20703600500d4001c681a0340350552200d4020004d400380d8440b03449181840d542c502c1030181e810f0700c1c0b0071040114443c40da0005001d03202031004104003405880d010800f403164600c044c0541e141070f07000d84405541003203400340341c2072440103501d10f040e4024400b1803400c1400e801145c0008040c1c000150082c03100000044800c00080c2e4528150300c0b03500240114101c1c4001642210300428842030030a0a10702040002c3c03804243c0030398840302c5d40c2c81c009011102070f02c0305617451143d00812a083d1500090078005103404100c00192003000b21800c1d0320314541a6180001c1101c5480b888840402c0180440d00c4c00e0300842c00c1c0d50a1461a000f260340c0d035551014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 59185165 1250 59183915 59183921
    0xd1805072301170f04030201090b072d050717040509010e04110108040b0c0a020f030d09020102150118020a03020d090804050f0901080d1404030c03150c05090f040203060d02090406 79
    0x815035901c80c0301d60503000650107030215501d00c5014018600035907640d03854a030400c0c1c00007042241103550f11010480091810051039004001666803045020003c4081040403030220408094046040841b090704c01d0340101110005c0c2d0b448a01e1102d04110645240d1160003950072880d0710100c0304002040100724903412134403450044c0765400420855200640d01c000c419180030300000e000b8000250718040c605d0040c4510015441200c841aa00301980350541e04820304030f540207034660250009569040250008a0541aa1003102945480c6446100c1d07451002c44603000d81d008100100141c0c0280d06440050920103418041c001d9103203004143c1d40d00c980182c500ca000c800034010103070304041e0b100c1410f80302280010700081e101540d0569020909000a14220000b0000800044c00020702a0700031071299142c40340c416144c41003501501c0c14040303001c00b0008140805055a80e480c051709150328070a0710016943d848a0b0082501000742da60040d400c0405403003480b040001a40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 59186415 1250 59185165 59185199
    0x60c07030516050609030d03020a091e080d02030a020d0c060b060d0902150405060d09060605031c090b0f0d0c022a0907050304020a0915090501060f090501030209060d180507 76
    0x10940b980152904200401d41c01065069905a48400052016140240d00a0404540a0405030041071f6070352030150544203e103204244240c3c50a40c2000544400c200c8002d21a017540091410301c605054020340d02c0b4081c100c04030410200040c0d89080c8001a4004031070300c203003d4007140e950200360104802138980c1800c101e01421054a155001c00d55803130903501580c8008007018a03150000084401500c0b116106807403181c2d5817000042d059800700000c3c0021030804580e4032452807240400f40c013540b03565110070641c0c1c404100540040701180c0c1103403078459081c00300207180d4142d14012440c15008101129618000c40143c400c13008485121072040340048402015554490000315070600041c0e60094010840f00410300100481d81c20000c4482488484001500d59a14401c001c0d500203a002d0b402241e40d503001c650806502ca18440058a401e090641c9052003010203d2260300c1042c0c61092047c3c0d9030f5200c0c540003603500218155084c0c00004441c4081d840d010003e40d420100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 59187665 1250 59186415 59186443
    0x10602011d0606030c09090c100c030e01020d08010b21070201060f050a0b041502010f020703170f0712020d0b0d05010509160e130516031b050a030818060c070305 71
    0x290107442200d40000c525204503c0a0b014010704403d52050140c04400078001500b80d004540c4001700b01d0315507801503241c402841d90ba1000350340b11401c02801090001030940d0440d004030300e0107001690050000c0d41168081c442c42035942d141200d03000254440d6404a0b0b44800d4480700780a0400c3d4150007030000e556080c82981602942c3e2001c00c0f1400100740300e00b00400905020410030340f2920280c014500352a4000410184e2544075250700b00d0740881c0c0128041903150040c01c0c0000041058254058071034030510030035080190000d044180108180d804880d0009034490110841d904180982078010b0002410406e0b240780c00c901810044400041c544203450384191001c8240c042003086401021074080180c071030462168840c00300c60720a40e005d01c44c0d254802d4120b41640312020040d409038441d05800011082c0e4041000c000354842803080c2001741051000c1100074048032180a844040c0450307880700c80b00481c403d0b0140c4602c42c1054080c01030000b00303101000c034000b14041c0304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 59188915 1250 59187665 59187701
    0x10051306030506150708120406090c050103021c05090a15090b160e09061507140d0215060907020a050607090911180f01050d0606030911010302041a0306010504090501060201 76
    0x3210300c128101c40b0119a190f038080c091110500c0d030595041c00500416015118641c40d0081122800c8054001079a0480780640e5900310b14050103001d240c40005010b0900e02989082c264000000d0108a8a004070810701d55820114a06240070082e061880380d000c030701c2d002541e010110b1500182440366081c1d405180100c0000c080d90300e41d8840d15030100300c90312100560b04254007800550040200700325082000c13000900c14425204001d00a0b89100e4444010b004c004500c0b0207007001003076440c039815940309115a0f0a1511071040c21940a50b059400c1125603581d024100cac58809030f104050311034060300040c45a2658045c030038100341d81800703805122003021512001c2d460310851509400002c40602c104080d45860048600039101c1458802d08180c0300e10529001c54400394086404a07650310307419030400c440310021001c0c03100242021414140b074904c90300991968074440281c800c0c000000540c450b030143c82a034000e000004001c010a603103840d03000c2d0003050340240c1e400c11f10349 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 59190165 1250 59188915 59188919
    0x602060403090308031509090a0302100506060417030403020603040803070801050f10030b01030608010e030706061d07050705030d0c090612052206020d0f09020109090203010b0909090a02100513 85
    0x400010414015a49581c2d8144407900c0d64030750708150f0708041c0000d1070580080c9070303244040da80d985480d806000600003505901e0010702c0e01034581000c545481c000c06003045d040020781d07a0790b0030955003241d00d003d41407104040e04001c81401c510503504000c0d030103c0003105010501000e000610f1041e1003070b4807102c0490f601c507010020340100040d0301301d41c824404445c032000c02b0f11a800c0405404418103011400310744a8502500303584a40d0b0380722000e40e002081ca0414800180140c100500c907008002d50380103290b20844211920082c04001400300025005081240070012908080d0290800b040b0450b21088010300402580c81188001200d000c6a08a45003451150303a008000080c00c24000b4840c509031408009480f503400d0380d030361f9402d10594402c02c565009920060116400000380f1401c0e40c400948108100d4028030680b0f071050006022074030103c1c00306c1c4c200c00402c4038162715943d511840e9904e4000c04140c002d402110352141c02d400720f5044000f80c05d680071020740140c6a02d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 59191415 1250 59190165 59190167
    0xe0c0a05120c06040605070213060b0f09031c02030d110421020a030b010806060405011e03060c09080a06020c0d020703032708190203060c250305070803011404150e06130b0d050303040203060106 85
    0x54ac01c0c0c0034140f1a03ca0130004200c400c20321000801c00c3d0ba40140c2500d01607410641c0e0003040e0581160101e01507000041c0300d69203d201803044071500f0030300c088000d041a0400d00c55140f41c4140030703060100e401702e00c02032405540d2001c1d031620046030b00c107504d1041c541c2c5883d291904e0300d000340d40290007142041c0020070780c0300c4450321104810b42c90704c0480e48010318545448024040f45003000307041c032000c81c2c4003049180003881a6002d0500a038009a82e400940e00741519040340c0c0003004045411030a41032002aa0060b20039600300003628010701003042080400c048182c0b2a0321100071880b845580c000802c1c8a070faa00c1040d40d0084044c1e5005d0741d6021080500c83c460240c03400c0100c0044400c17425520481003603080114020700d0181d051000a50301c00c1c0c100c0c2e10a80046070500b050403646d100c240740078000c070320b0286c1c00007008162191030610050924007000d0b02a41c451101c0700e00c2030722032009a500401039040014151000303101c00b03003800ca440340e1055400740e0090051000110f102 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 59192665 1250 59191415 59191421
    0x60703090206031303030617030403051b0108070809030f04030501050a320405030f0a1706060a09090c0201140703090308090304050108010303081504140702010e0c0a05120c06040605070213 83
    0x3103801034002ca02e5540c84a10488619034030301d800300d0506a075182c01055003000012071040d9a542c100003940c1c0c0701d04505055207004d80103561141084840c0a0844950f64044a0a50000c01d00d0900c0980b545900c01c00c01c0c194003c0070700d2424624400314000043c81015046503015644003801003200301d501c02050403405d404195045440c1c0f070714000c0e408600c0504209290300c107004100792400c0402405440107a0b40c44449d0040c0041d0441800859030043c8001690300304800321aa10b1034440c2001010309485260b110328148a07a13945c007c01c3c1454001e4001d141e150000c2040502c0c07614003114041e009000c0190f091f4005155100058407280c0000308032420703160141c6070b48500760f01e1650100e41203600200400c130f03030482d00c4c115140940c941d401000512000b007100700f061442e1540c0c0003401c443c01e144405036181d11080d541c020945502c010141039400641d140d0014010306140d00d40b0b030050007942182c21420004000403403c1e03110014081c03072882150040360810a4442c500b041d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 59193915 1250 59192665 59192681
    0x80a05090c0105090d020a08060612010c02191e0321021e13080102030c09010e090f0c0c01091707021c121b211e0801051306050312040503060703 64
    0x6076808241504030315030090000c0c20350481c0003040d030b001e4240786a0104104a1140c2d04c1041d09030b00c15021b1002518002c00554803403a2640020010071203144802541d880e1058410311840070a140480240405000320203050001c80800c00c001c1512490001c1100000464a0700b40c40d0b000074110f445445540215000442c420700030a0100181c01070003c1c1030ba100320035502405800d00d4001800100c28000f0390f21501c00b01c108243c88840d010001b505542d001b16005104100c108200005480300213600360b003080c07000c1481501ca603022120140185041c1d1005400c070741201c40c0650344001038030020f0001c40c1c82910080250702101007099084c2200381802001412071849e0601c036148a042c91103020005030320f0600395241d150b16042141d01c500035400544031000681102000c1c0c002010300604400d000c64a1502001c00340c1c020701c0c1c2070040c040c00344030f032114002c4e1030b03030039009600030305c014003001410b84060083d4142c005819602a2003101c0c02406030b5800100f40901034818001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 59195165 1250 59193915 59193931
    0x1a070b01181d0604050709050405190201120e061906180f090206030106030902010306050a0b180324091c0509040c030f02040b120f070e0d2907080a05 66
    0x1410381d0030302252691944600c0c0601400070368588a4125450a515210005844101c0584031909090410170b040c46110340044120714280414000002c8001030042c889031600300e002004401c1074401214858004403030640d00d0790804458907003481000c00c10a00810150310240c001e90341082440007501d05070700c00d4001980745002e900003034298135001001603860f40d5000042d074030101d5001460703039003080c1c10940010340d48008110855030988070740c001400d030449000c41c80a1415002180c6803295010300e82c25010080d19484041c0c401300b1201015462b444c0348003448907015219041d02d040100d82d8158148128000500c40d01078040e207060400525130355191405045c502800b01804448840504150b540c010032801441684040c2001c0e0890074107140d942c000d50a0034194088028101405118941d01880120382e04030241c0448803005a440040b614164200505004103c00c0d20701c105c42c0000a4000042c1805800076202da5519200c0c101661151004101220740860b0109 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 59196415 1250 59195165 59195183
    0xf06150813080702041401090e07030804050618030102030a091a01081e150109050106030f0b0a030b060303070807230a020a0e09010213030c06020111130b03220c1a07 73
    0x6440c00d8240350303041d0810340c018016640752100e0782e4040f0701103e0b810404480d1004055006000c0c0c4000c4d0300801c000c2031924002405a41c0c1140c031601924880d42c82228406d0701e0000700d24501254444030881e0090340100219101c0c030304608407001910105104440704080301178000000792040f581c1364140c0c0c1454008203010131041c0b10500ca603000e9048200464890505880d81002c1d103841d4441c00780401700400700e61945082005010f8030280c0003c1d000d041d040081c04086601c5000c042c1e01201c0e00080f240010b40c07504000700303055114001d0301620583c0d001940c00c040c40225405918510003145140c02c41440320800c868460045800c000e62104d050882000b6416080030900d8000e2840b2000525050300001c3c1d20507400015802110240044030040100c0c940a108a030b44260341c3e100c41d0740c540302c60340703c1603d0b01c00c00c01e005070300c5000004008104850000e51140160210b00c55074954031f9150781c10500c02a000e0351040c1513110080011000c0309417895010345580c0c0c0c5c2d00240007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 59197665 1250 59196415 59196421
    0x120f17070b0f060f040f0e070602240a0617010b01090e07020c0409140a030903020a060207210812040803102907050109020a0e040c060302070c06030e100e010f061508 73
    0x1440e4101810140e03200030301003951a00d5179500d21800030b40668030100010591001e060450506a4660040e01550482900341d01e120340032072075074400c0e00007900b010002a0380c0d40c01c604000301066001861022200d2a26901c0010705500c4844c80700001d80b03520301501e81e43ca5060348102c004031000001138016001000d21402e2580140414921521840c201e015611440c00c0c07404244000590000d41704007420415070030031107079802c064203013440581240c0340ae01c0840b04519911001550260b00e1142c0c14030140440034050f2040b9440414a180746428a0304180c1c00381d801c240d07400320b007070490068002604c921083e0074084091000c403e5035041c1070b042c1d00304036807038108000544583d501c07949040700507a03500c1c0c0ca101c003401902640003064241400c02c2c840308003070368101d80d040c07510400c00030000c02c00c006448001c13680a440d01007201e51014104034104181c00f8030704901c680c10003282407165441900503001006804c40104040741d40c80c550402d400b1007010422020030150004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 59198915 1250 59197665 59197681
    0x1107020a05040b0d0501020c0709110325020102040902040909060b010207060917030405040f1d0606060d1e09050c1c02060702040b060f0307030209100206071215120f17070b 76
    0x31400e00b490005100521001017a1122401d9910105840c80c180c0c00c207480a0010600307910441c4143c5034080802800c62401060882a0f24600c0058101500340301c5620380409100750101c501030614401d040d91610f03558501a40501040394040364030b5824a02c010240354400200301003258601e50f00c0fa2016442c1501c07010340d1500b0a002400345020402c4080703181d40301c902503070706240c1516100103070714088443d10b20550740b180f00c024529604400103100482d50f0340704c250380c80e0300c5104e800000c2401503c03caa040060440500c0c0c20001d0910101409124020420310786c0c1600c00e0b6000f010030f14540a498114007c401c0000394418410b001100250605602130350003204084d00007442d0218103402e419840c0c00480d0301100203600090f0140302410400d001801120143c002043c1f1410642d030f000c0e02840381810740e0746400d9a1113a500459100c0c204040d80201419500c1d82404180360411040e01c01668809076020401c1401e01d40785421048201c9940c903802440a8a090b115001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 59200165 1250 59198915 59198921
    0x20906010807091509050a0803120c040f05011803020d0c060807090b07060c0203070c2301080112060f060b07030c06110a090b0309010b04110d1b020c22020307050a02011107020a0504 80
    0x882d513040151014002c245506c0f00502400942000d100554880109950001c00c80000905183c0c20074018402000724601e50981c00b015a80242844a8600d510b0980ba0450f264141d0003c0c1d03110440207802d4050104404000007500d4a9a880c120259980d00302503812210034864015402d0302003244c1000f04203264032400d0030000d1803042c0c0f4609a25031b00e503002182c0c5c040d04031070170814881c081c0303401109003600501c03411003003820700c2035040d850804100103012001390090555912624038410001d10303540180003405040483c0c43e2509000e0a00421310b121042c400c5440728a04800b50311102c200341d042e540c4000c0c456442c540701c0d40c240300c1d04e158290000f0703000c4c840300e41d00e03514540c902c0d9480703003e040082099503025070340f034881c146410400d4841c1508201c0c06e20f0125006080c4060b808075130031800003000c0d185140240c4a07680e8851001940344003407601d5078404000d02c441aa449030007800030110f1580248070033451401803680e14402c440000398492031441c0200001d040c150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 59201415 1250 59200165 59200199
    0x10b0f0f060d0c021c0c02100c050705060d0c0206090105040f1202010e0102031303081e0a200315011403010807170a020307140a06080f060603061c0605010302090601080709 76
    0x605060b0401070800e503510251401d03810300b800580c01440e501810820791400c01800540603103405a00c007280c5401044014284060060401c0301c822001c00078010108900d000501d00503040c1590340d00014490001000740040c840c00600070400800c068820502030366000b00e03000005802c0c41011955843c801c0c0070560350510941d500d403543c0c8032800c502840617600c184c2c916500c2e000f00c010685002820b614000b002d900e00d12080302807020910105805581d440214450005a080c9910301e100c1c60030180ca440c840c080bd2000404c0011500102e000000c0c1c00000783c0340c0032000035180400160b240000d00480e016944065000c10060740c5003808981280d4000064445152950300402d0614480e50800c071440c1180c4000c0c868142800400701c030003801a4a071650722810441001c040200000e0691481058044081f070f27143d40d00c00303104008001000c0300c0101d401161b07240540240030240b0040c0d00c0340461000003402c950066100f244500243d0380c40308000da05221103013080c2c8010f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 59202665 1250 59201415 59201419
    0x5120f070b030717010f0306050f070207060518150d060b0a05070305090f0d0605010303090801021e03040206091e04050a0c0206040201111207050f0f010204030308070807180603050402030c03010b0f0f 88
    0x10013079010003850824034003a0105040c000b1880d070650601000f46d54014000e010312180090800c62129804640041540c140d4602581da80141c81610107212540c8000d865115400c2c900c04510812488018529445a050240551540c441c9072407414001c1d00c03200400304100b00b0020001900c0ba00090400c940010010b0018040300300c080b138400c3e0741180044034826074802c0148103050f00486000c0041007001d000b546016400c94140d161400201c4aa60a525011022804540e114029200c1d0b10101078910807503129584076035100682590ba0890240349045c0c0480c08250b2070b400760700810382080e0014405520756034011651880c1c4200c280e4024007400c0c0802c0e0502d10740000800c200c0d8090300003001d655540501560901104035039849d19a0b20401c8200300182e000801c16500c40c409003403075200307680c030b10070103a8808019000c1d008040f201e0071804520306805501841c011070082c0c045445824004007410b08072440003510a40c01510134000a2a40c84d0000781a4001030300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 59203915 1250 59202665 59202677
    0xd17090304030b19150b070212010b0303031f150504030b0402030f01020a05072009010308030a060312090e07090b0d09050f060708250e060a052205120f070b0307 71
    0xd2030f00c4140c1100c0056034061099410700030184130192040c05a84e0702c00e04100350b103c01591810150b0078191158240c0240260900a16600c0003842075011409860018041c0c81c2c0d245052841100490500300740038080149022001c23501700392403510034085070070545505240505584400700a803000920490b498030480e503011140d13080c00e0007d0600c2c01c0c150341f6403030788401da41e151a6460340840c1c0300910059080d40e856806940c0c40070601411250007003066a6a03440314190b14000e842c46400107440e000030b2903038604500d1790000c074560495901e034100a060782c032008021a04403986204089480c04103000c5154202d07943d0340050f51051140d800c0f2000180300d1030803681000c0c4200d40800101f03a6070020401c55840e070009503410000c030010303030340205000444007404412014507134130f000d250040f6569144078098000ca88902420180403400d41500d144600071510b040c1c0155401a07815160b5001101800146683e40c66120700141135018100303401c206030354100030322a00030024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 59205165 1250 59203915 59203919
    0x10905010f0e0c09090613020d0b040507150e131802090103080d0e06090604030815130e010c0c0206030a020f1204050c100504140111101a120d17090304 67
    0x2003481008481400000d02040440c491800c07030781810300c3d60050901406030f00301007021210300400c034141d22001032a11440a07070180d0000c9955500d400400400c0c6015940501c0103124000419038100c9103030182128050300324400840d481171807042407640051021000001c2c15016070000509018000c0d5041440a9103400060b08100281e200b40c6202500241c840158200380c0907140b80c2d500900020421400c1c14403800765510030051014041000145c0425810400da01400c0c1004200030f26008140c2c00a03035100700100a801c00c000141d40c82c1652032013485000d038040b00d104540040ac400d007143d45081d1110065480300c07981c031030502002c010840907681410301c407600540c0640010708a020090003400030f000207541d0b41d0018010700340000c024488040c1c000b000c28000030f1030400d42c2030b040307820b54625003407011807a08001411305001446404d0b088107400c41404c0d086030031003804040c80210302d49807959013914038000717810444040420009140002e0308940d03240e00b100d140c03036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 59206415 1250 59205165 59205173
    0x100c1101060b0405040b0306011226030f1501020d0c171b0f15040c030210030908041e0512070501052206051c050106051605010f060e0103140f0304170109 68
    0x1a00700d81091240080c0450180202c1c10180300300d4070080f5003a07009040c5075060260000159202e0034008182800310300403900017511212244441d03002c01c0f01c02c00c0d128200040c2028400c1001c44406d001c00640580b0103429600c00154007143d4500350b1280e4005030101d0b00c0f00034802404035690b09004c070b02008220240c00c0c1200241d0210028000034100c66040c021070a070070040c80500c070032a41c400c00b00511011410f002c01e1031003120f0f811614136011840d50300f000e40c0074102402001c0c00201e404600016644005a401d441c80700058600790800c41c1c58004100510a00c010600c0c0160f100389014042035000d8002450122980304000c2e401c1018051048c100c20318513008400081c00c003180322290781090480c908541004160240400d40c180540100140103428590078002c00c45110340d41481000c0d44045900c113403100060004603140c41c3d07a448800420300c0211000426042102000c80d80442c041c2c00c50a04040a503250a24000311100d003464800e41c203011035542e0780f401078009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 59207665 1250 59206415 59206421
    0x3090303140103050f0601060903120806010c060501150909020309060402240f0406080a1404110406030503070f020f0d0b06060d060801020a0207090c03150e1f0611100905100c1101 79
    0x3c500c2503004090990030030b00c4403414040d06034032a2060218100081c40003e19400c00003882600c94980300c961980d0f41d0b40102d811046c0c09101070620780c504000410742450510308150501055205c400900d075850000c10100d100c00c076506840c94204001140040c94102c1c2400d4010301c4504441001d550700969490103a03101210552800200140c204056600300a06613440ba00c4039408021640601c11008031083c40203100401442041c1813810041c0d9955004102654112080300d0715804c1e9442c02002000c1580d80a910401d140f404448003441d0010950720601d82c0710884140c292522000e22286070409203d00503c00d03140c0601160044091000e0065407002c1d90080045a1400c118141191a1500070008040c10904021a45507401c1003410844035446002400c0780e45004801c00703801e48407008440300c2e400344000041c43c4c036030017029141d0629840c1d0a44040c0320b51081581c0481da0141801030440d08100a01c0c0d4180c1040c0d4000d400700307031080c00e044c080790304040c80313a90071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 59208915 1250 59207665 59207669
    0x9090a0b2215022701030605060703020a0b1f03060204051e0604030605060315091b010809030909060d02150a08010914040312090b090f060c0306030c19030812010302180402060307030903031401 85
    0x1d58524040f015546e45401810000c0a080d510649090407580f4002d48428201801400c08986000411611a4801544489020702000fa962030548038a0085c010b0341c8180f0415101d030040a40c00f1940c140028000140f42c10028005490103295540d4132014100050031243c0c503001da913000c1007400004400683c450391031038014003c15a0701a10141c10444801070040c100010001040305000300041121403003042110403404540d42c00c0c00150b004d4038000c1c4020340109400c9a1551028a0000078115001c05500c0b080302c0c1e0781e211008981103940100c030210750001c484010a001c6401035580d00890001014089082c0a05484100000500b5507902600c0d500010286803c0384050040c2a0805004015580345d802c00c040040e82d0b460010694922480207003545090340244010360318010340d401080142c4460a490007411640c000b4030041c0c4c00b034070100d00d01e01c0800d4035086149200300c0e0300a02040c103507100e2283c120014221031004805040c1d5950f0f0940d03c0741d4a001c1300e280 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 59210165 1250 59208915 59208967
    0x1060f0905010302120c100e12100501050306090a11010507020105160b01151107060e12120304030905061303080c070305030c03070524131109090a0b221502 69
    0x441d035140d4410b110000491000200103604480c551042d20740d03c64440704140b54003880c2c0b0f214003c00050016000b8100314807040c000b481a44000c5800e08801d410050484504030141c80041d62100ba00341c5d1518490394004101485e5466034040d2903000310007410307a00e40107140190420900b09840ca000e51030540d419510302ea08040100300c0201c3c5441c4001c08500c29141c840c0c110a00412803075650280350050300140b1406442000c0d140d02e590a05400d14200d20080314010204800c00404551081c1c031b0a81c00120014004a42030a1002c101c4042c2c29080303c42100e21865919034840e02c0d00100a5484940500301c00000468810409400542c42c020082e60307031043e10745002d031729202c0100000740f03611403808103442039114101c904d070390700000c0c41400c10140c0444c0c1c41c2c00000a038420011907032105c0c4000520a640d580007807071005092007604417510313030345501c0c610703442c00c0c542c480e04403500c01c50f00c81c10700001642507902075901e4014000094280050a000700703c0c150842481c8007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 59211415 1250 59210165 59210171
    0x9030a060e010b01030b0a170f0307110102060105010507050d030506060409020c1005060a03050a11010e04060b0a020628150302060f030a060537030210021b0603010b160501060f09 79
    0x158052020f00c1480d840c100c0908040010402c40c01c0881c03207451403071181c0f58054100d0020003038040d0707051100401514846080e6541c406403890170850700188425040d00600c00c100000c1400d500038401c6400d0903400400801000c55004012000380c0001080207800c2001800009140310a81c0041c001c0101c0840140c2100c55540c4130348001c46800510300f900c1101540c038104080350f000325013000d80c0342d0000c0110101203183c00045c0e030703103da4045405420500c0e244000921020b40000b40a003029135900741c6c4c00135158900e800c540340c0c41ea031200280705003080050b00c0340c800003036110102c4e400c00c00010036822a030302d400190a41c1c020001c103c10428000040009040c120312490019003021500c02c540501080750429120b0f5008040076850402e51074000519854009148001d66004110805043d09504000e4a030119101d1030900d541d01c01c03029451520302503007680c0c10f88a0004803641440d464a140000490041c01c058420395615800403510b105c6241d040009010b41c01404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 59212665 1250 59211415 59211431
    0x10510020c1e0114040308040506070c0b040b12091b060a09030b07080412020106060512040f060e1b010c050c06030711060403030c110102090f060306040f0f05040c0f030c0e070509030a06 82
    0x500b0200c8900b080c0134040d00e0401040c00011492000d41d0280d94050354800e48804181c6005861403500e0b81105051100224001800000c0d800040c00040c400701c04c186050703140e10083d240d4801110360340d94000200440e0002c8503045c0300010b411a1113480c83d000d00050b03503d803200300881805450700000554030004210510413913440b0b0215000151008105d800d01e0100000c200d802012911204464203802140a00054079801d4014a400c0841042410b0442549940d9010303200a8110040300c00110501550f0186541d1400150050041c200500c000003c01655a00013002c50b42484020b4100d0f000c5590100155841184a6200090030910b0250064000841d40642c8101603004010000c507646559003060039203402910b2090b100c3d1a0303400010b01500c500210040000e18082c1c86085003402c0740c00507030099000d509aa101c0e103490300d8405070040341c0c50102800c148044036040010020b13105170640c0c8a01c01c2d150690800c00e007900022b0078041140b501340c400075216081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 59213915 1250 59212665 59212667
    0xb01051c1508030f03010905060109050603090a0b0109020f030c0702040212010b070c14060a0c051207060501030b07020303070807050d090210030e010e0c0d0b06030a0c1806080105040308010510020c1e01 89
    0x90006400ba00c4021410b14110004007a65031205020b403640351034440c00442c6969028008400240800a041585034a0205003959035004889415203a10000c50b0000681800610845040919102c2980d24560700c86c9200030703031540000c0381241c0203582000305150865907800c046000c0c20b240c0e00310795910342d1613050000c0d072034840c1e070400ca0708804034000500042c0e0310a403c45402c4206401e00141e40c580b07604009040010403541051048000151a010400c8130350100341a6403243c0d0060b0720a03103407010201da982c0000c07104a0040703141100401c9186011700050b0044038020300c2d0100c0c200c02030340c0c04207807800084900400841e40b103c202c1041e00d0350a0281400d040900d0001784a0038080c0320008420040d00440900110360040201d81c0c1c9803814030100c07a003035030043c91590380c1c140c0d50003009113200420303c00001304a151400200791520180616030041da01075640309500d0742040100b04441814441a00541c401c1d0311207402c158079104800c00c0000d9a04210001148000700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 59215165 1250 59213915 59213951
    0x1a220503010c2d1e030905010612021201050601081b1306050901030b01030e0d0f021504210305040c031106191115040b0103060e030d09060204181506030b01051c 71
    0x520582e18900725a52540d2103030780710300600c138000c0031962404c0002041c444290f009100e91a80a4101e50030000041559904182400c0d02d2a01c281c0f04d58100c0c01001c000c2d1402c1700c805071903240c001125000802c003850460076001c058051140051450801000b00c42c0c18080655840600890000314048030b40d5a05446100c441c48000c1c01c090040008040d6555203a0100c0250304042c03000450440d85002e1007004510407007006100310071490300b0705050001c028003400b00760701e07202d0021000c0401414401d005043c010341e0301041c41d00c5410f08643e85c2000f01c00480d084160072941c1400a10960b51009009100400c42c070b40315000e4a04840a1a80c2801d004100b0900651080000c1c00b00140c40c004049045039005000003234408035000b41c46080d481411040c062a1741098400da060024950062045514007000340c10040240911001070351401141c1c031909031080041040f082e4003a4002103102041494003c0c6020890030203041003442280302c1d00c4215560f41d003102c500c003040d52 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 59216415 1250 59215165 59215217
    0x501030501090921170108210f0403021309060207060e0609010605010203071202070b030901060e0f0601020307060b04060b12040b06090405100b0f040903020c0a1a220503010c 77
    0x4001800240d80545036804918421180d2900308440d4003000e01405105d00b000303a030800c20740c115805155a540c5180c82d502d9107105211403407492100418020f03e030700e0b08104da111141c600e541c0c81c10140742d90208481200c000d4044070403140c56541d4800040c41c0c41c8001c088261090400148001003164414034203d00100704c2840340c2e240c51003c4c00a82c0c0c00209031004a580301c0c1c1c03045608515000124240710385507021010080c00841400340c111819002102580e0072058440043c1d40c9506104404100582c2c1c0f150241e00100035003008201c041e00038001910000d8000b048140d618040898103a2280c0c400070b03404207000701030004000181200c250082d4084032010401e041075218584c840c0040b65201201955401c8002c07129190806100602a40103004000c1c4043c3d604020792548070383e5070a10f12588003400d010948601040d0703448910380360070060303a040121944101c6003080c1c101c0400403843c052104001030350b650034050f02007140125581c0070590507407a9418030070100070f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 59217665 1250 59216415 59216429
    0x1605010b120c12010e010501080d030b04050708010909111207030201020c04050402150304050a08030412030b0118061d150a0f0903050d05160507031103100203010e0c0a02030409020406090501030501 87
    0x18500119101d81c001034200c85900048401c042100c184050050040844500d0100a9400e00340006040d030004141d81c90302200c2c0303072414001c0380000c01c02c0004484003113a00401248207040184940400c603880b81203042d1203100100354000c041d00000760b1000400303144404642c0013250510031544d05100100d80744006544c2800306042c80d500103042c20b000c0e640d05c08603910700030000406010b010401c0510541d0040c401d03035902d0503c0e04140d120042403202e04000b03c0e041c154802c00c15403040180c1c024420008891103807241c20b080e17040780c11403034440b4003460b640c0944020812541d2080c002603407030000440c0003952842c1034600a032500344150709003018410b500d44200702151010414010200c82d6142c00d82d5644900750704200c10b40c0b103089001c0c103684240e68000c010440d080450b44070b00541142159203502c810100c40e4241e00c002d010301d082c4020b40360081000d0000c100302074005c0384424010b80b03080c04c0d260003291040b41c109501440000d50500313010002542c04d0702c5014050209 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 59218915 1250 59217665 59217679
    0x5100e010e06010b0702010c06020406050315030c15090d15020a09050604080d0309030512090601180e0c150c1203010f060f050702131506080f0c070317090703081605010b 75
    0x52403032142e181c0005104007000b040300000c0341021a071044004000c419804801192a1900c0b0b400040468000300c3c0c400c00201c40c012441015882d000500401a500081c01c5010f11850503000041365004030a40c60740000303d01080320700280d040c580500c4240070440c4016242c0b01c40e218010003841556010900a03071040103b0301c804080403c108195030050309001c58510044d140450707451242d42200c0301003107482c1091010310346001c00c2c0175048608480121404038150340404048801040c400c4000398441242c1807135908088074640c0c3c601079040310460500b0356101c0a58103110141e01c243c101c17005c0010050100a1105403041d001e04002c1c548000c80c070f0b18804000d09144242007000c4c0c41218a42d40074000c0d6840394020305541031000d0b860010595072010040c0410509840203c0d11041c4880012490710540c41a68001a0183d032940302000d1010a2400203100c0506280c804e4020204048082541d01c001400841410f04141846a41905105084030307004044148280d034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 59220165 1250 59218915 59218931
    0x10090305070b150409051e060c12100e0f0f07020c060f0904061502030a2606101803030807021509030a0f030f230a0c02060103060504030201090506010305100e01 71
    0x1920005407020150b00c01c15081803038541010400e940076220b802c240d4010b040ca08000c04102c008142446500d04030302012444050b42c080e080e840340401c980602d542c601c1400300100509034910000c0e00188481d64103001e1035100c040d071101210040700c9103600c0603000c0091081c4046000c400075401505480540075002103074000078100e1051030321240c8411400b0503010040c1c0e4480c0c2c00540144400e0204103281440700801079205d400149004010807160b013404218104a054810410110310084100581c1c800c0d0400c00020005c4c80710304200100390038108805c8039520030040155000b5101c6592518000c80300a2811002d041510680e010170b405002c5989000030a40f441618142011110181f41c0c140880c010090003949480503810101412800058031003101c412500b8208565155501c404001d01a84d041c2070006005a0101c001007001c14903d5102a4000d07200307100108140340152200c44c40d2a00a030415612504031f40280f0114035510b01c101c480030303c0b1600080c08280 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 59221415 1250 59220165 59220167
    0x331060c05120711090a0b1206011806080304120804030b0109060f060203091807050702030303100f0503120301120f1b050103050907140609150414030705090103020d03030f02130303080603100903 86
    0x150b44661080c0143c00200200d1b190345040d401440264a010f0800d003d000f0703d1a05a81d9030303000c00e101c0c2030481600180001008041030140d8001c2e5052540218505031802841e643d5a00440b90300b40c1e41c044042c00048001b411000c0400d00810000342d000c82c015044c0311581007044480d50280b02903510812001100b500c4106c604107003201c00c1103440030700d503a07440c00598191140402c001e41c140400400c0042c00502051103030b0036603050a1000003050785900c1415500d03049480303c00c02ca21420b000400c0103125018540c0029403068590084002d6107645e00512801e81820418035070b503010b502404a543e06200d0300d0350116000005103000c601d8403140c00305000140103c0c0c1d00949001403220090f8451616445d4070030b030b20800180c0c2e55a658001500c2c81c580c5003960038820301824038000b41602d0002911030507690000d1080208010070783e0164010b1110361800b51120717409000c400001460100801d0045011b9120306003586800300405061400940074901c8581c64190788801007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 59222665 1250 59221415 59221433
    0x609080c0a051804052103010f06020a050a140c0d0305031b031005040207080f070b0106090e041208100503030a0c020901090c17070203091c02130c020331060c051207 73
    0x8818503100307200d40f64a903400d016007410b0141a54125070406600101035209220b80254100c3d842180200b03002922014201e031a207000880c00351040c4d001d8500e40010504852612640c12409022140154450404203080746001c103400d41c0418800300400c28806818004003c40c8170145003210700c0c5203044040c0c489284c0090007098021640496003508101c2da030320884600504820b9640e032507228512708502030803001d01810300010760000000690580c15615240929030003596006402484c03d011104041e0042c155019400e4100340050b8036142440105000300d03095031180414080e50040c80100c1c001a40300443d00e61500380006c4416901014180a144042c842d0602a40b12802c1c200e103140a50302a40b9070044105038400c0d0112000e2a100140a2003581c0409511041c0e020007c2240c40d15584403000d178204100e0a04541c0103c490031004000d150030440e05031482c1d4014450380096a040031001c22003240081040c00300030002c54520300101c4602500d858181d54403011a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 59223915 1250 59222665 59222689
    0x415020d0f030b0303090a0f0512032d1303121b05030904020702270114090714090409081603030b0a08030d0b06040308070308040308010906050102072d0609080c0a05 73
    0x10960b458410f1119035a0a00403180d01c04002004d03040b006407071709079155660307083e4450070303104080f52002982c0480011096441502241c922102c1c0113440c2095580b459075030141e0280c1c001e07001c000700390054102000c0304000c1c6001d0722120400030800c1c10080c103003120308181e5616101100c590755000401c00001c480c0499002e5401584030816803020880b40c500d40c12901c14019a401d08403607100401800550480d10400c00c0345c41c000c5210310600001440a4900d040002d01c2d01040045040c5124010540a50098000a00d225040c0ca40014079002015043c0e0710180981c006014181d050064142c0c2e8941100e40601e0f1501e0f203800d840d0b4900c9002c12009800742c560700b02c440c10b56640c1c02543c2c015500101c140307030313611014500200500400c840440101e20701c03500100c3d0140d441d200300740c01c1d5103040e00140703c52410300101c1c000d440c81403140e581110070340484208001c0c0301c683c491001000c90351100b086081c2000320b06c0b400e113a00710701054059030200303508020b541c3c1c8841e02542 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 59225165 1250 59223915 59223917
    0xc040f031103030f0d020a09300302190303090b060103020f030a0c0918021209030c0a030c020301020403020a08100507030506010f0507050a0b070e040b1c020111150a020415020d0f 79
    0x11602080040ba04501411998500d000d0000c00c085c04081410340060a01e60860f0b030303403404010f44840204280051246090403002d2840d10030214807a0460301c40c0a00e07500900403a980008880b9a50b01140c0e526101100001c0c0c4580400c070401800201c0c143d0402d1003424194140070031001e65200500000b86103c000350f8440c091003c2c81d5000e40c5110003e0a440500c3c410b45250040130701c006035020001c403a4190940b0380008040980c048141c41400f81024007170500501c9540307085561a00180003a41d05560070000080103030344420700400101603460142c03100a41808006085900003840070080c142000208010392303a001400101458250038010f4444400d420000d02d4034050210061042940c40c007070010ba20741004482d11040001c0320700703000b41c0c480e40040c05590821170324151444540070740703400015030042c0c40041180503180100c924401d1842c00c000c00d0400c1c20703241b4084c95a0b00050a0100704104481c2c816080414001000740c44d001030030003044141e141c140d01d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 59226415 1250 59225165 59225183
    0x180f061d0a0b0325080601030c080c0a0501020c060702010e0d0308070f030c020a0b04140631020603040206030c0d02030a02130501020c0306010b25080919060813060207020d0501140c040f03 83
    0x801c202d900131108102803c282000c17111306603180d240200c1c0d0200c090042c0749040c070407076130111b030329181034117541c0c003604c0c010390161038154959021311060f600051800ca05010321012080c2c0251240c4c10850040e6003e5950f0307550382c1c1170013107000d05034490240d0140101400e11410082c625000103000100a510030b11110340d5584a0400c18840c07085c0900e071400368080c41051007113200801600181090800070903040302800c18501d00341c00211084002e4107d4028000100980380800195600007038800c041c3d4500944103008000b2030384121101500941d020442d079031400f00780e0350002c01814082c0000c1807103070000340000795501014810340c0070445000810240c002c4110646060480000c01c1c0b404550f10246060300300341c0c01203004030380a807103084101d040d012a00380700241104d2540c0c44480d01510354000540da0000795000603102c107030b000c0040e80c0044e2a41301c0725015403070189000181c08900704140c4c1c0e19089000c0d1400d048907200340030500c00c0a0800e0303404401c07250301c42091 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 59227665 1250 59226415 59226463
    0x210080919031103032406040e010b03040303090c03050313091811030106051e030d08010b070f050a0b0c090301050a0506010e060d18030203040f0b040f180f061d0a0b03 74
    0x842e0300800d03c50303030a80310b0700002c8140801691a00f0b00088034500140e51102c5040c1c41c80f06120700341c0210300c100540c5101d00030042081c1d091140042d5000f034020b20740841c881071300d9290074551150320f42c000c842d9984000758003c2d440ca5922410805440d0f100801c0c071000300c4a450341c4240c0b00b00c0b02c4d07010780010303c011018611030f9400d500580040c400075110f086092507081428400e140d118030352500a0145011100e400c40c410001641030b9886d104000741880d5030360f203d106142010100480d0640314001c501000304000381d080034480c1c00900050350359298694181420341e040500f0701c41055041000f408044e030b8112211000f01c0c2002e40712a034851030301c0c000d607d0141c0582d006400c10008109000024154044024815030f08260100c00c4030aa039001c038281148542c0c811008109e80341102402920101d0b0810780703201050030310118040c005204440112030b080c0e840382d42d42c06038030f01d0680800702d80c41283c2c503400030121038104020082480400d440303250340b01c2070010341624a00e032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 59228915 1250 59227665 59227667
    0x2040c030e010510090f050403200f0709020a110a0804090b03030702040507020624060313050102130b0a0f0230040b03070201140c03070c0308060a0902070f021008091903 75
    0x44003604402041c02400941004c161a241c8011036004044080e03042c2242e500e0700001601446000b158181d4030031080b0240c50b14120003d94402c007559041d806059041051280b08100050281c034403103800682c1c40707982d15800360105010f0f4108150a40100c50041c021440110650f400c44000c40c001040325034200300002d0451298440c000d40c0503103401c0c02c8c80041a8001001d0788240e4040c0c1c444140c0c80a03040fa44e002c2440c403540c5403680190108001070692982c1c0c1801c1c80a0f40c0301d0400542400026888800b04503515040b4080d1080c01042000466900480d0b9000460507130018046455107680e0000c8100c50445010031181003504070f42280301111003c0b10300510040014a07240c3c1410309009010300350461110441d0361900020500c84d200c0301c2c08132401120a030311080a03072010341e80c09841d800801491154403034140300c0d0000f0408520300090000510030010481042e801f88100540d84650350f01541c00c100c1e0b07034000c20801c0b0b0350020300d031402d80704800207002c400412860 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 59230165 1250 59228915 59228921
    0xf0807031833140d0914120d0b04060905130203010c0306050913080f030a140117060720070806100906030f080f0706020705030307020c190501260115120603020d02040c03 75
    0x81c42c40c2240000050580b24051305038440d004139032240c000502111404402255500301e00058920000010441c2018429840d0701105048501900c042001951144144100c6104440301c41e00030385181e22913401c5290a1003100c4001c41c031420108410350a000204043c4e107001002600d83c111b40500082c2442030003429603a003100381d001a00e40d80e207014000a40a0060300381c481c8458001c400c00410400181840e00500b420040c0050482d80d1701c416080310040029921503420140c000c02864aa200502042024010072401490a400c2c040c900c11a90701d510380c0004800b915202c03040c80001e008001d8400c00c0b5400c030b0300c01611040003e1901380b1a10988100500041c40040e1180403c440800510301c01d032855001c2d40d81800f1214241309000600f155500c002c14001c402c00e009642c007544100040c045054402e020b02c0d4609598480310302d00a800c0a030f18940c0312000c2510090740108904c0402034981010300c2654550b90100310080f01c1038100034882c5855510350004244a54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 59231415 1250 59230165 59230187
    0xf0303160c0204021e0a030b0402090f010309140d03150f05030703031412010f03051501050108010b1317060f250f0e0411092803060203040f0807031833 67
    0x4444c00391001a241085c5081e074070240320140800c0c00d004003404185043c0c804d9903442180542550758030300e07913617004400402036904102c54040c02d000800d02c142a00f0800d40e0b608040c0d030b84001500c194891001824110a64002c1035102103820f81440706d45c50100308001101d034503040c5241501f6080c20508885c0c090002c0f048292491700000242d95030501c600c840880e80100162045181450581301c0100e80900071207012409034001041641c00150003001c0405102c11000c20141c0c407442041044c2007900070301901d0742c2c040303014440c03846142030a0300d0300032240413403800358003203490340c001100d031401400e84e01445a200c17040820030b4020144643d100b00b004004000956000c52840201d401a44c1c00740d005840911221a01d070403048411403018041010346803a840c81e50b81c03494040d40c4000d0084070b40300d907550b428400160901700581b80c0c01d80b01c1d8840c1c00c80170300d4902c0c5c40d114180d510751107403e050030074102032220340c0940c84100d1503540700c1c503400295244600c041940c000b2001c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 59232665 1250 59231415 59231437
    0x4030504030f150e06060d030e030106030204050f15030f190309030b18010608070311090403020c09040501060312031b0806150c010e0606010203040509130c030f0f050f0303160c020402 81
    0x4940c0c01c1240f00760b00c8109100c0e14a070200004030741003200310b43d103950460305180c01890041002012038058044c03044810f00003000454455100e0703002c1410b90b40c083e11b02d0184140000300348111080030310001c484041c03059004141c1a0000d1400680c1c5440d40d107215208017510703030720010a042c49200f01001868201c1030381c481c1818190050007019100c1c0d0810140340d403810b44042040040441e1002c210b0390002160392821140a04015100d0b00180c000c82c1584546101e8060030784402040b00d115a010304000218545107041a04a0f400140d00050406180100c00c4218200c6507162001038044c0d403a01520f190740b0000410040c20741e00c2d0302e0040d84607010a860007925415044040e01f01c6903282903402946034840107903a00d00681c02000e6004c1d400c0000030340740c1074881c0c40c0703030001c103001d801150721f890303581c2e11441d401c006210780075107290b00c6075503540085c840104000420014160300a61440c038041c036a2146240c8131111a00c100401107560000750b42d115016200c0e048aa = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 59233915 1250 59232665 59232683
    0x3100504020f0c01060602011a011206170312070c080f0703030e100e070f0b0a180f090203090d08040816021815090a0915110c07030b1009021c02030403050403 70
    0x115107011a40ca8020043d040c501d9030a182002c14054030601640d00d10504603d8648025950180103466109010307910032032040c0e480038001810042404500310005125002e90f507901001071450100110040059080c010500083c1000500003811503c141d41459609900c0f44c01d640b5080300902043d40003440c00344034500d4050219070440d0f02c001000e0000c002158910fa5841d0f0110329995418841c5402103201440b01200490017100000d00401e82c0d041d102038078507107862541081060681102c10310940c08800c00408000410464000c005141800b010619107551a68803a11811149400303840740504960110740304c5c40f60060f0130414008d680c3c0600c0c07400c0a00020207844826250742b28804080200d0034181e940e01ca81e02e155900f04140c20398205121031254054401c0000241e4a01400c10110911001c14070150029601c1a00e02e100c0c182400480c10714030031055040040c42a10400600f54610940d007030151200324113801c09a100da989043c16035040c01590300c00761040207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 59235165 1250 59233915 59233927
    0x6151d1809010b09090a02190b070305030403030c0509030c10050d0609020a14030702150c0c01020d0c08090325020a0b0d0e01050f010e04030c020a1a0319050408040603020310050402 80
    0x354060018801d0008600801c40744140d03d041200006099904404075080f0041e410098140256100e071310341c44801840b0501903075100c114086900401c020750001d000801444101540350045208020407031a03c28184050440081e854076030452840c0c0c401c007440011610316030f0040701a41d904d0901803008000e56a55505820b000c5d601c000020700010b2100c1400314807541103203068901481c1c10345c4c01464180341e84561707082602e0020701000707119041880f264410b82030900013000041e1207817601054280c81707001c021349045e60150801080d40c00a0107590031039040e041a03140545c0092400e80210401400859122911508066051900002e5444c005071198208020f40021070000700010365550000b01102003080c02044400026900490007003885259104da04a00040200350600e0340c903009101d00c001c0f070713142c0250410b03004000c1000240380340d80300c900c4607200840e081c4903a290542d40c0d00e82d544154001c0f20141513003c400706d0060340160130140090080034004541d111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 59236415 1250 59235165 59235199
    0xa0201020409180b13030905060a020307060507020319050d09020406030506010e01140a0501030f0b0a12030e04021206010c1403030408040e10050319020d0f030c02100306151d 77
    0xd489400344051103814420f0a07001030799855010707144180c20a24118843d200e000c98100d1a800740b040c19820000403030404180303503403284010700351800c03240c00035965160035103801001d841c40100202e00b590800e1001140341c5074450004070308114203140c120307a201e0322040007100070017800201941140c0b40c10400310401c10002001c3c0c0c16510b84903228000c1d60f0707a8255003809241030032211604a10642e000308050b5009030081c100d1402940800b042d0385901c0305c045600088035a000b814015480903155007850b07008092a000d00c44282d40540c500006501c04044e40d02000d03140504101031414000c0c240f08103c036241d890b0382d0102e0256507490816041181c22a0414042d1114003007444000c0b9a1403580000120f084520150103000c4040482042c1d49601d400f4003816600441d8416100700059002d406881c080c0c3d1003600c078200b50031614010b0002000c4181e181e902458508441800030041d400402c2c608000c2c50301e480e40716016200e41081070800c25030006a0002c00c0300b00903400320 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 59237665 1250 59236415 59236417
    0x1a0a1106010e0702061b09060304241505010216030b070507060606032a0207030308060604050301110c0c09130b040204020d051005040f1a120708060f04030e09010305030d05100503030a020102 84
    0x5507070b890382100c00c140c40340c0302081c2d00b084101c06c00700c00c0c0d40c504000251150800e0006103178402c2c002e0f0400820460349403030720300c1c110600041c4188290b58401c41240d42c00144480315010344828402000301c0041c0004141d6980700c140809403200d400c031000101128030a104654015034410340903c400e950307810026001d48645001141102d481d00070005c00d98000094091003211150b0081c10b51600c0c50300c041e5007403032b005401c907500103004100c00300ea035450034028000c4040c0045c00161703507030050f40c43c0c103070030070000c407039403610504108092041c41e031050400e05c81801d40017054108641c41e03510004000384611001c803c3c142e41006c0400001c200d01d05407180440d001500c041c01001041000d405c11180881d40f1495840090303a140c40711401c00c10007001d03040b0512002c030b5100740c0e00c0c4c10405e4a088005c6a54480100c0c4031002c001c20180c0c400c0c0f200c407684905480b41440b80d41035030384468980c051844e013907485135a07800c0046c0300c070291941140024003001c0c094998880081c1c40003030103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 59238915 1250 59237665 59237671
    0x5190c08060105060a21180b060405010504050906010303030b040b0a03060c0905010504180209060d02070503040306060b070c0302060c0c04180c0b03071407061506051b01061a0a1106010e 82
    0x40da01401000040500b00801260f88042e49543c4040b080420001c01da81a40040c07080c0c1028680c0c0d41c017100034981a0740200102c964042c500724810703460b000080200341c88058100c103000d5802c0605021180800040c00c0341034a9040c2070100d454203015002c00c0040a480311100d500885104001082c45041d9100d0510440107030345070704c1e08075146d00041d100c81c40789100e65114002c2c500d04005410140da400703030280660080c40c891034003610760100410303078000e440243c5040d000024104204002c52280074000e041c0c03515000e08008140e01d400e18405a2444042e002d840006001841d03107a05114408402000401c1007107000984550746098074410142190b98400c0c0c043c0218600380700c0025a0704c41c508540e154142510881c074000d02d0342d08860000c4420584070b01000c018108003400040140100d96285034035103d4801c1180142d041d03801c54201c0d10392401c0c40a00610000252002c45400a00c6280e540c03601820011541c01d0040c00c02040d0501030703400003081c9102040c0c02c241c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 59240165 1250 59238915 59238929
    0xd051830030a05220c14060c0a0605010f090606050405010f030906060e07031503021e030f070e150909060103081605060a0516080c03060405190e0a05120702060403060905190c 77
    0x40040c4040a030954807440c00c00342001e02402002c2100d0032000086c00c0c0c8414024205c10304001c5440b58451502d201e01d4400ca83e5552920014030440104442032401044404402c0c00014079060000e44580306a004080c100110000064540d500076004104100c0c2e000d40108000daa41d51907220b2101004d48007540003908015643c00c204640b000c1140031b80c2e40051410310100c40d801c0300d001c140d400b25a80710342c01d8010365070001c000c12024010700d401010a800280582e20b03019050a08860074040c00b9031082003100c0502c40d1b11400041c00906480d440301030b5964440b0300a08004013049800002480d51254a041000c80541d90304245e008000c0ca644480c0d4091250b00c0940710040211803520495009000040311494503811541e00304a420310290040c00540b10448207030f5140c05003c01e11640040720702d8040040c2002412500380c213200b5800c0c2041d000d0b0340002d009101e540300107440c090319103a010b01844000d0016160030698004005402c690f10700e040702c03e03003440e841040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 59241415 1250 59240165 59240191
    0xe210607080c21070e10080f0a0e0c040b06040902070302030904060b0705030a0806040f05090d09140a030201143604050c0304030f090b03010b0d051830030a05 70
    0x742d1003604120544850f1014228281a030507098150180c0440c0e000300f40c1e404014406800c1c01040c0ca41e4056855408200c0e650705805140840d1410621031010342007441c000c0c038042c02e40c000c41c20049400d82504c2004c0341d01240e900c0944000900c5801307180c2180c0740039880040c3c101c0405800000500c02c10304181c8041c081d896480300c3c2c5e28164054810007802070742040001d0411382d0f11400f040d41d031168004000081004101c400d1300101d44003280c1910066200016501072150407090b944011700c21004c21000c0030a41c01c01107000d10b0320b1488002c3c18021a4142502203945c19419500c0100a4281d000d2032602c0c41c4140000000d800c440c40d031400403a00e004407459050900601f4482d02d85146480d02d151070b1507508841c050b5401c03010808201c0d15800101d94440e11380015070007840200710064072518450010002c4440280c1010142c25941c0c5280154510104101c070100a241d21070320901405000c039010130001030310703001800d02c500208101c2c038500c9960001e8012200070a0720 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 59242665 1250 59241415 59241421
    0x4080c06130b0a030608060a0e0f010b011e02030f0a02010606140c070302121005010306020a11162c040302101a09060f18090c04050c04030308070e21060708 69
    0x1104891003031030103021a0104600040c429003a03003400801c3e68030800d16000807490341d1601050f041450a85000616984903414074210000030000e0211440108008104044070500040d01c807403101661191159481c0580300c1c0131034000c4c02a900020001215959180301c1103000a0080c0310b90300526000c600103c00030011180080300b9182c0d1466140300401d491429a002c004540709a515600c005200b12054184d24444a019003402507201e02005a00ca200c041400b40c002002d442a822741a4000c0d05032900000740962480c040300d503120681600d2544a82a112001c2d03c02e011100405041505010400d0360005920300321143c100e1080143c0043c164081c101c2c0748200072550780c0702c001080820428034140140005da924010505c0e02d0140c0701400d500084403080320a81317072607044405070019900b45402096480804074104516290542d0b034050071204001d811001040051b90650005468802091400724008000340301c601180e03440e5103a990004039242c030300050790b001c08 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 59243915 1250 59242665 59242669
    0x10e010e0f0c120a0f09030f080903090d020d020d1403070303110f031902040504090f11010e090f04050a08030c07061406030a0f0c0e0903030103030f021515010207030501020c0304080c 81
    0x40c0710300911a40c2c208034540685214015030340540644942511a550f180e600d606081034402c2808080c42501c0f1204801c41038400030300341c40c50007004a04070350000c002c0340889070f4418041d104d1140c4d048030311000007070441c0040345064800100040c410141c0440104018100202508695110366070922048000c400d0f524058002c00b400307420240f1051001c03582640103140620001403a10300b0043c201036032a0300090548a2521041c0c5032041a001d0040a0005422400b0a290000c1c00c10381d001d4002000404e001c120014030105c0c5241c5c5100104007000814091000703960b8000c2d0509403a402c2c041e03e841c00e07550101d94111001894614400d0b811005015100d22441e402030103401940724030344600003003821194040750300c460240c1d004901d004503251080e0040710004000c649070b40c110300d00941020b081c118120159030110238007090032a84528941e81c040c940d9140e9502d038441010043c0e01d07020441d0401807407540082900c074010100000031740100c80f441007c9414410034881 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 59245165 1250 59243915 59243941
    0x30403140a030801050108090a1b060e030102030f0103200a0303030c081605030a0f0b0d030e01090b0403150e01020c2a0a080a030e0102030f04060c300f0215010e010e 73
    0x4008000c503c6a100401c001d40c02007080d00d5202451600340c0e00f80c1d802958994000c0640a046402031240180c400d100196220a0b10488254280c00852071030900d1084113070745c1441440f00600079078540d14045c041e01c40b6000302c4210000043c04600c4007030340380d1a000d00034040e900c2030b0b01c002440e91400180c8858298207003a1421555458003450350f1280841321020f000c0007200c954046490760400c03140b648402060480702806030740c5000020034240001045c034070a90b0b0090075201d40a020500220340d10b4014480e454102c0340e000501807203c131a0150190041c00c40400031405030740d4000d41c8024100d44200400c610740c0e0407150882d2414020400803214901407210a940145504c40010b405007084035100790050044a00300422a00075080700e502c00d400203800103614200d41020801250540610500d41414265035829a80750b042102004143e004007004098a010320000e0b000f0300c0f01d1f64502c20807a11050056840e5000d408200d0400e02c030350300300180711100203142489518 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 59246415 1250 59245165 59245183
    0xc09060612050f0a0b010e1207090608030c030d0b0f030a030903020405060111100b0406030f03030c0f05030c070b0403030b060f0304050d02010c170601050d14060a08070f0603020708070506010803040314 89
    0x145603403c9031203d115a200900e68104080c0c14482e54500394811582d514500724000c603110001803913820300340070810301034500301d90201210b50300070b200b0303500c40140100075900c000002ca100013504609030000505003415000d42d041d0540581100007040c59800000311094034000e9805000c00e032501001107400b0881c8070405201508090f26145441c4002e4103e01c0f81800d008002060042e1031382c070740c0815542c8401c2c003203001c2580e4400340d8140ba83c0103010980c400105080990461800d55000c1525100307600b001800084820001000c1500a501c0f2040619000d030203d5240c0160030b400c03010544c802e0f40c0c02d8034144502803d1014180c4140525500c40f83e0540d210b010007030031042d0030030080801400042c1840818042400d01118512685801208070203040700642070640030b112800307441d50000300182d00800000e0140c00c0c00c0001504c1150703a07511307005070f413503100d400c100c04da500030a0801001401104000100810000b01902c140c0e4010014030309007501d00450b0503a507220030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 59247665 1250 59246415 59246431
    0x9050d1d060d020f03010b121e040201050a11010606031a0306070c12031e050411090403050a0f09260607050403020f04090602070f05010c0e09011802070f0c0906061205 74
    0x254164003054100003002e400b40c5000c81502500304910072900515942090b08132241030704020030b03040c42c9500340561040e004182c107051640404c500d0a541c170f80c0c001004001a05120001642429240c400c0c5581181d030b844946c000c00245032144801401b4104103007003059080805100814a8600403518901620720303901d46039900c60266440b1440000c3d148180c40926641e20540807541d0030011030903d45100018000902d0f107880c0c03402c60142f01c8801c00e254007a2010a0802000a42003012503140340341038180444c240c1e140c01380c02c5800d81403541110720800c0358144080760110032800c0020202c003d24080d0381c03840d595603c3c12a114091840065070040210075210441e00303055100103800c03406042c015250015907101c0e000807a80542d0100ca41da9074031081154801e5006400124030081156811841c2d450280b26035414460290021303d0685d0008104041010074000750b2451a84078040072981d0b0b80c0c401c00c080080c50036104410110340c2c050301403c4400428071030144290b103c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 59248915 1250 59247665 59247707
    0x507020d2a020f183414030a0b060403060e0601061b02010311091207030b070c0206030f060307050a0b090f01030c08070806060d090807050c090601091e0902040909050d 74
    0x15940800c809043c3c50701c100b0380c00810b50020000385401d00150740748902100c604d00c000301070190410003030030100c075000000300703107000c820500070039174010141400701000c22411510307611044041c40050104081156002000240000c20000b040d00302d500c00740581410303079403580c2e43c5107001d8074010202105d04c25012a00d02032400190f00a42c46010826480f090050070005140d012413601c1d414082c401100b0b0340b009004004100c030080f00340364480017510304410100c4032030f4082120750002600401d03d030140382d00054881c1e101045588010b000003032420050540d6220079082c030350f000c800701501440c1260108013041d4040e018680a202c42580e90310344599039460100d4a12201400540d4418001c11a50032a0340c902d015000886002e420a19075805240c80c09520f8403103011a4a401a85040204210390382c101407580116800440c0d100c0f00800b030f40e403101880c2c0a01c0e400c810f40701480403030040f80d40d0043d6841a038030280b0440494039890812042510340e040c1420400c204080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 59250165 1250 59248915 59248997
    0x904030212070302070f09091202030f040e150d030c0b010f030807060213050406080d0315050a0b0304050c030a060b01020f0604170901020703080a0323010501050d110c010507020d 79
    0x5104000b010007070f0007841560302c0191a940703d034009040d0303035200160b4161502102c0c0248202d60131226024550b40c001903113070402c0c1100380c141d00d0055104800041150750300140315004041c011120140b0700501c0d03003c2d2a000362070094034008003842c066a10b01f40c070400108201c0b202d9100da0080c1c0742c2140c0c80f141040e4017542c404020b0362119500140703030442c84400054584940c060b0304060540744010f03008510540b20b006088402c0c04034a00b0300c40325100d03406c000c0c6442e40e07070b6120260b4686825503030396035a031130074618030f0500700000070354161150b0102c80d0113105103540401d42651090f4242d030a05844c0e0040603984040c240c1d4040d080d10300745483ca4004000c00001010f60b8081801900c521075900d40310b5000d240c01407070740312010a40300d042c60420070742050789010312503500401014065041c580000c005001d039400c4038240c6070f5a05101030341c20341c41ca0207907082e1424000091080d03250114009440c0c40418500130041038440b02583c1c1004540704031040981c140e13501242d9200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 59251415 1250 59250165 59250193
    0x150f08160e03060a0e0c01180510021509150109020304020f10090308030f070201051008060a0b060d1a040b060903060f04062403020f1002060f061c0b0f0609040302 72
    0x300003030081505018448100300074948080c022144604086513002039000094241c1604203901c00d24050b0410140012800321120302a6540c0196141074074800c0941c614000c0c182c0c0b420703454403080c0350358400540402142c400c0020f17a404104071203c2c0d1440071660f0f560a081d0582c00f085d10b00135405044107440c1070a504001a494003580610300d85100308aa803a21036100f20b81c03081c1c400e80080074442c001c001c002902406960381004000320049801842c05001c0c544620020303060100098966080d08003603038501d4180c80d81a04044420000940f280070a0401345001001e4140501d092120719001d500c1d00c00c050301c074400c102031301034000340d902d441c19a00025070082c8101c42da65612513142e00c0100203140743c44400d086085031403d40c14114010032038000c810000503803044520808800c1e0381a808546113411000461000206850740d1002503400490000c0d0031000c01c5000e04a03205015a0001c401d01030040c0c4241c0804075200c086c184841c1180495019000d64001100940c81d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 59252665 1250 59251415 59251441
    0x7060207120e0d1209050d0f1703040b04080a0302090a09051e0c07030c15091406090123040201020703062c030f04050910050415032a05060c030c03030709150f08 71
    0x803090b40340200c5c116494000142d0310300004042a1601207105020100f00324090311600c0c503a08441e8032682c03c6203440e035540909240020801851400c1c04282860300e00d00a4041c2c07805080010038004a05031981020402404100c0308480d0b412018001c0c0010840c424119600800d5151110361034000c441e10b083e40c1c4415628030403160b45030300b2410a0007207589803103420111445489a1513100c2140038002d40741c000050008001e0346d141562569042004002554541c2e8114080c4081580c841c00140c0c100451640054030345801d00f484080c14088a0850752600740350708006504031a01e13020056600d02078007800a0b2502010070090040d490603c16640e48035108420305d01182d6110300102d01510700003103502c003114200040510822108a0303444034054000818204814480c1b001800c6220300d9204103070281c07000007066614600d050003111360000828013103942c0c03824506001032501055110354a08010701d00040309150f07103d8020881006020f03038404045e07488100c008144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 59253915 1250 59252665 59252693
    0x50a050c0f090604050a0b0406080c09090a0b0111012d0207021c0c03060e100b010309021e210304060f050a0c060b0d0203060403020c0f01030b0105040312021207060207120e0d 77
    0x1200f002400001041d50300c40c0e03044006481c03401c1c0c080b44c58078640760014104541c0601221340a440c140034070a0396440d984030710766020f00d2440020500344040c00045e02c0d402401442c90300d1550810201d00213408a140070418504000285130803513550800d0003408a010f08600294011042c80d1411840c1c02c1204003a802640140b4a40c04007540ea603a40c0f208840703a40b09a8072858000c01c032444151103040c41402e0719100d003070805000b440c50746d500040b0501c00c861032510389100000c80e03144051710345810048519421490021100064000d0242d40c2d80251068600280c2e03444544205288600c00f61480030003107440d034989034045552424013074006a00b40c1500039400c00c19040c0940d03400c02c9414020790094001c1d011207000a000c0c000000c02c40010281410706100001a85992120444e81120b420030410000c0344082c0b8400c90404c199581d513030100c0c181c046803480a00c00180d00400705d2520a01c00000055158072041d0b81100c00c2d2110582d000d550403034520302049160300341d048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 59255165 1250 59253915 59253919
    0x1504120602030a1107110108060909030304020112020f070c03020f01030e1b060d0c0e1801080706180f0312170106082710060f050301020403050d050703141c050a050c0f09 75
    0x1113000d991500c00115410840084c1c540381011002d801c95540c00c201159000318049d10406000e03e0034405856881c400904000e04008010b4000600146264142c0b610954207281d2203540756498104900003c5260005910407403002c1c00450a0758028481c0005140c0c01c08050900b2010401d040300b0002800e80c0001e80040702000031800426892003000410340c41038981d01080210b8009114610007031070207105201000d00d005010030400041c2c088100e0f0f9603841c0c10001000c0b0b507007020210702c00c40c0c2e0000002c0c01c0d0080022042003400600e43c0c04034602c45e50380c000c0003140802481c820100a100e038501060440010131061000c1450440140c032403a89001e201b42c080c0094185400c1c0f04e51528802d50743d540d68103000040880d00b480d03009284c01c40c02942040d0079619541d8407004409902428000001019020180520502c60305030101159058641c1c904988040d2941d55440e510b040e864600400601031410510400303000f000c1545030a401c1150111100c00c0d1a402200856 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 59256415 1250 59255165 59255171
    0xe03070b2706070306060e01091a2803050708100e0115051201080c0301060b030c0a030506030f0109120f02010c080601030c0203091302040602010509120f0315060d0501051504120602030a 82
    0x3201d0700780104001402055141e900284036890f0603402800d24028241107410000311460400400008103c0110500c0c0740c82d00080d5134900043c40b2591500c2d0455000d0403a8858400801c82d503074143d400701d071150405d40c690700d81582d501c103c2c0e1450b91200c1d008091840701a00c00502c18200402d14002c048109030170100d240034a0350325400300c40034003640502d11942c0303c2042c007461030a0078001e0800514813003620b01d003142002c00c51040c460040b40c202038100b50b81d407800561555002c1001155415002c0000c000300c2d10241048071301030004080403404030707080d001c0000780c46205126859600582d6039074030710700e41c442c0d2004402802c0303030540c01c80452005100650a1703a5440c04601d091043c440c0c001a503a030b191041c00703030950300c00a001c030345141c000801c14909002c0e414101c40c0c0a2007041001070b501e96484016242103d40048010340214001c0349410b9031003035a620050590700210344040c02a20b140345400300e075208a02881903120300c0d1406140c0003440c25005107802000448001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 59257665 1250 59256415 59256481
    0x70b03040303020d140403020c0102011a1003090b041b0e04110d0305090312030412020606030304120620090406050a0503031602040b091e0603070f03030809070e090708010e03070b 79
    0x10240c9405c00d02100c204c508003400d00c020541c042150745c880c110207000a10103440c82440c03042c98481d0544410f402075840090080541d8401d511910b401c2d64051800e01050030141484042c84501d032516030300441c480d038030210300a80d00d180403d100d00c2d8000c04000505c03a41d0401e001c00c001d00382c0c1c0e00710244401440b481d0400d80c1d040c0407409400d618110019180c1c909814460280c0005113182401d40d00100103110550714080121800d5440c80504802e845c2050310b80040203240240c07441c41820014040b04002ca1410801482c4d54941240c05021080d02c1d1010004076014602c00d180d0726610401c9015648940b01d1300021003540014000a0101003400128181081c00c40d41e4403015080448501d02008203410801e8010b003040c0c0003005800d0804030052440002800080d00703211620000402d40101002044064080c6101c00340302070611003940e80d0f40f24041d004201065003003140c91205040e00000f42d50311140c10482800d1503132582078101050307440a2903c40085031400d901 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 59258915 1250 59257665 59257687
    0xf0e060a2102031e060a06080115050403062a020f0c010c020f030604080306130903020d052a0705120309060403020f180c030402010801080f0a110f04091b0f08070b0304030302 77
    0x2d18481c420020080c4004050a40386414018004055512a0001070030a007c41c0f0f038020400d44c15241c2c604070b180390418000009891034001c0d030348028105d604141040c010004412030f8401c444c14449038100d0a009c40e0328050741c55840b8007400078048d5110007024902988a55000d042860029024940b007201841c00703c2d04000c82120180c03039110000050041c2810204222811341244400070017540050341e038000d4642c0034072014001040f0000c00c49003100b003c10360b400c4a2040091049807506036201603225214101e51041d00e1084010001030b9890000100840f081c03100014034141c9024116400c205200d0f2912a00342c0d00450140d03926290581e60720600e9008110300075850b6264500761000412540058101034040c1e00300b0200b0214000d000070300310800c42d5100015100083d1050701050001c003000d00a02e40c000c0c20501e43da02805600c8110070b016452035450502c08545980789540141424420203d040c0c2c81754000708080e55810000d150864428139001d45072000b5002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 59260165 1250 59258915 59258917
    0xc091b140f0403050105040c0506070305040303120e06040b0108010606030b131a030303070c02040b010e0d030333030c080a02010903080d02040f080d0909050c0d09140109030f0f0e060a2102 83
    0x4225007580d075071407d00042c441429203140c01080300b01e59591500003190307001803442c041c0307200003801e116a8103029540c5c0030658102507801c0400004644843c58203050802c007a0500307203d5007400d9440c1080c08601c441c400d002d40d00652001a111100e503007403501c86030b002132015651103022078858030b1010000d650103000443c000c5000da80d8107020a562070041100301c500a4411034140a09803007801c841d51188055824407d0f09400d0001700300704c0c540a41040d0310075000588084848115031014441e61a20f80101580d001c0c0c007200b18a00e4940c00741d140e480c54203110180c08071b101014100300140c0d4500051015100c00400581050360302d41a005008510360004003258001d04e03a007000d010303441100300e401445c06032024070803400c00340c80c03a010520880d000c007201d440c0c41d01c040c101030000c00500b40c03080c080c0c0c0f0306c001c00c550765031414010311401c07000c800c040006000101080da010310949201000000003030040b441c0c03030601c400070b03101c0e071400c05040c1840e000700000b2544140f00380c1c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 59261415 1250 59260165 59260169
    0x70506070c211e021305090f01050c13080106060c08030903040801020d0c031503030e0d21021e0d090e151002030a030f2717160c091b140f04 62
    0xa0001c0d07203801c01440e00061080f501c1205415440e030416440700940d07509060908400c0c043c0a00042648a60a0203070070001c1101e04483c00b5803d00051061182c8240c00800890f00300003103e1100d0f6855072141800c1e1055481898001021222000b01141f0100002c41d005142001100e01d850340d03031410942a40c214100d042039070342ea540d18550007190180184d040420540c18000138141c00c1d607802518400d80781e03014a000b03c603801c22200c104440240c86200146400c12207031210491800000d503901d181850f8001401c0d040410480700020000e2074080c6516103464204415040c60250745000380020300a01101a40040100302c58886c034460036010714141d80656a90300d04150081e05603108803903200f14007440c002080c0c15043d8182000482429913081c3d4a1640d1140c0c20507144044010380035440142e0300080742e03082c400c401c0c50010300d0244600340c03101740580e803107542004030341c1c1140d40d00c0b43d00c0a81d010f504900034402d81503002e880c801c0605807410310202d26480c0710560455 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 59262665 1250 59261415 59261459
    0x60c100905030a0f0810170c06120405010b06070f0b1b0a03050117121603090e0906150d020105030a150b04090b03070b090a0605070f060e03091203040503070506070c 73
    0x3140766031598011301d202d00240c8541044011814186080428401180702c0c410b0350b1403011001c101e40fa0024000d00c00d030808010135403500d070050b60364181034648040e41c1c12203640d03103000554041810808141c4420ba6008690604040d400b903c41902c5420004d041c0307509011149040c0c4c0c00c44101d03401030008601e41781e40000d4a50305189480b0ba261803160341218060f40008040103e442c81802122201c04031105d11411078103003460f060310600c0064005050006640003080500d880001c0c0091050124604031040d00c4842001c0c010003880c3c40c000a40052002c10000b0722443c2141c0000b04601c42d003e207003800482c1e0b210012262604640c000c003d6094841140072264030f810009600600080c0c1c9030f4501d0224801c00207000e0981d01e01ca440c0030b109000c07400d68148030310b0080f0b04486581000c0b0502c605007004603169120344c070002c00a481004045198031a1900010a03582034031000780083c54001d050504104060700b00b86011a4610b5405101254640002c641d51425240c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 59263915 1250 59262665 59262667
    0x609040c0512070915051803030301061112030402010903110f03190b0603030301060c0311030903150603011a1012091203230c040603020304020d0f03020717010501030c05060c10090503 81
    0x302c039800310201c003400b6000c041002030200003803040c28a00022007180d442d85040040d03075001140c544203170240007000d140f580f44c0408000080c04a17000540d6055402004040d02d550140140015540380030030756003c2d0006025007420700c005506250003281e00300000b0907900e60302c088900000d1821000401000035950300d66552000c02401004054109030114040d500310760419400030a6240843c0010b0b00f0000b4114007006c0840301841104d0712120040c1c2aa451110002c0701d12000c01000d8640a02039881c0010b290030100c074800c0307100c0714040c000b007070101c60302c008000454006110b847d4100042c0e980352220700008030f02d900745666104040d100813420300000d110800c07083c4a4000400c40f06440e05080024003003481d0225415190f140c100181c41e9156400403501c1d0807504c070313001080088030301020400e0540010320101144e003880200d401d07001d58000b0341c500307841080c03100500c00380d0f80102c2404149010700c081c0441034051800c48000e54144c0c883d46003500c00303000041d905504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 59265165 1250 59263915 59263927
    0xa0509030118140c03150627011509050405042105090406120209160c020103050403140c070f08010e2d03040605030405160303080609040c1a03010f05031513020609040c05 75
    0x5100e143d0b91303550110007422040740c41d101c840107101300041140d44034072400a83c88491440b40b00d0a81c2646102c47e01244403036171500540c010300000d0190b841c0c085041031a001030540341a02541d442242d110780c00120380d40c0100080030208500c41034040501505014a80581c4c542c0e110711002001400c0b50000002200d005201984802400300800c0c008a50408140e16400520354070003143c0c207280000d4903a413030b41000c68603403107010349034040c101001070a0b0711000400104041034880c1140c80f503041c5642c58005508845080c410390341d0a400c5078500a0301481280c80c01195040c201c3c0c0f01d4840d1030394047c1040e007198043e4101c003000c18404020300003401010071008401d04902000348208a00350b4502800b141c4002f040b8510884c1c8000c00501040321314041c95004080d480620804402082c01c100c1c2a60001d0284a43c4601c0c000c0002845142c001807a038124403882d1104045500c82103c11036100301e07004010b80e041030041220340b26030b444502c1401c00f40c1c001603455a403244 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 59266415 1250 59265165 59265203
    0xc080409020a12060608070816050706090605090f030306010914240a030b010e090103110d060c0e090a090305040b070501020903190b13020a05040c020a0c06170a050c0a0509030118 79
    0x4201790001c000b0414030301e040100709070300101000d420041c42070b00f4407001c0700440381c1124240700300c078002090b41d42401e01a41c2004040d8000c94000c03c03142c4251290800e0303900d0361170303503078041194280d0010b05250b40411041c4100b00e15110ba801c0042c203011400041c84207180303095146650400c151000010303d030381c02d45505100304c08007017400b417814400c24144140080d000c1c00043c0005805000e175090320003003568a0601c080700340c56000400780301e0911421805000071010140c0c45014084890010342a184240300e89001c5641c162101800c050520702c0001d141d0b04603010484203903600300080d42e1180e40810a02d145001ca542c001c0540e4400c500c0c00c40200600030301700c500c6084010b00189c0c0140e4541404c0c00540e40107071000a801c1c00f0101c0c0c122702c1e0031115400900002d8100b1004220a58006440d036041c2c2c07042c03286401035441d40304084c0121a0225000d010700c560610048000303034440d0000340300210001b400443e2801e2040706030b028220020000b21890031881482200d64 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 59267665 1250 59266415 59266421
    0x303070b2712090315010b0c0c180f040302030c03120118020a08012102040203150102060f07020d0521070806030106061b020603090307050a05060604060f14010c080409020a12 77
    0x700c0c04114019410101007180640d42d480c0204258507081c50100307422600f501c007000a0090a2541507840700256958884020282d01c03941071803845000c0d640303103410f941c00c2c07501401c10100c005040a500c581d403241d843c000c40d50000360084085000405c8408220300b410009000c0b00c91031030407188590752508240103410960488520345903401809034240c55508041c0580c112031500c3c2400c800c118520941d0201c0d94008800298080e00c0401403005095540499502c24142a000c644c0603881c2c004603802801d904464140051b403200c40d050441510640c050540c0000090071180f128404403011181c21404a48190010b80722800300003040c602409040010b008904281ca0075401c4541c1440b0754000310720340603016920000c0841d4203101c040040391003540e0424191903a00075149011070711030070f09440c083d11983c20802d01044483c02d00d000c40003201c5c03070340850301c911203d03810040d940c5c2d000481043e40c0c010400d2200042c7c441c0740e070004000400c01580ca800e1080c660540b40421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 59268915 1250 59267665 59267701
    0x608010606080106050324030f01020304060c0504050916031d0a230d260108030304030806030c090a050709230a240c052806050603011109010e01020106050303070b 72
    0x100441e10b001041803541040440c0d4010420601c101c00070079030007c0d0b4004031404244950307018820b52614019001066024501a81c403643c0c0910541c40310750001c0b18180654043c040d440a40d51000c10002c80100400842d00c0d0000c2c10007054078900e0810200c41119600c034416103c2c0c000300c20950811040c0004002802d200007030b41c0c5410703c01000c506588004e00039582c018044d21304c8004250a059001603042c0441440c03e1048079a181c0c80426182c0c2c0055404502040c00400480c425207030204980000400141082d913107686c468080c0400380c80c02610010a04c2410600401c0070b8202d00b07228681e816007014064083e100281c11b02045800e250300c68901546171445400e54440f0035000c11841114038a00f111800031941011810003284038251544406c600f440312101500e142080b5000307902844080007031b60785000c00d05090300c1070300d0481c11081c0b10401544c1441d40c0a094540488501071000180745a00d40c00424956402040161407108510341081135aa6800300344600c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 59270165 1250 59268915 59268917
    0x4020d0603020126070c02060c0d1709030c0a0303050402120615011101090b01060507150f060302120312010e190501030605101e050915031006050901051503040602030903070b04060608010606 84
    0x584c1145580354491861003c1e00880030071001004120540d910b50058580d0118007405490320b455901d503016049007950149580709185241c00103603411404002d4a112440001c00351410200756074040b8001c1900900403644141066152480d03c0410001c00344102c80c84d058032800980d0030070014155100456030b6121a0b0705003083c14000607184503080d411541c0c41c2c10010b46540c064580210b03100804120400c0440c0351201d00d100c10001ca81049080324003d0300e024210394a0417283c1916441440240f6446d2490709004108080d42505000c2e80600084822070180c0d480e07001007001d84000382d000b920034540b10014800350a000c15031081c0208288001e83e510307481c21200c110141281d611403a4407911b2024009840984110388600155030011705403011070840e015118001d1141d4082e840c040c6a1305800401e150130f00c071150310211301d01541c503a821a581ca42d00e60004c2c0d44001c01600c0c040c007041c0040b10005031080c0c00325020303601c5440e01055942c02c21401c40e00715802644400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 59271415 1250 59270165 59270207
    0xc0114010b0705280206070b1b0f0306010f02010e0a05070f0b040f060c060207140a0327050622030c0806070801050f0402070201020708070f060206060d051203090c04020d06030201 79
    0xd000100f0000708004204002032104080ca207200780981d19150704440041e4000310002124410440344203200c82c412448d501941c5903005c105803642d807483c000e00400b0800a0303000c1003c41e041d0341c010500e0310380c0030132984000b04211560015580c1070100e4010111100d510450040c00442001c1604601401c2404e02580c0ad0a28141c2a050703940414422700742408501c55214040c025950101d40c1510340040c4001071007800441900d0783d03030415120582c002001e44050111a800c40322485400d5240d20784800c5c5628144070401200c0c0e1710024142c3e00c03030074410401094104882c04407100440c080d0a40140c280e240c240707a581845001000310003044420740041c8841c3e0b03180ca007225403201041d50010386407842440142c1c0350031169048402e06109007400000d0005944150f582a165a40c0c283c852076101c440c02e1000100c0e0b2214005c0c0260030070249103800c0100000a55440101281241c035407403ca940030808980c00010340b0a41d1648075041032041d543c0007282c00c0c190250307940401d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 59272665 1250 59271415 59271427
    0x8180f0f01050f030c0f0403080a02100501050306010605090109080d02010203040507080a03020303040807080d0609020a0e0102010e060609040510060305100606050913020a12020d0903030513050304031e080c0114010b 95
    0x82c080d208420a504041d0404004035540940e968282d5851410041245540c0c0d40c5900b00744400b41c02904000c0018030408510450044460080318100c40c0d024004240b20b90070400280d0f603c0d009200c00031304200c1c0b83c200006c0c040744104120b004d0759006800059507402e250038243e0074820b842e0000d00860b8040c0980307200013a800811a5801600300da0710a880e00001c0c07a103000e05100d81c0101c1c4100505003a40480c0c03070030f140d600030a00b40c2d400340c88a01c06100040010380c02da40c1101548903658003c2d000081e440e040c143e80081e0b004d03228400380c94076400201c18000440c0c0090b0000e0315168894070301d900e10310049114020207008142011401c2c5500400010a00000a5841c0c010307190041130b105440c034040e40d030124901c0c80c01081992a81740300b030455401484808000d4002900f0280403030411800c1c803150174525500280554a01030550716017140000d1100c20114030034102d080d072000400c802d000980345c005204400415017940302e28034180c05243c180c000d0861040f0030849 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 59273915 1250 59272665 59272667
    0x30c010f020c010f030e1c03060824070203070c0b070506010b0f0d0b010228120311030711120301030501140601050903030d150905010f0807080606130b0d08180f0f01 73
    0x100d164102c000d2070400132500c01014110301030540c0d60100105e910400c025502d40786043c1800740401c0e1966a401c0144d20394981c50356070b442c4a4110300144400c80200550045561922071503030201147c0112803a050080d80e0b58001c10700c180d40006000100800c25000300501400840d005141c3d800c0c00d175080c5079440384001414480e0740c40c00c4003029602e4040b01c801c0d9000307200d80341c0c8407552119866040c402c240d0405404c403401ca44115021542682c0100d5428003074801c00001c0b0980d54900c500b144e0320648191645c85441c6260501da1041c80d9031440c07030354401d00c0207502851103070002045800c0d0480007407215840282000d03060000522440e00580c60000584005282072500031401c0e050074084040c0d081c0c1c0715040681d9060070704e030021481c41100000101150310081c1240d076001d82d5403490f582c6590066954903400398082403802c803d0b41c4c1d02d0300a601d101600030b100442d124460364580005922454402400060b8824052000d103860a805543c040082d1550001101100c1c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 59275165 1250 59273915 59273923
    0x316030e010b0109140102070b0d020408120307020c010c0501090807140c010311030a0c09050604061e08061507031b1b06020606030a030f1e030204030b0604150303030b03010b030615030c010f02 85
    0x103040100401c5c007440180340c2e8801c00020005091502e0800e40d40e0307071481109000f960090052001610941c40c1001003c17880d942201d10880300c66000e003d680c0c50301c0004541d0b81c41c6481003600c5640d00d456000001c038400100400300307903200b01d4080100000a0004a040400c842d4801d8107040c41d00280c0940d036580c0300b040725802a80042d0010381001d80a200351480c2c4803980240f41c2166000c1004510b15030021070b5003110441c0030819180c1d1030001182203400d40021180aa04140c10723459001002e003428015046462007420030071080e42c10b1507070712070700b002072480705541012110110201110443e0744100203480c152020700b0b1585803410100e6942e24915100404000607001c00694042c4170380140c948050000340300d84940d0360031802c001d02039002030005640304940700b0046036080c0303058490314200280400c0340a800710b2035510290020290f4103003464144d5268440d21220347d070207011182c404d451903000c0c850071019060502d46084845d018032410b00c0b200d03640c043d480d150001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 59276415 1250 59275165 59275169
    0x90506010b090301090605012c070519050409050a1e1103040b060a05030709051b03060d1101120914010f0903021c0c0b010303050d0b010203040605070602030604020c030316030e010b0109 82
    0xd00c41c9568100d20000b00b070042c0655440985810700d88000030811450245005010302419401c00044d842105003042c06890180c400c50013107041004860000c00608061320342500c050b003086800c05030b0f02e01c2440107030b42781102c80380c518a035580d41d401c0b00b0055002c0c901b01c0d02c000044040100700000303840200035102c05800038010100341c000203991582c9910818005d800082d05031880c00b41e48460f8100548010380303c0e203a4084080c0402c5c032004010314152803150000400240c4683c40030740396940b04070740100f000c0d810015400c00f072411341c41071805102540d6126030001c072040d6000d042080c0c2120410a0188095070500a10b00c021130b500003000d40a41100800c02d4040d001000c1069500c0103c00e800180070f01e00e80f400000515400030058089244017070401c0c001c2600400c0120b032203100310300452002c0b503010701102000c20f50a90140d64420703409000140740c1110445030502c0d40d003007150350381c041c401100302208145600d40500701855003001c000703215030790145001078000200c42c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 59277665 1250 59276415 59276429
    0x70b04030605090106050a08030d0501140f100210061203030501080114010510050c0a0804050102160b0a1409030109050d260601260a050601090b0c03030604020c030c0712031209050601 81
    0x200c0105007450f4080d4403100040070003e01f200071250342c03520030588075040141c00c40011843c0600000d82591102c12031084448010149800325812108001105201411070f204600c920000742048440520400000d0a102c0025448101580c50024140d0b0310507040203140364108100414a00300300e001040c1501c404a074921103c0c0d00080c0300312410700880d40041028030032030f807915051190307550003001600c00a9003950040704459100d01a0012548101c0b1002d8030100642d041451090094030356481c108040c0b140360854143c0046e00755844c1c070406481c550411071342c20643c26000380315600104000c2c0040070038640502c070000d40191004060314103000303518085a01c620b08a240718680034140301d001d048181440500f9400504040b10a240819004040426502e45900c241c440c6a041c01000b0f500e9580d032001848082c0d00611008481c1d40f07c148600c0750540d105004803009441c4030600801518480d0600810503c2c10310401030885140690a00200d540400e07010b0551f020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 59278915 1250 59277665 59277671
    0x903050306033009030f0303100e150d02120109140105010e28090204091a1006020a020d061505060703030b13021204060b06160506010503120c06010e04081c090c08070b040306 77
    0x204c030300800c0c108441c4000d6024140800020468041004d10a040550b0343d103a1202c1155515541e101c1d40ca1591481c02035440111301504000501d000c410501203a201400080746c801ea141d82d520020384070190a040b801d944650040c0031045001e01810382c40201c1c55003614087d84501c8924140f0700c00c00049c215400d8640078034200f5034031650840690030350700010444c2516103101d80f00d003002c0b500750b07201402e0000041002407183e00c0001c914000742d0700200441420009a9900340040480721413801c3c1200c025500040c583d503a2a000d0320184c2e00945010407550400300c03c00c0528a80c61211484452051001c07490b10028119116401a03100318005010400400001c86e14040d5100ca605071400503001a0b0400501103407079812140c040e0101c9201da801c024603680c0501400d003811800d54821401040f003074907103208454105020341c201e0352401c81001c060070446ea41c20003ca142c41c58840389154108030038030b001c0c5401000700701d01a020841c180b29200040d80309921000e4040740c0c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 59280165 1250 59278915 59278927
    0x30809070e01080c010806030d171305010c0908060112030504060503060310060f0801050a0e0606060a03110a0c03020d3b03030c0a031d060a05070609050109030503060330 75
    0x100800580d40036041e100025149580c0d16202a9911560003a0f020300248007a0080b82643c00c00240d04100d21605031101c8600c05801860145002002003404100540d107100c01408100e080c415803012120603600d004103d4108040c0c0c0b403400030181e024049664402c000200400c2d07000003560241c5030309240159903500c5003070000346464602504083d200c1c3c070388900069001c0c000b030008803c03100200000d114965661001d18121405540c3c540c000b0340090000940368030702000149441207142c1000900d1044000c112461500601c94104c04100007441100505804100e80101030f0202c1c9008048143c40e05040a40e04016a041400801e46e0701c92120542401c0d81c4029501e100140482e600d50080e1140c055071102e1010707054000c91014180003600560041501008040c05402d40d4900880100c040b1b819600c5060140c4007aa070701c80516001817420b00401032158081d940d0306440e07007815801c0508082030000e2180d114140a0000b0049980b11034152071101c0001b00b80301c0d1070f24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 59281415 1250 59280165 59280181
    0x60703090f0b0a020a0905030307120f0207090504050c010801050607022b0501020f0a11120702010c020609040c08040209090307170310031a04120c051e031917060f09040308 76
    0x2041c070301c60003089100c4440800406802c41d03405003100608030350b1010301c180c0c1c2e10030a05480e0300c5480342c0540141c00c203072001340700d4901a1029840c20940c61040701c0a05540d40c0d4072000315101507030b08640a4110308400c950307540e845544640501803c0b03502c203192407100d038001280c0110380c52881c52908021003800b103817541c0c550321384080990044000e5540f071043c0803080300c05502c00c0b1750b00c0012414603885124541030015030400c00c142a00c1d0040d207810340f2130b001503d00c080442000c9910100030032000d41d989c1c4031401180c10002c0151203903032543c10306104018900b540245810030030f074002d00c14400400c0f008440f0301d200e080030105040c1d494a41110001c05003d10b40c10140c0038800d1090180c400d80e8105c81140d200c0c9020f4410440e4060010408841c071401c5100d000d440783e80101c40796004888012802c50680c140042100e107001d00c20311860403510008158000485c1d0000c840e150070824280ca61980700e04d080301c0386140005420000340f0340b9940680098100f1240c1c1e03000600c24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 59282665 1250 59281415 59281433
    0x40302030c0f0c0901080d0f0819020f0304110f06040911070b07180905010303050d0e1507050702011d0d121b150e07061209020105040f090603020a150206070309 71
    0x644014060b18032200c6080e007050340d54603403080900c0c060000c80b000000c0c92500071542101c501d40941e5485140005540103c0b1940d40c0034210810340002d03112910703669000c41c4003c02d030903a6038590183d00c1345014102001d00b01c41c0704250307500036043c240e8028169070b42c0c041101e003070b9004c0b80d00000d600c03e100d480f281003501482a0040132440228280844c440d0041750f901c80d0540c1c81001002c80c26100e41e000c1098600a1000a000c10303c180002104441c054119601140d080d0045420521041107a6440480140c1ba00b502042002401c0025035074050310030040c05200c2082c1c444003a580c0d10104181d2280120003501c8400340c0380d544043c841c0305900d1840c207071071180c1982d6078060b801c1c00c200c01096900d0401c180500c1c5402c44480300002c02003140300448074541c445903840306104a03044045c0c070341e815080b0f0400004000200e9000103c1c4184805801d85201c001007060461060040220341a0019803889000c100070700d4120754009541c1c2d50010661130302041244483c5031a10700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 59283915 1250 59282665 59282677
    0x20c09070e011103040b0408060f090a0305090103051e0f010513090b0a0c0c060501080105010914060a03030f03150f0503070b040e040807020f040f0b010807090503100908040b0f071b140904030203 86
    0x4061b100150004411900091060180d410364003050451348544c0c46461350b68000c2e40006020030b00074481403030190b010f80c1c4059840b181409400c2c4940d0304c50321085005500894164502c2d06005006200c14200741c491001c8103c00700ca401c210f114000c1c2c4510b00e40801c010281e6244a443d0072105000910078811644001d610820610007961186a028040d110901801c64282e01d000c8010b1072642421100030700408014201000c8541541c5080700c0c100f844540040c180742d1103015641002c1c0c400c0c2c03141030081c1401c4204503c40b5060034100340c1007100e40c1d4014080341d04240006d0040b0440c0303500003174000d9031100c545030391040d0620220740c0e007018020b4102c0c1d00030b2801c01c20700c400e140a0b0300041603000003640c48d105c0b1030340e6840e01078529522502402d905075200440c04807444c1c0310303580300e0070401d4050181c581c2441e6450818003001d901004454001030004680c990401c08468801e0340403001c020050501281041c03038255440d1100c494141c400e003140d50128007450300038022030f01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 59285165 1250 59283915 59283929
    0x406141b0f0601050108070e0d03030b06160303150801020a0504060809010b0604060201020307110601080c0402070609050708031c02120c070309080118020a080a0b040803040515070f020c09070e01110304 89
    0x2440d0781d2040010791141424801c40c1c0c080b960b50400940054810a4841580000100560030700040f03918220000c150300c03213000d900000100300030702d108002401100c4140e880303540d01285070a880316151800310010340c080c1d27066a0042c80004102c94002c8140c40c2035418a180403e00b55a60104a42c0500a03001d061a004400050085039076981034005500ca14620b4540484124400c41c582d41d4403613091048102e0360b0030101007030781a0701d815001400e8503030090f0400b05480d902c0d9292141030000c0d60348004074a0f0700020307420207811590842109002c01c004021400e00f40700504001d10488014070701e68600328001041010180266441c20161000400030040c112000c1c0240f01303a2110008242e224845100700060b1102c400280c41088540c0015441055200e554441101c4e8102070001c40705800f800c0c0c4035101c1081c208140d170b0311407202981c505121038282000a0b040900c0000c403e40204100b40400510a0304049030009000d420301c0c00f458401601c1d11039a00b940520b8101d84 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 59286415 1250 59285165 59285173
    0x10120807080d0203090f0f0303220602030c03180102072001050d060b030709050402070206040603090c1a21040203070312120207060209030c1909020f040306050702100509030406141b 80
    0x89a4002c41d6016622928054045072004062542c0c015500e07000c145038015554403c10000e00d01d0501505031007004941e0307003480201c4400ca9136580040c0d8204651205160101200704000c000c00c43c035024400d107a4020086140c00388548801c02d40030403164240c0c0d4103001501c0e81c98002d92103401103481e00e05403d80c0c200000b0707488181c208070642c0103458280005600344800304240c5890310882e942194006c02803840c2928100341603000d06054202600e15210400c00040c0d0f400031906900d041d00316606055a07982d1600caa0003408035120385482d10140280c01c10000141c0300001e1503c1600d8103c248000d183c0e8918408540b80c55885051400c00c41c004180c5a04025254000d00013142045003503942d17040d0b144003440511a024005009150344040c1c041101064680c024106501441c20451400f074690311220150b9070140c030a500181d004ac551801085228030640b6004903600c400b843c41c0910307184000b4801d0701d542a1003482403e0006a00c03400d40ca14001203482c10480c0c030161 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 59287665 1250 59286415 59286427
    0x30218030109030c020909010608060a15050904030201050703110702033414030706020d05040909021f0804060606030204060c08030603070e0421020703020a120203010b0a09021b03031012080708 85
    0x4100d80010013040b40900400c401041102206009a4041c1c0384000c2c014201640d441c1c41600c090254414010034008248102285035269602030a20542c006e800108540c00c02c00c10043c1101d040341000c1d02c01e900d00340658001a83c000c60881241c1c0c0407070001125958041c038206060040303122604041d00000c050000719016400d00e14084a5402c40c10348540d680d594805070386030207984d040640041e00c100030501c03c5c10f0056010ba1a594005032041080c62582079422a1900001d202c400c0800c2189040104202180c00781c440507140c90b180c25814145801d401901104c10031034010404080840010000c0e202003001c0c0c0e00800c85001400c1e428201401c0082c20002ca01c03500b503642c200a401e0404a1600020f8001d04aa6001d001c0c190410325000c03481800e518500c104a80c19501d0304d407507120303540d10a0040c6020704810b07440140c0e907c042c0071492030b20300110940a4503079041030040103c248180240081215034094010b41d0141d15481c00100a00c5a000020517149001c124 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 59288915 1250 59287665 59287667
    0x30a240503010b0f0a150c05030d0603060b0d0302030307030e0a08040308251a0a020c0706050c161d06060714060103020103050105092514040326040305030a03021803010903 76
    0x20421580158002c0001001100034008483c1080103480c0d007207000090100710b40f00b10415805207a4101d072818907105a1103a07180307810740d40f11008030f0328181d490302030600500401d4815a0352100f0210f170480103460207564041d489000003002401419a43c1a076070800710000c0c0000d13001f490b032140702c0ca80c0c1d035512490b06c445c40b40c11079a042201c070043c03110f69024113040007942003d0075401040c5a61495407900c1c0480d54980c00420200415400307100000a01c1810071036075026100035140c0944880e00750034014607140e42c1d03a1600c41c1c42d12040708200300c1c540c1252051546128071a0b461040c1d81da400c800719011f8410314400070049084c000c03103094204008a01c0b5030507a4400da03000d00450f42c0c2c50042080e00702c410ba03202c2600d8161035200d00885c20305134900c4c4000700007909107205a03051198800030103401c1a031055410342c608484011a0380c40041443d01400c40c4010000d041605544580340d0744d014032030152080c10790008140003c40c060351020900d11038010002d008a40b903c0ca4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 59290165 1250 59288915 59288981
    0xf0a091a0a140307171911120105040209060918010314032803090b010e0609010e090303241302030415020406120f0b04050a0212010501020c010509040504080c060c0406080702160308030a 82
    0x510201b43d141c00360440c0038018040c225440700d403040104824070790800041200940c402880143c0c040010004440c550b00c5191002c42581450894242c40d585103080c550a42e41c00040340c0f00719600208036042203103003102c401925440c01c61000403080300800d4020780040c4a0341030050500c2c507841000085150f01c900300140b14040503140e20606076610061141010410340302031041c0e170001d00c0018803035280d8122000d42116006044080a184640481c110110b410301006400d50000100130138002c10740494005002c0c51042140780c00d2400400512221320480d0403c800c2e510f07541400e0320701e102da400400380800d00a00401180c100501c2e4400254442003000414140160001590f50f00120b03000301c0015040e11421715100d910300c100b00003880010300445031a40700380700c205004001001180d108007400090165100d00700039002e80003810040807030f011035005124803140c40302440c03144400c0344ea22641c032584940394411000003611209145c6035030301c4140c0302004644a0300e64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 59291415 1250 59290165 59290201
    0x8150106030c0207150c050c0a0602010209040e0c030309060c070e0703060e10030b011806030803040c080f0607050d0c022419050405060402010509060f0a091a0a14030717 75
    0x30700c0030004080c00c0d44003682c80d02d500d84a03007030303d542c4c0b0710320085403940c011007195003024444c0b8290f90064450100203000085d080d004100103039400304444030036082c18400c030821260703610018a2205d040d03c0020780c1e2441013042d11801980040388050480808206a00107001c10030b0002400d0b152801c0c0060062101d4495104020300c44c0c000700d13566800314803486060380d0300252030805680c24074022002c1d810404d1000d1107c00d80e81d0900001094004001e940110b00c20041c0c001461300d4103a00307510341005140340000c15007108081c0407059400c0400c0361394a82d9140c1022940c1c0b000ca400030303070400b00340343e841e0100b00c91481c081d01900f004004509100300b441608a05100718a41200300854004aa00405c01da1122006c0b401540c082d50252690880c001c000701d14104515090085642103070705d24070b000c516240801c3c82007a641644070b0349038440b641c148505003080c41a0040501500600300c03503103004000080351200f4422080c6408000045400911600300030074070000e110895 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 59292665 1250 59291415 59291417
    0xc030210050403080609150a151404030f11030613060b04060312120e0a020102121e04030c050102060a0e1507020313170d0c1502031e010305010c030b03030910051308150106 76
    0x150001550382009840784206c5490041e140303c920302d089c000c000450070542440d2800380007010084800100600d001000550b01c650030020450215160410202800c00e4a203032080d0001002c00005090426070301010b1604170f02c000c1024220f010116006204940024288402418030346840d940c0100003400205a41e06041010b0381044001075111286800700a00580002400d00c0e03481201c030014084100720f0242607400051300c901c000c01c40307a000c0d80c81100c11340c0020408004035a01032284560020101c0e80502c06100041078003910713407a000c2518000e4908420214204520030025070b4002e481904e440c6107030548618003001211240e9410840c03a01c24041c407090b0b0035200e03a0b9040d002035481409030f030110390060382c81006900000e001102c11140b000300200c540d003141d0240c82c02140140000104a00750a00040071307a10135500a078025402001400c0700d80d2502d6100e441d035001180341440e01d40c18040e0740300e04006500d600c0b840541c420b0405407512000b400046034101c8641d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 59293915 1250 59292665 59292679
    0x31a040f0c080a0e0a0f1a09160e010b0904020d091401020903010b120706080705070c03030e0315040b070c0f0807051c080c0f0903010b040c02160503010e0d0c0302100504030806 78
    0x501003161040d60745848000c1ca15070042d03101074000481d00ba51b01c0b00303e03511800340f0484502921000442c115011644d1040c19448414032001007280c480800c006001c152000c1d0070703e981000c500724041c0c40fa120390b07103004940c0003981105190f079541c0b04000007540b24407a60306901100b0780300c5020350440003401d8070075403800d4560b401a00c6d0040f01c1d490041542d901070b095180c80e04409641060000f4140001c0c048108a00c20019002c2010100950300c07940300c4003070181c0041c0c281864400450845e82c0300805030380034000450003c8201d81e45c005442c0c602100e207800545421301960042c0013000f00300000101d5210204500410740d070107900c400013400341c0c0140c40d0030000c036030101060f0360904008a0400291000d00e20b41001041030708406400842c402e140c0b14041000c481a0b41c1081b00180c003d61001d04900855001c0c850041030f0450003445944140390000c0d07241c465a034850780a1294040b00202098001c1c403103050203082801c030800c0949064100985a0082180d1652155031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 59295165 1250 59293915 59293921
    0x501090608070918061d0a080304060c1d04020f040f080f010c0f080402190b130603050c07020f040b0406120f110a21030909020408030702130203040201020607031a040f0c08 76
    0x10080c8100c400108030800c041540500603250800181b81811242c0c0620301d9140d1000d20712002000a80c1d1024403503644a50b9034034242c1000c108640e26541510b0030050908220300798200121400d2603104030882d00182e0b10180c0d13283e014100d110300c1e0f0129454421400001500f1640841c05400c01600c4000034041c04044000403205034501810480c00305142034045000b46c10144c8805042e00c1c0c41d4600026600d48507210101700e600884040a40c0c1c0094690900440358503005a54000c4010100c250a20700c10b42d0000300d421020410a0b4090303130380d8000405c07150b13075140c10090040a11000d110400c190a081a400075200340b0f03c00c0ea40b11880c014503000e2800c0106121003111010a03402c4081010300b02d0b42035844116030f0080c0c08011b00c0c6180440d41030355520040c4014040e40008507a101e030103105003d0b001c412400101c510610520070000542d070045409640503001d0f25001401e228208824005080303501c213030a0300546401801d140824031740d03001002030145900d60f518560b17 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 59296415 1250 59295165 59295179
    0x70512011a180f13170702010e0108011511030d09050703030201050106080f040b13080d0902130e0309120703120305010905060a05010504060c0c080a080a080903040f05011b020301050109060807 85
    0x154000b00c40c1050161000001e0540658400802d81040c0008510003e69555031a524440305e2084c02e03000d140c1038001005c000b1581c1002c0102c0280b030080c28400755030341c5401d20b0003040c0ca1441400c0410700901c842c60840d03002040c0200ca1050114200401c200c40311400e040303940740e1850004501541c43c0c00700201e090b13402070500910920040306049c21583e07071641d0b086041c00018042d1058443c1c6480101e0000c0c8200700500740100405400081c4041c05004100318403a03030800039924189085655980d18801004440c802c2034155222459103200441480c504100c81d8000381ca20012552900e503110340c15004a4103d61021009004507281c00f020480d5400d0548141804504104010408540260710340540c041c010b0400c5226255600c0085091455426040740c00c00000580c084440f500310740c92680081051008500b1309003016041c005044480c01340a05108102c00302540100304600420005035010b0006d010550792008100045d144600a800c4c5a000c2c24501203140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 59297665 1250 59296415 59296429
    0x230102070b0f06060f0f1e0a0f0309021804050a060501080303070f020d090311010306080303040b04030f0206010602060126030a0c14010e0c040e0307020303041203030506040b03060601030c02070512011a 89
    0x103090002e110b45d00d406044604903240d0b40c00039070500c403d20303414004441c00c0d550340c20203e40c440d060039495a0751150741c04001084138803031094440030326240a01410241c0c070750699509810100c0e1048665135101c41c2081c0e0301e40107400e00020a0181042c0c0049034980c0c01001840c000c24450312400441042d80c10242c1e03c2701100300e03c50000a00c41c007800c10210340101c03c140c159080c1814001025a1507089440c110303402101c0c244c814907024000d00c010140d001180b02e110274894805404a0350410b4002074580304103129030101c00c0c1c4600b40b666902002c41442d500038100b910103daa0f100c100c4040038001d104c04940554001041904114a030b0344103000da54146c1d44040701034582c200012082000400c4d40d51b03410709162000b4401600162406c01c01440a41545198180c002c401c61030006d055070001000c072405182402381707000c0941c80010b00140c120f402424040349510840340b04030315002190340101d901c0351456030560031100043d401034602109100280c1e00304003841085c0302803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 59298915 1250 59297665 59297671
    0x110705072102100e19080303010f050603060604030b0702030906070b06090108010203010815150306072001090312230c0702040f0c0c02060f0c1b0306070c02030316230102070b0f 78
    0x660030a00b44a101e0322411080c030311084c1c0142908412a202d038080006800a0381105445902c00401442101c0303040d0011001418101c41e114550715104021030383d14012403000512000d084c1c00814a014020b00650390240e20241c210340e1901c1507420410241c40341500d445008075400c2e000030500710b9041c02140d06070354a220080a60003060b42521105c04d9004040c01229400044014015078050200c98061426607440c600382e100311008241d0250002200c52006a14024000e000284c01c041071010310501880d001a503842008200480c0004000c10160b40d001114100a9031141d400c1c060502103000f40c43c1085070640d00854007089a1091a401c1c02181007100d2460051925000900440c200c5039642400c10211030070700780c508070041d003000c4520000815020010705081000e5a40180309203000c0b0b030b4050740b580110b0348a20400e4001c110501c0710b0044071003403180c80032080005042c0b02100c000442c8018211600039041804200c0b42030488102140401001c2240980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 59300165 1250 59298915 59298919
    0x1303020303070e06070204050c0c12071a0612060702010516050301080a081303212a03030509010b0619020c0102060405120304150504060f0f06060504050409020103110705072102 78
    0x1296840b290020b54042000e10304281d88040d007000302000684407802410f0007950701d4115180c0380c507070f40503819090411444055042c4181070003d00f000c2589081f214180303041001e035210b03858441402107150840041d04111191040100b481012036055010502c1340f07440c0800410061102c1400b11000c1c4020b21441025612403802d6002050b00c0400420308961b014400c0740e40f840c1e81e55249a8010f810f0444036207080ea40c807214680498010758030030660f0105c0045a41a40c0340c900b1944032203404408080c0826656100044920b4025441400381140c02015941c03103a00807271009141c25030002c1140010b005410b0907140d44e500004059005d51b034008058125a85174030b109044039000140140c1320340400e07030f40800d6510310a04c03038640624004c80010400095154428003550003080d00c010045190020401103998805c054a0a4610844000c07484800c10300040f409002009100000303003000007001806c00c02e000580e80c049030448404640c10701c64030080c0512800061501039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 59301415 1250 59300165 59300167
    0x807090605060319020913050910020a050a030509010b0307080105061503010303080f09070f0303260601020c4b03030405090c0c0703050d0c0b0604060311060304060209040f02040e13030203 83
    0xd2041400309100d602c0310b44c542d6001030401c0d02c0d4000050308902c03810b81700760240369180207204c114103080c4814000381407020f0003546001412403004002c0e12440c5401010141d58101007610303010700b0b40141d0001e00d03006045607545a1100c29481c020042074402620401500c00c030104900b4070801a203040301d130582c4401038503640740f0300c2524620340001c040c520503000e02040803402d01501010280071318000e64400386000b414000c00c0e440074075054181c007800400a0104100c5a1780014010812913040d129105035005401500440240c80c624400d000c40900c030703144541d0000c208452021006660000180d2244201419242d01c220300800fa04150f00100007a601816200107100d654000030844051903030742c1d243da6060800c40c643c0e0b040043c8848540e2010f005602413619000801101d04000c920b2869403141464012821501d020b00700120005003480260380c1540c01c12100903105202060300c0d1004180258054045c40681d030b4010804601c007000112405e61301168160011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 59302665 1250 59301415 59301421
    0xe011b021c0303020405100503060f010809060105010c0302030c031603120b060a1b02040e0f0f01050f0412020708120a120216111c0804090c020a0506150d1b08070906050603 76
    0x11504070007030080305034103068003040009160345600c18001402d1840fa9039407610b9040c90800c00c021510482c0449040002040a1084104001c100300341110ba0900b00f1038404200380c6002d03802c6006411021516010204250f125401c80d00f60720b100f814402e681d1100c05203103064440b800c443c52040d52030b8103c20148001030301d40c0c2c05404c5030b80000441551300d10f051120341e8009015540110f0f01141950418204e0301c198076010800160940340c0c0e100244010701c0c10070380204408400910251440c07014040340c008082c000d1042c1405000745000f6954000946c0b81c0010f001d52090909100142801030b00b60301d0898503100f034440c200c0c207400c001b0078002110388600c461400075900e03083c4c0c08244500b04e464206024620036500030312030040700ba2610301d0011900100c408145001040d9046070301c1c0f503030000e4404100d0b6640900600c1041ea081114a808182c060b4640400141043c02180b8100d40361a0440400c5040f586800c3c02c13035000b591a5010f41055984511a01e60444800e1002c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 59303915 1250 59302665 59302699
    0xc051002060f131703040c14040612150603021008011a04081b03100f0f050702070302060318070b0301031b06030608120d090218010906050f0a0603150b04060e011b02 73
    0x302243d400785146180301c000403c04030301e090f40144c83c11511404482c40400c486c080076a21079408020465040213039601d441c0040740b0012015070020069180288950803503c210343c8a07502941d0080d05010310003218440142c180182070240004120040c2182c84584442c07400321819115154003800303181440a141c100311500f61131156900d40505514808005c1d544c0c0b01d02c0c889070000c49004030303072500c50500b42001c60304040c3c044411908048030910140e10380400701c1e138006101c05103040001d040c82005a040100503005102500c0001000100380420f9000096428044481d5080380300d545410590868805201d6078049400c8050704250047e01c034005004c643d000030001040311001070340000c8040c14000c4800a04042010040c060f00305c00d403140d1806030074241e9660b40b046680c140010704500c550f125903420503440d00307080960b0b02072210000c0000d1482002c82500d481d00d40e14050040034000d19094000343c01840400c208416804161480c035030040c084500904031060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 59305165 1250 59303915 59303941
    0xf050903011b0309020111060108060106111204030f06140415110c01050a1d0303040b010302091e250e06030a02030601090f080703060b0f181b03040c051002060f 71
    0x9145500d9580d400204100680780210301440b000c0310342c3d0001c2c1d241c0f602d10014010090360941180c582e07101c403005019840d40000c1d29415203126040c40010b1510701e0300200d1412010a510b444070070404100007003040140985000c48600c5110240070460081500445912048402a10312200d01100311081040c55202e4038101c07030050007150ad400c01e01011907080d141c003650361144c10b80d9201102d82000741e55050503003420410f60003651640c01c084d101ca086508040c00084e1040d0345100110360351060707c420411200071842e20b4000580350000c82016140344031007009804821140e91014050710406078440c408c13400410240c21a1907906820000350001841c041c141b12410781c0c00b240c40154203040000400c0040000d003581411131504c0005c0d0340c50402c0c0940141080c6662940c41d0352030b104950b400800025880d1801d64800c240c900c030816071480c0c5024250000010320040c00a140ca041082c0c940035200d05042d81074010017213076035900855025800386181804180003007580e031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 59306415 1250 59305165 59305177
    0x50c010608012c120d0c110d0e0411070203060c090415030f0c09021908060a09020f0c0f030a08040b04020d02090906160203040522060e07050304110f010f05 69
    0xd40ea6100c0512074211403550740224600b1880d1180600c2c400710084207500309402001c080c4c0048050480a03500500440c5400000162605c60101556110340303940101482c00504840818800d0100540500103240c1118043d030b090810546202002c81c048a4040b075002e00288066a0b03a02d81611041d00030249442d80a0749581003c0e5100b010034000788055800344640030142071040c50300388040441540540d00050041c07000480d404040442401d020140307003007441042c1d0b2403000141c4460155009002030a10100306280010500d4001e4804420000301b210041346403c54019600e0161a240c035000644a0000400091610f444180c10030f201420300c0812030300b40e50006021030005c40d5000b0b51a40100104031081d00ca071242c0030000710960000d50320302410030000c20a5054003e40700c0101c2c07619000c01060700d00c119031244006215030015080541040440188258010b0308d0030395200440c0d0002c06d42a242441d1482200941610b0704c0d00710039440141922250405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 59307665 1250 59306415 59306437
    0x11e1806050a090e130f0321050115030207150e030a09080a02060415030605060f07200307090b0a03081306080a060506030f041b0807050102070b0f040b070f2a0b0307080705 76
    0x20301204000600142240a8640e107e40c4a150144500310100011104201c2003c000e2908041c010001d00e07241804810422041d46009130b5100400c1c10805050000141e002e8046491f041142c1c1e0710940200180c1410400d540e24444180d940e0302c03806644501e59440030f54015000c22082016103030340581c12000c2150307424040385080d81c0d0b80001c1d02c03d030410610101025030010f030680402c01c0f40084600d0f608074165181c80044a00c03008260349601502421301072555540c2821070030b80d954000e40008590149595585010b4070070340c96140084c9100388030104420b200490300189503406028181c8101900c114210380d0344424401c6850310140c4259416000c0c00c022014030311310070a5040140c040e442c02001581e2911000a150103ca80c1c8518135050341030000b80014511041210103e6005458844e103804081c1000c01030600715940041158412509402a481e00510001d0344d50384001048000e8641e909200742007440119031000008000c0000074060501441c0a0440c10201c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 59308915 1250 59307665 59307691
    0x506071506030f02090a091101030c030e0f0304060e0d0f06090804031a0402030c0609060316020c120114070e0d02100e180a0b010201020703020a0f02011e1806050a090e 74
    0x120240140c11948035030029180071000a4008055007850b003100e60f00000f00703207010840c1c80c00781d4850a0305034810b140130504058503101c000100034801c3d0010440381d0304030002e84100c0000d1040680d07407070f070251180b03c020442c120080146442c00c100d41200c0c0d56002800840c2d41c44143e901c040041040c00404c58110800344008800f2620014600100104145100030345042c907004052904c4ad400002c00d110310310410640919880d420290f981103c10010104a82080c0c618180d042c40501651241c005080c8403080402c02c805401603884403c8401002c84036032030360a411280584103019186d00030300c9007000c060041c2050305480319940e07141c0c54440ca090340c1000004442da800c1c0d00c0e00c1d583c000c0280c2c052150f10346003446a440d402c03a090000310701d020070984d8040d44569100d03a02914540b0901207410969002d03901d1400d100d0403e900c0039160340b413551070103056035104010304540e4040407940442c6540c040e0084840c01c1c0d49546812021a00d440c0103c181010300400381c00288007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 59310165 1250 59308915 59308943
    0xd021005100b0d0911220b030f03070c0e150a031b0801020406020102071707050715030f02030a06060206060307030b151f0305071b030c0201080402030a0c15020d090b04050607 77
    0x345103000e05401d10f42010301007505400741c1001c0412404a406003481070608002e80c884d1a4140008600c0a003008500411009007400009040c55200c448013900303800002042c104200084054009464049000150a440e810449a85d0358444940190000c414000501c08218041c060908681d0715a1281207036a4841c0c542e03070300760303041782c0c2c02400540c4d00854244104424252104611302c000c0a0701800d0065940302c2c0c96585400d031254a18021000300c19138113191083c2c016078440700b102c160540d40ca082401c0c0e400002c10392403203850014007540c4c010503418a404150740781100d0300501520110f0319218080d13035a50b411007410603440558460a003054020f844901c00078000b03103890015151400b00005000c20740c00001d012585500b01c00007a00280e0001c2c00e03811410303020b282821080d82c0e6440883e12f082000880500782c4c90004c130340021001100d600e150f6101c5000e90986101d5195000e050341c44d02f0040c086c0119945043c0010701a0b03003040750250012a008481132500d000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 59311415 1250 59310165 59310179
    0x30105062512020d0923090714030f0115020c010c0212151005090705040321111903030b04020406020604172802011802030a0609050c0616020901080d02100510 70
    0x4661090842e001d13800606245070501c0e00300804200078034016134030f0b4010110300e82c03200541c071060316209842000420085506240b089506240e500210390034982d480c20494001c01c6180c00922a1000e0b00b4010f1000300030b9180701040740c468684040c1c58900c1d9542850303081041450341c001d01d100d10b83c4105035a01c06141c3c0c0300a1514025881e00610204083c140405d0000d14003000342441e0510100b00810030000340002038240030116503204041c1d200348100e0040f90b101c1240700f0040d181d445540f41100c003e00c80015103824241c80b030b480420070400c000082c0402ea02591158401503002580040c0c00705403008a04000060141441450503818156030816a55003001d41d40ba03941e620302d0071000c259024403403090000240c0d80800202001071f07000079500c0015910007007200d0f03111f030788000030003504105049040c040280070300e40314088030b000c031403180c852440300703038801d41c13021000003420000403ca0030349004d0700d6400742a81e44d58110414000d41f4014120001c201550400000c0705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 59312665 1250 59311415 59311433
    0x150c0e0d0303090209060102032109010207021e0108061f20030a0c0c06090308030a0c030b0a06051e0a0512070c1a090609060105031f09050102030711120301050625 72
    0x34034071035140090711000c640140710110380010020b9041d54003c12840c0b01f8425507070000f00320582d100d6406201650b440154902900a8240081d0090803012040e072074500c41e040107140800d000c0c0c4e0740020b04d50340c0008005c4520701e00c03919590200808011108420b100341c0c0c009100080106454410070fa4000000e441c1d0351010840e900016543d00541040141c9580d46074014800d61500d1030701c413030843d1280c440710300c0061300145d1055500c0c906402602d001c0e0704070304420700000f0207200c91160795030005800d40e44209405038030692204000e5002502a8064401070101d07981c030306042044c401402020f681c00a4440d00600c90503070b04c80b400050140b81000d03107a0200b00740050803401c2201d0024540f110281c0360000784d8000400522023070700c1c001140305880c441c0d1030413a1001c032000d004a00c000c03d440040500340754000020070040b15003000308c24a4040b82c1c24101e82c40800319000081e2030340400c0c050994080c50402520702c002094595140d04228102d4416034080020759894800c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 59313915 1250 59312665 59312689
    0x10e030106170f060c03090601060305040f0b010608060109060c0c1a0c01020f0d0e010b240d060803130b0a08040204050402040e0316020109120c05090a1d01020405040506060403150c0e 81
    0x70590000060040f02c4030184135194000c0b022400190031420220240c03619040b050085008166843c00001c080c0021320a040e5851a0010444d0090756190700f0024007503041141c140e408101002c100040c0030307100d11102207203541c03c62072400c0c8460415180071400b040440440148080500c030b0080400f02c284002c02141c400910503903510085c0039401016103010541d02c140c21b17490181510300710344405007407160101e41480c0035450040090f0024640c0c1c000e400180c1031261801c2404298030300000001c2400c003105522200009030307540c1d07408420741b049452103400900c044010034010306040c0c011581061004001054070396610007503501e1900071059143c05003096044400c19540c220765040e001d07110103541d4440d400b03000d44416980c01142c1c0300310780c09a106000015888426a0701c8188a00303c5a45983c190180c12451785010750080d01500d44194500030100d920740c60000b04aa007220342c040b10000740a0782442e1139800501d07001d103c00c01404407242c49400c041e5a50204501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 59315165 1250 59313915 59313959
    0xa0309020102011a031c031e060503100c050f0a05070b130303050a0b010c1401020d140a06090605010e010507020406050405010b12101d090f0307080403031106040809010e030106 78
    0x181404140002425034401c40140707030141091100344600c4e03440c0410300e03ca110898100d040741042900808600604082d0107040d0a0070302251000c0201d05030b50040021607a00710121250b08001d050721100b01e465002802005c10030800c0120014001807020384054212814000c0c02d0400c0341c3c07104500c81e030048402d8004c40000070f482c2c00c10550503104071500501c0d1000c04120810b410400a0003014102c2c070060544481007490f44015a42501207030b0b0300d411a90000d0104210741d003c0c0f0803004109075600c05030241441c00204c0c1c6151544a10401c442050f56250b10340c0007035400542e4150300541e000e0381c20030788594012410740c0740c2d801800e0003405117110783c0d599404084e401d41404103000e44402c3e41a00c0407502004040c2d0740c0d070040440da100310a2502a951075030b990380f500d00a683c04600990380004a060414070800300b021340301b124000e4482c950f100d14659041501ca80089030b00411034502480305030100c1d403040500c0c3e031840802030000910161200c40320421000700d105012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 59316415 1250 59315165 59315171
    0xb070c0c0f08010c0c0506011202060403060c08040311060601170a02130e01080106050a0b0301030209060a030605040602070b06010c050a0602031e2d07090308030406020708210108070e010b030a110a03 88
    0x40461402d110b001028504c40c034182e1404401c941e0760540359013062040f20000c3c2000c0c041c003020b41d982c66003103030000c55004400b0000610907201c0070b028054221800d0700421250158680c2041c008204c0f103119034816916015005950b0880c12031840014002145141d400d1003400110340144580c0f00191104a1245800750715107611182911165001140070b0600003908020791800034007682d040d0f0b68101d4002050360317101000b207a01d00300301d584064091800c1500340418030445c1d80c010440c00e030048000030400c2d41d8120041d1071962010b00c1c01001580203081c800d020071099130103141c10038402c0700594080380000c200c000c0d02a0003075030b4142d0110511560b803400d40101c94109004500742e0b241d42d410b04d2130000f0303002e040d4801510003e88000c000100180400c082070317046420250b44406201d840d044880a40001d000c446421454007494039800496044c800003030702c404640442600000e540c0c24078586105c15000501000d14650301e580802d40072252030b5014155280f00c0780d41c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 59317665 1250 59316415 59316419
    0x60c03020c06270109170304050109020613090f020415180518160e1005090103150e06030f0609030a0c0c0f0b0706050601050412020409030216080c0109050613030b070c0c0f 76
    0x82c510006080d20952844e8980b441c02c0300001c2e01c0c0f990000c5c41000c0010302907220340d61428020f01404210310b0096201900150300e09103050f40800c200192070481400b00300c0d60b4aa88850000ca101e07034000c031101000b05c582d911790301511079840713003440031101844000150740e0b51010403909140c0031901d007a42c10080042040d01080031035400701d81d41103860701c03181c2410201701007a035603021a2810070400c40700107440b038060790080e0001410410b10a42c8075103066a1107501c401c0a0000b40c480f64868021402905507a040028440303000f000804003461a00b900800c5c1560840c00414048134100980d1400084181c0100b40c0c050080010000076540c6401502d0104215400201002d050040c240700031700c1040e440034607006015506070f030000f03940141c40c10264501a042c0180328800110704a0116011002103003001c1580c03420380b00c5a8940ea152010044503000307100c0da50001d882d00900801c0031031185861a41c201c01141003001c502f900c039845801e803a00c0190015180d0f9807001d801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 59318915 1250 59317665 59317711
    0x90d0503030702030901030510050a0b0c0f15041202160902070f02040c0503100e01030507050d060b090705040f09050624070b240904020904080a0504080f070306140405060103060c03020c06 83
    0x160342c1d84581d12707044402600d4203090000d600c1050758095882e115101080c0000090000c0100102d0010414112403412019280300084540300722401c5880804540039001d005000103154a5200705295003030b52540e00b0504114025080800e0039500000010f5101015840e144150790509095a81c1e0036034034a03041d8035a049030b8800340e21144944181d14010008200c0110b4030009560040300c9101a40000f4204140070b03008440ca4950302060100601c02a1500300b0f000304126031940007098a40744d51200e8280032038204071005a000460900d1800d5940740000812109803100b085035410140292103c003004902100c07682294411210030395040000613030540718412080790182543d1034140d01284a240000d40300800d0741038003084000550740200180c030b010300b217420100c0f040004040742541e03030b030320252109446942c9451000c40c840003002800301e00c2150450300a014991950340c0f0754006280704400c3d03404050f400d006000f0b10b80c0341401094000d01001144c3d046412000c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 59320165 1250 59318915 59318921
    0x209130f050f16050304080a0c1e02010206070504230303120109020c0c10050a0e040605061204120302041a09040204090905161e03030e0a05030d02030414010311090402090d050303070203090103 85
    0x240d0300d82ca04049101c50f019590280840e90b00a9010240076103c000c5810241c07422115000010101040c5135082c40b2198081401d1303c2529000368200d4410b92240e900aa0b00361086005582a405001a10030444001d0400b84014610040c3c1120300e000c01403100590403610a0700916011600080c46d800d0314541001520003410302150605005158248003a01c02d02c1800d0101040c010042c1c1c010b9183d54850f070000008100180a1980e20369240d00e140507810003c460072610300a03016107003c5034030300c24803d5030103842c40081000012903a0020141d40c6400c03025200c1d0703010343c08210205070720384d2034026040414030500c000c0000d03071031060101d102c07002d050b007084a8120880760302011300b21204411380b08684d0035013841c00c0e2041c000c0020840100c8140c0185405101c0c50078041e900d00e50020050003190702c86c030741070300902036032900450640c4d8101c9180c4241c645d060002a00619055006001080300100075000300502075603400c0c00e5400440e40c1c1c4016030004548921f071544c144c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 59321415 1250 59320165 59320171
    0x24041103070b0306010e0a080f0a1506031a0901020c100603050c0906011416080c0708070b12042003070303270302030304030f08120f040c0e040c090209130f050f 71
    0x10098100c07241442030340d0307409001c014103003410443d0007002400c480e107400f02800041d180010540c0c544060050040b6681c481c0140c2c201d840070940e110307429882e4502d10408080c0c079070207240e444504c00342c09401102c151002e00406015542041a5601c4400c100580250380c80d080101098291950901038104440c020b60980900e01e4041040300c0c1d40c0e400012066550300c44004a13403104030301c207604081c20340256401030400c440081d1558030803a0004901086401d1001114151034076032007140d80c1401035241000c0c61450300d43c04140055240e80e5400b06c006410000501c04410403000139280021561050300406e4038603883c88a013071225608070903104004200c03c40f4061459020980d41c0c0329520029290544e00c2c0c40d80380c200040c031001c59038030b440c404c103110502e03040c004182d6082c01d1040d00c00f103440c52042080000c08560006419101d107400c8040300d01441d02c0c10100101035400700c202158052840768081c02040072610504d104040c1002c00001da520b012601070f54450005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 59322665 1250 59321415 59321419
    0x90501081507050c0601090e10020f030a0501060512160c02030303180c0a0501140304020105070c030501020414040509030d15050411030a0506120a030e04060518040b070f090b0903240411 82
    0xc000100910b9000190141142da0840000074001c0c400408d803424007110005a42885000181d03002101c80584003039030041117401070410581e40d90f040180c4c0d90344107040c08034480d004200001104c44a2071082508801100e0900c4641154070b81c1c0003a003550720844188803a84140003501c401030004000e0009100d170181d17105c440150905c00080d1508001360307001a01900004000b0b011a44258142c40f40191b0041d0303038210080d224a4114081d402600480980340d41000050f4401e1406001c0c0500419509001d5484c100111070804086d1554001a2180207102c09000038036445622030610191400324880b5102d00308a10890141c41e409010f0380c2c030440849281446541021500c1c0110a5041c28003c14500c01240820094152607110713a601480ca160b40000d072541c2b11400da80300390b101f09114030352a599844144c94032000c0c800d1280c009050030b282806090403440003814882001001c40c0e40350380e003450104040086503407401c20400501f10501c420032112500032110302c602 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 59323915 1250 59322665 59322667
    0x2060f0112080304060f0606090e0903041802090102012414030303040308070f0c0f290c25080406180b1207030507030905010e03090a0f2301050409050108150705 71
    0x1602a900641c51007689000c1d00c080c20000115041180c0c0d507000ca014459488030070303c170503a52180e01908031445071244d41140828000040d43e080741c080112030642d003c403500d0340d5850b04060201d400940115000d141990340c4c9615010500300f80e8075400c2c029800320300c813103c0402d06020400020100c10304106020ba80140144000241c01010260f07100c01d4a140c22011005068422a400c08a10b00c0140c18140e0500803c4140600112415800080e60006107040f4264007204548500d00b11880c0320b00b10b00134407030703020200001e240b00080d025402c0800c28a40c2140c2e161407000360b10a41c02903003c00c46420002510b1f1700f070610306000a02040c2040303420300c1820200050b02c6100200322108040d0b480c0006468180203500c030352042c5410900810902c024041800e50700e9111080701d42c4a940000340008111303e104841d8420303900d2800e4018011784281400407014844d0b003a429041c40010301003c9100c1d6418801c81e4001d00d5600000c090405000c000c011011102600000c20008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 59325165 1250 59323915 59323919
    0x6060321020606280b0c031e1303060506030a021e0319050a060504150e0c010e0402090a261b04050c1615061a130801061d04020406050a060201090302060f01 69
    0x2031044c04040c14100c21801020310b10301507075071100c00f5a099402040d012140441c0b244a01c420000160040c90710390740f224401c03050340b40750b0046280601c00f0034031940301d0702a2003400000c80c070fa00041c2e04240701400311600c081701c503400144021780700b0a440c505094038a500e6500b5140411600d40381001e0145010800301864031541c0c2c803107054041c050042900c80010404010058126020f8010407078001c208810501e48815182d54002c4807090000c0c162242004113842c00344203c030401d800050003020100c1c60103000f41c6007104090b42029849400f09460040350b14107200e000e490382c4111603148000c0000c0420801203e1024100d4208024203018466454200120b031180d05a08207150901541c540e11250340030b8000c5800000841d180000b40c4008412014040c12403842e0f408507500a983d16007040c2030803180644110185401c00719000403050580c1c4a5032a00a8006030000c100305442d031000c9141f43c0384940c0100d0050399140f05000078150b041c09000d81200000c004040700754 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 59326415 1250 59325165 59325169
    0x10204082b08010f030602030c040b0a030f05011502150c090d0b1909020603040f0203010e030408010915090803010e040c090218120a0c06050f0c0703080301060f0203040501020607030e0a06060321020606 89
    0x60105d02000305078582c0040464040006501541e008007e1081c455a80758ad8010008014111101e61085c569040c00004903214070072044840c0a040c080d4000d0800303181000400d4030b00700025160386c001074410041445a61030364036a00c000c0301d00070420310419050008486844000210818280d686020382c1c50005940e5501101e401c40e0b0003908010411034580000303801046601d013500260310001a00081c90201908509181c07406920036105801c00c6038a00c0e800c0d030342600c4d0300400c411400c20040c043d480d2041c0c00141c00c140070300085100a038442c1c80c40d0702260b004804494002d100513004601c540390202c28190744402840190050300b82950366090000045c0c09100d042c01404242c00c826515220f050f1030b03a1400450880701c1250f502d08002d801a4000e015074400103981a0211154078000000c07542120700c181c0c002c2c007459840c01c4088009000480281038103015120b845404039400d40203c101460241c041c006484031182c040107220000d28001c00103542003881040f03915 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 59327665 1250 59326415 59326439
    0x6010905010515030916090c030c08040b04020d14060903040f14010e040f0b041a041413080a0c0b0a0e0c0409150906090c060206040209010501090521010204082b0801 73
    0x3012040415130b49a894144c1c90b1420185011402154020910340004042405401000e40d580007600d04122581604d4400c0b12141d104a0300038054030a80d102080040c10030b41e40c480c0071280074240305201d1a030b000b1101810800c00399505116680040340502c280d02c22900301d4070082004402d040c040581c0e600000c2d000c1011200060703c00c568400d2a42d4040e09203420100620100800401021251981c00d07641c1816004485014520380000701503203c041480380b60091010109400d440c0c030301a40c986005a1203000224100103520076000c00041100c0002401092440d2002c00d030301011048461074001000d0341c02c1d10890030040308102060040c4c0071042d0302c421682d40865415002e007886e0010385022040104034a040050000e50642e000c140140240c1c802c075080300b0700340d036503800446022140f8040d665100c41e01c8415540030114040550700c01e99040307000942016070b5000c070241444c2030f07607056664401d590041002452504e1000e0560340020381801c41295040002007070740 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 59328915 1250 59327665 59327689
    0xf01050a08060406050a02090406090f05070c02030712050a0b010e0411040203070905010c0804050904030c11030303060603220507140301141314031204140105070305161d09010314060109050105 85
    0x10391540c0e080030600c001b2581e01111081c0c0000740c814000950380304003140040130034120035102c881c41c02011a900502c900980c22200da00100100402070410f41e403550b0800e59070004450b14464808500d001039103084a0341c1c001c210008039041c1c146041d040c0a0480d00424401500c00c91040081201c0c3ca5082440030003503075000c1c40d21811800c02031500004600c599001681c6c030521400c20001019484143c2101c0d50f4032940812040118800602d580c1e8002650f4140c0e1160040c0000f5900c1045054100c40c05a84207408480303d55180d15400d003000c1081d04043c00211041c00081d0303450400b40100540218280540916864005410014051450313001801000000710188103404100107540f01114030301c1e0001c03200c2c02e007481c24642c00b942068510b8919402d0000241c052070103071042c0c5115070701100e807501c1880000310381221090b552840c6000400c80c00806030889032561010540614891900d06180802c1150b10600c0e05074141e202e0448282024018810b0b40c031540381880c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 59330165 1250 59328915 59328923
    0x20a0c1406070602190207080106050a091a04060305010f180209040f030903050d02160b09011d130509010506010201050115090b030703021b0a0606050d111e12060f01050a080604 78
    0xa1880a04000101c0394480c001d800f5041a0002c540c2000c3c00155214000002401360220703140d143d5503903078450a0350140d10510341c4c4042c004d17800300420001600044e000c000040c2c480c036030780c0c034125002070111542d641050751143c0d500c41042c41c00e0700c424440d0080c0b001c01081c2c990056406a0700042e22168000c000038580080540c109003010b0144d041100510350213070981c0c44040078002e0003503880c1c0d0385041c40d003209001420006401241c000c2242c0c1c103220183c1d10390360a8000a4000201d02031100c01d002d8002c986580046200c8102e481034602801c40c680000c10582403034000242520010703040001000c05200104071801d0304840c2c80300884100140300c9440e55a161816002401800d40c3c0000246500344500c01010307001c00d036421032600c2040104a041d8441c81440980c07408e03828020940c0c01d8003040d10704180342c24464145c00355400711000074110343c440040761030b900a09020758000c3d4080d800f03014554000c100614003428040e030300b030350790310b807610305066500c00001e00050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 59331415 1250 59330165 59330189
    0x3030604090602070206190f0c1109060f03070e010f080f060414010906050c030a050a060b09040905070305011125080306060c0c0a08070603050a020a02070302151c020702040507020a0c 81
    0x1000300009901070f04c8046030010310381503e90812014800c03080d921007078a030780021201c02d0743d41e40242c0a0b48010410903000800b41c13a01c0841101401782160b4060a02c03940300e9160411000345581c1003012501070500741110361165450b10700002d8900400f600444d06c10380081e03802040407040000c002d6480b42c0c2104075624a078112624090040a138245d020307100754203050400ca85049404005c0d4007444a60b9800c103c1591965201c900300c5100e8000c2c10314101c01009203a0043c5450f801201c012801101074031300165490351850308481c288204c90f11840008200c00c090440307007040e400300000440302c14003c110019600c0300b1007480001c1825100d034001140c46a007000c410403540d000b810004e0702000d401c90719909400c0c0c0da10403030700c100d800007800c007030004241114a001b540c4d0010100e0b00240b0700242103900b08012078018801070b401e002000d20611125040b24143c0400200303414000694030043c500503c01234820090243c825588483c2c1c0c3c4030001400115403904807881e1404072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 59332665 1250 59331415 59331431
    0x206070c0f080301030b01140405010e07050a03060b0c06040201120b090703020c030c120c010e0c100f0212070609030909140402101106090705100206090703121e0c050c04020c03030604 81
    0x100302007030031003040508080e02c044004001c014599045c0e5042c3c401590044100030548001c000948009006005d00e4080c0c200c0820380301070090002e42a51a9103040201e0700303e0300e84000500c141c10100140f81d25511241c188415940c0018554052089030002030206643d804041040300310090044420140c2c00200c450b0125802d200340e60080710034106440700e051146a80c00c0d220781040e40314a4086d440d11400c0401510006080c5641540191800c1c0d0b03150348100d400c0d40c0c482c42400200c8158080c1d113240b0071142c0003082c0104409845080001408202c50a00404e2200c85402c018011072800d044828404054502036510560450b845040c4c1540014225000c0c1c840d007070500d1943c440ca000b440450400401c026040d41c81c15102030001d2000c0300740880c4e841000340d039021301c02d4000040500102e01d103a490310717003034201e0360511a030000300e116a40d111411a0b8846000003948008030135040103000d00c280c0b00d0024044500f9030078000d4460941d600d910014160511841d524002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 59333915 1250 59332665 59332673
    0x14070602040b07050106030605060f03070509070315060203070308010905010501020a1506181a0406060f031505150c0106060302090f01050c0c090c0a08090a11040b0a0b031519060206070c 82
    0x40754060080c14505a0300c52401e407419501912003408200d580b181400002420f40c18603a00d2520310782d078005c0082080724038060074050010380c00b804110416495154001000211394054001410b0720f07070055030b03111441d0400624141c4c042e000001081d04140040100703a900281c50000c1d10b410040722000411003040c0f0324014841070303001203250500004175807070314003591b0700000d40d0546400d80a220840c0002c10001140c820b0b0091101046032030481e00c010501ca940301307404041c00846490141929100000c945980b2007680800307200d40025040304000007802034600a0045080031341c200b40c0007000040503d000e4855a504001c404102410800010448200c01000203842d100c0365040460301e44007594040ca0324003022034445c2012071210000050407402843d00440d80d036500c00c0a041c108400f514401c1012a03015295500c04100311031482d00640c010181440300b0032510000c4018003181944020071041c4100f1040800c000864012a1055000700c85280640b60b0040360b1030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 59335165 1250 59333915 59333917
    0x50c0106030c090f060e0c04060c05010603020402160201030b04090c05300a020307060c03200c0301140114030a0b0a0b03030c03040b030109060e09070b09030a05010f0603140d14070602 81
    0x101c041c21150311114000b5004000c3d501003804694440801d1250340e4840651802440054071225100101000200050780c4103100110403984030b070300046a0555207070002001c1c1e0300400038065164038034158100071580c061290b0606154151070901c80d51744e26454162141125200b0341d030140025940f00030880303450080fa401d001c02981c05000c0c4002130b041031a50b544480d00d90482c000d126002000c15420302480352506503076071603038800d505000380400aa080b00c516451050251280318089a4541d40a02403190704d00d0790001c15096562520b1840c00741280c1e8442940d000cac0e04840041e0002c94402c08a565020f008a000811810903a00110b417452099101d030b040180400719000c6100080e0400441c100d80c84940f050000c10345690550090001c1030321200d01c00c1e0301812041000c211540060140224001d05481d125800c5890b468250b4402035128000240e60391800d1040100d01e03280000ca174492038000380445003980313802408a2010021501030403070301042e00410404290 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 59336415 1250 59335165 59335169
    0xf070315060f03050a05010e0609070603020a0507120c0b0a060302150a09050d081206150910030b04020f13060503090706111f0f110c0703030c0807020409080d0b0102070f06050c0106 80
    0x1400075003650f0390703410318980750b0f01060303021500d55084c0010000d42400000f6030b01d00946800e00540790035840d201064000354000b02424040c8041401100c02203400c0c0480701803070003c65106c1d200d0170091441c0003001c1c52401402d10507120715104050001d41c032070040c071014002c4c4079000160f0300c8a5012003600e00200c158080ca500c104401c04503004c0243d05d4001d0251704c00c002c554216161103020410002000c10407d164880500740b2505196141c030359504d00e1131110300c0c103000030785c420b000000c01c00766030108d1544024440001180c0c14442d8501e1b41440051040745040c03811814428070305504c0b02e40e00e214410801508c440c1030081e00030103200410140d8025035401c0302a85128088001070030546107541c03100d034900400461039500c0c00088940544908010300210f5013595401d80f140300e0030100c1515800c0c014030400b80140c6a9101d00c1403a203020b03034202a120302400d6050f80a4420742c1140c14115000400204281c011040702c2e4400e03030f119810200d454100f0400d509004091a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 59337665 1250 59336415 59336429
    0x2040209061306020307140703030c06020d06090e070503060a09111011010c030902120601051012060b070c050901090908030103020103020702060c0d030b03151e061305090c0906030f07031506 84
    0x2d05000191942c0000040182d40c0c42040c0450850360900c0b90319171102154800640440c0550300c007072000803181d50080070101800d0f6800152181c0710070048045507403810070700040754010381c8140040d02d8104141d0354492501c0006214841d26980e0b9107061f10414042036001741141d0304509941ca005e9130300b03c00083d80c072000030000c0281064004014100612052b8042d10038200700d00ca6116022500506035500901800c04c051081d000c1100d400c0c07002c002460b24aaa6214040b03220021031004105d400e00800aa0640900b07140800010180607445600e48034640110f0400041e490ba00742c074112602400e0050301c406841c004550f10707114076404110180910310070901a41d41543c02190300040c00d400701d5a020f03842d070381c0503002c3d44401d952914800c00c249407451498030240c2e081c182d1000000e00703100c600a45032440e600580d2419035103040280c103c9480050282441c52001d648036800320700810400c69074180998940061b400301070b1503a403805900e080651080d0300000020242d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 59338915 1250 59337665 59337697
    0x1505030d0f0c050303070e040f0c0c0b060d052401060c0c0302040f060308120108010c021b0f03030c0601030602040e060a06170c0c030f03011406040e15010201151206061a070204020906 81
    0x1b0b80c070300400600300c1d030855902c51803030007054285400760303445040001a429107428101d514603450340d80c000b010042805510209043c80840000c3c810b200da160480c04200c09032410707200c0003680810080050f0800400c100401840d00c000c90700034900d02c0f084a40669001900d002d0010100014045507000500b40c54000a1000e952200d2000c24504075200900200590000d0f1002261540c00e190304030f541800079000b17051540d1914024070010307000e00a045918052604807040d0408509070700a60340c00390f02003000c001d110380300c41c0c0c1039901c0391041315044070340e60170031001a006050342c0e205e000c01442e5110000b046172041408a40e2030004400c1203d40380e09034460381400c00e0f0f200b4024111000300390302d00618541400360564044d2090109100c0c000e94a2a419503104c1444100c080d0466485410244214031b222100d10082c001c001c1d6a5111640541440742c150360042d031202070cc50740458a018000d039003001c10f45441c10343c100c401681d102d1210000445c2d0740210300c01c0943c4820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 59340165 1250 59338915 59338921
    0xb0406200c0c0411120a0603020d0b01170601030305030705030a0b03070b0d0f0209060703050d0b0402030a090212060702061603020405100201141807052205070e01031505030d0f0c050303 82
    0x540c0e00c0280c000c0c22040c4085400d080c4806040c4070681d5070501408142e00d00a0020000280700f041030990b0265061200040080e034903000a5640b408506e4203554a0b02807000500156000b041c1544100305114000c020310b51441d034009020744801013001c010018080045500010150403142207118001d040755480340d10340805841c41d6220b8000b01e2034441c582000c00545585a0082c0e5010240c0144464107003192514203403031581c0a1401810265074950110003e1b80e59440030f03500411304040001040210351041c01001103200c15080c2c2c441d4000d108110a013540007440544c00100c0d460450002c0503402c00a6010f07014503001151701414004070580a02e9056004603c02d4040064100d0507407541101010100301500060740c4680220000380043c0c1061401c0c0c0b04041d000c242b10700703186024030788048201c9030291200400904c41c01611030700c9613418001c490050a1b0703249000011482c0c00d001a0381d4103009101942405061010500f500d4010800d00e640103404c40103a0b66645 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 59341415 1250 59340165 59340221
    0x2060307261602011e0903020a06050f040b090c090403030b06090603090105060f0d0b0403140c0105070201061707050307030212210409060b040b1c0e0304030b090601090e06040b0406 80
    0x10604540d208a00400070200402c0ca03071050007210054000d4510502c0c40078807214440d0b000d0301c45110164154480c0603440c10009040c1d00c038061044541c0040b000d1941064509224100006415507601b5844020020241c1d074454070100d07003190741400d00049240c240d1001c41c403a03000f9001c00300d0f40000040100610201e040d00044c0c0303d000c0403507006009170f894004202d91500740c1c4201a1066a041000800190203a4440351034045640a154103002500030480c0c01c1d120700f02e07440c80050b51104800c03c03900514401d424941030300302014007492410040400c0c5c0c0d490052201a2280e50800c6080542642c1441440029251030f81480b9003504540300807100c0c2d500c13a2141c500c14030b00e807910004561401d407003600c040ea11420509843c00002250804903515003540100c51940c3d00c07600d51046500400050006600c04c0c00e1002041c9040c40115080c10b00c140c1c8000c5280f41003200301c050302d030300c003007280d07603005501600c00c1a1545035420900000d10084030035015140620310075018030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 59342665 1250 59341415 59341487
    0x50c060406200f0307110306070c0c031403040906030602130605040812090d02100c050c040c050412110a0603061806150c0816030903061a10050703120501030b011712030402060307 79
    0x101d800d078108e56598461206c00c5030803125014010300098182c5100b4000103461491000c2c1d1082c041044a003403d48079001c110440d04581e20444040340d001410390585841920400700824103801d229050502e061303081500d9500340441c0340d488a500160850f2103a4800360403d40c4e068010b49032141290590b1006070800c00107001c2500c0a102c2d2024030141807903d8000c8400e10949540c1c0c1c103041500d40b2290880000a07440101c1d407560903044120299100c0f202030000400700c0782d401044240c900644c540710780e00342c0f406c0c4c6840c0e10b041a5052060b608000c1c504c00e182002494250312000860401320b0b018096000c030f085451322444441c10525610070026002c0c3c07400703840104017a0340070701545841e80941600c41500f00341c1c00d00941c5040d034066006020a0ad00900740031106070407ca10170340454900740c20461b0451090030050040440c203800030034101c0103400040c80550b41c48a606840d0707000050000b846102d0020015009512913000c10480410080c00481c120303002c442d000c944 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 59343915 1250 59342665 59342693
    0x4020c100905151803040509040311010906050a0e070305031207050d0f05060103180b190905190311070803030a0f020705100f0e010618020703020705120109050c060406200f0307 78
    0x1404495001280d5810040c0d648402e041140e240217600c0c0628203000d001c14414010015020301110260007120002e085c0a50380c1b850b482000b0024151800f40c0403101154403072079180380180c1c000041803001607000800c8601c0003090f020301d007045ea0703a2290200d80034440e110300305041500700a40030058070415044075014078000d880502040301056080d03022014030364000380ca000703224800300d041d0441d40000c401250365031910126580e4500e85600e854821038880c0c9420010080354070b04185544644004031050445002d01503943c58420426503a010141400b0340c1303207a450494641140c09503049800e42c941c0041618103003020000300100800e08190054120b0741000c040440c40c10040c0300300710541e07141c01c15000683c0b100460002c000d4008a00032030640c8100030000c101c03540ca00c9100c03080c40d84000c002003400740d028904170341003520a40c19140101028801880702c150005001c0d140f54031000e0b030401142610100c1913252910700282c4074040d0000145100034040e69180030783e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 59345165 1250 59343915 59343943
    0x91e03011506050c100b180703020c030a090e0601030507090e090a060504052a220209090f10060e0d140a0b07090503070e060f090403020109080a09031b03030e04020c100905 76
    0x445217414092540c1910324840410b544106012000c55102d294400c075650042000c2c0350045c1806007000c680340c5168040508940400e040040400c811503020250940c440003c0c6400c0c4503d041505010301070071402d00414240500f1400042d500403020840d683c012904500107000d981050706041d500c0300d084000d40c0b20803550507040610031030024103c0c401180c0340034141514081f030b00c40800d4042c1e40d034084101348031a000c00200600da03541c40381c900e0050340311110125113420081d074100a000d416600403010302c11204030888141d9100070712051507503007008850718950008501c1c40c0c18000d0500c0b0040c07440d0740090500000c1d41c0e0041c01102500d1064045030a00e5403151901180c1400451740581c1c800610203140c141800c040181d03640141c0b00c1d0002091656040c3c0d00c48495402143c0c140000500d105010002d003c0c04420002c20b5042d0b0439500c22001c0c2c2903072401060000c0c5001038501480d00064030041e81031040050000c0c4c2003c0030010040007c4503d0704584074400f4841d0b00c9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 59346415 1250 59345165 59345173
    0x2280c080f032d010504090312020a030203010819051b03030c0f010f060911032a0c0105100501030516081801020f070201020114010f180609020d060302040c05091e03011506050c 78
    0x400c1e5030034900794501050703c4a030300031449a0b10307000400000d4102e0610031420441d0540300011035074110b0002d0f00001400751401340c1c481d81410307503a514182d03c4d000c4040100b0100e86284011590100e080d100d6040c0c011303048a50320b0000d80c00300b0f2542c8a46c01c1c60700c075544540c10010207002c1c2e0651000450810482c82840025561482c41c016210013410058071360108102183c0030114640001030114100010001c1c4915014601040d541020220318070a944907420414005c51403103400001c0c0c038007400c0070801c0d0700b0032034a04152030150181c11401d100c580e0000c941d0b08450000030720f00c40650080250b54582620b24400c42d1508680d50407030156080905c00d0400c1d10411820038141c2e0010304004c9590361030030a890b5616140c118400d84800d0341c0c0c58010400100c0c500003440b00c60780304031001c82d203d0714600c144400c071010102d00000f0080180715811040d5074080c1c03180710070408441c1101001d071800001a00420100c07405000c1184070307100000741e031070b0000b01418001c20190151 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 59347665 1250 59346415 59346451
    0xf0c10090c0f0305070b030709030b010602060609130f030c050709180507080d05030c0706060b28030204080d12060b120103060f050c0d020c10060b130902280c080f03 73
    0x840840b2054000241942c110349800d0040b40d082c5c8000c0c541c400d0682c0f41c00d1440319500c1e15003018a00b0281c02500041e00b0100420103241010380020390440c90501500c046200f00f6200d00c2030103601301c2c10040400107464040c1c0188201084804094051000d08110000300070710b0814a0050200c41110707640180180010780500c0401c1e5481c0c080d00503240e062441d540c4801c040520351003180704032500c030396075000070036148500c10280c6201540700382c200b01c6c154800f4a2944001d01c038038400204060041200b8001d00304080f076080d140c0c03000740c1807861020081d0ba40ca64040e00041c0c00030388440001041c01c0701529191046981240d000744410404031410500a40a0317540480c4c2110b40b445013000552007000c0b0584c000c1c4800c000b21010789400710802c8016100f40c0e04070340c0c040c2c801e42201040d0b03007001c940349294010003040700e1103085280622501104108440340296000411091400003c0043c0120901980a07601c21065a6602c6400031010a240c2060b181010420001500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 59348915 1250 59347665 59347679
    0x402030c090f10020703350408010e060411041a03190c06020a050703020915150903190b01140d1203150501020a05100506040603060207050105070f0804080406050f0c10090c 76
    0x10101d0003d43c0e650150030164207540340c1e19440c844102c0b141015007110741d5650001c22003210320140500320f202200356690301d440521400c5d80c481c0496480030380c0000c0b01b0b00001275420124094962000c0c0c40205080c68002070b071030000b08081c0d4226405025114074555200a468044400d440c03165616150b1540c03038400c00ca9840e204900001c00f075501405041c00945030070020700740c0c0001d140e401810380310403020104820002c041d410000003917000c1030024103460b00348007071007031810b8184012403e80801d440d02d03c1001418030880c81d40c50030071140701da45500c9011070807040640014071080103d031460310080052095149515140d416203801058640c802b0619916868001005082000a0540000c002e040261110b0b910981d00d900000000d001c80c000f4000c200d014000000c0c0328502520094610300819001e20104443d0108100005401c0b09c155400d4590b980741c4070380c8600690440740240d1261059908007403203004c1c01c0c0000003459400201c40360f03218080c0b5943c45030341c0740c80e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 59350165 1250 59348915 59348929
    0xe040201180303140708040302040e0a0c091418010b0d030e0f0616030e01030617031309050610030203071b050c040b030c03030901030e2e0b01020d09060f0e0402030c090f 75
    0x70001000c40c41307000c040c011903a000e8010f182c0503210403894541e4950000c0e04503601c0b900800459007201d1030220611608800c908001c1900d00000d0000440c40d8400b040c032000001c0c00040243c04000d00030204d058258424958980060008100c0f2402410040c0800d211000c18034843c3c40c51250351429030a0400650f0541c0d540501c2d8070502226540d0240c49034080c02103540c0c101540c41c1c0c00003030100d0111064141c10f49201000e980d4034240c1c400c5007072440c0500e420030085c9a08100902c0030325200c3c06188880d1600904e001a140c2d1105001140c80c4076415400d83c1c10b82c1c2d03500038070340700303015010584405001c42100c007040000262014141c8540028401c0d40c0d040d0000d022020080d4040c2c3c11528030a07546005445d0b41542d0103603403288155800010015440069400c804102141d12608589910034002400782d410064002060b942d0760340912000c01c001c0d2500c5110042c080d440084030301d0340050042d9103a10308000b0900d0a6000182c0302449842100715140850a14030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 59351415 1250 59350165 59350169
    0x714030a03050301030807061b1206050909060105100e0301090c060215010e01140d02090a050916050a21050a050f19050c040203180714010f02060717190203010e04020118 75
    0x42c0700d05086030b00e59100d599480e00019800d5030910727100d009010754061882c0d41d0340008149a1190050031038150a03903021201035400c054050318601c1d041c000b1001000801904490080b14952004146402c0440d003049061032030fa0342560910610004205001ca88042038500584c210790b140c001120300300100410a115101e01c074000000140081141140c014001c80c5d8064841d669000b1180c7c0428a0010300300c030b10300501569903003400128401405030050350005980098055070816000601d003c001c0e01c03034a13901e0451120990301c420788040d01c1c035901540100c15034103140440c1c00d010f904c8585240d0341d501d85009080d1209003804580107100b841c1600f00c8020322501942d41e0a000003948040c10106420500c086810414182004070001400d0100800c00d0720000100014000c0300307190f103001040d0742195003041062584106200c6604820300c003d8411501c52030b0383e0702d44040140030319507100c500010000c5103c200d003005d100d0240303200b039031070211175003100583c105d45d14164 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 59352521 1106 59351415 59351417
    0x3210304020a0b04060e0d230d02160f05060d02040f230103050702060609221a06030a050304030312060e011403060601030c021e0703140714030a03 65
    0x341c44400401245412a0400307042c442c3c0a400410a58402c60080c080740c7e80450501140054032a8500025400d924107800340d20300071602c1d081c81c041c0c9000544515042c0b83d64190103030b10604101d800d0030342154801e40c20030041000b00e91260314030500a40c1c00313100208110038141d010030014907142c8545c848616440c000d00c081c405205800f28181490902044007841e000300e207807580705408480105c01543d8804503d4085c071200c1c031500b200e2400c41c4400000f0000085002d40c00340800c00400212075544d0000c00d9070325000d0075001007141d0018002000000c0c040c10500040f2022810302103812901d07100482c241160036030141040034075200482c0c045040a01c203254000e1001c0c6000c0c84100408800a07503140b480800d0042102e051310312142c0c911400340b1102d006980d100e80020940c0101d90015543d4044502400b041020800301d08542403030f0010307024902300d0745 = true := by decide +kernel

theorem cover : BRFrame.Cov 59172665 59352521 := by
  have h0 := BRFrame.cov_init 59172665
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59172665 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 59172665 ≤ n) (h2 : n < 59352521) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
