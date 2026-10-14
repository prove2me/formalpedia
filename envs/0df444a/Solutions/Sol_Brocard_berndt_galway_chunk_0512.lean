-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0512
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:11:27.303376+00:00
-- url     : https://prove2.me/submissions/0fb1b366-1e46-48d5-bc15-18a4248a2f31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 91906475 ≤ n < 92086331 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 91907725 1250 91906475 91906499
    0xb040b031f0b0a030b190b01030c0c1106040b03040804050a080a0c0501031d0f01060602060c0a0507060506040b030a051507080403231b060a0b0108040507060813020405070e0a 77
    0xc801418004070910805032140d05402101d1202e500901d19900d00390340b0f031281807901d9800c5914030f40d054803810f00c048218029105a100942080c038003000004407002000d0700c0d01030001d101406041c0000030000203070b0fa9a0044070080c7c44000c1083c4e0f120f051510700308207190030a0080900c141c25460021031074010004074080d1043c0c002003c040f0b0f1526220042d4000d1075181c1010400c0c240d084021040442c0412184c115041c0c03400000900d00d1a0140082c20f00801074002d0020403400c0020240040d80202503c40700c2c0d8100c2c1c0c0001d06c3d42c507100c0000c1d00030802103a075160140615505042131001c0810540d103003841d40541a1080d980d01507045861500455005010030b640340301c0407168000604c005c000003810a1001c0d4601030607040c40d450000740461a102d0f8540c000b1b410442242a40d01440c49078020030701b0241c615060a5440c80c1e1500c40318020181048825000240000d11141d40c224110f034001e4810401030815040c0142503140d5100c18a01880c0007180008212a501c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 91908975 1250 91907725 91907743
    0x20306010504092f03090d0221030a02040f030b04060b090f01060f020c04020301080f1e0607121b0e09180c010e0d02090c070c080601060801030809040905100b040b03 73
    0x699074500c2c2034104480b1400902ca180e000038001000d032a4a54150110484220000c002c203611407910f0f480c12614407407900340d002c05d001c82150000c0882c0d449408000014071409044031100c642c8030703a55508120000d0145c0c2c4d00810b02d404000d000041801500d01c00e43e809030f40185004e02200800d03a0512060040513580c610700241400c0c010800b4501c40c600d9070010080d2841903550312001c07040003070141d070000e070824151508a4140004e044904000803000706081c2c203144003996021051943d00c42c0c100078100014131151210035000315a01d41d12141c029245404c03064840643c42e14010001554243c042d0300903d42200801c2c552a2002000d850f85544c010041544561007001100c0300034044900d16044a0448024401a0f80b1701110034410612a5502502c8002d0303420708501c42e0020381c1c044402d681008005001542e800368a0344d055981058107143c3e90040100490018050202e003e081c0d40524070070104210720725009001c19a0084070203104c0340e0040c10406450340619 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 91910225 1250 91908975 91908977
    0x7050a1107031211031e0408010b011418130606030501141e1003020c010603080d050612070e060a03060509010506030d0311070b0603070e0c0d05010611030306130e030a0c021302030601 81
    0x6032101625118010320044d4540900a890521103444101d04103000745c81129040d043c40803c084c030950100344030790410380a003440d051254000c1140700e042503118540340c003014000c103030031030084944840d080c01e1055103900000300f00d51952088024000c200a005003409440d046000c0360162800d814001c00e14015500c80384820000070341001f0380f44100303407034943c2450303003e00c20715403c04002e00c2400300850181350526034810003000d5100868800030911441400b02280128444030f00091440507185020400105900ca00c40054030000346035000030b000906043c10886d803840107400643c0285d101f5030444e40029890740042c0c040c0e4180d0b094080d1741500c180316400101d620f2514654001001030141d540c601e40f59980d161400908403075071200d09000140321070990f14035204031801000703146080703204105142c00b1203440f840050003c40c800c0680d0040d06132258030980c8140c0d11603400c28101c1b5650311140b14094400c1107a0745059200d44c40401d40c40d0046401070003260311070081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 91911475 1250 91910225 91910243
    0x705060c040509070f02070503030a0305010806071701030b040501270309080d020d14131203140313020d2f0112050105090408070c180603021903030509060a1707050a110703 76
    0x6144005c80d01001c4030504842103104a10000965407001d1008100708070556402040070f60402040c180b6103a00a03201034104945c2107084904440d03800030460559600400f034000a4460f8100140035110515915985052140d10940707c0c8402000b981c071030900c203071201c00b103072a501d0b8901500c840200304280056040000042103c611440d440c980104041c10036a042c444201e6481e0401c5404c7d130403070b940c800b002c40b92010a05030000306615005407171001c41403462a184d00300324000e0000b2007000380142014880d160070043c840750321200441400320076000012204d00c40841c4524150b0300103004c078407401004411082e16000c1e15059a030050300b0b11115484560700d80c406540010425102690b0402c2c0c003003203c00702500f040358820105607000c1019070840c0100b01c0d000b803550644002042c2c01b40000c10020b40c0101c02c1da44083c200300c0d001510398aa140003594103203600d4507800566a0550100400560080003420a8460541d920510000008000c664626403070001071f181e00c007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 91912725 1250 91911475 91911481
    0x90507020f1f0c140f091e060d0c0c02031f0e011a12030f0d0207030e04150302010e131b02011503030203040302091915030605090102040b0313060618020705060c040509 74
    0x364542202e00d9600fa246841685076011030303114142c039080b4080340007481600240b40ca41d0343c41c10844880000203036501006250782e580c00060120300c100c1418008058980b080c031900180981340358402190080d00352003c120081e80c051340703510031303860300e841490345001d81c151801001446034520361032442d5600c5a40003001d4042000e030004810640e12107110130051001c4404403480070300705000e00c4140140e02d6002138035000d0704080e803944060780101d18007125210b0307402e0300142c513004694081c04c2c00703201036241c9000300310f25540354000e1004603410842103103202142055038000301d40c0342e03500803c42404002075040000119110180041e84240402d10252a010344a140c204210545851041c4143c079030200c1654240c0c40c441f64000030b4100308109020352401541c1c0d0009003400210324050510b6002019400064006540562045403a608210031a440340c0007800040c8408078203c10640280da010b0341c4000d0341210326000e400c001ca40d03202c4410301520151100140000140e50f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 91913975 1250 91912725 91912783
    0x7050a0204050c07020a06030501060e090c1629101202010c0b09011409061e0c071415040c030c0608060603070c030215100e010b0a02070b0c0c0604090507020f 70
    0x180a440604240c1c401c00144c0010390b01d440c1824000c102940303000c15251f1400350060400009140c0d194040c400304803c000407010030004071801416a6403081ba601121818041c1c140340010400c1031100081511800800d620459001c2c0b142c010900300d205400d4031aa000d010b000408400240401c1401d114a40020b10b00d0ba20b055004207618000140315011141c8180c001900f03403200c084a800617000d103c001129505401040b80e10528641000d041c07020200c8514401d40d50301826140429850140e400c0e000d016100207000e58003180c0895040a04104640c51140e1004884500c02070000080d082c0c09941c205114840c014541070a40c0d5443c0d400b5552611030315400c40841c0a0442c1d00d00c1140d81c0a41c0f441e02588242d807c4e090680d0030301c81921401c500c10381150169080a0214110fa59400500300041d282500741781501d9001011942d0b240c01c1001c0c000903440140400c0c08500036541d90b1006104040c42d5003100c103520007806803144c036070001a141f038400c041091520702c030034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 91915225 1250 91913975 91913981
    0xa050d170f09060313110f031b03031308010c11060c090111010209030d030e0705010309020303090d05070b0a020a06060e06011d010c08070807020a0b03010b03041707060905160b07050a0204 83
    0x4404418991803800b031882c0300040303003940101e5411130030100580c1c5203401c0c80400292042e082000b0744000174030251140000707a039032080040b40c0760000140644000350361424400d544030841101082c082c91a02c90710b807140078169008680c00040d455a00d0440400c0f4005030b403502401082640c1850541c00d900111b52070b0710301ea41c01d01e96642d02004902c1d26a20700700541100d04003e5600051080c0000b182c140c101110341c0d10050416040440ba00050b9038007000b140c4107400112030080140109207451800e1860720f9000314400900402e0001401d130300802c2c2c80c042d00d441480c00300b05003a00d41c107074240c1c02c0b142611590300203a150850540318100c000e103034614a060504182c84900d056a0f621501ea0703001c2e040840b15038501040d4201141024180c0401602d034590b100d42c2075604080ba85806404010b00c00340800e41543c008807e17020540045a019607040074007031001843e5420030f00e9031070f03503000c05092000c0207906001509500c2031041c0c842c0c50354000c0180440c10b04507003c100213 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 91916475 1250 91915225 91915237
    0x1020d0801150f090e13061d100b04140c0702040f05070806150d060605091503061302130e0108060f0903040807090221090d02060c030c070b091c0e0a050d17 69
    0x2801800140807801c400a040075034890308209030035540301b0b81c01e858000c0555105440c040902c155400c0c004064000c0070903101d23001001c0c0c0300d000901104100c0040d016201014000c5000c2c250f0409026840c4441c8004042c4c0c580281c0c0c003480420f044282d0700080b1441100e04400242559020442d03910f030a5000b40903c407003066a040c14143e10b00118030459003107900400110342c0001d034041450500c0b104001220404519207415490103c01040c8442d80ca2000703040c080340d0001301c031041d0311210415500905005540c7d40c10319a110b1074480d030382ea80d040d1214210b1044100c001004000000100c80c1907500210240c01841d19007000c0b80d010350003404072082102ea84001443d0b0b89007240012600c542040c1e4001d00b071548041d0000b80c185140a002919030860800400100d41411402c0303072000c90b0301030203a51407640c41c902c0c000d0034080b02b0905200d91502e0000002c4080703a0041e0408105001240c00c4031242da540c50811010141c4104020701142c03513201504400612000a011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 91917725 1250 91916475 91916477
    0x5010f0503280e12070807030c08120103150b04050610030e010609020c0d090603110315010c0b0907060e010c0b0f1009060810180b01030209130506011401020d0801150f 74
    0xb5400b240e5070703041046000d00503014044540e5140b0441000f54100180d1100c540c00c403031102d10700050398407481c003a4400c01d0005003c0c84085065801006096000c41e1140080350a40404c9561a0300d840051140c100030030300e091a013800c05808280c501449118040c86006065805200721110150090030300c00950003d035540c0c8a200050481c0d1600041051001c0c14028090401c150f94018060308400c0d0846800c00d4688030649003030210a4007142c0c3c0140145007500040c1316580c0040b940d040f04000004c060604120500012080000d20302041e01d809499810040701030200458491600050241c00b161080f00071804108035003035a150410a06003810072280c0c0c5031310041041e0307606603011200e1580a11200100a4041d1248003940e280131702c0100140ea840ea11842012034041c08080e200e01d04550101783c0b00300011561050981d407100a4030304660b0f540750000c040640b0b074000036001d809000440501180b01d0130095058581e41040003800c5ca505c84803c480a10310342039154 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 91918975 1250 91917725 91917751
    0x20103050c071a060a0b030c0406230d06030b0606120f04020409080310090f1812051c020306100f0912030e040603200a05030a0611071209090b060405010f0503 70
    0x4400b240101003c0e0b104500f05618030212801c01c00d040c040e070816954070928000030700f4000d0003d000c1e070900071a0100c40c1c1c00d142c00100d04260303540b03070340203180a0089a1084400015000c0f4045400d41058080f80d000c1c3c410320b01c031690342105001461060f580e50700c0c030400180300010010552607c4c05500705002810000e010031150351120302661040e41c90302d1000c161660108003101c0e03d4003071001901000a81803100303500422a654000c0b90302900148900350710b00f00c00c000980300368107441c01031040032440401403044602480c002e41c020340c1c107240210b441c840042d60007801580d02460685c9240e607280711307081c0b410b250742c0090890707074070124108000328114100720740d43e42c019038001e140142c001480f82100b04054550401c451182c0c0b034000c0f1115841082181d402150241d000d540014021924544140b030440451103940e200034103c000c030030b046c66202075224400c90140c6040050411600020343d04202c528081ca1184500041001001042140c4120301441c3c000c08040c40c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 91920225 1250 91918975 91918987
    0x6020a06200417010c0c0f201509090f040b0402062b06060f020f0706030c020a020a0303021f0b0904140f010f0b011818090503040b0406031d060f04020103050c 70
    0x140180c1d1082c3e124142c0e00021040320f40100e0001e1145030060010b60501404000341075840060001c28880d02402030660324404e1784803585100d101c000a400c0040040d21156000c008003002c903003051110300e001d10408400643c50403442414540203e4000311800000d0f80d03140c0c2000b40b140d00804241085011007034050105803c0824240d0b2070380b601c004049a01c50401e400144003040001c100f004560001910615100c80032400e203058400034500031076010341858050345030000601000303400481c040c1001080c95400300303039a1810820f04594200e81d8080100d02020703030790103050701da500051000c081000101720040f1240101e14820544018100c400d004508440c82801500e60702034888145510303d692000d9503510074500e07a1806071459040010b86d007401c0345100140740c60550360380038000c1402810000c0d20700500003519029030751911600c0050140c020b41441c080c8000600d09103d440b29004920f285c424002205015130969aa0b00110043c00340034242c0c01c0c10300b20400030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 91921475 1250 91920225 91920281
    0x2a040f271503210c0b1503030c0a0b01060c030f03091a04050a0b090a2307030f030504081b03060a0c0912111002070f030b19052e06020a06 61
    0x1080040580c0880e028101071542c14441c0004400103010318448800c0d1101e0360003c2d800c00140000260049020700c065920b1050804000b00d0b8240d1407681407202082c1c909860750b0008080b01540c1c481c84580b005a41e0749d0000b82c4140c04809001000301c1d403880514a020f601c2030b0b100300300840c094880d11000002c0302200c1034101c20243c40c241e030643c216542d45030900c000700c498250442d20101c002c01d5a4103003500e5403244143c0c20008107001c00140000964003400402542c0040c640248101001c0072280ca03001c1c0455200d0720078440b0901844403a43c00e0201e242c24075400020026003d800e142e03550710741c1000100705080b03030340090148000c00401c413401d5081140d41098414024801181c00b00c42c100144051078000231000c55111201c203100d4191108900d0089940c0200610a29210200251030080c50b08588224881c54041003001e0403481000d981e400303126800e070549079015211411310010300940200c02c0544d102d100d102c000102c0c5640824403900003160300002c8401c1c500302c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 91922725 1250 91921475 91921481
    0x20c0715020a051b0d020d05010207020603090607110c130203061f020a020a0504110403081b0303040c15031109150d020301090501030212010204150c060209092a040f27 74
    0x203503100050b03018010314020090308018003030f40b410141c0e800c1d030201d03600c0c807000801401100c0030080c00744110030f4131102002002d4040d61403095000301600c0e2245020700b1656070f15101101e8100000300600b540561090000c6000804000c0162480103849213246141c0041d500241072075030000315a40705410840c01041ba283d00f1101c0b55800f405100c145801000151100350308080d11680c9448450300300c0d40c40c4001203404507076006901d01d071640810102140140411030384801c0e00c1c000001080200001081c2e00005e8441c0003102c0050701c000d1500c00c40403a1600d41e140c010182c82000b0310030f418505030040506010340c2d00c40b86443c1c24500c800d0101603801c2a4000720b035041d00c1da401802189000c10084010f00d0b201e00086041500d080719a40d014600045e0480c284030106003074509120094044508681003d03003064041e00302a0380b045043c640300200c0110550700b540c500c80c1c51481c00380c1101c04948802001c00d21060909408155401e0040070020b4503040b003100c1c105800324640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 91923975 1250 91922725 91922759
    0x1807030503130f15030519020d050a0501080102070507260a0506060a1a030402060a120c0903020f0a050f15040305190c0b090102031204050c1c060c0806030d03020c07 73
    0x1401a50b124a91000007510401e542c3d00b0a01c06480700c1582804241031030f0802801c148020300c0e010070582c849803200c888000601c540134092500009590384400c0f02900017600484050204003d0343e80e0301c4000fa401c07806940e100a060b0f40106e40200f00e0442d0070340035020582410404a0505104101d00a01c0c0040180c4112940e80110b0304020642c07601c1000f00340144501d28104200c2c5141e04e03a41c100758800100003e1041c6804255140a9441002c841c00300c44158501048541040a80a000b1030103d00c4100d1290b55007980320b09007403e060500408840001e0801da1008e80070360104519000e840c00301c079004080030302001010071300420002c5400c4195a41403240300101e41040c8808005a4100400701c800400100d5400e07640041103c144e0075954443d109180c50780c0c178005040510540c001c40d84140d2206109050019500c0841182845003200300300700c8412410541c1d207224103c2d403882d403503000701c03501c401c81e41c0c000d8009012401004c002e4400e00c542f03075070419181075008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 91925225 1250 91923975 91923983
    0x41803020a11060403020102071a07080703020303040b0a0b1309020f1801240e01030504110307060504090509011b1805180a0509070803030601030c120603060213060309020d0b180703 80
    0x81d11050080c40072549000090340020349485141c0b504680003c1d5a4240c244614008520341c030b40c0503009400304005403002540c0c0540c10b1030b520151420b009540f500140d9040d143c15020b40085041182c1c14802c101a01c540038003032207216014280040010f1201c031905a030041d80094407030200380e8505800592141490310514525414800108101c5070145007403040300d520000c460221360303044150031024807805d1801041c1c9035a545031050151883e0440c00380c0500c80d649011440b250801c1c0600240c590b282800c00c4150396400c0e5180c00d0b5020f0034182c1001440108506400620414072030300705003550102c0c05a40e90307461002c078070f4010444118002c2500d503141808a11821406016082031806004102e000d040400254491002902e813506140d600e26214881c1401540711580c42c4403001d40400401d0398070f080c0380010b035005500c0420782c680d6902e0701080131030217842601030700e94028003074212a0030715036100c00405070081c0200480f01c5008040c2e25094034100911401740d442 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 91926475 1250 91925225 91925233
    0xf072301050d06150f0c0503160807060501090515010c0807111206040b061002010504050d080711010e104703030304030f020613020f10090e010b0405010212090f09040204180302 78
    0x60008001c1c617a000d41da14482c01c024605443c2d0b404a14000b003034401a461040220000207550719008100b4424040c005001c1401c000001442a940d0f5000381d110301c0c2d8040c404c001c42a03201004460410010b000100322542c140070407c0070400140884001b2100581210302603e5503400340d03441d0000407601216591030090410070b0605012000030b507883c0b8240028403032030070b240c0c2c0c4140c0c48000c4952407008101001e000101441d1107042d4040280b018817000f04031150f007410b03400740c482903481c005d03c4071a8204880304004001c12074203c00d41e454400f40120b1240803003220741d081c41440000040c01404d42201020319950240020750085101e83c94000040500300e07000703070500d5401400d00c400251303522124070141e103815011404c032501c02c9804107110001c40b4026112460785401c441680c8100c4400030941181c41001841517540076001c41c0e40984070700300d034904184500030526401120500c6802c05a007001c3c04800d410901c01413000c01c0440c8001c03043d48402c0f08100041d801030340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 91927725 1250 91926475 91926509
    0xc0909040b090f0f011b0c02130b0103020d0e01050402090f071b0501060f09021e0406020304060c0c08060c0703020105010b03010b16020117150f0303031b0703020c0616050f072301050d06 82
    0x1207111942da1602d007087c180300c00501c050b5000541c0e40c040100d00f41421a071143e1041e225a88070740d04580100700104401c100b00500610390030300070b00c0700300c0d8201d020b90b00032400304411070074407070b0b00502c0b50440d50b682071100000801d124039540d4086000300d031950340f0b413072012803503503100c500c050040d103104000140c48000030080182c0381ca2050007442061501040188041c2e64048103c400b91742083c20044000d5070580f80240e000c1c4510b5006070b50368040e507020700500304030100c000c0030700c68025402806242d80b40e41c000e8540d84028420b01c8884241084440a01c00f100c0c40101c2c1a9401410b1880522400d03002404104404071101a42b8450a002e40700300c91400103065030741024240c0c0110301b50718101c6069070019440380b900002c0307074101142e0001090b1080048649455000e000240c6441c81081c0c01ca29600c3d81ca00221038500400109880c241000500c1008403002c46002c9010036100a4000500507407001445040140c01c105d100d403204454041e0034000c221192500e070080c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 91928975 1250 91927725 91927751
    0x809030606010c0c052b03020c090f130212010f0507030509010e1c05091302040b07030917100213080a0807020103110310051306030b0406060503060c0909040b090f0f01 74
    0x4103008062030306100d09000350002203010081d501007501c07011b48048000314603105103000307406642c0b103008480e03080c140c584004159000c03a60070141017003074402d5085500ca044000883c3d00080f569071425504400350080503260403985202090006000001c807a0300d8808441c00380c6030111100c00c00700c0e0303c0d5010310402c00360034410011024040b402501e10b0798031090000c0c0f6208100140101001400700c0c0130840e99032246100c2850340d904072002c55030785d03594920b002e240d070308641d90960100d000081c0002d031100c7c904104030000c00c0e02e03034040c050520b0780d0341c0740c100250040b50340f0f80f06044108102142980d03040191140d03041c0124003d9858562610004060701d5280b5400c0f4000903052050040d80035041544000380c1d6412980c5007a900803034a0035400400c0c0d1070380081c00c055a44010320080c0300c000d9209100b514003d03415a1a2507850341d10400e282d100c0d066486402c1030204001802084d80a440250403024034002d039600c65022243c0307a440c2940d1016000443c2e55240e8100f0040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 91930225 1250 91928975 91928983
    0x20a0e100c051006061e0306180504170a0f1805031e010518030a030f1404061508071a0306040603021f020f06010b0d020904091509030201140f060121020403080903 72
    0xd0050301014084113041c590010800c401d8581c5846e10303c0b29107480a40c00b0360180c1c0190000c0c00c41c6592024500c08404181d1020b000192400d4626603802c0410400b483c240030110741c1900740584071580700e803400d000101d5440101c0c440901c800001ca03c40441d1540d007d2000c14114480841d402111820480d400c03821140083e1401c00083c9915041d520110004401e582c400c180c141000103070000c49a00d0107000c1d0085070a003861090540003000304200c441c7e40815070340c0d0300c2d0100101c2d480c0d4480c2e000c1650781c0300d24002c04490301d8023800c0e82c0c10442034500c02154440c501a10100c1d48598075404182c80c1d012100e0600c446140262120a01d0303a41004a4070701000240c0046c4265450702d15501f20600c64260070001d000d40024010700d4503121500303d91803041c2d110040c0c070900c600340c00b45800100708400e4214015400c0105c032040c911042d0103140c1c051480382d03a0807030040e00c85100540d40301d151758a4400013184c032041d0781c440307485661014000a50042040c10340c2d4041c0c0b24209410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 91931475 1250 91930225 91930243
    0x61c06050a0b03010e0c010c02010503090708010c051c0506030303130615080a1a060d0b0703180c1d0c090603090708060403180b070c031101090503190317041203020a0e100c05 77
    0x2240d8414506c610861f80d00c516031410080c3c086c2807151707480e29850f029504055681d0842d00d66907003400316a046041d0b024000304091000078220241640258035402e0a542c0c00ba20031a80c1a44103002255032040c2c01d41c424004940b140000240342c04c01c3c00911110500c0070303406290141c1002d45044140081040421756121614a0011452901100040c4c40c1d005441019200b00e40c0710340080c051500960044442522911145150402c14989030f001006140204104900311a03040d484001c074aaa00c0ea004482928000b4240070750034003444204c0d0002056020b49119846000032088000e020960040c0e00903039603005c2d0103801c80508000b00b02039500c00712414100300300240124000012960680303030700c1012410181d42c00c0004882c1c91225802c00342c0e05000e5120500781540c19804114845131103a114041080c41d034100c80b40d10500116005416550f0708800d503009039100e940100b0048a035820803410040004020600316100750802201003102c0c0d04040e018040f040066240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 91932725 1250 91931475 91931501
    0x6080603030a0206040308070302041d010f090b01020729040f140a05010f0f0e061c0e0604030c0b10180207051c0207030f0206070b040b151008061c06050a0b0301 71
    0x482d0074000c1c0c1e80299140d000601c068100110306001c1882e841c841c0e01110000c0101c00380c40c9402ca0105111401040003e1090001c01951700d4000180c140c914018001000701c1600a00b151030300d000140b03d80c048901280202e078405181811035901d80754000303000500080e00500241d41d04003126030f000c001266001500c00c50400c60100542e80e4010310210b003a04903481d00e852400881c4105643c01900c4541040e8004000301d00d901041524075100b07400360490301410301201c200518500d448550588025000404d0000800c001ca40c124482e141c1040e45061800c101a0795007a4080b01001401e0b040d40e50603800040482c1071110170400c10624080e41900c4804040072041d019607100d0042c070004026441c040741103015540c03480192040d107a003218607000035207040c3c600700500002c1224045410740311030b4044003240c100304d14040381e00d40c0144c480e130641d522007000308902d140c400c0003501034041540110b9800170741d9074010203000703031100c00c0081100c180c4d5400705420740f120612507035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 91933975 1250 91932725 91932727
    0x50c01020c0a051c05060928110105070c2403050f01050915060903160f2705090f0f010b010e1e1002030706060303020703140f1c050903070e010608060303 68
    0x181080e541c0c2560101251000c58800801d131075040440c10b040307101c42802401d0390180308204100000041400d0070020510002442c04010500d0908252104e134000605545400c1c6400c0300603500510003401d00d540540e40c0c0e821031960700e401c400e001c03c0c0c160303201c8802c0c1130300342e06056070042d018040c0513086918010000210340c10180403500003071000303103a03541101d5043e035042103e40315481158003002c3e000e001e031040580300702c0e81c0c0d40043d4813170f1103601c03054039244100140309003003014510900d0b0316030103c010b28150100e510380301400c3c0240c140f5140380940c108050320054208220001c40808030b00104000103c0c0c0000340480304800c00a5014040e0f0b2801401c081da00d09043c030b503664100301c41c84a42046a01130072071440c01001c0e8001c1900c2d01c1c144010003450780025215003141d03c1801050850010101001c0e1241d1641100d000da0790301140c039590104406488030000d1a0151500500f0902c3c00000203162110700d40c031448032000140c00600600303900c0680280d20a409078015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 91935225 1250 91933975 91933993
    0x906080c10080f0403051e0d0e0c0d080307032003070201050411041104050603040501020417011a1c12140a050d0507020a02060304030509010e04020304030f0f1b0b0c07080301060804050c0102 84
    0x72601d07012000340b000b02007100007d25600f8401e80900a0b09403e000140c119458042c01081e00380241581d80600049107d1070040041624050142e807048d690301588050030354417961801d9028001c1d411803410614034240300703a903180240350040c0d4860002540013003030604160908510040c8041c078418056412300c203021169030b14003001c8030101da0090360855a00c0d1b440b424546d00a00039600504c000d0f90131250018001141504544a50030002440041d10090b62041100759090400038025030790100505201265074080305200300308041c00c01c1500085000c3c0b09201075070200c1002e03800f040c1e0209241c40310814078880c65900c1f954900052000031501d800046160200400c01410030900080f1100d65034131401280c0d00c6030303102030419500c9062500d801780922000354241c0000841d4500c1800e98544114070107940c56000741100c103070300750b61900d660100f20030041410000090030811000010b0035400114020030040d0348002440c02c00303181c0b05041c014072aa400341154003284007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 91936475 1250 91935225 91935241
    0x10e01140703050c030c030a0207030606080109110d052107050c0904080f0a03020405041d011521030c08030901140c04180207050a02040e0102091201050f0a0507090906080c1008 78
    0x80301c0110360542082070700e0700781c42c4504600d9880ba603d81c00c00d05000100d07800103075076000120754060301d104540510041e62580d565508071a040d01020302081300d110071000080c00c100f625441e2050040d0141d81c800e58601c0f4401c010005403140c41324110b20001045010b11009001d40ea21801086441e540d4506280d15840a64015104580c1e082c40b0300150341c80c40b00d8000c2d8100c8008000182050051914401032283c00c4849844041040d50801d13035a0800d03031242d525084d05844174401046000c6920010645804240b10012030074444004c92060102c0c1e0700101031449405480000300d0180c030030391084000320380060000b00518a00b8031007400840c1c800b8024007412a40d19800503280e03103840c01d0583c541002182d000c0d40262501c0c080c40103108041d0000d110000d01950350010f8050910505400c0303440c1154602c6048140001181d642481c90300040d07040384042c54107030440c686814950003151040d0380084295130020b1103a0f42c0c581450410f02c403441015007803168403803170000700d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 91937725 1250 91936475 91936477
    0x10b030606160c030804030c1205100c1404030b060f060a020d0c020d02040e01060e16020a0f0204060b03071d121b060f0f0c010b030a0c12020409150209010e0114 71
    0x1190038419800410741c5011640307209118400d154006001900c40c3c0d540f82064400d990203404240c499104ca030401241e520800d94940304100e520000401f440802000030f034004105c40041f600810001d00ea0f22103005001030081d001450140c00c0c0960343d42800020000c0f072826503004140134100034056110310300d401003a0b08241922500340140020001d2001a000e8803040200070740c041e16000701c0c803004030310540c011029140c90004000454407601d000d0b00e220881c075101c00b00140d0014194100003289801c01d0044a4805040818038a40301c080c2d100194204035810000255038891070700781c1c45404404000c4841d4141c030b0503107401700f4003148952100085445a1140c98407880c500e0b250b030311000c0444018040c1d11174415140e1a80f0709001d20305a200303030042c0c01c456003001c0580210385004a0664511f560041c0850102440d0001080380e1802d091805c1c0e07445030303030380c0d01a0001c2003a0301000f40c0e440d00001030040e515103200b0005881c26891080e60742c100110f80c01d000100c0c00d4100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 91938975 1250 91937725 91937731
    0x30a0501060906050d0b01120203030d090503030f0606090a1701060f0b031005010e0901031e0803010f08061015120216081c05040b1f05030d0905120c01021b030a0b040b06100206010b03 81
    0xc50b456208c001900100b807544c442e0801d6208450f26200d040c00500801001541c0600061481210a40c0307a40080004a001e4400d9950b44031016010800103604c0486820502142d00800454584d6441e1140b4200100c9507001c1004040c0001c20007406404010607140505400d08040c6c2284111030046203641e00705003c01082d02e80c1c000c60070100e441d80010546800c036030005800d6582e684650b000780304100688244201d43c0700f680007140d9600c2081035600181c1d06400c0f62008a00f21006d021187c510406400b5200541c0c02c20050b040001010200304482e80a02e07480782d618801d00c07c0310f00c0b0082c581c00414079241e1611b011312000540c607024041d048000030007049408100d1149144d161031842c1d00940d454450001c103002016044000042119000c440350100315803503182c3c20b622185c0152810b401078201d180081207401058441402c001c0340581240d00c2c0d41c0d441d644100392902c09443c107940700e1502d00108030951030100281b442446662000e010315515104140e0402e000c0a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 91940225 1250 91938975 91938989
    0x109020f04051003022205040b010e0603041b03081306110307050c04020d0f02070605160f0e31050a060b070b010e040614010902071b0308030a0515030a0501060906050d0b01 76
    0x10004910b0b603c0c400d806980c25242c4001c1301b8080480c014030045e00c0c10b0505e1081e90300607820321052101d0b66006210011803c10050040d52442c0d881d079496408042d0024040341c15243c01c01c1021000c00c1340007014040da20b5104034000940c90900c1000b8149a04081e005285076004200c10700c0000c802050100c0071500070ba4001d6254641101414040c00280e000c19409038400302e0310f10305001c00368105501030100b803c813180e40c140f007014085800c0b1101c02c1d40d8201251451039008000d05118001400703402251100041d25051031260705131000340d02c03000084158950b024858440c14511a120003004100b02ca140f81400b60b13540e0000a0405120301c440d002d04031030004007806045c0d0801c0c1c0d1109007040c110324040d030712000060000c0d00424019102c881c81c8180000c8040071075038003001601e8000356018116a250241000507080044c21302a03442c1e05013000c4052500c0402660100320701c640c0002c120203041541c01b104903081075000500c41c3e42c64002c0040850429030106054440c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 91941475 1250 91940225 91940239
    0x1e0507030e0301060b0c10060e010b03010e190509010e0c0105030121050f010501060807120207020d020f040b030111090103050a1a010c0501020c0d03090506060409021f0903080703030608060109020f0405 89
    0x1d0200003a0041243e5070104801c08400951190b80c1d803004143c20341e040c038140c401084415118050b0b020100800d0103103011080041005110b80e05070b110410b075100e1150326030f550b0702502045408040e1001a42d130444242e44412501c68201c070305001090303905000b0718006085624040c43c0c203100d1801034060a8450b4070f583d06910074004180030503500142444024040fa594030b210060500f80c1c100d5044000800b030b052890440390303a600841d80790540050850b00d420242c7d40811120300394214906a205685400c03c140e1a282070080883c0e00d04d0b00305601d604d84c80360900250030b03948028078444070035140482440902c00d00103407441840d01e00f0f01e81030800c40d40902c5c0c05802885072140c0c2010a100f02d82c035144c211503054005415561044007500c44a480b00d205200507150500c1c4003c2d48100018031105d80600c01a0880d0019800c500d072030000c003039a0380c0365420103600c5500c045d0002500c0d846c06102003401000035500408100c0e0045141018031205000074ec0154081c86100e001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 91942725 1250 91941475 91941497
    0x30c09051b0405100c08040611070801060803030402010e06090a090e0f0105061503040203030d050a0c1202070507031104020f030f040209060d1a07121505030d09030c050f010302070506040b01061e050703 89
    0x71040e900a601580d11145281d1f40c2c1c0d84404014011020a40c000500c5201d42c5501203801013040c010401241c208000450841d03c5035401581d00f41562038640c1e803c21414844a06180e56480910000701307040f141c00104040f407500550b003866000e0100741901ea05040520205842d018480c040741040f01200c00c1e100c0d10380d48002800c40c0710b4040215012410700c2c0900800e5101035100d0300c1c85c90f007541c5452042000100c24207003030303000304030018056800900040000c03c0e000140b000f03459600030300051a02008004070b101c0354005581c00e10388000342c1c804000840c2041c0386000d8001800322480d982c00d510303035038aa0301c01900455030842a414044003060020703000d44481400d64401010a01c0041d0140613061411189446198072a01ca140c581099045c05207900605580c0c000300344a01081c24002408201804280001e04140d820410b00c004070700c05010203030046110300310703201e131f02c4d4036218006150f0394000c001f1203801c200798090340601d01d811004072010b2503414200992000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 91943975 1250 91942725 91942727
    0xd1205070203060a050907120b070c03050c0a052104080319170103030f0306091b0509060903072301030209010c03110705091905090304050a120503070c030c09051b040510 75
    0x101034548001c2d00351050308240b080c80c911a40000b841408804100d0300b18695800724041c42203140d24000d03003180d41c0c2c1000f040089124050451000b0b0003070400c14500360b04039503094a89440a0010b0340c068001980344416900c290613522028508100313003509050a0400d4281c0f0b034401d00c0901480c0e035224103800c00fa81405924000c80c1100040d94140303442da5207042c0a08840a00c1d1180000249016804504002a03205200c4e070244440102c02c550003544c902035032954400e442c440c0d8009800d0000054aa40401a010252a0824010744041c0c030a41c00d140c01d840341c4920713150616005016201e49640d01c60780400c81240c1500e000c1c4042c0c00000035403030811040c0d40056410502c0d207400c11414101e03c141864141e0b01402c8208220340e01c980c60f80d912400fa90080d00d5003c640b4880400400000c0c01c00903410760b0043c42603030b01d80001503035804d600c80c105030310894603050301c00010000c3e450b642c0304055102802070003250324504522004100c0e403046005280c0f04003004203180c1202 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 91945225 1250 91943975 91943977
    0x3010b070c0909060608060703140c070f050303010b0702030f01050f040206030a021603050c1b0a050103020703020f010c0c0308161e05040302060d050402120706050f0a120f0507030501140d1205 85
    0x426841104010f0f1003076500709840682202d010340c4e941840780e0800b14448034440c2c4546a05180300b1104038101ea25030707000c500203030707030200100b40c0c0da480080702c03180301055080c40158004c00d440b88915986d03030310310300c1814100700311050100400d03454103040100b5102034811003640b0540c1100d9090380d035504d01c507a0900034021070b1201410300b140302c00900b04041d0040010301107684100c0449a81c600c40d00c0000a0321a4580152034004060364010041540280c015010aa1090041d1002c0b003802c04c800c0c0d800c48100807088000601c85610090526411580c1a904070000e00220f1881002e14100507150415614010150b50050050910021712920541d00603660051250380d0f100071490303d6070098101034406074414640c90700f2009400800281450480310136403034260070511440c1000c41960444950b841c10f0109088128800002074030a60800b90301c00c1c07030005080e0515560080444005800c5454243c181d98140c64040e90b0b10110594200c1d400299200c560181c02d07012115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 91946475 1250 91945225 91945229
    0xc100506131404020a0918020f06070f03090e01240e06090d030302030a050a0603021509030a080c0604120212091207031406070e030604020a140307050604060302090f04020a0503010b070c 82
    0x100c2407401801d010214034841080f4091402241c0349409541c5401120048490241041800891070b40103c0300500b0b15120356042a0307002802541803207920785031038245044d8284120002a2101c1c41400801d00100c821400740000c0354203004c00c000d01c0c90880380e107945000202002c1c04413500c182e0340280d4a503004c6503c081c002412900c245262882c0c050080d4209a98103500107040c40000751245880d03124500840303400601001001d2031039072825400350f021024282e007601a5007000340102c0d02d50300040100c0f40b4444010601403609061009003c0b00d207042034803c54104c3c400440005600301c0c241d94110038100d4100c0c070042c2590020318a0b085072584005e000c00121640358405020100b42d02c6d01c14829500c03400c0c0d60664400c00c1503220881207400a50010304034a080c0600c070101c0d2200d1585000c00f5044600e0951a400050840d0300158003202c000303500025031041e00d007041a891500000142c60541c00e088104001070050b0005010b800e1650704042462001c0c00f0300c00400b400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 91947725 1250 91946475 91946509
    0x7050a0501020c07030303060902070302030405010c0c03020d0b0402090703060506030712020417150703020306061c0228030c020606060d050601021f09170702030a0b07110303150111030c100506 85
    0x1645424180743c0710303201e002a11080c2e0210340f5159000400c10030790300807078820a5240d8051883c0a04180c015180e1119811040c1d40f2001ca044001c401612000c449000250040500e94013a10741481080000708008020004060401104000d5902c440003565048000303800e201800d0480b50320b0311002030155030b001d900000a0094102c0300d40b040482d074044030000d02c034001c1d111966811001d400340e1000b55042a0808010821915501c501048805258802c240d0244c9000342d100d030040c042820910a505107902c0400f00302e0340f255014811060810064000f038445440c0c0100000c0075400340b80f03000b0b0f02098172040002c400303a20a20400c00301c18400a190180d1503e8500200001e02c8001d004441c02c40000380381c80c5031045000f00355080710364020b00130040108950307512480e480700a0b113060309104c440c03440041480001d1000e5841002060001840002c443e00010500580d401503105139401c10400c00f000b005000c81c1d851480c0840100c040f9007511140c0200d8484007000b403d40b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 91948975 1250 91947725 91947727
    0x506060c0a0b01090c050a080103060902060d0f0609050112030804080d0908071b0b040503100b0109050a030501021c0b090106180909051515010c15020d06080706030e0d090b07050a050102 82
    0xb000400b14205060302e802c220300704084915981c05640c00d2140c040d150000c141c0321801000000c0aa070800c0c2c4140f44080d1005040c10501c094203016030b024815404e00d501e880300014803121a583c0315907030051170920701c002580700480d00d004c0c02c0840003a20117058001300141500d0300c0c58044e04602d41203580843c8055403101e0600b05504103c0f0000030904074a522200c0c0001c0d04801c5c841a10300b0b60707a001707018181400080307952600406914a489050200c581ca0001da217a0310120940019030050002582c3e4410509800845d140c402202112651034925501503507190001e41905456050030300c0500003107400280f608150081d40415a03840c10000381004014010903c00400c000408845849448171590080310b1040030b0095400140125012408070380080403180c100880351000615010b101001e02d401d640c40b5412440580d4004a4208a503a0b854403800054881341c40160140300161000104100c0f564841d090780c0840c04140e52041c48028410105001d912030021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 91950225 1250 91948975 91948993
    0x804061b02100608060f07110c030303070201230103032001020c030d0b0111060108030a030c12090303020309150103150203150406080c0102071a0405040c09030803070201022a0a060506060c 83
    0x95540800031500b0748542d062400008000310002a03203802001c1c040b28030b02481d95413001c2111041081c01c807195091080c800061170a8a06100440c0905456800801e15040c880d030005c00b01d034050743c18410301c0784000c001000825802401d44c4034955006034000c030800d803090141c81c00b80c040c0d5240780c5814000007600b5820900709a20101c0220350a032a5080030034480c408950b10750301c09109012040c0c00c104400e507203107446984456400344c0c0721300b8900a4851714011500446681c2c42003140440d600005000054404204160040d18050030310240c56056030303900c03147c8048003810b1601c10740d00400401e5201390580021440c0c1c0310050410001a82c4c1c440c1170320f68485988030140c0c09400750203400706480c091820180804441c0050440c5003034580b009200040a42104010070070801101c00320004030800000c4d070241c10300da800580c40301e10480350544545440820005040c5d81b442c10038200c2d1502040b8088060740000000445079106000700c3c40f02d2260b86089030440c000d41e006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 91951475 1250 91950225 91950227
    0x1d150c0718020316020c10030216050f03031519031506030609060b01080601020c0901030b04052505040f0e1504080c16090b030c0307030b0c1207030c02011a060a0804061b 75
    0x145102e0340c4e98628450031420300c40c80a9032103894107a1180e4000001040d1488024001e4004041ca0440c5400c00c043c480055115942004511103c0709899000003060000040040d0141e84111340b08541d0b50b06803217045c01086625800a00c4000c010b101141442d071410303850381d07000748000c6401c15001e005080480c50254010955000024085101c41000c1905940b0010348c0064403079024041204a9017192180880348800a0044503948102c286581000f85600c0082022030340c0c3c041035418142c240410001a1031080070840205403030714031454003c01c00040e68504208004400c450781ea11242890b0342e40e0b01c03030300034681c4452240e20315104040030501128412188400c1c030400450f5446c004250319240e92008066040d44a128188007088150703c00c181c105c51a46000c0345401044002d03004030381c0003103500d4404240d491820034862134082c09071401c4a03611840c105806003043e0000750460240384211f074100400200010200845640110408014040f00c00410b001c1400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 91952725 1250 91951475 91951477
    0x61113060e010f080106090e0603030408010c230304020a0308030601090b0f130f12121b0b19150b09010507051b1c15020a020109020915011d150c071802 67
    0x1d14280000c28501a124610744079100c454161400d941e6071000240c80c041c84030302c00e030304050007a60345400300300000902c4030024803036130b54001c6607515130301e00700e001c00322101030503c00b180d00006981004000308401a629a03c0d072100380ca500c080c8081d03d0741c81e01070040b640241c0f0f68004508981002a024400051180c0500711000520345420340c070a455281c1e4149000b201d04c0360510031002100d441c0009000821525454103851510400300800b460355401d81d9640c15000360354440d680d906000f006040013620388510341005800788071001c01d0600700307907000c203da10810095480115096000303a1003070f4202d624498010040700c5198110700f0a0200803100c525401b4032031448101042032150005611109081d04204010070501c500d40b07001c406980403110340c0e401c65584120100050b6034055115020304103022000c1c010340d622600150000c0b20380c0b00a441802c40002c120704803a80c1d040d08170f452003000c2500540d22403401d640f81610305001600800311001042d02090315205680d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 91953975 1250 91952725 91952747
    0x7060302190507080904020f12040f1106070b010e150d230a030806060307030f020703030e010b0103061208070f050613030318050604110a090204061101150f0306111306 74
    0x940141041d01224206031400d2191090041c01c458040c0504202e600c1d0035405060410303c3c4281c030514144c008400c100301c4640c00c8904640700340c81c44610300309001550011682440060390398901e4050203845019260005119150b1049207201c00588006642e00002401c2c0001a20341005050700e49481005090700c00403507100c01401c20030342812550f00140f06548143c0507120900151141800e000043c0d00003020702c014942c4a070b0289a00c106c03d4402031035054065a0300003203c03460500e4003429109640c00c03150400d4200b2405002c40050300e02084103d43e40000c1081d0385105604d04201070121080d0090700305d0041a040103a884000c107070340c05500f0720958003007145d5a81020203a011102000003d003080d4040c034000740014280c1d040083c81860300078040101c043d5910010820307644160800d50003d090f407850441220424000c9642440d0500050b402481c1406980da070703c20154030016040640b100e100f80000c195540842d810000c016030900951525120050100c00181e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 91955225 1250 91953975 91953997
    0x2030c12030f0c0d09020d1115040f1202150307020703030908030304030503061c1217060a03020f06030703140106110d022107020a0506040905060a09050708070c0302010b0307060302 80
    0x4400005081180e060440b44241c41e06081e5400c55201e0400706075054008a150300360003030380d80c11a080541d480041b040c007018411480d007107466409100b84820320040d0310f191038a104042c0000d02218982d00d24075016292207004482c03070102070f800081c02c00c078007195403820184000000d0040312640801d01d44156402070320b960341d0059442000c29942d2100b164041c2c0040c00a00100b4220b20b004110095100245603072040b100015807180b481101c0f0180011010502e2b403c0d00c5004000c090070f01d240d01140460725440b0701851034000c141b0140c074011100b4446d02000000812b031600950000c1c07859680c030076040825607101c4001824010800d00107050901c101c1d100710720a030f0320000e0701c2c030001d0708207004e80c0480c109203a14040f0785400844003268044840c03000415552900d4010b440285100d000101d0750b0308040080c0303c1201d10a0f00304090103030030201007011584d048600203801264518000c080c131394860400703d0040c549880d566500d80034150000403a25895006402c0c22508 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 91956475 1250 91955225 91955233
    0x4060b0c0d050901121805120c0708070f090c09080312011a07020d080f04030b0a0b04060806010806010e0a060b1602030706030902031f060503120c0c0103020a17070e04020a02030c 79
    0x200c80066a583c052680030301c1c0002e41d02e2000c1a00c0d0362098002e003202810024941150009903074400342091079007091007081d054041392038040310a08024420040130b902d07002e820b101d41051910702c0145014010f010010707031101400e2540c07a1040d0f90b03802c01401300c402965220106688800d003d031a007071055005070030f001e0b000300300c20362403080465620641c001e04a400c28010f41d60b0f242403a0300200140412500d00380400800b04040c1b50165209200301640010782c81909410402291340c140c10151007541b000300184009000003c0040c1540e25400413441141d44032821000500f250383c2000e003107040c1c0460340e903031040c0e0881002c914103482101500c51194036440202d00f1500c42080c041d42c940d00080b0694182d003132240404078407160403070000c204c3e10b0300c40e0042880c0514842204110300c074000341c1914201e40c14045516a10070034078041d8a00080d80400034a0a41e0100350594544625000300c2d0f040c034040c142da000400d40140003552240c540c10001381d283c0e04040c2c42d00d032941c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 91957725 1250 91956475 91956493
    0x70b0a18060201050412170708040213090f0c06020d0210050a0204050d03050d060e090c040e0a0f03090602070e01051e011e050409050105091b0307021f06080d030912050f0904060b0c 80
    0x401001580343d4a545241c4038091f5a0f5510b8003240c42d07450140007641c00484084480c2407040f854052814806d00502e10034103190b8907464440c10601481d888401150003800703a01403080d80c04036200600503060200821951507052254009100c1c41d0300ca260b0004000100c5000c040e0048007601d558801391004015699540e003250701c01d02e100315000c0400b500841082c090500d801d50004091f64146400c4a0b02c64259981d040d0100c50006400d8000c10910101000300c40e41c1040481c001e40b4200c90700c289554035140200308085600c0c07100443d4008414a40c8107141d00c2540c0480038500b20322801c90204140917009005070740580288440b0b2410800040b030682460448107008404044540040602ea814801031503000035103044118001c400c0140c2d2000c4125141844003a0280000100b241c0381491285c500b2451039655014941059100c030081403c14183c2c400941c03490412944d1000307540a0071100c1d00c2442c0c02c1c5940217151240101d02da110b102c000e0486407020f041107a003417803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 91958975 1250 91957725 91957727
    0x902010207031b09091101031d031c0207050102030c040e0c040311060f070b0a20070507051c05010608060711010b01080f09030906130e0601022e0e03030414010c11070b0a18060201050412 82
    0x26918000f006960320800841d52f68108a22000b20400c01d400c40c01030034039545580f007500b66070040d180c0500000b40410244510242012a0758106001c004400e1510b41340d603480580071101404068450100494810020503403d800c451110364820741c04211031802d00c120000622005207184000744c22641e130310743c02d242200c0031500c40360b41000c01010150318200410040d4203807140a95244074045090350b001072801d010b06c001074400c000c042e01071403410340c00c014614101c000082c1c8807607040c14a80030345a44c2000e009038204250074040049640d420301c89619512980e50080e03001500029054030b400d0352015203909460f08007011203040c0e103c480049035540c140e03c0001241c02d0000c0c8003c5034121002d40c14503104201141d01040c02c5000d803400a00707540046506540c0400808164058000280311700309140144d4107001d80480490000da50703840c6c40714001d0345103031100090b03001c16490041070080b40c641c07d0000c00301c044585905000b4041c003416141112080080c00c103001c566 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 91960225 1250 91958975 91959011
    0xb130c1709010e06150f060309010605010e0f0d060c030e0d0203071209050916030b1c060b01050a0e12011503050d09060c02060702060a140f1308010902010207031b0909110103 77
    0xf03100c1400400b025101c8015800b00300601500b402e0307000b81e000a002045440e04000b947c8a40c1d50400001380c898039000016012411078a145445000ca02d8818203d0303907281010145ca50340c02100008424200200c2903005140519032054544901d188640a8650000040404c0c03440382c186036154003603074101515408198003410b980107aa0308005122181e01000c000700c0f04d4000d1034042080600310000c107800f4403003084608055208207082001344811400343d001c61240c28a015888e0007118040146100044a42e040c880c1d1521104090701c00d001b5080082105800154070400c15900d02c2d01e80c2c0d0b1401c52010382000708042c1440054081e02035410642c26a4016086901d00b41c10b5a00b00071055001207109801d120040c0c4022010440700405030024452403011207550b129285810220001e00d03030301c8a8000d030304201c1c140c401070360702146080032290301c07443c0c502c00c0c0000c090206a030517040d5080012400d2600d4145018041c0501e41e41c01c3e003a6081e00c2c1048070f060070842c45580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 91961475 1250 91960225 91960241
    0xa090204060e060405090f071403070305010501020c10080a180204140f070c03020c0105070302031306020d0e0a030f240c020c0901050609010906080a0917030a05010e0103050d030b130c170901 84
    0x106c0b001190020707080a50403881c05034410789515100481c0c881d4038019440e20b4006035801c10010b551f032401030101d942c04202010030094101c030004c1684840500060007070100400d20400c89171145004003003080e45000078524190f00810078402401e401d01c010b00040400c44020320400220004122058011400d00c10b1300d0340c00d1f50140000e41040d40047d07541e58400c00317007101184020856001211140c08001c0040d00d01580640420400108000c2440402c101e2a074800d00d9004010000900881e604074407003039200b518441d542c5000c1e1281032651141c00710402d040c50404a0500c1255404120301c00b4205c4115442a4141d0b269414003083e80503102400b80841d4441d8004c2c401c8502660300710380e0142211401140b40140d594501e18003030b07012150449220004018407031403010b20b000745800740001c907030303117042541c51603c48655030081d007a420304c203140d95000001314584078085110130310310480e1018450040c00f440010098450308031840c0d01805800c0105103410410300940003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 91962725 1250 91961475 91961479
    0x40b010f0303020304090216120206090709141b07051209090a05010b07060b0a17160608160f020102070206030f18010c05040303030509070510110c03011512020f0a090204060e060405 80
    0x1003043e00b8042d2880081d4815040d914905015400d08e000161070100964548a082d60251110742001c0c2001464144942c224480c654104642d1161450401172004d03480450041601e8201800d400024060702c211000035181d03018043c019441c042d8500c0c0100384644058800d405141e42d9031005170100c3d10280645100c580c000c200600c0812140d810440e4124001012100700956a444001200c00b980c01800c465030442070f02003801683c1451400001c241c5421b000b013040ca030003030300002010a40348440c0141301c54440410000352007541600c10b120741c007810f0359949040081001200840840305003200950606d2094802e140c1802400a460b010303856050806080d558181c000d460300030301140e00c5208034000003c0b150340b12021080e501000303450710860024008685420501e00d00741090003a03060200c0000403990b140044c0003211412040c5a0f5141ca051001030b0b0a06904940d035603026515a80200d0404081e40c010300c1100d4031a250a0030680d01103090000300c0c0258400c0036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 91963975 1250 91962725 91962727
    0x90f0a080909060f03060106021f050408040608040c0902040b0711010207030b060f0103090b2d0c030a020c010f060806160305040209010603090f050703111305090615031002040e040b010f03030203 86
    0x450541403580000e500260001c00d83c500c1013031010046454400241d02480050f0b1000c09011040c610f00213a10441004181c07082c0154034041d103c01d0034521441c80b810303080003405000102880f080400c0840684140c00003999103569803000c821170b6800961042e2184411402c4031080c5600014201040360340c0002c080e502a45c0c1c420030458040c0451200b18141500c03034480e1000104001440c41c4542d0100c0400c0f030700d5012080702c8031000001119101280c2c00000f0520103130340d403800705907503000301c0c4107c001d07039a2070281c6007907805810b02d0380d8004955070810002042404010404a11448150a180d95540f140040480c2500d4090310041e40086880d001405100e120b90403800300d5500610807104a8841c1d60341d501d00d81440c40d4020781704c80c44850464001403814503140103070303e01c1c007940911160401207041c50301d0307000c080e120306103103040c030503004001d504c090219010018014000719117503555031a0701242d600d0308450454850400800100321254420340c204207032600740c8e00175 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 91965225 1250 91963975 91963987
    0x20102030f0a15120f050111040e130c170a2a030f0206071a25120e070f0e0603060105010f020d050906070209011205010b040b0d020607140d0503090f0a08 68
    0x2050080600c51480f1100c0d10f01d0702c0003c0b0b140703140c04080b94602c0e485286212406181410f2290031140440010a04404200700800c40001c0c1507950303517009801111650440070791468415800303201c95115a00300ba4480842062401000c10210310b042e02843e21141545034280e00070200e420307108241d02e0036034180601400840d00165115a8403440684034500e082e14039100c7e501e81c8100076100c4662039101c03208014150902040b428000b43c3c411902c405038141c041409040300030035074a0041c201c1d98482e4003807100c43c0c00304080b1009144800000708541e41710070b03600800703000840d0740900038801c80e000020365520810202040a40d143d0107801e4440c0c0301c0404840d6076100020441e0700100a21045d0003603595850f00c180202000700e12807113529480d02d095802d54800c003190310312880c035014003601d49031902c5c3c40225845030b048440c1642e400c501e1500194134854035507560380c140304a088000e4400d800c100214060202039040380e01b01501455103594038410400c0081078000240a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 91966475 1250 91965225 91965241
    0xa090f0f0608041b0b07050c0d08030f04030e150d060e0906011a070501020a05040305010c080103050c060c030f03010f0501110f03091c060e0105011d09030702090403020f0604050601060906020102030f 88
    0x40560414426111034403105042c2c400004c410010b40c011682c2400009000f0040010400042800140c01d56095000304000d80301c0082c14040184115070600d965000203003010300c240508c13010a2130003096079004c0d450b8980c3c18407140e0011b0340a81c0303215103480400b18080e4244003005208074450401000e241c1c2c2056107447c0869181d0310410741000023484403c0c0051000c0c00038109840c8107544041c1c03107901e141485400e4030761081901d0309000b2800010f00c046680450020080c6105481540e500c1e2600781340c0c18514480c074203103903803004404000030030380c8240d009a900440b4000d03a100c004104900007159201d100728001000164010000d54105040190002602400b06500800b0522494a8400507552104a440401d03551400140a0b40f41041003400c105080030070302240c00c0c40d00d2121a81c0d24411030f50b01a124489000021302018408c00c2815004000d0405840c001d0400780340c01d030703a070340802e01648001c6030490b040070901910501c01c0e24031a00160341101c5a41c0c0360586 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 91967725 1250 91966475 91966487
    0x801061202040e071d07030c03020c0d0e030c04110a020c03031201061b060509070509010b040602070e1305070602010b011704030e101101020a0513050103020a05070314120109020a090f0f06 83
    0x20748200c41c00b544e00d001905800e104c200402c048400d21900d9281c1c90300020040407585620080e106251050059510a04001071f004000740600d003404c801a54038507000918140750440c03c40c0c1e005040000204000d841e48014003c03020742a001c07581d40951101c201616030060302d06510440e400c02c1d0040281e41c0c0710304036480080d05002c0604044007403e440b40004e46404a40f4145e00b0ba0102000700502d00705016114014020003100905190800320000e44882035403140ea03140302805000b0403540003605004101d015401021150078503510b08000e400307403451949450120310351920502480c00301000d4070717100d03541c950381307103040039004004100901d51522519420889040600b183c07102d42440140340300d1400d41c03585901e4070102441c11403000310540245040500500882c00c0858102d016540410b9040c03c09e81103003882c0003240e044d940070300b86486012221100000690803c158020080d0740c130b540d030f168407800361903501c09d10001c4042d104540000061020410140784154 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 91968975 1250 91967725 91967741
    0x106080403082206020a020d090602060c041806051f02010b06030112061d03160506011e17030708030a0b0f030a0c090b0105090a030c0608010e0f01050103020d0b03060c04080106080106120204 84
    0x8512400d6043d010f4807800126000000c0c42d0025034003051340c41c101140c001103014010034240c4010405844d001629002d03078042d901c902c07214886040d664a4184907a07800031000b5110140c500800e03090711114481e0408102800321015510f04098448507041c01000c03641680e220045110289180383d548500800d060741036201c40140e04900b80602c44c400788000d10a01510310f003010044051410414113020b010380c001130010245003445044040512110812120800300c014441030468170481c2c03c2d44a0030341c0003003003604000304004422140d40c0c051046000c090720a0700c106103121003416691640803c010b0088030341c80c04200301000c184c0e00207030001c5170185047c0b400d01940c2d401203211f104081e08110b9500c0980101400901d50000403140180500e110900d103a04041c4060060110180105410541c0004214649840d903030030802d40307481d0217000c42c0e115140076280170144c0d40203801031030001c0d400c181c0f000038200e105005040964035413800d01c66030301c5400d508000045c02c1c1d02e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 91970225 1250 91968975 91969021
    0x31a06040216060606390c0308070b0a0e030a170c07020307170c030a0b0f0c0408030c100606110618010902060409050a0b09280b101106010608040308 66
    0x8100040c01c8807002e00c407641c0020320980c00801d5490a2001c00340c2400568001300041e04003600892490080e80407050342806c00b00280c8012620441c10a039003c1821904040c2007540005410402c02042d4000c2c14030800c01c0c52010084031410351030580d100d204140e138000020750f08600403502041c0c112030954005205003c000d26010081d40403d003842d0035a030012000030420f03c0c3c2100c0d04001401403040e0360034200c0107412030980661b04c0c0c800045020344101104446100064012414001101d010702900c1c1d0440f070702c0d003401d820b070720390707039801818080102600700000011254040d04040c125034940c0005000c2d10394a1080348800f0740512401101c1c1592a0480c181c090380f1882c0041c4040c050300100444c0c1340c6000300c110000c1d5211066101e002e000e004003000044031001140d507402d503c89800101080c80b00d4091400030f4030a0b9425603900c051208410f0b1001500240c8081c5030b40111000c0ea43d41e07a036104e1080d84c454000f120068041032007a00044d100d446980e070303460705824074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 91971475 1250 91970225 91970227
    0xc0806070e21100c03020d0f110307030b0105091f020f0106060f14090405101406070305091e151201140f13090503030106030501080c040605060d020a030e0d0203071209031a060402 79
    0x2803c08a07070240c1e40300502110110b5400191000301d44c02500601139140301801050109002082d001c9a0030300c001841942010381da84944943c2e40c1c41034044811482d4000c02140c40100307200742d0710030060514255000948075031341700a0b807881010300903501120b103c1d03124040161245103055030b0380070410700402115201044074001c9691a4032609016205034140450500d040c8000c1c0130382c00c49041c1440d1300c144030074441c03403000a62080c00c4441446c0f0648802d40f0202c006460710280601d00400c643c1c0c0806940740290b0064008e502030140b09030156805c090690745d50900c0540950351544140d042080025100154204006c1812088a11141c006803072102034956a007550000e07080310002a494000400030101c1c1048503041c921400c49041055601d4540040c0303891040d9001016000e8001c16240400d90180e030100a001c1d8510781070350303001030421030001d403039500840f0111034a288442c42914918400c5802d40182c0340d11542640d00080102c0100360040b00060005602c260 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 91972725 1250 91971475 91971493
    0x160c05030f030415020c240c06070e012706050306120105010602030405010909020c1e0304082b1b06020717130314010207020f13060e040c0806070e21 66
    0x14104508000074614070091a2550306250b03507a21001040c0940408650140014085603a26100742c2e06162039842120344441001c02050b048070300031a03801c4801c5004d0441000819074016644446e0106d090381e4100d101c581e01c10200d0300c40d012070000381217100e4421a0a0040701d00a4000f9a00034600409003005040860241030942d03c003600b108005803c082020880c2d56040344140029012848096003084481e040c01c6079100d07094094442401005440801d00002c00d0007290042c05003002030f206411244030b100018100350300345440012a041a4190f9400d125151401c1e2207401070101c0820741d2001e4a6010194000e1403060305c01c00c1c6282542821450f20400402d40054079130034100c141850f6062444011240050b00f0820740d0042007000016502c100101082c61070840ba0407041002c01c6441d40c1c01040603400101e03088a101003404180240d160b880d0040b6030503141120342603901d00390b08990380188603115a4100c92060708000f401c802e00300c80002500001012501d41703003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 91973975 1250 91972725 91972729
    0x80f0c0f07090e06060a08030a08060406080304032d0b01060806030115081606020c0f0d1403030103081b120f030a1103070513090603050c0105070f06020f0405040b040504020105160c05 81
    0x41640d0740704407480c0342e83d0104034142c2038081c0325560740410201d500c00781c030030b02e001c481c0c644901c01c00b03031108108454480080c1d00c640d625803280000d840c4180c03c490f01d8039281c1c039041411420b14054840aa0408844900041030b02000c0310205940a25035245691a1030b0342943e100101520701540355486418501e03a00c03906050707800090100034000c10708411840c8800710310304080d4102c0011500b01000c0060280c8170182c0001c41a542901d036a4440700050818030400c0300701d00d4450181d170000200010501c02104054070400c2c001e1a00d501620b000c81c520943d0302c0e90b8804d0362040010051010240741000d040c0916800501400040703034008500241c0304944c0e204a44100100b140403800c2e2072014000c1903140080d20021108021803404d40c0c0360250740da01c04200b401d0410200103011000c000040700e82c003160913880b2780f003903459a901c58480e09140e086400b61501603031809456900360300e8103000d40c5001d1501038540c14030340341961302d4000040120410a07104e0000c0090001015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 91975225 1250 91973975 91973983
    0x7050f0a0b180d1217090d0c020402070602030a02040f0902090108010501080a02070c080102030a0e0f060606210103030e0f09060d140c1302030103110307030818131506081003080f0c0f 81
    0x5548500b4042200840113400500745040707100041341300c050038070300b0010601000501550380326100d003007008224036640300003000703031044041c02007082c1d0012040c42074400321500a002500c890041c4002d00b00d4039400204100c4c01401e0805000030003500c0104101e500603462a0740210070b028001d881d100807601d44c55000803050b8001e4a02d82c0d8000100502050140315410258000c0c50103001e041d103441d120103640340009000c1601c90f000020341c0320080814100360414070302351000228000d613035174100030f4004580a00b03042d0207003002801088107032900101080c0308002c0180165070b03204607034a4a20807010340c605070404034815941c890140340e55944800d42010755100d00941e4942c1985040c00ca40e8001c2c9a01d5402a80b0208007407002901460503913504040151070b142d1150401400a001d83c038000d402d40c000513240c10f4003046d00e0079a142d8074009464180d1070f81c0304c494640c580c1d07183c3d0014803440041c00049007070299444c00f501e084001c1c0039070fa82c1c0c002101c1081034026403007818 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 91976475 1250 91975225 91975249
    0x603050109121b03020703080f0405030d113702030c2d0411070b040606051201020703080106020c1503060a0e1006020601060c0c0611070f06030e07050f0a0b18 70
    0x700240c0c140c40200d459215070b00e8200380032551401090721485584c06542c0e50b03450b000c000c01c4440081051107514000d002076600518000342210ba0a500081001e00100c1000d6600c0e03d0318010480707513280d0042c0075010300042000101c5400c44c0000016000c03ca03001c80c0c42d4089a03d40103203000c40219546240c008084003580301d519075004020440b1060303404040e15038450080b1f0504c0003400400c00c052050719941500b20300070070030790303642e42c9451b000904031500400d610645105105000b8001540949403940c440d440354400c5980300d400c140e03920b40001c0325069003c220030500e0324258119602460f00504060040050389484001d11030002804032000b5240c48204141009580e50401441b030040c00b40381020002059540c8a0140b8035807140107120038030840120200102d842000360800601c507900f902164140c46900040144c4008000f1070894480c00601090a01c0c000b6002e141002004220306111841c2036845491a005030100b0300310800301e15408005600c0c0c040a280c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 91977725 1250 91976475 91976483
    0x60501080d180311060d09170c0105131205070507080601030615140f06091804080a09170a0b0c0c0304030305090a090203040c09020d0f0e150606031b030601030603050109 75
    0x10150281ca500500e41203280d100e4980000e40b0780c0007003011642c0325075140490310b01500e81c00c0d0f8810318400310001521120394001c111201c42c0383c1c009200300c18800580f0105081000901090b20345a00301d4440c1c0c80bc0440141c916980b44025003040c81c010740050024922030030076948810ba44596090424400341e00030b5803100c0d15000390607641c0c2d01149254002c1c040043d82c001a400b1000007240c5540004043d0038002c1000003440400d42d0340300260300042d5441a52013103090310b401d180ca131405420000031500444d80204010a10038041020040702c80440c20050480b074003da00d441800c1d51005d008a500070804110031190104280010406140251292980e414501003880a1600070740c0c044258203106006010000e00b0381d14664003200d0301c100016032680fa040100c0401450008086480189081c0c1944070000020658038880d01040340c940c111581c1d1001800820301c400c035041410210344140500c143c1c0f0301c0714095500040c0601d40020b9a40d2651f50310307401c6411002042e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 91978975 1250 91977725 91977733
    0xf1504030203010e1c140c0a0c09110c1203151302070302070902091e0109050613090b010206040b040605041a0906090d020102130302010806040f06060801080606040204031a0603070306050108 84
    0x200641c207090113003856105444006082000030300403803884541e2050018020003000c62001c3d40116101e41c16601102040d0040c0e65803e4640d20345442808150b1049514480c205641e0101d041da100702500d03042c10541001d084040f02d01c4020300000d603c000c20403170f44144048000703a402d486803c0c026600790b9a400d40143e4500d40c40c180a07143c804a903100b01d000d540104490030031912025210421000ca107107190440e618050010b03100307017806800c400c4e000000440c0251610100a41c00402c6030b441c240c08010b860b2050004a80700e10044401500c0308030781002280001d0300c10ba20050380180034101403070714a02c2a05039a001280140c42c400c20950060041c0188503105200c081c500740d1450008501e40301130005071035a4071020b88000f9060000000004040351940d40146641e4100b030b1101304000c2e03807034150280202c1c0081c094500a44542c40008855040a20848013926044000c0c010382c80b507003440c604d10300100200080c2c0c050007110000070000c2c1ca103000e814081c2448001070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 91980225 1250 91978975 91978979
    0x80f03040b0901050f06010507081c020d060303080108010c0801050d031e03020703260a0b03010e010908070302060c0c03090d0201021c020120030f0a0507050f0a1d06070b070e0f1504 80
    0x89400d503130000d44600d260542c49002c0c0310460780c0100440d4000c0c0c2d0304c4541e80e6118481401e071407551020740785074401d00b00d000140812040040364000c2080e203109445045c4540d03200e80c402e03801c980e1b41e000e2020100b003001006105510b070110741345503c28032901d009007429a4200721050160416016440402d4020071100d0406800c030b90b4aa43d07210000610410041900e1003600c81114082c0c80c41281d107551707101044841e1001c3d04444024400740c0024401e100701c61410042560240d20154014000c5801042680243d0400c99a005150340021414a030960b800c0204070505010304134150b100c2c50704d40c400100002c030482c0c0146802038000003250034481d2410301c0030b00308680c05044180000c00810030407170109008242c00490204002640b0fa4800806a605201e50060380700300c01c0c2c0110398460b0403503203e560031a00c1001e5142001804140c0030a010850052040081442c07900c240001c0c419071158401c4000300710b0048c00c1149000700f80c40803d011b8481c900c03606025103c00101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 91981475 1250 91980225 91980241
    0x40b0d050601021902040c0216030f110907020a022205040501061404020901080109051b03010e0a060b0406080402190512030306040c08090a11012607021005011a07080f03040b 77
    0x3060350220080c0050300603408455a070036a080c0c1d040000a20807076139624040d1a1307a200b0804001c0c40b03c040302007207460f41e4a03800c00e140d2010501c0c0c0110f40c1101c000d0714503c3c0da800e0819440f40144003c1e0028407000d40103508004040082205803c040ca40149460595048074020039004500070000002da040c00c00d107480c943c04d0408640107002e10f00400903000c0a90303101044904440160000041031380758420818600c1c159000d000d40041000b100101d130403068a84602d0141d0003c2c90300308102c50356035101030076038000c40c884e41000c00d80440000d000350401d425003115030640d03060700b0001d40da142d8000454085c2d1070010030805600101c20015113041034030034128003c801d400e11b0042c900e0983e041590740d0002d00401490b14054400c1d0f9459640a050441445035103880b0010364024082409900742031b0480d50382006101d182032060011840d40318503410b0328580f04100c1026580310200b04113680c06954110b405010400c858550240004040c600543c1b18454184070303401c0c007100d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 91982725 1250 91981475 91981481
    0x405010614071b05060712020105090a170d200d06050a03172203061e061a0c0c0a08010204032a140609031605031203060303030403050708040b040b0d 66
    0x99014422035a140611400d10301d0292615a60b222614500c001440003080c0c80080352580103d401200c04285007042160102650000900940c000c02c60f5a8486a0083da11900703400d000e040e00d00d42900307050f0805100e80c000c000350741c1d5460011a0021404540f01407001d1514040b500c2c8200204505c0d02d4000940038000003010200c4d034001015045403038200440c1c1c4250180c400d240000240407008401c114a03c25100824002201d01180e49052400181002c131020650060701c8a180008440c2c19103c0c40c800d455220000490004c110701209181d603115101c565114410107030140a1a618481c00c0350141c10b001001585641c51482c001441d12125145c1106603020010038130b54140104002d242124624008241480800000304070548240121290540251240c41e012a9003ca910300c04542068049905914034003441c0300140c041920a5903142e0810408200801d01c1003004d0011f0b54000d6508502d0a580e40540d00d84507406548040f12105001c28030b4006411184 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 91983975 1250 91982725 91982729
    0x7030c050702030304050d0f1406040b0c0c0a03030c0e1315060f020d0309081b010509060601030207020f0f0301060e16021501120b191805010c020c060409270f02040501 74
    0x420100c1c14015907038006900e901550080c00e006e82401e5140c103081c883c140e8200e0199a42111410702c100c4d18400300e05e61100c0c400c543c1910550040404501d4503903c5600b250f5030040c0c0034010301140020303903800701c01800362003400d00100304000c0c0303114487d55615903284284030180480050428907040695001d1911948a00c1c24844914000e000c49500403460400c064030703e14001450007042d1511040c10302480b0024120071000c043c0c5103068000561001e80148204012961150b41d0500110141d101d00c00c40250081c2910103001450b081c00d16580600c00700040011442c0c030f441d40c1d10310043c66801c880664000313089000e15448079406005000c20090305080c19106581403803194603900141c040b0080040e0503800010b41c5502e01d0038200d000c1c50203009014045160303c0a807441700c1805106060b1195485c0100c584900c5000052000c410440070307101c030382424501048a8001c0c010000840d52502c0342c10f0146a0a0080c49240c0180c11300c1481150b11080032030040c8811242c0503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 91985225 1250 91983975 91983977
    0xf0603060c0f20010f0218031627020d0e06010f0807061403100801061d060603010f0e070c0203070303050a022116050a06140912031b0d1e0507030c 65
    0x44000c240784103500224038481d959003548154114811411200e0041010551130b035517086c07011030782103003000104800c003180c4142242102c40e440880807400030040b84d82c1c816080b00d190300841d16444612030b50b0b44801000c0d0180401030400a0456100c2c003600d01e08282210070381c1005006100321b00e20300e000d5501900108004382030640c01c00d103019001c034180500910302c00e240400088c09014080c281c2c4005880004001d00946a40e110f0654417a03014600b2050000350050004c0c550307081c40000c2d81d04840b141d048000110345040350301410711001503c54003c2140b40403000001d61410081100203600c255249aa900e43c0c0e403c0082c1402c214019660241403280c1e54000e0298544041ea10fa0b4080ca040d2280c24008a14105103000262080108171504000c1902d41d10610040f4262240b03d40100f5a841d1542d11003031100944000c07584002c40d9a0029502c41c0d014981c40c0c083c1004480ba00341c00078040b26480080c2e0300e070051554000b0b00071516030080009660789806400c03001c61003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 91986475 1250 91985225 91985237
    0x1003031d090a0b061c0b040e01090506040611040b0a05030103060b041a061309290607050a030516021206041b030c1e0510031401300212010f0603060c 66
    0x80390000036005900603060070b01c866101c40040c403065440c20201c03852000061585510102d80b042d10102804802d08154840d03403034030845404281041c0100c000f5141e1100291059641d16904c0c1401085408400c000702c2d0001c5c800030030152031074401401c1160140e150f280d1250724500c1c2c008280d070382189503540900d041101e40f82860080200050014108440e819212105000680404041a40801d440a08050b061010040e006802c11241c00013a04166400048002844400c1c811140014000c0d0310079462100030920076009440c1c4106250991400c0c86039580020f400528510b5110071035401150a02003006415205190601c00c401045810300e49182c90b81031000c402c510643c01508030a60a106446010040b94000b03003c00030103510a10490880081c000c0c02c0b0052800408207460340080f4007015580c01074080c00c4107003400c0c43e011001c0440c0c0b01c180801003c4080b0781143c4010804240308400b1701900010f00d02c8450002050340c51801c213038080c2c94542c0c0301c0e4000d200c070f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 91987725 1250 91986475 91986527
    0x70e090714092806030b011502010c080117100501030b070806090c09060702040608060408070b0106050301180b150f1c05010b03040f050a02060a0f08060103050121050312100303 78
    0x11810304056000070140c40c00c42504a0000c640c29045a11160543c00a440c02501104020750a140503059601e015440d844030f1000d813074107a080320031040d0010040741541c00104681000c0441808001c00840151141281002c5107003064800a80003140c42100c0c1e0002c200c800e95105080c40c1d0b00800c00c0351043c003607081c2000e1035000e42c451541114010100020340c072056490716000803000385900401c40e8030700c0c54542040f8280c4d4100714070880380381543c7c2e000003484074400c50941e130694aa00d207880c0280c0360010300380e070300400c601d8100c141c028000212005514541c003018000002c0001a01d980e1501144207413404401c648800e50350881c50000140a00c10030700c015240e029030300c48000700e1124100d0070035611786401c1080003940603c0c00a0000250f0354420344010554031a51a400030f02d4a5540043d801d0b1842401003600d010401c40010007200c181c0d80183c0085801041940e103007860050080354007603001c8404503914030205200b0020107504c190040c44590741000d11115002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 91988975 1250 91987725 91987729
    0x160c02032a100e0402070201090f0b03040b090105060a0b09040f060b030109110712140708070807020a050306070c06020f09030a0507031a07080406090204020c06150406080d0203040b0a11070e090714 87
    0x83c1012100e03c0c05580e0100d025011a402507944d04081d0030b01001c0c400320070b607a900c00320700e455104982c00c5504019090106010050500400d4010350700289455441801c044a40c2000c0d000440c400340e000d070700c0d16030303820120b03c8501c90880509480c091250307980d0b0400c84510150307044d00003100c4814404002460104411480400101c0594170b03052006015644001e0958081d10101030080315001400008001d10100202040d620950b10502081da544042549a031411513030b0001044001e800600000c1c03941e4000d1004111281045081110325000329282c46c101c01000c4405900c5480c0c28018010b4840060300659100c16810b00d8a15000800520202c4098801000903894841100031076840740c056919640c030043c1100d00ca03140207a600451134604550782c500540c6404004540c14901168150711082650025480c01d468500e800f10745511541c0c1d000200604d40402e0102a18240008001006030601359883ca007401c4014506242d5558003c103120b01008244800a0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 91990225 1250 91988975 91988987
    0x152d060109270b2206060305250f0315030b01050a090525121e0b03060108030906280f0318020a090203060310110a030e01050c03160c02032a10 63
    0x900c036100200d0f0561081001c030b84140801c240c003e010130543c0118480300c080c1540014221070141d5014040d54850100b00c0050514015546101a034201031005030f05025000c81030400740c4500d40000c04040c1a8041e515800e003039041218418402c0004010b070f032a001d04944090300c1003080821003420480d400780c1344401070301400364185130070700c000e2050507004811184810a0a0800f0720240095010030800c00070180041d22201f4075000244001c0c0c2030029610b030503501c00b2002503203800311140400c030980d04034000d6102031040c824410711400000c00d107240e41c00e0a042e110700802c51102500502603e9003402811007107401140b8000240e50b480103140d0407510f000d200107907a41c6030700d008a410920035080c0d051070311381080210008900c180c070080c441c0c0c08440d90100039540b020100b16087c0e44040e10700032140d910900118000301c1d0085c9490301902880c1c10461810b1416501183c00d0994821315a881c0080e4140220340d40c01e290038060a2041046801011881e00c079500a085 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 91991475 1250 91990225 91990289
    0x609070807050d06140a050612010501050108010909020f03030703031b02060702030a08150d030e041a130507050c060901060e090a0b0106050a03020912011b0809152d060109 76
    0x498010f003203040061241030342c0464140c0010780003109052174103200c0c03040580b07801d480da140a4144664100200740c0c041c4101030584505039140800c070307440d00658501900d031b01c410036a802144a4500c1a2071355041000305411803180d00c001c40c010010880365009032494910721700554000f0000c02c1032056000c01210307000003181c2080f0046441d40304041494043c42c0e4040e0760840c045050810074160003484903100600110b0701800505201545929000750034140242c008203516080c00e02c0c82400c2d08042d0303200c0300d10f190107402c14140d400305d2450258161802e11f010795440d803060103c4072000344400e034018061780060208034403541e240c0103144c030f05200c0e01c410000082018020b291180d01182c44407080104410040022980054001e1003451b04000c3d105000c881ca00040e213001e607161070f00c0350001001070042010003422445080a0080003d00c2203001440014100703001c40c0a802c007404000300c1840e22514000340050700304c4c402078002d010512401d01c280c000e030b030240086d0006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 91992725 1250 91991475 91991479
    0x100509120306040504061803080f01091503060903050c151f03050d03091b0806180f030415090b07050604020a0501030e030d1a060a0210051506030103020405280e060907080705 77
    0x3419641701d0516500030000e07040400e98404032041400241355114034101d016036126001c60600ba6624018a000c83d9034a11172044407038421002000801c400c1da0003c0e450301d0190810a1a01c2c265041460600540714200c0d1004402c590030b114125440c420100e54005001003c083c00a00395220640c1d2003200d0f100c444101500e411480042103400140c455a020f01000450103180d01d0311a5035444650031600302003894180a40c2d036510480c0083d40d0799010450102031468517043c28403501444817002d142c1c1d0141304240c030000070101d15190092800034002c1c0060680d07400c0900c104481620294091410036043c924001941e0340b0110071119040c040c074500060714040080342404855403001c6141c2c1c00712011a03618140c03500030500b109007a226030000c0000b6541e02da03e00700c814006800d0a50080804e0005200500340b5600c2030b900f10039100318000003101c0384801d42d019840c1038000c19000580b600301c403070800f031401c1021175003000c4154040d050b030701d050401e045c0e5036080d28407802e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 91993975 1250 91992725 91992731
    0x20703050301140f12010902122b02010612030e03010e060105010813050c0907020d08010e090a060e0a0c090c0905060309030a08061203070614010e04120e060c01090510050912030604 80
    0xc8450364559481130444032000d40112021101ea08905000740031035070059010305112041104640000f04003440001940c4508066511a17201800c0d0141134101411055640e180c2d00400e0007944180242c0c11203221f40c2c0e65003082d45a820a06080d22841d01c00081503510420040c80141c0c2c11030780d115841100ca108910041d1481c0c200340341380111081400e41c111100c4018089003da0101d14015130003820344901c0c3c410f903660880c01d00220005c582400c02e076088201c0c101c00190302c4e504084101c01441003144c025800f203860301c0030b80507040c0d0f01004c2541e598200415409400103440270041004403031403411464400f9120351644140880380301000000000a980c2c0d0341c41034000d4450b03140c5813080b40d48440f11450004001c12000101585c042e1140d4000544001c90800340c5216030360000d0f406a00c3e99165a05403113501038a41c920754050414440040281070903c141800e0500680003400c620048044100880d04050b00c05400c0ba000faa0300b03010501e992004898003c03005543c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 91995225 1250 91993975 91994009
    0x1120b03030d05040b06150f07290a0c02010506040c09030605070c0f050303010501030b04050402061605070815010e071103030c030c07020901080a020108061002120904110c03070c050103020703050301 88
    0x3038114801c0601c0000e03001c1c98030050105026222902c2c0744548030603074030060042c40d03181c41441240a049a1136010314030030401c60000a00e1194403007280728500e04150310241410b10504580041180c1c002181130707031103040020700f517824041c040d04901e05035400c0140c040e907648010102140c500014010380d481c0c20202e20307983c2c862141c030348940740c0065071b5000b80c28891502d141c0700d50007803140d140000c0c00d01d0241d14640c60140704442c000c6900504407031601d8103400815842c2034039003000f41c42600504c1c00004501e4414011000c1046000703244038480d41c140f0384e042d01507900152010003007141c0c580346186004d10000450f40c112015144050300e07551a0945081c0310300c15810025007080340400009074244000401c000014400d0b2544000c1d9900c000500060001c00c0562000603841126a00002c020510003800160340c084d00220b00301c980003408000343e6003d10220b0155502c000760040901003505448800b40400346401d40c90064a510000c050340018040d110303c0c440d106040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 91996475 1250 91995225 91995229
    0xa08030415050c0703030f0606080a05090f030c0a03140c061b090a0306060305010c110d120f0504050a0219060203040e071209060203100512190309030c270b01120b 72
    0x110700c0c070711601001400140792440c181102500148021008682407000c2c100a1110501440094a034141e990341182d40d05d070036994001d024050010320781c03406407402245100c0014001086032040f824005c050300c00c0c007445d00500050b80007060780340c1a0414090381d50384003008106144c00502e905c1c012845c0580f0034215114038425524a2940800300d200f0001c03c200c020313000707001101d01a03c003c0114254840741520742505081014030035401c10100703042c1c583d008012011550180c00780004a000000700703c86d046803c15207060358140e00c10300d0404110700c3c000d0410070354451130740c0c115880d103490f0182c06580d900a5001741c02d0100d0b00c0c440000d40d1148110008a40080c0d018800e0049400381d06040000303520a44225007100c1c5180d4010480d410015841c11003140d07141d0080002c2200400c11141c886c00c9182c0440c100b01c180701d8004003240600303401c90003901e4243c50103403600034010611428618924801140300e402c0c8001180f1b140c0c1c200c018044205001c03407001c40c0d21607032440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91997725 1250 91996475 91996493
    0x120a080702121c09140303070f06050702010b12030c190507051c06020a09081c0210050a06080a0b01060e010c1124040e0a061e090906020906040b0306010216080a080304 74
    0x140c090f008840035074007042c01c1a8094a801c00329060170840b81105100c0310141910f80c4034140d005003000300c01d000d00e8400a20640e001d242c0c020018400050101e0301040095008045407800501d103500c00304184034000d4050203042d102c41c51141415540130020350700c854407902c0034031445208075010030901e00c420a26816081c0038540c00841150354480814001e404080c0354003546c00c40d4070441700d4940d4510013559610722008050b030000e00590344540b41e26800352200030094030203192950070000e44101e08010b80c0d00110b1281b4100e020303660420200400e01380740101020f041090584012000c610340c540c3c0c05903948000c0d070f4603141d076900041e40951405c0c1042c0c0300502e11400058001914604051401e00032111030106000c91035840003034180400003450004030105e4030780760410500c100b59010003140c9214400c05801d11004900041160704a50b003c00911038002040104540e414020710601140340c042c1050811b00f40b2104030340d01c039400718000b0300c0200300202103014041c10a07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 91998975 1250 91997725 91997743
    0xc03040218070c0506010f050105071e02030d05121302090f04030e090a0903080109050103052d0303010f03060b0d0320010b0406140907020d02030702060702010e0a0e06120a08070212 80
    0x1980e00c035020b0512040c02488155031010944041c050000040741c109107040601003144c3c4165141403e0170180c0e01d8107030000e01080700d8070310f4442104281d040161810b011909500d01c00d51036980c0c030303021220102440070500820010135201840e95420043e5103020700c068103d0281c003d004402c1c1d4440c0f5003616110100f081c040e5101d9092010420b1200d8190003062209203c1e603122100c64b40e172f0700103c40c00e44000303020050441e000855007440b00021072450342003172440021209549002520068115402a04200444640d640d0184144407003030281c80c94180064810081400f042e480041c03030012440c0011908181c51001e91035158803d401c031940031a402041000030503514000348031202d2140e04102e0250383c682d0005030107540040b07814541005242c000e140303000696401c1240c6603001040407410300c80c1161006125440e58806d10014145044484100b0700b003a1040000f02000020601c1c80c99100c0c01c0080300060030141511007440e81994103004031902003c189040007039032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 92000225 1250 91998975 91999009
    0x30c1502060136090605091b0a1418090601050405160e0f06040305100f1103070221270f0402040303090b09040605090c07110103091110140c0f060a050106080c030402 73
    0xa1944d605200140d80104e005090384c0c0d04aa000d0800002c40859130700b03075841078652242c02d1510400401e0001481c250b0740c00b000501c8803001c852041c1001a007000c0649075000541e0001d00180410305040c4101504a81d0200b1050034481510134020210784821024a00400e103000c2004e85544840098030301441d801820f855147c4000030f81040202403508241c1c0c4450f00703005c1c160444c0c280100841307002e8001c075809003513010304034030345040d11510540701c18804400c00c00030520728050080700c08442c2c03007040c41d082d074400c14036804004210404121540c0715500c10482000000c0d04070202d442140c0b6441040c41d25000003600040c020001507002c1500001040108a41c010580e00180b00d442d1060241d03144050106004404a50613560000c0660200c01945012071a03e0300c0d0210f007424161030302c495146403d440071080c41c0c200c8102c059041d40070790311a80118005010791580905240030400c0ba56240c000001c010700b1014161543e200e4000000c1015500d51442c1011100c1103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 92001475 1250 92000225 92000231
    0x2030d0e01020304120c021f050706052401020102040b0924070308040c0e0f04020111010905011d10020a050403080c03040f0f051305060f040e0f07030c1502060136 72
    0xa1016050103035004540403561242e05d01c0e50310030b81707502441480e003a981d006026052240603415603103039220700c04007041c420b00005128003030000f122070003440e1107a0342104035105134071404400501d030f0304124440181503900510040c041c2c8007007842516600042114a0741c8e410002c102c182075182907444a05001c0c00d80000d01c0e4045c5900401020301032441001c5008041d51341c1d500000703040d03e080c0c0d0003a144840003c00701d0090340c03040c40c100725060103041c0000360340d12050343d840b07084030680d40c00c111600c038040c0d1032440c0349c81040c0014549803007121800e620744181c2800c010070764400d074000202014030210700c80c0e0a410040060390080d280d0707103d41040b596183d00740050705a10f10701c035032840b990510154541c400c001d401854000d05000e0280f624060340082007001502c000c0001d9001da1185100c0c1c041120010010781000394059200d4903030603130804003004004104505603d083d9408140108985039403d02d0700c04814080200307200040082441000f4020704011319410b4440c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 92002725 1250 92001475 92001491
    0x112020403030816020a080409020f0c0a0308060f06070507030210021e060610020c0d030e03010f05041a01080f0c09040303020d05070e03010605041e050c071211010b0d02061902030d 80
    0x1030030500481c044d65402d0649030140340a5039040f40d440000140081c000c410038041002040700c19005400700c100f840b25401e040000d241081481c0041034072044d4000750160050081e41d0400c0a0302080b078450555109207000195100c50341e0f26041440000d01034400d4940c546800ca00c00e00c0608444024501e0b0304100700b6400042c16a518007e07101c580c4506540c4c4040c413200c0d400042e0b84038034080040d0001003840d041c0d48098900400341d008141d00b40d501d4a142901d18000c6100f0a403045105070030714103441c10842d00070803542005801604440d48620840d030b070019400282c159044100700c45441740380c0d45501d0104c3c003034000e50140042640c141401d0206058001a0301c0d0040203041c4d0003004115034600410083d1050030090b05102c442c1c40f0740440040c011608140e0380140785064091410380c20343e17201d00382c84c0100a0890005102243d0034240e0330001c2c09490080c000c110b0b2a2102410982c0024007588540850503c070280c3c48020301c01310600a005444000f8082e4504209002c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 92003975 1250 92002725 92002727
    0x6060714070f03380a0e01090302061e040c18091406061315060e193b1321020d1404030804030308130204050a060504050a1118011202040303 62
    0x905020880c1e5156034203119244041c560900d1048207000c4180768060041007094071a0115130162030407000d1502d42d5036415220409000d032100b194440da00500d039070b1911034210383c0014004800705214010703410512001c240004241c0c01600c0310090800780000d00500510010242c00e04001d00303010000258020815011468620030070055440c3d8040751450325262085500520521100d100038000070302c40207200b568214001c40000d0b00220f2808000428242201110340c06628040c290a0f41925a4043c400211300c412040c21080b40d2030041203298002211401862110803028105245092221a0004601c1c03200d08522000000b070100390000d4540414008030004120442d03841508042c4010403075045a03000720786207082c241161340454000344081c006025081d440c040000259070780b03200349405052015030014140b803a25040c00141c400003010311006620300780c070380308150b060301080f035003110000d41c51402c000d0b0500005032a005100c801c401c407090700c003180110802d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 92005225 1250 92003975 92003999
    0x70506160c030809040e0601081905120d05060a0911040303030b06070b0702030a020f070e0a0507120e0c04050c090d02090603030d090812100b0d0c050c0f0105010303081503060606071407 82
    0x104015102448221100280700e507480c07d00f1721402807a58131503c602001c0311148110350300386500c1401502c103440403201400c10250020700c900c4140e1650303941840701520340440ca03100140986802070004001590622660b40120300c005801d00d03440e00d0002d5090b50f5107a00700d41700c5581c4000001e00a082c0018000c1d540c0d0406007451016100e001c05840380c2440c002021301c21182a01344102c0c40e9500c18007454003800d0027802d0f4005100c1c41c03012040c1030040c9801000d10b00d008102c001c1c41c5000e008020403080c0c2d4001790070354140e604204450041034883c0c0e41d40b041841e4041d100442d25440d008013081c6588110800c4504107072402c45040e040112800003070000d2102400000790702c0c0c8803000a59200d5502e4071866038014802c1140388001a1143c00004007551075080290903c1c14134080f950800c1d03a09244400e15035502c1d0010310406030800f59240d0002d0100508041c0c607041c0c440840d0742d50001501c0c1030b00c1000c012440b24108501300700400c00740100c41081c3c54039299102c02c0a801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 92006475 1250 92005225 92005237
    0x30a060b07150b04020f040302060d02071205091009080607180b040b07050606040c020303220804060302270f01180b120a050703140a09020a0306060602030414060903070506160c0308 80
    0x742403c0c0000c0042c1c030300d400e000740c518450504c01114905407840d403c1007003e074056108050500d409020000204001802c501350300401da4840b10381e02c803010f90402181070742400d0160306000c040d4000780402c0c0320015402e5801103960420040b003000c00c58504205508640c880080300c040001e000c14207010a1001d400580d1181c4201c1e00c558407240c080200741d50712503020500503401440020f0368560300a0711070080d60034440d07008440100c2da842e550100e034080d40201700802d80000b8003841d5580c01c20f400000001c03014035105042c58a9100180c0c640c44411645410040314403204040648800e0303e0320000d11000c601d00e03a50711118000119034000c120742c201c501d14074110004e10b64501034010607a00c130f815418903024987d1424159070050400c180243c0e00502044c0011000444034482e140290a6036001107031034514140c40101400c0c403007034845000b804d081c000c039011a10005020001e88400300d4403107440713028107079801824280c8844081e0942841030800000e2085240c01849 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 92007725 1250 92006475 92006513
    0x140a0c080a230a02060408030c0405030613030e010f020c01030c09090501120201080108030909040b0405010f1d07050616060b1f030f0f0203040507051e03100515030f0304050402030a060b07 83
    0xd03032119560b0b4504540038030820400907820000000e000a0500780046038845641c040310f60820340c440000c40c6c64120119007421100080a040342c05141c0c000c0c010380101402441c200300d4004a4450003500c810150121070b0500d502c6003002d800d0113001b01000405070005e00070401c07040da0355000d01483e06003003d6080c0e01040d107070400420400030210072a8100078000d41000011f864555801688000050003525103560f960170003c4100c643d80a50114081034081c1c4111b030141c10210941050b0888c2d00880c41501c1c1003000080284e002e540b287c000c00d0f0010303400a080071007070b8041800302c0c201c05129200c0554100786c040c2c070b058060303000d020b01d41c032160020005480c3c410251400ca03c810b88015001d540b14031001c101614103142c04224103028100004002d14860021a10703007801c0e0720b101101b06483ea020400f00e100408400c59a10720b04400074002c02c51100c0d01c6507240c0c401e50068501440d000000a00440802e4020200500c05840169075403905405c194243c0e01c45483c5002c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 92008975 1250 92007725 92007767
    0x91e0c030a2016031106180606060702011e030902130515060711040902040b041d010506040b1c020a0e0a02030a060506040b0a05130b0304230607140a0c080a 69
    0x40c0740344080c03803041a840c012030030b003452400c070300780c0000500403006020807410051102c481c0c850812060106d14002c2180302050a59602584c240908045000f00f0030b81c0110310600205026030b901c200d29013150300c2c90b010158455001c407074044020b00450140a0b40202902c44000c56060255002d9446200c4034260184a40441d4040044500c0307a54405030006c0754996a09005152036407040f0304e80740c4020800a2160303241c41c0440c00390f82901800c40c0d0041c14500040c51000801c6c0145940044216003c000c20800c220009d0706850320900304460324005201d10508644a0030f41480103800c090480880340c2c0340803204180603506c00c0700d417092614140782000070b150410301c0940d41a58882c1600c28104029540100c456401c6840c0241d42a40e500c20b000072a560744c64021401503001f0481001c2c20030240440a040010000c80079101e07522403002c0223070103540300b0710b8151441c000c1002c10f555420400b000300c1e542c1e001e04802504100000510301d41068015016800200c0109240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 92010225 1250 92008975 92008991
    0xb030a0f05070818010f0e0109050105060a06050f03070c050a211e050a050f040602010905120c0703080901030e160807080703050705010804020a0e0703091401051302091e0c030a 78
    0x1041034560540790032010440e490003042034040048004010090210000110700c800d100600059407440c10700b47c503da0f551050800240302c005e00400354000800d80c0d0760583d9514040f4010001e101c0c00e10010002c42d80032010940c40d92152a00f400100d4202c0200c41210300b050070066038903203d040a5000301c2c0c0c8800514070388203001e0580c884200040f107051003c1010812020fa60703540c04182d4007820004200003400c00c150601002e0005000103a00026404490303290070391a2000a0281e08507205007802450b51360000020070100b07490340070f00c04980780c00401b0010382c0a040301c0704085409000303080e6401d1040001840d01021a07880c6030440d1083da5036182030545a41a9001c05001da0b00514424442d550086040075082807004e4a14088140c4c1c0d44c10210105405840003c002526a1104801d115580d0000b0440718a80b600802c082d051042000b811000364200c024040c21400d00000d104840c1c0c01107594040c509001e118002c6e1900380112102c1e9401290032000d150310b44004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 92011475 1250 92010225 92010251
    0x5030d140a0b030d1214040609111c0201050f0702060304060c1b0201090e06120a03050a0807090509040201030b01030b04020d060504110a3e06070e091b030c040503070b030a 76
    0x1540b5180311000c2c003d420020320071801100d110070b080a41e01da80d59201c43d5860300014001b03512511550040000050484981c581080001807109034184104000408007140407159070101c002d9a60909241740d5414490503042d800307005090010394001e101004010600c0102d402581d0220000e0f40e1b45044400001d51030240383c841d90074080c0c00502090f0091010b5000c643c0a2500a003000300034803010024022010300c1c010b10000b007100081c201003000e4030b000e034110b110079401900700e04040655505100109562540050001e07040603101c0e240360b1000c0e4025807044040700b0000e007040d90b032407420340d9044000c2c000c144507613030059141001703607891914035400707a80c0700070402e9482d0762813910b100203200c1c49881201c103070502c80722181910811444440e02c1801504e0701074406065a45028800940700c0081c8000e80d42c01400c541003000a120700000e01c882c43d010f5156082d036203c0c0c039410b0341c0600d1741c00703950030298151154450105821200c540510310401102006004c3c103264104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 92012725 1250 92011475 92011481
    0x1d09010b070209062e0906020a12030f090203010c09030b0c03160804050f01050429070207090f020c030406030213080a0210030b1201140702010c0302041202150705030d140a 76
    0x108064032524248100300041c60240310558002030010a6401c03505020b6801131810502d001e2582030b05800e00c900340e2503842d00003088030028611030001e40091403094540c05810b006040720ba10805550b0382e145162040b56070b1016040c10b80150003005142141301014114030b00c1800b00f5214800d80400207001c801150013142d01c01d5000076003112a0200418044e141c5041c0640300b1610f5010314140f000a031002445580c0c4124081c034404138460100001d0b200020700200c0500b0103210000d420019801c1c1c000800108807040c0180000b007885807030700f0701d030004d0085481d128910700000400060248d415000340c0486c4060841e24840c1030383da08503950b590050410029040b144014a560a250080e8014403075100050f0810001224155045003102d4040300c0c4503d00d0546801440a100d0342442040c54641c11403c046180a00b84094941d06160322040248141250300c807a803142e02001c030548560070303889000c41c0d4a03920500c070082c0107400304041c6030494070b030610002488050640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 92013975 1250 92012725 92012729
    0xa1e020c1e07050f0a031406040b090102070525240e0109030f02060901091806080d0e01020c130204080d020616031a121c110d081e22031d0901 63
    0x700050444074a044144000700d20040740d0381c0d500580c2c3c00320000c003081407142c2030402140ca140140150385894075045030781031000380c80da09041e881803005200180001541600b0b0242d900001c044140d80300a040b0310b4100070b50041c003000824240c0c00030104002d1400d5494184454480c030034101006401180c80c11503500c40a414401140e07501d101504082d00200307000c10040c0f411021031030711350020181e100350041031001ca1598039102000700d80d81c00c0c0013011040c203c5150290610110800003503680c43c514203061301c100381c040d0030420361101c1d07a4110741c01040f50702c054600d4466101400707911030310103c03420003100d100210150748007807181c400d00090646900c816030780003102074240b083c1c0c03d50946c03240700c0910601d9104c0d00c00340d9200441000704641070356041c1e0616020480c1c1420131902c0c56004c000c0c040070f0003c0c8030304e600c2035140c458000400d54030407820395550402040000704507d078051f001030220b0030519040c107a01880c0d200c0058007070a0a10542044182803100d001030034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 92015225 1250 92013975 92014033
    0x6080d0804060b06071205030606090d030c02090606040b070803090f0610060905010810060c060e120405010318020d030c1b030b010501030e16050f0f0a0603060f140603060402030a1e020c 82
    0x58210044035009801442e002740e0003400d800c0c01c01c1d418001240c024100000b0981c0820500e2800c1d20841c41c00e0700c0256803100c1c2c00d480c41802c184c50404004030724012003400512101c404400205007000c2000307600400b440f942d023216294240b0b00110300e40c0f8400346c00703900b002864440e4049015400b0b04150380c0109007952039283c0040c90305a00301c854880c1c181040b01d01030b03101c1003080704000f42000300d1345920140035541545c0c1c0c0d00c1d02d0005030845902252030301035210742c010144096030b141d6481c0f03100d403909400e101c04070710514035050450209148480010703403403032800841404601406541a598282c8003085a03640c4611075583d00d01100700b2451060348148028056400c1002c070850343d250001d8843c00240072560300003103044406402010000342d44e0003040094000d4601040000c20440c2c1304210402d0b241c01c04141e65201c001d000c6405190004085102d4003003a51040d6101e120100121588184e00c01c84807010790300040c1d5442451050342c2c0000e05d060704010310510758040c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 92016475 1250 92015225 92015243
    0x402120105270411010c0210030507020705040b030709020a090e01060201060303032405060a050d0509060405070b0703020c010c0f0203060a050a0606110606210718060b040e13050106080d0804060b0607 88
    0xb6513035035044034062001d420341045010b105020068964401c03150003203900391000b091078600b4000003480c00240754411740c4118144141700341030380c40c04103808080e540200c1c00581d50349150320082c0e488031a9540700c070300508103000c000600142c0c103600042c1aa0700c00d0354240424810f0004100300410403481c94013000d2281c107020041841d10078000d044240a0307041941c10040d003120584200c0d08200d9a9042036004002000100f000502014001e0288409120b003000c11685000b50f43c4c91400c001070307060183d4540d4900070300040c101d00b56a03149c0d009080704c1040c40c0c0024a00c01401c8141c1e17144090b1810000007080c0e16002e01309111091030700301c0050030355603140c0041000c0c220b4800c101159151000c03100703101d595401e105550141489040b1400554a80400380044420301e500c0300d40100c2c8207100902c0322425101c6620742001c04800c4e8000d0002d1582811401422907a02c040610b00c200e0900700740c0345410103100d070320950003500200411300c0d2050520480f84030300e034801896010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 92017725 1250 92016475 92016481
    0x1e1603110108072a0506100308030a021c050108012009030a02040b0a031208090f07050109090f1e06050f0418081b16081b13020c010209040212010527 66
    0x112403941954000e8a601e0f11500f0007091142c90504c010285828640501c1c00b0001d01c410701c03008210f000d410103036110110743c05502d035403101d0160b800b010700b5130480980c0000b40a0103200b84c01140300c4000311006010031255a40c1e9001d02d0003880205800182c031106000301c80200c0c9110800e60382c00701b2019000e040350002e02d80c04c00006000038000325a00840c012000303c00b2940020100c15000215190a0181e043c030401c1c1c503141000741040c140281e80102e40902c481c0e640b0030854011039588460210b181c4180e0720201d0050b20004900030340c0d0703044044205440c030b074091704440c0c12200c0c19101c519500358180d0912050780c4403d5004101001d800c10640000382045000f8003000703d0b000551b50035000d02c0403e150400b00d0320540e4040c0f40b081e074a4284030420040c415031040c0101d0081a0140c3e0030450081090342054112000710158041800c01e50914290121850b0440081003196101c40008250180030420300405000b0b09000200604440a4400340041c1c000c0d02e14041c42c040c1e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 92018975 1250 92017725 92017727
    0x130e0a0b031b0d060e0102092b0b0606190306050406080622050a0b04030c11030109110907111e0721060b0112020c0d0206060105130e07020a051e16031101 68
    0x82c22107040707250003c034000082c0e80403802520403e007403032204400144c4d07074443c803904000251010142e90b00c10300782e242c60202d0050820034081d03a11540d21803203072025541e41100003209805210003814502c03090030b00d003007400c2e80d1540c020019202d0031107080041031f4032440c48682e01c1104586548c40d00000c148540c004405402c105007689204400319143d001196451800504040d03a0460200c1c602410350f03400c210810030040c001a101342c000300650060341d101c0d55446201ca150301c2d80203d40300d0340403031145481400d4411402035100101c4440018240302d0650040340200008100c1c011904003140d4010f501c0c4440d9101c05001c14a000e55003040c0e140d0000a020510740141444004000d805c00050580081c145801080001c2c001d000c01a40001c0d0500d0300040000d070401004220360200454040c2040d015198402c8950340c450b601c0c0070059141c03000c8100041d1462040350040c4a600300d820a1010100c0006000d507186c0c8071940303a00c441e5560341408001c2601c0c14900e0300000035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 92020225 1250 92018975 92019013
    0x4051905071a040312020706231b010b0301091109010602120f160204050c030604060806060102100504050c0303070b190915020d090b090123070903120903020402130e0a0b03 76
    0x2d1030300c1c0c106103041ea80350744010710780088007500c1c0b01603085880c0c100010364210340e19070340e0624448110480001106481140741c0704404a9a0703130b40b002044642c00105007507200d4403400e4800741c020400a0031a003442e848400c0c544080d688502030300c400200300144003082031203107103654428940c1819048907040d40ca40c1c0140709001c2d05179003003031600300240c0d8540c0211400340d02d1842c202980ca08044040c030003a44c0441c1c11214441c0d00c64000e000090364005200348921010a13800a01d030745541c9040350074140b4004000c0d5040c407011501d08281f26406000314010b10b290400340c400107071024442d1095403501c0902415903090581034905246031034004003120404a50000b0784034100da0344003040c030039064501010507036442e01d071110078210f20007803000c02c82407141442403d40b92400e801070961001c0d000c01481d460459040c1c6040e41d0082d5148005542d00420541d2103032141c81c0c2c00001c45149103e603854400d050030100c0d08030400c1e8890440303061400781c042d00425025105039505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 92021475 1250 92020225 92020259
    0x170705011401060801060e09061e0a030206040632070b07020c0306040501020a0e040b09011406041a250314030603070b18091f1401050910080405190507 67
    0x91552188000000855004101c0d4064809034951141550526800410102a6014190003565250700b0311503d0381e184144619008014216014074440350408581140300380d0340020340114000c070300400c406400462502e100000b240b00c0281a010761500c021103640183e50012049100b00080c10200d00bd00c811743e540b0600b10300464000f1965100400e1406000b12000e90302a58045485c110140d401003040303881c43c80c211014003900500c45c0019030080d04c10320603003001100b04009040700e13032104819a402801001c0c8081e14040b41302218800c160b00002d0201c203d12407240b0007241914010494850480e01556a650f07000310701121910541d03c0a00308640c135206501c0c0001e000824070f00203002800105d172904a076240c0700c03000d0109010014089900300400041c03030242c9602c0400049040300c40801304802442030000042c1c1c0d152007403183d965004250712004128064104a0050203607119004030355505000d0903800c03e5034501d20100514a40142c002000071001100c03151300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 92022725 1250 92021475 92021483
    0xe04030c060e0d08010e010602030c100e0106120c09050a060e070804061113030c050a050d0609080906071406090d0f0c02130c110607020c0a061211160b090a1707 71
    0xb441d1019101e0740385800c070305200f03090005021100602028103404103c60040105000560500044400c01070312034001000c4400741e00e9480740c40346d16040e0b00350402d1004102268042c4504035080c18003040140d042d010741d00072a410b010105031034280601c01d110854a50f200b044a46495681e004c41e0360810240040d41c10544605146822644000041013030341c15440307840300e5061451501007510a000c1d80110b00ca1040340c1c1c810006034841003030b408503c1d40d10640000c0c02803000d2038080d05a004946115802503c041528402c2040c011136020385034101c0d03800c0760740daa51455400740e03541210184480019140e0102c5414590080c00503100136031000f07020650501c0000020300813943c01c0007d0800040741d1100c0304000d4001407142c0c88c6c0042c81c1c0c1c405020321717140700d03030104a00f20003600c40d8508101e0010799901c00c00341182e01203071081198600c610356413040d02816441e220512181510010315140c080740c90014005007152a595000400350580c8084a5017410341da0032116003030b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 92023975 1250 92022725 92022731
    0x2071104050705090934050c031b010e0601032301090203150402120c06030f06010c02030d030218010c0b060d0515010f030b0109140a15170304030201180e04030c06 72
    0x10640d44500410b8441c250365900c00d51a0300d91141000305c10360300940440d10040ca2070300c22001d04200341100d00181d2143e40e29003000d0144607402141d00340b0401515260030b001c00300d060780b20040002d8551700000c0440d07009200740884803903040e8807403000f84070040001503441142c00f4000421b0040400c0c50082500000c0c1018060300842d0400420b0750003102c50321032660400045142c0150350b0321012200308020456284880c01041c128400604031941d2081c0c00400523013160310810982c03a191342d014095402071074103800b024000e074100c210101c04504a0003440c0005504c00e0700300080450f0080d004c20429160b050600003e0070083c2c0043d1064018000c140c0314260103503414038000c100c4029200f060620394104a0b000080c1038010301e02160070654040843c5620011854021080c040f00103000407040702000d008048a901240c140d4148150080301400080040c10469000ba01d0303170f000800194002428201850161150780c403d0341c40841d010910900e030300c23082248508400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 92025225 1250 92023975 92024003
    0x714010908011404050f190308060d080714060a0902060d050a150b070c06050f0306210a1a09010b01020d0806041503080c0d020c01090b160b01060c0c0e07120207 71
    0x106082d0b030300106801d4601a0f00809000c1002010042411407180c0040605008a0b0003031400e041d0390890f11001c1e0410124001007000d0340d4502102d00001c5074000c1c074059403000f1500d00480250500320321252030340036050000744009618050040c086070f00074400d614150400d0b00b68401000c002d80804c1900307586404001c102c16081c01003034090012042496203441081c130b01801803003d40d402660410105000d0300141d0000c9034162600442c0072030f240079014012186440300201071400110300d62140500803401d001070400c01c80c0f103035490080c2e200a02c1c0d4402c8450390a0b140c0083c9002d0041c0d0040e4445410380d8030400e180b0fa08104002d0000c02e50740103055055450b2002da80058402d541c2c009400c0603107600410a224100c12036002034801c0c035001c140040c00d5103009200f0042d112500091040e0b03920308008525506540c007643c1e000c2e9650b1074940092440495034000c50340490759240100782c801018007901c0c4980c01e00d58440311904001200d0310041d411143c0219071041000b081b13 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 92026475 1250 92025225 92025239
    0x1a03091501030c03060b0102031305130e060c0a0207050d020d12020319030b01080a0e1e03070c0906050a0609300507090b01120e10050402030f060103080720010207140109 75
    0x59000b1401406a00701da54110300f000c0040312401c418080c155801000714450000c00600240101c40302116100c2c4100f0034205c01c94050061400703a034016000f02010400400105400703040350341c040340d089031012074581c814080458a42c14001c2e501809408003540002e07440003000e0381c10101407050340d090403c030b02071480050000081d10720101c1d4036505000015603000a481c1e5100c81e80d403001b842030390008485680c4440c0c0c01140030000030071140c0b1074103051204200701c6111b980c0c44050440301a60700ca28201c000c00d40c7e400f034940300b81580d20300001d200e842201e2030b070300383c41001111543c582c8141c4410f0401104010b0115802c56100001c0d202050013409083c0050800d51000701e524000000010f01c8100842c50311015186482d214405040300000d13400d1a005d510440000c082d11680002443c0c904d03921030358101446060004004c20566401400a041c468070100300401d000320341074501000d40c0900b240c0160301c80c0004000149020f1036004a101060400d15400c0b03840c0c01c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 92027725 1250 92026475 92026513
    0xb1803070302030703080a05071403070207170a02040b010c05030a0e01110a05010e070b07030c08090a030f12020622170c010c0914030d08012903010608040b0604061a0309 75
    0x4050780560008a45007090541024041d41c2c807640031034041005280a030303400380840784581030942d00e4845c048001400c9600030800b4030050040480d41c44030f40b00700c86603a031b5034500007003a00301d0080f0f081079203003402c03940528402071000b50b0000156080900d01d07101292411042c004a03410000e0407515044918424090b51418034003a9001080d42d03414068820320340307107940c0c1c060f03091000c04210000210381e208100c1100b039503100b180d007590752544400242c0c02240c0380cac1011b803003100261424010040051803240740c04506400350f5a00355540d60384d01981c0480a41c0d1013021301ba19860101c0000c030040740c50310b48000d8460840f82080000e0340f0450840d1041d008460228042c1d146c180b007400b2f90144040c8800104074010407810003518001001c145040c0f1501403101c0b80f013640c2c5018446112204112401200003a503100e43e1b503240e00802401068400b610b00c1c071440d00c0480c3c00fa0070f0500400003510700082500862800d01c030011485030740010030050b103078007401c6a03010b0548070143c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 92028975 1250 92027725 92027737
    0x2010903020603150a140a0e1b0406020a03181a031308040906060e031605010f1e0305070806100516080405090906040212060108071403030d060e10140d0b1803 70
    0x800038060014100c1400b440d201160015445132000c500c00310900d0342c2d0b51f01400140e940ca0a0135203100c2c2c445080f010300070380301d6081c0321010742d40c0494041902c40c1c1c0000c400e42c03842e0281c0d4801e40107025444108555100c9401002c083c0019041d00080703007544071004580015030b0391a915404509629500c6154105800100c04661611810030640c0d91050f402104003030218042d04c1004880521500070358524410345040c05000104000c116010f20f210001da081580400b50a5011011000b0000c080858028010602000c00300315a0704000c2001c82c04494103864161900c081d5045031001c130000e00600700c0e01d049003003201261a484014882c1d000720481e4008042078141403040110700110040282c0d1703150f110b000100046c0400081c01d00494018603a00c0d01c1c01620500030038110700c60080108021418128001802d400c061110744c802c4050003140d8007550340341c00328050344c0c4c1603407030307001d54440e84000111001c030746070b441002e400142015500b6101403003402040c0c11a0821 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 92030225 1250 92028975 92028991
    0x8060a06060318060c021603080a030c050703090b0f090604090f05060102030c07051c0503030f070f0e03060613090506011d10080a06050a0204050607050106030c0b0f030a0902010903020603 83
    0x1450a21440801500a08014051504080c410f0600d61090740d40d01e5030840d01c1c0640301c1030305c3c2c1100404250081c44280041c00300904c001b800d2a4881c149a1202d80c007811100b00080d2424096140c0700744a4400c1c5c1d0320311035241e6992000c8525113515030260307070040c0880144005042120b010b4540e6000000d0000b0003c1600c00324074003e4003002c1008403030740240164195003040101008401003c101a002d644003182c52074805003100389000015041d03a50000c05612000081c0100b480c082d0711030724450220380e0b0302c5200f140c12184007102c82d040d9801909400da8002070101d500ba10b0034481e200c1705050185d2002403691080e403140e6180502c01e80c004100078040d03000c0100c4000a4074222640201d43c405ca00b1800c0d80b230a8182e42d600c034007107103003c0c04140c1d841c800301c0c60f40d00c0584c0480300285030050000380c030382c143e505007940202850721080307412603504007000521101075025607040403003201c00c19003113540d40c81d103a00207010a03d1049041100d1100c001c0300603903400307014500a42e16 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 92031475 1250 92030225 92030233
    0x91902131205011d0303010605030a02070f0b04020306071d090402040908040308040321050a050d0914030a0315060504170a0204060603051f08032703030301030602031b0c031e090a08 80
    0x10360400608545054913030001c04c181284200d04096400402c481c116422880c12940d00d940e00c0004100a0041034801880500d03111030700014080c0148486010b04c1c0200c01303940440e00c81e2001500c42d1100c00199106160040308007580500e002e0ba1000e03132150010b040840d030801e603a0754007416a07015400459500b0300c041070605c1404000c0001620200c0c0b2141d0181040700044005080350081490200800c100001e0b10341100b40c40b40c0011107007036400b102c0c03105103031500e5a0454484d001204580006494070018160100c0381001080850301e2071345419140900780b84030700404002210740000a4414240792074010784407407080300c005106541d400504e5003042c1d140020809100e82100c4801c1714500c01c1031200708000310450307205400031000403031084440345d0030f00b04c0b510340611110741c540000f2000105000d6a60020340c4268001d07248400401b0715014600d116014022200c0e22551041c403035075041c00b11405080c044100d0310070420742401d050324002254000f50341c00c19901600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 92032725 1250 92031475 92031509
    0x20f0a0302070e0703090209040b0406241403010207110918071e0506070308010b09030c040204030605070e0d030504060c080405030109110a0b0f0d090c0e04060207030810030209190213 81
    0x308543d11543c1003c1c05140a1025100031340004030384100103000949081d0314071010034200400c55014200c41c803020340302540014410321040301124214481c40020000b064000c0e1424603040c401c5500301c6038040300d8050071901e424280245031600800c41c47d601e103514800d0002d646c100304164002080f0350143e500c4e08805020708154107601e154031403070088030b041c007c400000341c00420b994191803059041680321076040b0000703854424003644c440c1e0840c0c0f001401106200316a04903a100740416103a01c6444040c00e42800400d240704203000c0c000600a100520015119003030003500c0324040c4103507505140d00c800019007100c0c84542c0491302030002c0c210001080c100003020781d0007810801070b09030900441c4080031103607110b1035082003061603030761300b8600401c12a43c2d0040301501000c24000031510302490498020350000304180c0100d0064070001301210700302e00300b4505a0360b01428205141c0c6506402c0d00d100e100d81c01c2d0165015400f8040d041003c0c1181c00181c0041007040560701c0044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 92033975 1250 92032725 92032739
    0x1090501060e0a151101020906040b130b1c0509010b09090a0b0f01120f06020c15090c0d020d060c0c080a0f090b09030a0b0403030f0f0b1008060a06030b01020f0a030207 74
    0x907080a202c2c0c2e0080c601c0c03080c2000a2201135020120503031207401d10440158540440e0f5009101e94005950700040100d00072905511200160082c245600c0d007c044080c1c8170300745490740e4003504541034070040c0c104407940700401c00b58114079040f609650021074000d0041c8d0019480d0790f4225840d000c44d84c0031480030414014030820094010404a10914a41d41005954020058030f014040c0c200603a400500c0c04000881d812605c512414406a40c0c108554845a904142003500c9000c05841a604048014030348030000301a030b19801000c0046255059455030003402408013200b090007840d03100100407400c84002840604a599542d01c106903c5442c09400d402460f00600d4444506002c0502d40d0380780050740c0c107825600842c058810b96198607007100940035020715031018034144840c4200100300c6410403510300300c04580c082154280b0540403203400104a80166006010605c10087c0034007a500c20410f9540c1841907441e20081000d416280c000b0710328084006a100c00b008018903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 92035225 1250 92033975 92033987
    0x90d0f0c060c030f090317070213050c07021e03060f06061603031b090b07020111030d0e010207020f0108040c090e12030c0903010e03070c1509090e0109110103090803040b04030e090109050106 84
    0x1644c203402d00d10581411600c4201410440607280c0b10b01c3c2c400000c0e00d10655640e40c10940156203944024031251801c41901070303aa4001040c101c1c001c003891750403808800282e8002c074642c200f000d0014001c1e41e44000740d03410b40c800041d0229070803081c100300400341e02c111000420b4030301d402038801240c00008904c82101d880242c180003000c0040e8060306010403c00c90782226492502403070480d5011200b09500c5055200310398a400e5640e103024002401050190081c000e928001c603826070040e4686001911016000c50303005280308503003135050110394074561003410580c20300e10480707490901400030304a00e98015100c03a078881e00c0110300c0207184d240c01d014110b06484558091802d00199548104094040340103141180701500c8440c0d8041c0e219240703140003070a4035131062020b6402c050074140240000d103000d031400d001281e02090070354068050175001c01e40c081070716851551642c4520641c040050400c8082003115101180301d0b60301e100b0718a000e0141c41c0c01c0011154506031010344070f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 92036475 1250 92035225 92035247
    0x10c0806030c010c1104140403210b01120903270801050a0b03030a050c1504030507030e030c01020c090c0706090b01080609010c080402010e1201060f080c060708090d0f0c060c03 78
    0x8680d00c01884105103984c0058200902603003d2403500303950300100300142c05004030039101a00802c003002007105140c0d10000d040901c01c21000180b9501140c030b4610420340d0303900607105020540750b01c40c8924136041c55000d030040781e01038a840c01c4001d0b6020f121103928501051440840c855084043c05111028850180c1060040341e0030030424802902107520717802144007600070302c500840c040014032000d0044682c2d208680c0300581542c43d02d441e001c1d06940112000f540040c18007821600c55080000e01c0c0d21100005800501e2107000b08020050000c9000b032061300141c0003400300700006822405110f4006115450040e500c1d030411403a00c0c40c0110041421215a04000c40140183d402c292015045a020702c0e0582c03055010304003103a08400c00b141054815860302c1400500031701615004002d440014094030381018081007005003600680001821082080208030000d14110b44664842881011030304a11091922182c102000d694840d8010404046025003010b41c00719174440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 92037725 1250 92036475 92036479
    0x40212190218010303091a0c060f160206010b041a0903061e070207060c02060c030c16060f0207050310150314060703050106050310030201081902130501020606090405030904090f0204020c010c0806 86
    0x241075031444d2401005449148200e083c00c0e00301e07280030113001340c0c4074003112000703201701c0100c80480c202080245240c010440e0b022055021645c00512f440d440031680368100c40500c421315081c14188142c3d601500c90707000d04201000c0d0100003011090f202480424490760181c40103402028181d01c4201c40f141008010740210740050034184002a0000c00440c0c0c1c01e40c05840d000d4556400643c41461449000311021044c811001000c44413030514800009550b11a600d088011414220a0ba41d801041c095141c1c960011000640c40c401c89a00c54024804400056290703180d40b40c0350102c45180090444100380c1140c0c1c01c02c00c4490305401040d004002c940381040c43d6181c0000b5074070600341140402810420301d03c01268000b02d204c00a90400540d000045507950b400c1074072820301e10600d102d0b0345d01502507400000c905291500c6081c1c031894012006d1458002c1003c100f00c002c20340d203042260440200c00c0128003503122807014024581c0309500005a00f282d00380080c203c00d0004042034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 92038975 1250 92037725 92037769
    0x803040302150106050d0b0d1e1106070503090d050a02090a0c0305060d0807030f091a0403050f0c030604030c020d0602030108061f06050d0902040204090203070203030a050901060e010e0402121902 86
    0x70001764440201c070070704103104500155525401d00014200b20300c08502900c1c2c10300240d51103e17200c0d92900b0b0442c44a2046a108200740c45460601585001c1d803407028106801c140001c400700c1c104800c01d071a448c0d200c0c07019260041116800254892001d8900d0122103030f481d1100700200750180315075078010400321000d40d00d099955a90051921880c0c9009041119a004c084480c60203104040c020302039034000645e1848004600c9840ca41085c4010360b820303c49e0359007130fa6403401c010503852001800600504860390322510140c0d42a44100403c03a003080424a880020034558801303035003e01002c001414550030048060000c1c407042d000880d0f0b00c14451a010801d89030402c04980b21046201d0f800f0580060500000c0c0082c0210f0b03002640c09030000040052595020004500c44c01c104c0d201041b960300e400c50b5560881e81580600c0e000c20720040010700541c220a44099442403004005030b040140c001002820050964414882c1225070800d1004528198000d014019101d624203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 92040225 1250 92038975 92038979
    0x403120b04110f131a0a12020405061b0309030a03030b01020615100e0d020a0603050601170402030a02040f0b131a03031306050f0c120d0f0c08060103050c04050d08030403021501 78
    0xc2c000d0307845000c440740360b8200c0006240c2120110180070100a1074901589140034a1121007401d1a510210040380001c0d041100350100302e01a100744c40030b80e2005803401d400d200e800070610a01d45003520806200b44414001d81d80c1a0f43d00f0405a03004034401d03a808900104228006481c0c0030010740007440f6684418001092611003250001d881c4a04d45020380c60580c180010450105500302c0c0070f50003a001000200c1d00a40541090f0b0042c0001c0c2e941c40e400c0c3c280d4000e4000d01580c2035800a41c9070700500b00050144c60b00b0f400107111221004c07400901840c07000b0004110180305003d1b842c05030340f120b040c0100c000000120440c459010381c0035504d850100020350031036a03894011030040c0800402d2034440311a940b015a86c01480440c112089600c3c1c0500e843d650b50802c0803122012800c1c090403a0040090f80200654a43c941d02d82c0003c1e41c4603440103602800006112903540da0b0180000078603035696814150201d40034cd103503131341d5904081c1002420844500110000c40b80e0070001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 92041475 1250 92040225 92040251
    0xe0d02150601090e0a1506050a1b03030209060c0105040323120709081506040b100c030305180307200306040c032a1e140a0501031e050403120b04 64
    0x840300ca203940d10000344a075441d078005941c0d614058100041d20039041d0304018200c0b00542c071000c803c915401030280708540d552001c841c20700c40d003006600090312000a0102c1210500503402d4003600c242805403c040701400454180e80103000c0c242c034169180c00c00c0c04240b40e080012502044c10152009100e01c40200d03982d00b0b0b92140030440700ca980c0344c0c0000200d00034440c4940340301070700100c010fa5000040c00e10300c9207060401540e101b440b0b18a0442c0c0140b071454140c09801002d45151070780426014151400e030000c120042044c4801c4201e90007100400d4030074401811400e20a009a0342407021484c0003011404101c60f955000e58041018040810460380543c41140c1d40007079001c2da28002e00c0d9400c03140e50035401039601000510100415980003503011220a40e000400c81c858040d9030312000c0074a0740d201d0901682004201106104a501c0f0741c0000c002024180040158100c0701060042280c00445094002407070504500c01454558065101e00351303405c840c1481007285c002e032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 92042725 1250 92041475 92041483
    0x13021e030a0c03060f0b040e04050f0a0b070f2d090f1502011503051509030f0307080603061e07111e01150e0705090f0d02030a1b0b0f07060b0102100603060f0e0d02 72
    0x88c10489044400000c00f0040e0400c00c4c4444100b100b8140c400e00e5803a440c00d10100705081d650f0b1000706008017860b40485210303404000c03d12603968801d039502d0308402c58010840031011010010008a43c0000c41d4001c2e540200000500c00156102900b024040c4000c1c21600000b41015409580000400102d600094803910092290064040300e846030a2028510310800420740003415020081140a43e0002001c920461094049c3c40480d601c04004100302c0c0c0007062a40703203d181020200d40c00310b06c648884000d69102e001113501c00d043c0040000403a004800c0c880e05130b69142c4018a0f07001c921100e11400401400800e040c1c20f00708094081e04a025500c1d00c00e000e000321200322846592881464003550f900502580da081c100d42c240855180c1e1601c091403030742484868002580001101120b41002d40742070310b0741c100441651120060a01c0010b0541140301d1000080d8080e41d061060700c0040d40320388030000f01060860f46400907141300351003203c1e040d0010041c6000c0682c01003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 92043975 1250 92042725 92042729
    0x1011010b0316060e010221040e010504020c0a110d080403110301061a04090213031a24031207080c0d030506010201060f030305181f02060609060a0513021e030a0c03060f0b04 76
    0x10416040410303138000103c2c40c000300c3c40d810360180110b0649481d40d01e641c01c0020406d4400a05090b407242c1e0b2a5003d120980c40364007840c0c59560701204096003c078a2445010302c4001000385201141035050302ca140160308a0f07003060302d09401d0308486418038582446242c0c010304c0c1070101d0300c1140b0b05a007142505405280314804605800041c044005911100c0e00805503500040340c50001c4460404208150f804403040e411010950000385103014102c40140078801005008014141038485040c204c0d402c070a6044a00850a100e002c20320340c014408642040900d540001d413501c3c03d90002400d441c0306601115690303192910900c0440d9200088607110071210326070100d0540214003142c4148102c000110f20390843c4045001c50b180c0c0410000d0146100700ca00d8149da13250441000745000044c4105c80d40003068030074121402245802a0038200c03604184c01d1035844114000b640e00c0e900440e00754001e1380c0d65000120303205030180328050180c14038040d1015140d0512003003492503c503c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 92045225 1250 92043975 92043977
    0x601080403020d0509010c02130203090106170c010e030a0204051608130b130c03120906090b030c03060d03021006030b01080d020601052202040306020f03060a090c0503040f0201020a021011010b031606 88
    0x1411720160b40100d03003003640c140d4040c0c4408051440e50108200035001034540341619401c0900010f04440240b1110316003480a402409482594800640751400900441c9425016240542c00543da941c81511700c140d02211808040b0900c41c5c074020950080200f0440d04440e0011410010848404944e07620403a088601c50712111b45060400d050318040e48000c0c07400411601d00031010ba44042d402c0c049030801c1d140c00750981e03142d4200c036500d40000c07101c04501a1090000450074074040d10b00d1803000f4041d0060b01e410f26107204401c429200560000da403144440001003103c48020800e19440e10348520190060354105800900f40350800c448582506054280e0401040102d034116402554410000c5541d03544c00714900d20150021510035104810380d10300022100054080c41e0382058090740d4a0b4a10399482e540c01108041c8904164114860f101400700180c54912040a400302e00f80c81d02004052441426801d446c21161514000c0d00425400b2a04044004004003038580c3d0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 92046475 1250 92045225 92045227
    0x812070f08010608150d05010209031219050f040f080a12030e15270d18030302030405010513090903081006031e020d021201090b0f0d03080f06061603030203010e0601080403020d05 79
    0x558400009000c0841622071b4010490b2600c3c108200c03055000782000c0d04103500ba40c154402600406190b40204040f0980c040144441000c000341b080b401801802c0340d030f818003418103880740030100d510505500304bc6070641c45841244180021012521740d07080f130603e07062290b2105003a2480d00c404522107030302c0e0399040c18004a6984400e00c0702494204030791648040035168401a1740b5910881d5034451400300b400324040e514490103000c1c90000761303900354004600d800e15040c0115081da018a101070980306070110b021494181c0f07800340821060280d0344080d094182070501c00c800380b58550000042c14078292045800d208221030390041b8041c001c00041e100c0c1340f0194028003901c1803002d00c05030b160700c13640041a0386445901002d2100c0c42a5107600c03400c1051402d100b50000140c00c05804140c0020000b040500440041e80d8005030181c43d49060444d10340b01c002028556000440100380c0210050010084034134401d81c0c030080900c1e0110040c14292003b0b9241e40c0305101090030044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 92047725 1250 92046475 92046481
    0x30c01031d010f090b011509060c0503091e0f03032104051504050a03090801050f0c0a0e03070909110f010503040b0a0605060403030903060b01031a0d150501030812070f08010608 78
    0x1a030760207004512030320100280849590b46002200602c1425030403200200d41c2030000c10007000f0014448400001525001c41203400e102d02582c041180c400c040b10b00e03210800240c41d658542d441009420701410700840c40f0760010710200a4120200c00c0654001e82c0148810305500ca10444203075007039580b4200d82c500546450030800d0401215884110030311002e00188801c01c00e0000c1d681005a010b9900d10b802c0584481c4403c0c21303110141c462007911209100890f4215454a0040840c0341c0349041c004420030146000c00d00300a4a0b80c002c20a0542c0c585400041c0021441c00361a0039030304a031400301400800c0006400e40c04094006032141d00c0c50170010780c2c2407c5603441140075100007030103e5126580e03850024448587d9000481f521410040c000e00107500900402700f45a00448000d1a4601c94100b4008003c1c3c0c025001d8071b40500d0705104000c2c0000c2c521a140c00313903010300c7d0390f943d50b0008440e1a25611701c0c00381040040042941000030030f158400841819150689003500301c0352 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 92048975 1250 92047725 92047751
    0x6010c0204090203030a0503040203100203010f051003090c0b09030706020f0a260c010b0a0e07090504021e03010b250b0109020a0c1a040615030201080408220801020702090c0306030c0103 82
    0x4002c030702c0001d4041c40001414a507a50708200035610840c4210202e170300540482c0030083c1a80001e00c030740c0800783c0540d41705122514107a04030450f00d11142c070700015242510b40b200c54a4150b560f208170f80c01400001e0b204d0180c00c0500081c0301810450000308040310034800201d903200040c2601420300c40c10049401c091413103a40d0b2800c102e40090030010b44440749101030034020a40201c020b449000000070000e00346404800c40c0744190041d403980014035140406000c0a540700130000320075820020134148003224034101842c080c0c520bd50f0030300c2d01c440920000c4a13110b01803c03501400800807511b1400054001700b14141500c402180c09030301c4866190054030b0051050034001d0026141036401c425032860400018800c9010300c005220454400304041840720281c040030b0b0003d4400400580400c14010042c140030401001c800944115812500d0784d00e0700c0340d00444807507500007418406500d0f00485440d00813200d00c02d16865418210b0000f42d840c00380c698094180342c1c0f18150310b600c43c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 92050225 1250 92048975 92048981
    0x7080c040b0f090a2901021e1c0c0c0911040b070302070308160b010906060f050322030c0b10060f03050402030709020310230a0314030c120306010e030c010806010c0204 74
    0x41c54001e0150580d0b414801c1382c00300a8140c40050200828045082004004498000c8100080181c01800e03050741d10203000c0b030500c422503116100b14400c2c0700c90460340362451104498001031701d42c0c03040e0300d98440780b03000354001d980d9030b01c03440059050104002401c86000300307d030216440e15070602d47e115030a140503424070901e0741c0040d24806002c40c44e0905801181c1c9401c00746441043c070f5554036030320307903004030111005400b030900050000000c0d803251502a17401550080030040781005020403002d00c080340849560401c030006048907024104001c6940d1b02e9039081140301120030411410704e98010720551992850008064482000c09c007591001d101c1c0c0c101806100d0000e40da60f281c44030603403200c00c80920503564074401c151301c14018103c42d031140e4501d01d407000f002a40000d03c0c507114024440d000d14403500e054041080704650860301000000355510840850a482c0c0c0307020b07000500750300380ba441f40a0280d00310465024890781e0029805034400002d08040d6602c1c07100380049001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 92051475 1250 92050225 92050249
    0x70611030316050c1501090b010e04090c06050706330e16030504140609010b0a060806060403082a210306031507030e0703060603110114040905040614070c020306070207080c040b 78
    0x1017801d0907800854819100c1e080424011400e0301c038440541c440505001c03c8409070280a00405504e11091181c01d220f40028080c05002d0b09001c6072101d08500070803100028540038017010042d88805100141240150400030210464a0811490414000d80000041111030340c01c169540740000d0420950301c1a28041d100140116034580c03420104280c02041080e003414800c0700190030019481e0312620741c00e807051201810007810185140d950940c643c0200f541e00045040303140c41c50508260003280300800d2000500180381c156620b100801941030498811203070031008008004544c0c500241030103401c480340501803d60341c0c40e201c0440040c045154984180c0c05888800414807078541c0180c01031b24011a8450a6941e900005403400113843c04001143c03503040c003003084800000d48c032841e0301074043d440110306030712041d500b003400d81001ca845001040c1a0504101581000c001e419449070b03441c0000d1000d5406d1050050340c030501201c4103031186803150b80500b660b49840003880c0d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 92052725 1250 92051475 92051503
    0x80d0f0f18051b13020a09051302030f0a020a0804030f031b05040e010801050103022110020c0a1a07090527040803010602121e07111002070611030316050c 68
    0x400300c00400403116462001620a8034640309081100d03420111407039000c1c003c80001410034903224101c030b0040b006508005818800c1c8002a840069243c030f0716805c0c1c1301900401c0310f0060782c07480c00d002142070102c8040e00b03803042d80c0c3c8144900c6540c00d0b002903105800680604000c489625445c0003200070f4042160100d1102e04900d2600403020b4101001e04255020024160501da8803003041d6400c8500901c00654400c0d2240d0301c02c281c02d541030503410000c0141c5030684203500780b0918000300340d9104d0044013240c2c0e07102d0780c110400e0000d80f9a2003000480898032600305400e03c200020400e031854001ca5104242d2a09a082c04d82500c0c072213440c01041d80c4840404910b803c1c1803442c03950b002403003106c2c00340c02010320780c08100f5990008c440e03451441183c890f0180c04090310f00b44098008000c119442c40000c144a0515034500345006031301800e40d13000f055028106a80140040044803503895658014401d100042007e845643e1408045103069070f201d49040401e1840d03c04140c5143c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 92053975 1250 92052725 92052731
    0x140d050a0f1a120a030c140102120103031d0d150b011707020d02190201081501050c01090503030a060e010b07060b01170a0b0f090f15150d060603050c07080d0f0f 71
    0x404000b03420324800c10741200072990908040d0015035003c1e191140b80100400203080c072034203400001d8030480864003102d00b0b1b40005007040350029454500d00400e0700141c01090608100071010341c84000b800345200c2c410f95003032481108135900c035650b403012881207040c01d94450241751510303486500c4c60541300f22034002c480a141043c010181d03c89040c54030341d00050043c90401071211612850700000240c1c1a95421104c0d5511100b540c404040e12007440e040220800004140c1e020900404030700074010000707180c0e2401c218203000210341080c0d0000e2a0585400d00421a500920b0b040d651107039017020000c02c5070b42c25400100e58152507091041601c0b0402030900c099414542c1c0700541507581914070b400c01d00c807010100a080001110301c84807090507040015a10b1047c0d20600c0300c2031801410b10f6035002d0799000300030101d411260000251694681007000426850302030b450300001091911843c007680c4e034541b1a954807d003113406504a455040c01c40c0301001e10f038015105848800020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 92055225 1250 92053975 92053991
    0x1d1c1701031a01061d0108060a03052e0b030c04020d0b060d06030605060904080a030c122901110601060c0f020a080a0203010c081611010e06160906140d050a0f 70
    0x80c0c0312000101003160314103203660004500c4c20f0040140750030340b0a14103030500c94042c0e00d10044851f00300080100b5042181183c00100007242040035a1145200940b075441030000a001c0407403040b03031780c45098519802c1045001a5890120712402c07640400c1d01c001d80e89042c8140d100000c0c150000880381c04c10000202a83c074203406174483c0003503078402c141c18000c980fa01030800514504c1a42d020745015403c200d610145802544420340794605401c1c985218060400700358103d48001c402c55001449245041c1d490f022051000c1d90f90001c01d00300a0080582c881c1c5180e940d1505020b0b4009100280050301c09110804041c03421f01540209260955515106019102c07590b841d0202c2c029030800c901080240d0040880c540b1071302440a80108240d2440401caa9180441e80c244556560b58846002030401c24808580f103080000c8000490018821006007010025070090040101d035140300d0401da18003070102c0b000600039620204494499450840050104807008640342d494a00f503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 92056475 1250 92055225 92055233
    0x1b0503041a1905071a06010903060203160206010510020d0809070306020703031a0d02060f0f0c0a05070608010e0705040e18060103060c030f05060d0f031106040503030103061d1c170103 81
    0x1082081003000e06400400e03401c402c140c2d000c1c0a1140000e1951a04e44038010b1030390304242c4a654000c50501d00050155600d07228070003241d10959074641240603240440742200d40400070076004103c107680000420314100700094441c440c000076107081004400209070504820003411001d03540003402150380e404246400f8009000d520340c940108020b184583e6011314100c810350001a030040c10061501a0400041006500020900c441a101449000c1e2440070410503d081c0c14800c50003003465500b0a0340142c40b105050b406000c2c401492010890415403001c162000c840c040c0c502d401254071240700314030b02c0c40c040b40c0843c89144a8040000180300c41c941084030007a04540f010445a24204888415074004a03406908400c21219100c00140c2000c0700c41049c03070003450101404104070700c00a0a015054406545a5201000600030b00070144240300d002c01c240c0140a146480244c903040e102d0180d01c02030b02c0390800d01c0350402e6245020b100e041203402c43d14100e507680c03580c503450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 92057725 1250 92056475 92056477
    0xa1701060e010503010504020a0306020309160314010e030f0405220e0706030c0513031707080d0c140a0c0312110a050c010c0305040c0e1317030702010e010506011b0503041a 76
    0xc01e030340001c001100005000e04042c82041d0045801a01c18940035003581c40b0000650300103400c1d5080c81c41a4030300341c1c074442c3e5200c0340e1001541c443c00c06c4281001c0d030142c04600f03644100310003140a400c2003000c01046240d0f44101d404071001941d030f1241e14480207100c4403000030301d030f6405070b802070030440303241c040c02c0700800d0075801e07541251410082003200001c00c413054092002d003070b011640c0442c002c0c0007040992001d10f90620030300c10b0162502a842d966a020350f042103081d8513040b43c03903a1000b080c454000000c02441c2145486e4642054840c8100a044164106014062040400483c0003048650f00b01141c4034801e010320b079580d12102d01000340290702000902d11340307519010b010600c82e40300e8021140540d42180c00404040e0038482c0144000402408005000c0041c5292100156850040d030303229030104404240c60746000b040c041d0030b461450200a0080c0d14001c100709040c1c0e00010300580607132400071151fa1145041c90280c0c80c40c4210741000482604001541000c004c03140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 92058975 1250 92057725 92057729
    0x1090e0703060b0a02300a030f06080a080c01051b12090f061005090109050405030318010204050a0609061b0b130501020c060903040303090e0f040303181b0503010b120a0b060a170106 80
    0x2140002896000d1080c1e500340c200740700c6c481014400200416816030b4800d17005224000400440026656902e083c4030f4034060170400304580413580421080107030f4400303200f1030f0740c0503668030703600d4128101e00030030001c0921610300d1011fa030321642000314004680810042e03410418580480322039007000654012100e01901c6550300c14be41d5038001250035201809828001c1c0e900500450468490034030303030540703101c0c1e002040c41c056500b8400020180e66140e000002041c45442e0741030031600340b0724020000c8040e03151000380031040348510f4001401402d60a50703c1280420404042140b52900a000e4414900ba44181d4030505c400e01040920210081041f03e00c03984807021507942d980c2d10060040f408a50f8480800410000540428080d40204494142454a0382d415101c9560f8240120b07162140c141c06038003080c07a00b4400c6040c2403143d122451000c44802003011010142166280b41204000f40503100000c0170a00b41d4031103d0602c03003c0d100d0302211802c6680c0f1000c4840c0203254234 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 92060225 1250 92058975 92059003
    0x4110a0e01290304031b0c061d040c020606010f03020d0204030501060503150f0415090618021905090c0706020412050c0102100908030f070e1507020907080601090e0703060b0a02 78
    0x8080300902000841c2da240b0041c046880c201070965503140c405891148070200941409445e541c42d51000495520b03005010740241d88544a070100940c910301310800c8001012809a13103800b8070030710300a400040e480d03813104091074100c020224111089001e4040c40c1420740c01c0a00100b4080b04000064001e84103a400503070885100315018044082988020340d0841c07000c15000d004100070032501509410924003022011030001d0482d40c448007181c1001212076409403680040f00f0031807801c1d00040312040750807211001101e00703200001d414440050100c5812074400600038081244507010b40b0000c0c07070004803009212019040064441007a40da609005014901524078643c8044c89800180e9822440803810f42d9200c0d1f804001610000e80408140b005c1e005019a40d0742c0e84090320810740d03074003200d00e03600e40e030003441844910b80380070380b0780000d00403c20100541130b68002400011034a035400190469110b2540c254000c01c0303183c01041380020001641c4c800140c00140140c100410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 92061475 1250 92060225 92060249
    0x307031101140f0114010507120c0b010602160909050f01050106050a0306080313140f09070e2106061c05151f1a07030212040e010e01171504110a0e01 66
    0x8a0501c0c00d065400c2203540b038250382050343c01441140c1c1058004113920380c040c1085482c10009494008055100078420000a130b410f11001e8100b12242c040340c2e0041990380002e040d010300001007250080c6075401514100c0741d60b404000240a0200300c103007003441c0002c000308901d5840d400d00030840c0c0d00c00080c0401090400781e0000c1d4500001040b2980b40190040180440b030a1110350101c03100c025000f541d1191036810180601d540d020140c030700521094407104085800300341401502200c8a0340504a04000140610320b00c1000c1510b40d8007450440d081c1d120300c046d08800c2c50b950150708602422900c109642d50442c071250040c1c241c025104041d90004c0043c103180d20300a1013806000780c0d00c3c80c910281602080780c01c91809419490701c24015038118981c00c508001c210707040fa501c0488503080083c010004000c0d0211907a0140081492010511054030b404943d00d4900c2000b600046500000180c1446400d5003000101c19006042550282c1c1e40ca8000031034400a010b80714601c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 92062725 1250 92061475 92061491
    0x1124070303200711040c050910050a0f090806130512040609060e0f030c0108090709020d0203060108011203051c060e07020106080d17060f010201020c03070309080c0f03030d1109030307031101 84
    0x5107070003070380c0300c4640c04010752802c071341c00300c060201804281c0c3c00e5078180700007030080c21211781c2d0701603203504002017698a49071221484000108601c0c1d0084101d400d2200d01c0b08148203d24010895950001d07440d8028170003481245440c1349031003000d201e031040301200841c0c00300b11039520082410440e540750f6501c2c03800e90264000c200c4070f40c10508a00d40e065010714501000c80d406218413940c0b1076002d42c00c0d00c1c01e1a6803600500c090380c0c84a9210010b031a80007041020315170b089078009000d0b00c19194010102d415a560183c500d00c00d444602c1044207030309d95210300d08116a0401405020555440140c0e03041c001006030203000c4c0c40c003440906005492080e0541c83c800c515803003035001c91218403031050b11384100348442848003150b03a41c11035408000010010008000074541c09209503500078030f00d8a00721080b402d000d90003010602c02e004002c2c5a0b1362907a0000240d90102040440000d14a0940341c90702c0014070440d02c07203036010700002c1640014190800e0f0542101021603000b408885 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 92063975 1250 92062725 92062781
    0x11110150f06021b010504051002060a140403020a03030906060906030809090705091e180c030114030a02060906030a150909170306010c0b04030203070209010b031806041124070303 79
    0x128407800b800005034005104500300ca0032a0081c00600501030415070701e02034803030020581d40c505041c504000340c1d200d401440f80f851014400c3c10711101130620400c0e11030600790f800030340b42c001d021030260806445030142020302ca00da07881300004007980401000301d540c4d240380c0034210307400902105200c3c1e080c110010f07101d180a1011140b952100400c8524081800429482184084a03205401081a1495518054100c040c05000740040007825071698034015002290040740050b40d0b0282c0c1000e610480140c070380b0419122038039422281c07182ca030342d80c2700881c500412100d1041c0071015550000010400e4655000d14015402010298039005191242c03020718481a2402070000b0b0901441c00c3c0440c40034001d454100f442481603030300e49240368002480c5507001307801110941900205202d0310040f25045240c0b0038642030090a458642903c0c1d054516200901d52801a9510418408501030503400c0c00e580840403100342d07441c2c0942c1e0900400510030a1462440499512aa1640b00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 92065225 1250 92063975 92063999
    0x3140601050a1a0c0304090e0f010216030309050a120f170c030c070516030c0513150302100201020d020c03040501030c11060406020a0e030a1416030c030f0201111015 73
    0x2984002c2c01c00d02c20545000803009031400071000c5994030120078020107200142c1480148010301c1004404644203007201030303d40c14400c1d007410b4002642c1c410420b1032402201c0d44090a41c00d901030400284911560078424180034604000404000c426001130794007540204100440c1d0718140da46a6807204120917400f1500d9069031103c3ca4500288001000c01d83c100c0000c0c19118801c074140c80c684041b1302e03440c00801b209504200c5202100034418880c40c280322030611103140b5a43d1050048856110302c0711429035090101070b0140a9001d2007200c024000d40448034000d045000465460018440070380d00d9421600547e80041d050402140c003107440385011340c10300c4900a01030001038660b5650000250b103c41880424003c03401a80380c46554240019800c1a001d014242000f40403417a44a0600100080ca400b040180400c1800440c0ca8011038900380c03903110320b010b2688002400180c5014100d881e441c3d0586c401e401c00c2c4054500f0306e4110008825400c412480515119000c01e051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 92066475 1250 92065225 92065229
    0x6090605010804120207050307060507060f02090906040b01030b10080108010b041e1a0a031a0a02030705090906150c1605030109080904181b0e1e04170409050a050103140601 76
    0x1a4022002c0f0740413444202642c3c00300c2e0300c1401111407072566040481d00b030100c0e40e48000045040441d2a00c103004003402071180c0400084811480c0441100005942c08405070585020740e0381d502c2c991030f82d0307402640281c0d0320000003441d000c404841d43c0002402076030309000c2d48010f035091004142040c00d180c09131019181c084401d4008501214044000404844c84c03002401c0042040d08041030300c84501d260050340c003480d003038960041e043c0803160a481d4060109600a0300c1041008400c1c4e07403240035a00e561204071408411602d0f180001003448203402e0703220340c020304005048022000c000442400d00200c50510b1a2881d40c1c80c000c0500b02c0d6031440c4040c0203104100900d80321840d05a01100300148941d1201400014a0300e480b00e40d4940410f4000f0007540303e0109210381c60741b1342c0780254010a1a0419107900b00c1c122036039025048080d01c001c00d101000200c10610b00c07a044251405001141030400103440c02070031090160000384000da44203e840351003080d40d05030210302541 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 92067725 1250 92066475 92066477
    0x3030304020a03020616081602010818030901050a020312090a020114040f18092102070522110705030d0203070905010c0b071b1416050618210303040b0a0609060501 72
    0x1000c2d42c034507003e000080d44100446462220542c404000003045400900301c100780245c0480201d9245100140191401900c8410528100146c191545100008580c10042c2c280b9085032a441c1402d416031550045021400740521204100000d69400040041d45503000340d035222200343c44140f1a0b00c90341300d00c2c0504480408410800d02c243c0035240700900c0c034081340030400200d9080c16220b081040c3d11000620310a5108202140c42c00d40d81084104054441102c202c07003000404014022071040d8000040c8195482e841080c034800105d0040e00c101030380100c103403603413000c100c852038000354012520140443d1400f100421694403a8541240c2140e10140c40102511056010348043d04c10002000340d111503010b001c00080d0700d07540308001e02078800300200b8000d0502c20301c010781e003249030300700a029403410302c0b046100b04516001d508000a041d00c4036030700c11051280d40c65107410341405c54001403000105000c1008078401c4180c0c4254000c5004200301074031440c00390103503a854480e41e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 92068975 1250 92067725 92067739
    0x405041103090114010e0103030c210305090c0a050f130e0303011d010603020a020322050d0c0f0902090307030f030c02150a020709060602070306150905070206010e100e0711011508010606020c0303030402 89
    0xc00040d003cac08801801c07501803158001c098003200300c0300d0403002c241c5080c440001c2d00d5500b840b50600d000c01c43c20303c4411048401c20702c00c1c0e003040c0100e040320391905102c600c03c1700c002d2410a41203581c2c0e4400d15001c0c498200303072950307980c48200c01c100c040100340c1001d485218243c00054a81d10901c2a03543c200150380c0a5442d1082c1001c8417103504042071a40700c2e96030101ca4000a080c4c0e1030040c000ca071584260a0700404500d0800d405805d00b1341d907070056031418010805008a80d401280038020340303500442a81d0410058101100c050503030220003900300314074020f4880070b4415500075120031029030b800c0310855500c81040c5402d07191207100303050141e4091401400001d0341500000c00a400505c0910085513035407450405541c0d083d5142400350700003200510102080d40b40782079100e01d0790105100010300c0c20364403441040008141e44200074a140c0755030841c078001e4204480007001900301d1107550751990748050090507507114010152044182540040c00c002c008d03240b003240c00178205 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 92070225 1250 92068975 92068979
    0x905071e1e170708010f06090e0705060f1606050703020c06060a030803011404020d06140a0b1305100c0f03020601260d05030606040e090604141903050c030405041103090114010e01 79
    0xb0b00c51182c4510025280742c040e41c5804104400b0900c6015201030444a0208510b840c041c50407044400c0c40b1080603140d00094401c2c41107403190001c980d400f40c18409000d513103400100d01c9078140204071500805541c10712041c00301095040d00608210386412050760040e488040070800c01071074600c401420300d5000d000420003181c1c242c4500d001900c02400161a005018048004403461a00420410000754000c61380a0802d1080ca0002d03082481000b03240c04c13540b07600300026a1030380c03058a04c14209000e0552010744202d01803419690710441d5058084000d140203506c4500034000d0003d0800d0030b40c200d002113030000d428040389058000280a80d640c00e61f0080b01d281d40001c00007508803008100000e900740c180d01c0c40030310480a240c050400d500309841c0282c01e0f42d20300074002e102c581c40ba204004c40c0f5a001e480590095625003415550344070388070b0324a8110b008039401030740e005150100484810b15107034010f500c90503d000080019041030000c2034002079080c020302c07000071155401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 92071475 1250 92070225 92070239
    0x10e0403080402060c1501030c0f051009050f010c0212010506040f0c0509090403020c09040809030c1005090409110a0f030b0603010c02060106111501080318010305160804060905071e1e 81
    0x20078106905c41c1c183c07211000030350b42c01e0508420a0744103d0781e5099060007040100001e4a041010300011a4810219081442d0003800d61440d80106441051902170b5411941e0042c14010b1065a000c1d04d101e821388040c00c1000d00806040781c0c42d03402103040180038517500300300788aa40a55110350f00d409051107059400e1040b01c08004108505522500c100003502e60765482c510b81c0700d14400d40c12190b4459043c01818103003031801c08024003c2d0034140e507020300c154110080e0784007800e003641d0000300107041e4209000d65039aa11343c0540c101c2d40009000c2051941d40c00c40c50181e9004040c0340e90180c44203410306080310400441c07840180c00120041c46961700c41c52001034402440f20440383d8090000c0d4604c0402d10080c0d00003402030b4400140c00329494a009041c2c2010f080900b0200101d149c20801c03c0700e41c00b00c241c284d10400c50610700040410a8551240c500a50010115480c8640300d400e00085055203070040c00140c88100c43c00118075084022200e40a2880402e0102c0343d854010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 92072725 1250 92071475 92071477
    0x314090114090d1b0f06090f03061505040c0201020c070b090a0509090c10030c0f020f06070309021903050c150c0a0f061811011202130308070309080303040b010e010e040308040206 79
    0x114240d002c100680c4150100d5043d20842c1c41801300744898143e12440c01c1c0c840900342485502010500160701c030200007000c0032118103c1100d400c040f01160080d8441240d40d02c40310160844e81d031061505031201800c42c3d05501a0110380341010031240d1a0352100c02c250301d0317070042ea03c1c4c2c16403108644106000c2810301000e0203801c82c06c01d10880313180b00704072030001c0c0120184002520010340d460170035a00007544048403080481180c0054084409000403079601c60700020400024544c4074050042151182a48590100004e00fa15544c00380c50345012038407584905011481a03d989a40c0c2040b400b0140c1111009204840140f58401d06940ea0205182150790241e415981e201840c031690740030380120f412481c0c420f43c00c0c00e01d940340342c00001d41f1f12200c0a5203020800e1044c00074070141c1817608034202c16250002c110030384880031803404a8518409030411505d80c08040140020855a005090f06852605950b900c040e81c03110fa102c1d4101d982194040e0011369050045005801c21030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 92073975 1250 92072725 92072737
    0x94701050706060806192c16080124060c031206030b090c1905030601030b0a091406040606050904110904080c01020705030304020a06080601080406020a020c040908070314090114 78
    0x3050060030825191901001c4a80ca640b15403030903002001004007201200c2084d032100303000b0201c1002803c040b4074403485c021442041d00842c1c10744161210303580000811445d0750341800c81c0308100c034194980381c1080c083c02c0400041c4900c00c020f01d0b045e10740701c2e03803620b00a019070303641e680c074040e10040c0c6032000c41d20b0703410f6203c18040940c3c1e64034022022500203500da0b480f440380d9400038225408614184a81400d15a024080248144a06104954001c600070381182d400c442942100e407aaa486800200130b900401000c0202c001c0045100642c0460194230039409941c081110960b241e00340038030050300f107a0007013503683c18896600b002d141c80d0002540082c0a055020300386200400601d0882c3e02c490400d51750340d400841040f045207000f54945014202c01e1a2007003c40c240307100080d100d1180940300030801ca40104607d48514800c002e040b200c00c03402171041c0184003060401034503651003450250001500c0290906034172a441003161a180c0042c4d592034111a02406030909a80141c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 92075225 1250 92073975 92073977
    0x30d1e050d060305010203070f1b03080405030c0706020a03080105030109030f030f060803040b07061d0712080706090b160801080606060f040302060304031808150a020306030115094701 81
    0x380701c105031480c1c051242c6006584200d0005981c0d050194001d86010b184545040401030380070214007880a0a803800702035a94542400c03030164649262040c214011500c10501e144600c0000050f043d50000f10218450f01030303151016607076214401d00d0700381d542948014002c80d4584802d540c64a1081d0320030040c2820000740000c03041d44a1340150b055030703c6540f0004800e5404503950080c0800317072181040203414402c00f8011400b603450081d03203507001c500c1400e200402c2c1e02c2d9030206010f2450115221558400b801f00500340d500c1c60710006031030007540c041c91004510804252500d00980f000c40c140e86003d4000c0400789c0c0c1d2a010420290310003d100305a03080140701c004010784900000d54043ca2003500d03002c0d01d034030f51440a41c5096105078401400d941c80003c1e14126540880c0c4081d8002d1000c0c0805070303480c1e40e100301003409004803e61640c800103900000090901c06940400495030105084c040d87c43c02094040824058035602486981440901e17001425800e0f40725400c41101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 92076475 1250 92075225 92075227
    0xc0f02010c020a0b040501030b04060503060402040209060c01150603231501050c010e030a0e0d080f1b03190801080f0303130c15030615081302040b01020102090d1b05030d1e05 77
    0x1d0741c1c00b00c0d407411000d0384214040c00003c20140220741c0c02d80240d40c41c00c1c200351010000c0502d01000a541d40300f01820186c003a541c005a103a9258441030300711011400704c40e000b80400342003040201c40c0107040b84a1640028a054061640c3c0385180500340040b007901e100a420b6a100c141003071026100000d019410301c0010484070034400000e020b0700d00000d0100e009580c0360744205070083c0c041155491214400c40c410341c0c51000050003c82034a01401010b001c6a0300e95600c5002e03800754035400d0090341003c0c80301003060004401c441c90018a8604143e445102a0740d9406001da0b403501d81e4002160075400510002d64500b100c0301c1e08135802802502500181075444400c1031550000c070b9580300000380c031030b502071051a0210540c600518154034045100d4505060b441c421214070b400002c0c4200c1e2181d907441510303032003501075404010b80209107500c40072041c60010610040042c80c640140031824002416190100d505c2444400c0e41d242d10302c85201c0030100c1e030248409500300c80e0911030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 92077725 1250 92076475 92076497
    0x160b0a0818250602070614030603030d050a09060b0616060b061612030509070f1205070e0112020f09090319030905150108010b0a0609270203090d0801080d0c0f0201 72
    0x10708000c0030760b004191042100003050301c91116850104540c0140b000e641c0005002c100c80d640c49410b8942103c0074041190f01e035111400042d00710310a6542e004140c03410001030000c07038034180c3c0c00f4806080c8900000c04c82510381005000d2540210480303d800803030b07540c4603080854107c0d00300300015403008003440e00c1e01814100200120b11402020b84000a2801fa003806094040c400e80e50085d04801c000c0c290103103442a81130044000c0d005805036103a20b6001e180400500b000300c0d201502c0301e40900042580c450052249001001100b6803090180320307141e0206007080c0440d18000c50b010000342d494500100000d8620f100b02203080d40c10183d0301c2944201080052005010101c01c2d6a0040519490110520f0a41c0d088a20303640c455082e5001c2041207030f03041420381c0c00b03c83c0c46c0448094001280010a811200a0f000b403460441c000000c1000c1008045000c5440c0403483d06c07a140c550341c0b2011010ba90398082541c0a0224441052240100e0b0001d00781c50341d5203205150451840c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 92078975 1250 92077725 92077771
    0x40906090803010501080901020702150d02131403070509010e01030303051b04091a040b0d0201030c02030408030d090203070803040e0f10050316080d170a050c0403080705060108160b0a08 82
    0x1400d00c10291404140400184695030344408000c0d0401641d00c0203500300302c41500001c4100f400103c0c00450b185000840209040c82a0192601030082858002c10306580f00e94039403000038884c035602c1c868001c03550b002c5004c1c5071000f44203041c2d40c3e201c036000c0d40503800e6540680080c44094011144008071160080303501303658400800103020080760200724a8040701c01e990403040291200c034441c50070000c0c0704003152070b03444034006010340910b0007244000c0c400d01d06074158400d64010142c02c1c04000340309a00c116440d0405035010f031080d000c48000303581c1c0711920394480c012030042c0d43c1000e100034041000c01402c0c3c070070300c0e8000c0110a06e0b45010b5641d030b00024500741d190f004003d416000ea00d0100101030083c011401155850f040c070f0000300e500c1e00702030390000b00700510700740c645641c2e403020482546440081d5405541c0c031038039079590352007030f4185199207010034803500b010ba00c101c3e256500c440e10b030019104112418881001e081400f100419a0101d030b00a10544000341c40d0f00c000071481d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 92080225 1250 92078975 92078981
    0x706080115031107150609020319050403050c07141806010507060207080f0a0c06050601031b0305040f1415010816090504050c130b0a080c060a080405150411010e0f0f040b040906 78
    0x1074803511440d000c001c8105c02840550350705a0261040f90b00c10b0040114600300c004200c2200c0d4860000000c2300d030744d1840c0c203039180c0c00342d0000b24105100e400c0000c180b41e0141c81c43e118810004072190f242d8a100041c4450000b80129503607800602e044c4400000920301d500540710080c4141410b900300061031401c2c007110380010406500082c40d070040142440320354810a501728a0070305c1c0600400611149280a0582039801c00b410582e031040024244141101c0c218003c580c4921080018200201503030b50710f2140300d48461000e145480005100e100000310352080c00400d0588101c028a004c10900060800520981e0035011b103910351500c56131910b001510400740c10031300141148010040c0400c03064190007000f00e030b0b07000710040011a560881964070320354403486c0640c43d41da5070703181440c01d00020407501d034400340f8400140420803a135003580c01c260703190a07a5400000c7c448101040340c3d0711a2590b0241e0070088000840030300d400c0a070000c2d000003a001c6e00110320f40d21150307a03041c12 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 92081475 1250 92080225 92080237
    0x70b130b1303060c30060b03071107120b0a020a03140108010f0c03060e0f101206050a11070c18270302060f0411040b010e0d06061707060801150311 65
    0x1012101209008025161283c070398059050728000302e1a08a2640b000040031000f41071440b074400303c24440c20150501d1b00a480608029900c007512800c2c681c00142c003801100320291524054828041389507032500c1c14003c8410f4000c0075610352900c406041030000e50080c0415003c0585503c1c10600109000a646000303106034030001076503020784890030701228080c0044c07108050070305004001042c00c41507440c0e0004641e900c085516264001c3c4c0c503a000c07001d40d0140c80403841c0500b100c42032000303d17440039110b0300900030709101c00c091060440c44a44101c42c001400c640ba0a43c0c18041c00c4902c4a00c6d80481c095040002001c41d03070001030b49584941c03910344d000d4800250001004142c2d041c00300c0c1d5004403422443c1c8240341010350390806a0f0505852140c0500d40e200c18950013a84141400c1c001c25002a001115502c41d600f0000301514490151050080c1422101c00e40d0302800201f0f4421240c2940e90f80107070382d084c400c00031a20482c080c5100d04042d101d4898500440c120401005c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 92082725 1250 92081475 92081497
    0x92a09060c1e071401020c10020109020d11041404020d230f010e011103060a0e0a0207020a0b030403020f0c010c1b05060408060a0c05040614070312050c04080f0f070b130b 75
    0x2200401541018036200f00e0307400840721000005180301c4640d03000100310842d074104840c0e50800e0604204100c0c01081a50f8010b58030000c0380c0004014000000b401942e808000c2e181440411800040d04440840584000b0b4110050b1064040814075107040e050a08110724010380d03203050071181a81c40d0003d9040c1a4625954914081031900c400740f003101d200d03001c811002401c40c580407002405402652042540f001d01c43e4000821440960381220080da90080c1074240c0c850b183e44d00707070f4400c4e00101c9086016104e0801c5400360340c40000f9030b89031416016034509002c0d004940d2034489511303c4018182c4448400c3c1404611651803002a1020341003410003071486107400c000c0c40d02030341c000c444104240041080140505540303d03c40391a50165110400c0e56000b040c581210300780c0107043c1074a40e0924200a1141c1c101a10009000700c0d01c07071000711034008100800003905d0f00c1e03450340740c000c840d4801c46081000c031a0b01005824149030400111028540c0c80e04400744a030f0008000311 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 92083975 1250 92082725 92082763
    0x61021060507023003011203030b06040b090907080408030c0703051b0102070209010e04020915130e070812040b030a0902011b050d0f0203180105090d02120102040302092a09060c 78
    0x40e4480000b0a14000442c0701c0810b04c0708440380c030042d071451621041c0a04070007910f4180d004014540290050041c1c0724005c0e01482e599961010091100d80000300454441c0088d040414140303403207482603038029078022908503d16115401030003441d5214910480901006200401c44e84101c810800c01d408442c5002503583c8031188108684c0e414160816440148104103100150f211841100d030f000024508401c19049000300003036480501112507107059040c400d01101d141008140c0c1c000700d81c075400894841040803110f4501c04d0050b030240c41e00c2840203000081a401d0702e500b04841d0310b80181080340c1421120003480b0040c04d9044810b4a255000c0d04852020070fa20511180d6420701902c06541042540181c0241c1c900705c1c50742c5c99041000220f02d602e45070303460307601d010b004950090211405016000085001c2d421034401030f44616490b01c001003264050301181c0103580680c00415403580c4a101200049030407507802d00d504444144809155041c04220340401202036072030070317 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 92085225 1250 92083975 92083993
    0xf0515060c0c041d1c05030a0209280f090e0a08130b0f0405030709050c1b0304080f06150418080f040f030303020903010c030b030c090901090b01060f09050306102106050702 76
    0x403502c0c00100185c040307001028041500300036035010040c0d13500100c0300080503a552801c4400600060340d0202d8011b07000102000c100300910800201c8804c0710b42c001d43c1414111f940740041001c8601815031841d0300e0704411901d80014072900c000303210031b03089294400c4455442b05048103d42e00100207850060000007001d028510301009010000d084000703040c401440e141180017142e00510b03400108201c03901004007142d0b04144103542c00ba010741c1040309c1d5a100140006640c800b01900d404e2000104510264154101400390041850480c1043c1003001c0142d52004c44030790107003104403040384042c00b021030f65101c4c851800004500a41d400750303c0314140c0f0101421941e244003000249490001c0003005901e000ca00300c03400c0710044074040740e507a44500c8030707a014000310750000b001c2d90014000814040e80084180f991050355950301d03e1415212001e0682d5003605440d441e00b000c10007501002540e98031454078180c07400da200c54607604201548d0b20800d031782040d02c1d42800340e0044104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 92086331 1106 92085225 92085281
    0x7060c0b0403020f0d0e011103030f01030b0c040504060b0d0b01110c0d020102030f03070305010305190b06060705010216050c040e06011401030e03070c0e06040f0515060c0c04 77
    0x43d5017074072170150001070011001c0c00d0060701180c1c0c036050850704001e000054a120708410000b513800303a421910344083c00d46000340302c00000c080820000c2a107486602078080204074003a017054588102d1100d11040c1c6400c1e61142d41000040c1c3e102c0070200c04005540c00300117100741c4441020300041e00040f420b500c1000620160140000280601c00d07600d40c0c0f200f8102c030300a201b43d4a501c0510300c2c2d80e00744400200400b40050f040c0c000030071140d203004c03802400000c1c41400014a42074246100650401c01810203803002d0300f281c0c80c16502400d1501643d040500140058032482d03060825505031005207009150405503651451356074040c0070421143c4468003c0b001304001c5948810b03243d8038a100b11039180c081c80c1006e05000a54045020302401440e000e40840788032030220044c018950402e0800307005910400715003001c1c94503184600c0036420000003105289500c0f12030 = true := by decide +kernel

theorem cover : BRFrame.Cov 91906475 92086331 := by
  have h0 := BRFrame.cov_init 91906475
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91906475 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 91906475 ≤ n) (h2 : n < 92086331) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
