-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0488
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:03:55.499144+00:00
-- url     : https://prove2.me/submissions/7733d603-0fd8-4f5d-aba3-c231bbc753c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 87589929 ≤ n < 87769785 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 87591179 1250 87589929 87589939
    0x8060a0f0e1819060b12162c06061608040b0a110d021e0a0c08010504120309031421040b070228080a180803190c0c0504020f04030501021314 62
    0x111003007079243c1c08040100703810400114105090400203505560040b404114030320603031000c201c80e08500c0003804100c0b4001e40410012102d82c5010240305d40d2003520000031100403030001030031880d00c13401401011119081e20420000195038041407503005406c200342264005c41c2d5050010f9210502c1740090308d02038041c115003012001d02a43d6048007403100304860140e621494a0010700300a84e90285070020810186d00e90703a00e04084c02003000365010ba8500d42009220a2000c5c00b9000d2419501d0349036a9040c1941030719141c00e81c00b6044200d079246000b00000d5a25114502c4048050040d80600c0c0c66400c64104500064500030070303101c030043d8800810306049034504104840f080300c0d640003604c10390f49002c024411640101c401c12103140400c5c60400104d0b80c079030004090f02d204002c4034001240c10012410a0b01c0105c0407400051910224500500040c00c15030040c0901002c40340520b42490b0322641ca036030030383c0c1005404102410300b140c0c082000180480b4040c0c021842034070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 87592429 1250 87591179 87591193
    0x20304110d1110020c0402030a0e0f030408030a08040f0501020a0e27040807060213030507030201080a140a0c0203160308060906060306030d030504020f0a060c05010509010e030a08060a0f0e18 84
    0x794100608403510302d41032040d25103002e4800818024003602c010303110028021552440c2a0300090028185100815078a10607143d03005a0316400000300c030706903591076009506108441d002150000001841100c191035a001d00c0c00019100340068081c010560b15400c1a0907614010720404640465064100d841501e100c1224414100c40c2107030042c3c2c000541700d80e151928140403019200342c82c0170109155000320300005000b008580042503034401d90b01c60042c1d8485040ca1419207400880c4001040e400c0390100d6a00c8605903c6000c5071101801900e040400740c3c140c400c40c001c1002030684c00b1940401c1001024a08907a035a43d01410403202076041d410b00c0d0000c240d072000c417940c03030209160b541d80c0410150741c1c802c0d20200c0b83c0c040082c030681e203541d26444020964403425200b100e0300d6003804003003100900117014a024442c03840c0020350506241c036400315680701000d0301050308030700c00e040081031060b044003440c000303080c4280406809003402000d550b04505150701600c040d800c086 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 87593679 1250 87592429 87592433
    0x5090f031f0504080c0304030c0e060402090a05090703060e09010b031c0503060909010603080307030b1003050106080c0a0516140f010207080409020a030b12060702240403030e030c01060801020304110d 88
    0x211581151001210002d610f0340c1e00c3c0340101d00342c0b040b101d90f83c43c0c0d44404100001049048070b200b80075158221083d1480d074540d8814001030740603030800c0c140d010b000c0c51424025420b0081d00341d94820703110316010610301d50f81c806401c62050140c0e941c40081c0d440311300c1c141e00c0303090070042c0d40d0355003414001c03030415104551001410b03030001510080c451001e0902017118010250064409503410a04503903580c102180d003d0b00814814407090b0041c81c40c20300c540c0c029070080c840c86049500355220500b079035940d40b107c50340325449446940c05010003440340c1c0904850403011002c816210380c4051480541100b0103074039102c0d00761004081a030040050000040740030040d1022122a44809070300c602d080d0a0640181003241400c50b0410003410310040004800901d40740907194a80a44220b80490180082c050500f076a0113100c80e40307130001040001e4840e90100c01080205410340e8140345582c044542540c1441e03100010b20781d00842444103100c080420343c1c1d0101c07011038004401c15450703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 87594929 1250 87593679 87593713
    0xe0705060c0322091404171603050306011101061811130b0904020904180b070311030609040311060405071e15080c0d1503050d0201090201120b15070305090f03 70
    0xc0c0007002c0d054480f900d05500409810040005010650814411086491108042803404039400c1d01c0405803403200c840c0c910112011034181000340f082514070740703036640c034180d81c50780c03000c2c0c4428100300c8044c4408802880a01c94000074260500c0311103000700007110344e81c082e80c0d001d560001c0c0401d01000a5600303506514074180894141000300340d2507400c2100060000d0040120042c0c01070306040e20326200c007800f08408007040780b0802e1f10307603126182c100e012405c40e105030403181911101000411803a2a000407104e0780700303101e0b103818500c0100e18250242416011755089841e58004001400240d035050310120744000c3c0241c03810440c62030110390241c5040d0701e820000a002e8188045080400003e013150740410280e0400d2003142c44445684c40748441034401a82c05010b00260484150301c180140090b09030144e6a2400002e00411010000e00ca0503c215501055041c4d01030700ca183c0711009400a5402500d80b079413180301381c40038010091100b4072018480d40100084e9107200c0f4807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 87596179 1250 87594929 87594937
    0x10501051008060d14010203100e060d0212070305030a120501090b01050706050709090e07081b150307030612080a08150a1a041d0603120c0601060c030201021306030e0705060c03 78
    0x520b44036180d91591008039051881c039003805042044007889091500105400540c0900c000b8144160f0342640d03039140101e0341030142c80c10303075201d190510300700007500d05000a2000c21088009482145980740c0d5042e146611402465010a07886420341103038014a20609006100680d0184941301043d000200340e4803c8080082030140d4039808218860302ca503d00a000d0040792808018000300c405803aa51046a813040308580e2103410f440310842da489103c1e10500744030190242c1e900c8007440c145518643c000030401e038105541d03030308001520701d492501402b01d07502528500c0c3e034400c4c0020000704030640040020300c4503484004004110744401813580d0452710303600c00e90700044030b40d0001038425101c0c981c0000840040c803aa01030218107121b05180c01500110100c0761411008850f101c158020700c900c5540c1030704008010803800e40280541c5d031035184a880014035020740c0c00b41c5e507100308205070010400607a40d28040e016010040010201800341150090708000381001601e6403031003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 87597429 1250 87596179 87596209
    0x1140f01052a071e05030a02061e0d091a041a0601020a020d0b01080601150903030e0a0314010f0c1829030106020303090c06040e07080c0f04030b0405010c0201050105 73
    0x186008680040c0a034804071000c6800c0001c0301c0c02c640301115a90f640706001da007040c0084090035200c0c120020100d1411680c001d40a0404010b00c0e408206598018501c2050101f80030812901c2058843c00100034582150000081e4040c160800300c0e078181c101018019542c0b0b080090101160107a180c2400e01c00c0c44d100b48620036551000101e00b040001c26000750804035181144080041d8024040c3c16684003000326022681e84822104165042c0390280c8082040741c003051002c03d1085500c80e2241c500905070080c1580d80703903900480c004070b01c9011090345e5500c00561082c01c4290180d4182d1580924000001c112895035489807003d4900c940c04501301c5000c0d0000744c2081c0007d0001c40141d1090b04c1d95103d41c2e483da4063b441c0c3e801120440524050102201c45c1d900c1c00390282e9041e1102041c1c689a2660b404006036080400a405075102d00340500c4102d01c03080b445401000030f1442403070710244504061030b01509603800e00e07034840e0669040a0040c07110b512400e02a5a041c0e07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 87598679 1250 87597429 87597437
    0x61b020703200d02040b0f060d09060513080a0309110d030c050f033c03070c05060f01030807060213080f0d03060f120209070c0209010f050f040507120207110603010603050103020901140f01 83
    0x45403c00c0028846403a0300b006e503412480100d418150307509c40e54000e405460083c6c5051102d95036001524030305c1100c030400140940310500c440e00426210ba480081b4081c412410301459814010000384800840354044001881d411002e9082082c1400f090a60050081c011400c0c01e0200d00a031820304c090350060410345030f139484c1400a84c00703200f460351112410600495079900b4610b034014030f85d1400c00e005503040e204070404a20403032940000355042380d40042d102400e2004640c3c1c0d1102942c01229032010300a1040404500d08000340200e040600c0031500071b1000815501c0003509a03070555124072258080c81c0010030640304c0740d200c40c40916a0448031001d890340d6102c3e09442a8001150194100c2c4200f0000b1a070703480042282410341c1d00407110414900101c82c2013200b624030071914200052103165050807056550b40240c0301003440760185090341c09100300800d5043d00300b648880006901c41004005505001c1c0d4454013400c600e20040c044140c410300460510340f41d520400b170402c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 87599929 1250 87598679 87598691
    0xf0e030d150909030503060315010503030f030702011e0501090f090c1502030f0d020301060e04090302070911091e01030605030307051207170d060302030618120304061b020703200d0204 81
    0xa50700c640c00368006007640748010054a1420b0600400d19041101c07014061710901c0c101845440800300d0b4181200c2009005500d01124900d4060032600060850421b642d00c0e062210900c9461000c0200000e480680c0081c9545c500303018241950304005003454030310700d00401c03000415003001019080d100201943d420524186504074034512800001c0501c00001040044010741580c00441c1240c4955441c1040014002c04100480c0d94054000700582c4c0301c6071042280010a4101c11110f1101d110002e0070401000003091452090100b030403100202082c6c1e5aa456800d886004080e00095005500b420342582d01e141c2e860010101c0321a1401002c87e03010200001ca04803400180000e031003107500d0b0b4105d81213880c0a8901800308921901900300004c010741d8682c0a07012180003602c00503c002800141022a11f52000d0425181180c4801c903105000c207a40703c040c00241100e500405055107941000b100c00d580050090074078031546041c0007142d543c1d494800014a40459000601c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 87601179 1250 87599929 87599951
    0x6041a0906151c0606180b0711150c0f0d020601060525080d09050d1107030f05030904060e0907060c030e011b0c060201020d0f020a080103080a0c060510090f0e030d 72
    0x143c02144224107940d43d26540c030b088581065000f070000c440e2030b502c82260f404441241d9050118103801003072980d0300c0620040c00816007001e140c00010358040d048054a030a01889540b00340d12038000b980d501c2d0310000e0422801982007010040126051010708899410020000d000340706580b0040c00040004500a02d140101d20f1104125035000030095555003c800f075070005464600340544007030240310050304200d8010b0703007140d403031074a0720020f0100c5600710f40d90150300c1c01c03007c00300b5100c0d444280900e5440392140d01c80c81d4041c00700d40a5180140c0ba1250245240c00780a400860412006d035110400281d0810700c80c21000300d09080600c8005d00204402c82c0c401034440c80904421200e040014209030194002e2a05942201c001d000b0380410303002e59402d0303100d06500310000903c2c5000401c049070341d0401601d4000d40d07901c2e00d010b40e82d1041d1154000e80310140c44a0440c410080410800040f09201e0020a00e86504040c02869000c8240e2900d901581003418001600c41c1d00c0214 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 87602429 1250 87601179 87601219
    0x6051005030414100c02010b010f091a09040f090209090307021c0203150103030909270201030902060c030d0203070806030d080615040315050405010c051314210606041a0906 76
    0x5400150504a4255242c011303c000080e251040300d50004d546804e0001007294400d812400281905072100384100d468010100b80c10f9006260002c16900e041c0286c40d040d0b0f4644c010881c44d03101e09603011550400d540100314541502400305101c90f44200b20020060b16070030001c51102602013040f0007091000d00129060160311006000000c072420004010160002c60f02c409980c016041049400a035001c000d1010b071404081d0f50203207402d650705000540c482c2d004902642d1001e4503c5040040c0c10000d6869a040400440c10640d00403040182035540407807826800071084005120141c40300b00c0107444100054000c0d17008221f1250b00c180f408003244202c5000b10791180b00f0061000343c000859004040c00c0d28125169400c01d091900070a200700c0907907a04448a071740a81d002ca01d40302c03808916401a10040ea0022400002d8012400100c41c41c0034140000401505c040c2c640300e070810003160700c1d0100c44100c1080380310642030300381c07141c0700703002c1e404503003a114004c013042065211a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 87603679 1250 87602429 87602453
    0xf160b07020d080d0c110c130c02010603020307030c060311400311091806011403010b04050c030a0e030a0207050103150305012309010501150309020a0503031605070504060510050304 80
    0x1d07004000c0025184c213450890f91101c1040d508a6591181c1c0d10750160307225446004d58030072203622004580c0d8401e8521020f5111581015541c000011500c0e40e90b80828100302c1260703c162054100c1040410615416015000007201c3c0501e000380b8001d400058a488200f10030400003080882085010100040380c02103400a00ba03030f00d0541c00d680e5246065006c807061800b0706400380303028101040c91596065040400f18000401030300441e801d1515101011510b034844c56455074858181d05100d03210391181c180510110500e9591300d240510102e0107607840070815081d680d00c00c0140b184c201344d004c00e808095520900e800700310303200d00319165000705400f5000a0155440c0500c4042c0c1480001071903074803d00c6000004480d80d0751003040c0c03400c95500b4458141588000080d14140510a50107080340601c003c00c1c04802e1910343c80402d2031b503003040150a81110311482c41c00300303028003000280000c100885090217068140f501040969490b49880c400f400f07030220208081041e00e40c500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 87604929 1250 87603679 87603683
    0x301090c031415090f0c0906010512091006030b0609060a0501020304090b06040b031e070e01090509040201050c1e01060f050a030204021c02030c0d050106170606030711010203040f050f160b07020d 86
    0x60f0405081a407241a124041400320b150f06110b81d401114131814001358562090b281610b5140c1000450350100700f0740b0300002c01c813100c5406600041c10816010780300d040c0195015468042452502805012a411000d001d841c1f042641c0d0b8002c20507a0f80c00000ca609590184801199086001d00450030f14040c507000440c1700e07200401041001015004805034109034002076902d20b0301c031101700740e0b05a4060b0040600280c1c0140040c081c0781013100641e41c0051062600701d1038010340303a41040c2817985803e0b00e10b0010401e0701e06c486030600240600e501070401740304400051b03884c20780024880310031407100030700458002c03031182d5038408500e4072150512204081550b4900c0c100c40c80c52020703170284111050a0b1700d88000407aa00e40300304038664061300d94400320034036511108204100d0343c2008041a0411a95583d003429544084c000b560050f032056410515420b1107150060900412822038400c0b58071100f41200c100d82c3d8000d0b8038049030500003130329694038201d00110b41d6941b200000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 87606179 1250 87604929 87604963
    0x3070f03050a110a050c1014030a2a02010903020601151d06120f070305160c03120612050616050313031d0603130203010f05161d0a0308040303030b0301090c0314 71
    0x80542845000304118000d0b075021642280c04501c1f031007094034030300e00c0ca0521504042d01130001444010241d400544241c4d0411760041046040d07a180549041180d190140140d455480c00400c25404102d03c60140003520303a031020800350010000c0c010003586125204058022000142544840303003141d414410100962001e071070a2000508410307400e642d07080000349804001488001e0303103211503c00b10520b68842c2c4030050603480c1212214102c115400c651540c0d640f002420040d425950607441d4402c0020f01194034000d003440c038216400c40c8580c01401020410028041d802c001040d07542c0740e0500b0070410b42210f81040380910480d003211590005000000c1c45003030890803103c1080b40d4403c400130f001c0402c5006000c026500280c1d4413507040e1051203070b02e81c606405055491603404200304903d00b8003040380005080a141d50f403080d501c2c0e01c4002001d2061680c14010000340d00c02c19070003030220302d460340c1d07500440c5101e9200240c641001d040d21092181ea00388880e60001c448640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 87607429 1250 87606179 87606193
    0x30a110f04290102010605010503010e070905040c0e03100c0912050f12031501020a050309040902060c0a0f020907090e04030f0e04060f0906050d2303070b0403020d08070203070f03050a11 82
    0x45100281d840424010a4400b40c8100c0c2800641c4140038030815a05d060751031600b143d18101ea44224440050f0142090101740c0c2030114880d01c07148540c071034451a603514820121003081c2807508180e484489050854100303600c0c0100d59400287c100c007165400306003c0050784e41d41c108079041209a0360440450701038441c0100e0503200d40400365010303180b15043e4207001440f14005a03910480d0f03000c010510b0700b0a0260304028a4036500c00c5040500240c8001d140102500009040020001d4225804440d23002c4607001d60900c406515406040340c00c281840a081c54a02003090b18014130003401c010540002c0104540b00b020840d07c1034002400600103517031601107188507003206010312900c45290030000a00c528140056401681e005065185000882c1881c03047d000032000b40d0800a00c406c000d00ca00007200041e035117208502070790107030500d1618010000c04840003d41100e04551042c0401804150381c8090646125454180155a20315001040d900840b00c1410a0305d80c0c09004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 87608679 1250 87607429 87607451
    0xd0210020307200126011a040e0a1a060f041a07020d23030f0316020109050a031707030903020d0309030201061208180105130306020f0d06140a08010209030a110f04 72
    0x61020705401002d885640074400003401c0e940a2410905d401d007581800540100031070f5100080003441941c1d40900185081d4807801445040300054860790303422581d4162503100d801007035010811502080307035003d02e02505a00c0c3c100250081c4d0042c03a2401c251400d40e08111400081100e010b240c0c00f0341482003801040c01c00703c1040810800c0c2219007812002e40b440e941001104652a4403000c0c22802e05546629008000c8c25801ca0016401d565841d800a03020900c1040001c24080c440d5407605c030440740164840e03031710f400d01030402c00c18141030051000c00660041082ca42e005028640040c0b60149424100e0140c4080d0f401142d0350504208801d00344428480244050390501c50401120301c07100004480901c90113408030040e00d1010310500001e0b206400825401c03d03598400e03401d20076401280001c0712403d62001c07d548100580103040c0c0d00705034030b00b5001841604000c41c1402c1003800801d44a105d811001424040c0c0702d03d0f08a9585e45949840d80880000742017004910460 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 87609929 1250 87608679 87608723
    0x405070e040b0102060105100e130e0d030c0306050109060c0c05060309100b0d0203030405090405030903061501030e1b060a05040b07030503040218042102010b0409060b0a050402090d0210020307 85
    0x50a000d03004504100c0d0030722080d400081e1890407141d002d01200f464000c202801c07100d12074001c850030361055029002c002c4081247c01113203580c61104014140100d04104050201d0700c446001006240c00c08000b040340343c4e00300d00801c044071214102442010060714200c20f1401841c0c0107070350b0203034004c402d008140320002040c0c1440d92039a0800c002902200c4100038242d00c034800300a5040d40100401e1210b8149000346541252003901184c1c10403245000103418010115064504242414400320540d03a060041c04031178074001c00078008510a8170703c107207002a070b60104030740601d0000030600f2000340700e40f00300d40c01440f01c0c42c0115295023407803800400325403080c2c8007070740b044001c0301c1000c15100b1441c04850180b03501c6440d60000581c80c000d0030403000450584c980a55590b10342c440d4041d03c0c0c5010701c0b200745224820001c0c00e070442c0c00c1001400c600c143c224902442c4140100a00d54440000d101a826011540d04044c540b0f1380f40200c1c650320030000000c002c4101c0806880500c40301c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 87611179 1250 87609929 87609947
    0x70215041b090501050d0f15050405030307080106110703060c05040b03040b06121209040f0b06130602100603050312060a030f15050112030816050408030406090e090d05030a0b0f040507 81
    0x1c454240261664985121080d02e400b8060258080005045200011884007103280b50610801c1c105402c040f01c491024211407040fa4251519000007081003241580300207998003620701410b1241012034410308241e62031030340b404018030f420f54075000514604e010728113603801080801d500d140d4900d814500145004029642c60380141c3c101d440864603142d021601d880c013540d4409000341000710b03240800018040c070b8424070f00026074500c1002c40d035440b14001000c60031440f801a0719450300e4040002e14180740100491007191403c0001c1c80002c20201c00c90310508007000a048a5445010024a0100ea198401803a80d64192160010800c428031001805254004100187c1c0e0362410b104e0b52101069000400240c2f000d000507080c11402a280701f50380e1640c2ca4002e041035111000d03180b0b15401740c0c00441c0410f096010030000c50f0020058154454141800303003c0c0c0c84c018400c0a002400b02400c1e204050f40c032860101040c2d190410003100c660001001401765003050f0b107018100c804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 87612429 1250 87611179 87611213
    0x130203030d020d0e0114010302010804060b0f130203060a060914011d21060f0112081e0a020312060303040e22120504080c0108220201020f011505100f09060807021504 73
    0x420001d241e80c0424412403c07d0403250180c44400e09503a1340d590b41001001c160541c580d01a41c17140900e4203540300d00301400b2074034404140060303880c141103040018998150707000404021031498140f2a80d1104500820030790303020300300b504100c80c4c16814658400010046035030004100c540f410071851100343c94040584404c0c065034940c2c2c51b51545074801403802d00408540030031a524900015100100030311724006407000e01301c1c0c0300e2036400c401e240c51f501c14044c00c80140e00100350343c11003c035081c5040350042c80480045180526203407000f05140801805091404200c480701300c0100c501b286203c9120742d115800510344500c00201504540207030246020a1080c107540000c29401580f080303000e000031441003030312080030006003140c88804010490440c0140440a440701009008190707410b4086c2204442c034905100902c9460704c5203042c2d00d810003462490003004141c024181c1f4050b103840745050022a59a160140d141a1071348a1340c07002c0e4104041000b0910216400680340303a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 87613679 1250 87612429 87612431
    0xf0f0a030f090609051002011b080a0b0103051b1b1207030801091e1a09040c0311030a0809010806060906030f1008012a0908060106030506010e0a0806130203030d020d0e01 75
    0x301d0381104458040d454010140403800125003441203180c000162014201a88004540030500b49212514080e9140b1840c002c1400341e0140504140603000c0d103d075598007031900304554688214420080d02001d5100d41c2484d50026861b84500c08a1000811074001c1d00e04a481886021070810040d5103d440260300144101001154001041c02900b4810b00c10414480022402104241c01800740300c541c50040c44105041c1038054589401340d0707102d1402441003043d41ca2039410301407090b08181c4131591081c0c001341042c1002500d20710590725210000e10f80380055503208000302d045803080800711a807002011040021a60303c410b1880e1160442940303400d4090780c2d40d01c5d0b06007640c5223003c0d040040308210400c00c1052200300c0307682c8800c102906d880e46804d40e840350200c0c00c01000380c00c00c50000345c0314000c1080c0e03540c002034025400c9400fa111000c01e1898081040d0300c03001d000e401c0f04c4043c40038500c44015503030304209403500c91044030803c640da801803240340c80040200f81e079480115 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 87614929 1250 87613679 87613697
    0xc180a0b13050409020d0209150301060b0408011401061d0d0f05012f0d050a02070f030c050c010503010b0a050309010b030601060c021207060503070809010f050c0a170402061b0f0f0a03 81
    0xa05180c094030310001c5d80905104084891035081115444000748210355a2618080048141e6003d004101c018030000c04c1035a500c07420040007900790b4008951349588000c1c460010400954041c22400611582240b442580c3c5250000240d292000345406041c91500352200710034408194000c410031529811100c070307a1026030b0405120352a620584200b280d82c107101a4070250082d410165002403050001464065141e49058074480842d8007540094001c2441008000041084041c0f820003402d01030304540c5070989481c981e1048010340e00400c5800308c003062942109400908007030750000c060326410340c1c50700c80c000c0000c02c4000060303100f5a00090b80418680b0003150f404240c0c1c000750f45a40c6907950f0410b0607107200d0000341c594a15996030300145040300000d44541d500913a6240e00c07881d507404181500034020900c0c6019048191440f00522005990702800c680c41050002c040d4114072581c00099820003024601d03041180c001e8810500d0f1851011541103034081c1709072500c0307542d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 87616179 1250 87614929 87614939
    0xf0513180803061e0306060d020409050604050d08100513020c03070c15090e041109060d050a080405011d03061506040e0c040e130c0b090a0306020a02070501110c0102060c180a0b13 79
    0x404184ca41099406800c0040812040c0c24860301210307415001034404103514003c0d5648924143c002c4906441941040d20680d84040d03100c24943e41140c554017050701000d050000080c1c60080f035a02c1750407034650004d112824202d0034415a07450340c0e0000d00710040c26541d016081740100258540e80d0002d2096100410b4882d0031103000c03806160445406e1181744440d10500c21170b114040e0005038050b0300c00351610000340c0708010142d1030a104074805500c89241038009001c46a044020407c2c6081403107400361070b610002955075202041a010030800888140410b80310b1058dd004600100c442104024031401002c00420440c1c5110700c00e21a107507200c4d81d0201095183c904003d0402011006c00c010100c004009847c0c4284010301803040c91b9500c0c0e441e40c2c201d0344018240c00150300081410460b40d030300144c800303c20455400203070040846110000391111b1004108924000020039080d001802101e124260b8820140102c0000c1d6102d80c02c00030030380c20402e64010100042d89001c81c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 87617429 1250 87616179 87616219
    0x3060b06040e04021302090909070602010501170d03110d0f06031205030c03010b030c09090a090b0703020a120e01140f011a070305040b03040f0c0609030303060b03010f051318080306 80
    0x104449016401010390f0310382d0340c20452401c0034802e00d640b4494080c0722100059a42c0004e80740030b07142d128010840035251020282c00c0d924140d001a08202d01c040008441000105260b5800b00180c0b40c0003403807e00030390f65026180aa40b821024603450028040c55440c1c25074008400c3c0d9004207141c0e0b00a4290900496030b5101c2126810003a001c00c0c0b00420070340c40181c02454204c4140304001e400c01e40707454081703480c40d0000c843c10f0b00c665440b0741d18002400404d0080c0c913004600c1d40340035880d10742c2070071026009034681280e41c1a840c0d52407484002000003075101186400205541300354500346030161140300c41080c00340c80201c801411181708a001c440d001c0390020303645a103e413400c00d4a840c45420807070300300034005d48034040700c2581030b00003986448418001d4002e544030484072a00f942002400c071405030704026005001000140700d503690712039903032003160007c844040c0c81c414803182e55806003005400124003d403411740400c00f00034620029500c0707424207850060790802d94030349401d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 87618679 1250 87617429 87617437
    0x712050f070f030f050309040f0b100f0504060c0c080105090d020d02070e07050307030e0706031a04051003110a0305010e010c140a0806091b0304050a0c0518070f171003060b06 77
    0x450121500100f0000511044250f00d1243d000303600b070300d05008500c001b040641d8401101d0700f8400d5a6454000a80e1400204070f0025100340c0c07038684918622000d010304184031b980546800e0110004139441000601c61040001d0038100c0b000707001505020309141d5886044c094420091b01030f00741e10601062001400108030340403400c0c0c146081e154100199481d501c0a8002010541c60340110000c0c4003081203018000c3c00740b5a00005c1340c9400005512240524105041c130940c06c002c144043e200b0009041006c1c1c079000b900300c0780b0b80e420f2840000c4030038001da0f0004145500b40200f0580300b90042d0b200102c611041c1c0c0754843d404108442202d002c0c402c50490001107034030100858442d0800012280d80540800070720700304401440c09040c129001100d00301c510790b0220a81d10104480b403103902c402002c060703407510403c400a1100e6041040d00500350010056400440d143e103a02c508050500b41d02070315184c6016050040d0703002c4017207110340810b071400c606082d03038000b550408900325 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 87619929 1250 87618679 87618689
    0x10609050904120e04020409020c060403180e0c0901050903070305010c020606060403031b0804050d060203060f0904080406080402030a0b040803040b0f09030d0209062101140102150c0a110712050f07 87
    0xf003c40940c07846025291001e12003080f98010754280720104540010348010305a2a9000006107040c1c5018900103191004141c1c05001c18040a003007000b6040d840782001e0740001d0000001600c03a42c0c42001200d690003540500c0f58588030b00d60000003401010351180592146c00c1e429902070703607a0345080c03101e90310403440f00600044000c2030140e450b0003c0800c620a0f00e02c0307210340c03078900369546001840661405009550069002040c0a030700e00d0824030880c0207210a48112107070b03150030388502d056406184246000d024105000400319074040c803000007242d60009050503075007042d0400041c5600b0455040f1210f0b818400880d15212081d00700510030140940110f150030b070705601400280d001090180d4001c0018800b099140804a1512022a00707403d0218469890021081c0030541c1c0c0c005907070b0664000c40030149000040410880d80030f200700510b1561020480c008950458100b041c966050080c0c00b400704050540c101d100407041d008800f01c0d50030801d219196500c030b0300c5a11030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 87621179 1250 87619929 87619943
    0xe07050306040e070522180c12030e03060c030f0709030c050112020c0f1c0903020607061d0d02010c09060e091305070f0f180c0c02121212010609050904 67
    0x7240c600d41504040841c80900e0156407010b40da43c008500c030356249240d030309201412401c1100b44241c072441500d1492a9a0401540030402d5880311b6503076001e40d0051220841807200711005150040b0460f03680c0220190803a64645081c00c3d00c40407942090741c1d070310949182800461802031050351001c0c1503036045a070701e5080b9071800300150762303029150743ca03000400d409105000940c80300b40902805040044050440498100790989156120801d9542448a1000140007688480082d68851035001c030700008c200d40030b40c85080510301000c0d50103119106006006a95039810741007010f5180603a203074036032000c7d1204420f40fa000c9015207483c1e0441b40d200c00185402071100c3c289031410307004c0e100740d9226503100d2075012152002500050042030604204000b40c1d400f0000c4400c001050140820201c444403a00a00550b80141c020344140c03034190200320182d4040c85414154900800742c140e80700c0801c1c82d1011000c01c02d101d46804110b0f009000251424440030841c415540020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 87622429 1250 87621179 87621181
    0x207020901090e010f0608061501090f060305060d050a050a021e0112050c070b0108030a081e1501110703030804110102030301030b0a05040c0506030702160803040503030a050d0f180308010e070503 86
    0x1158070040c10f5042600c4425903c840585003c8091441400050001c540c043d22603407401103900114444070300c0030181007240c01c1030200103004408403c3c41c1500c0441c907005c41c2e030b525004009440d00b10504000740582c01400904000c12100098408005200369210701130308005200388464450452469400315902c84d8a400c090a0305601190388240701c0c1458908150143d164014542c400340c02080d0b503503000144030360000d070b008a282d0344d0104001e542e007002901c001da52280070030b40140c64002044010f8446070b1507603000d010503000301c00c00c0381c0c00c54a03660391b00d04004020317100540301692454078446d2440303510b51012040302d0589400504500507920390f2001000103180080c810b0700c442500100106103907458a00a5000362113a0340200340342c80943c1e402c41d50740c0c00307030f41d220380c04650080104005548002c4142e40c00d45e003003400c0c8075840d400980c0c2000050b00800b0060002249403941c001084121000c0030100c1c68001c1d9900c1846a8980340d5103030322b003072007a9405400b14000384 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 87623679 1250 87622429 87622439
    0xb090f0c10170c0c0304030308180105060d0206030604140a020a1106040209011a0f0a0807170402151315030c26010b03070516030302031b07020a060302160804150f030207020901 78
    0x901a00c0c1c100b40d00501013840c0c80d180100e03007801d54000e03401c11000641e8000c1440300d02c411104004005131900302c004c2180c1c1c2000c1000401c2c580380a60002c2c06142c0203c00220580d0700d942c042e40958228030041605860300f0240c810080d40b00100b1840846c4a82a1020700650001a00c034466030f4090304400c80c80e400c204d9000c0d80c0b5a000e405410b070303010041000150030303e0700001815100d541516a92682c0c204080c010b040c140740d201003101c0c2d9484110030400565101584a00078406200f0b4540e92443c0840c50401441c0701c5070020490880014210301405605900c18052014603170350701d2560031941c00a40300f20104411045030107490309001801030510280007103801c80420b0412901d0300b0340d5400340d19075190392580c0030f80c0030a0740882000001a0f1004d015800178a1001c8240e1400780d071035001851906281c008c2d4000c160340812819000f08846c503c4010094102c06066201c43d5148091126140b1840444000940505070f590900e8028004c1c1c0300116401422a01d5580c248 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 87624929 1250 87623679 87623717
    0x2070b3d0b1e0a120f0c020d050c01020909040507051f0c03050d0e01050a090b0105010207030302101d0a05030d0f0e0d0309111e030d110307030f0c0b090f0c10 70
    0x510a2107125000001801c0340074a400e4001d00484a0b10303180d070380c004004c441054013110500b4038894401c80c101504a0a140e5000c11402e41e04565414504e40711034030300d001c0c3c5009000398091107400103004002d00083c070034000f5005048480850f800f401141030905050343d40180e41034500c0104450150920009004001601c0310007949900003a6030540b0380e6006080d503200307482642c03407a41d403440007005201104686501521080c001020038620315075000359200344941c081158aa9245002d402210200829161460780401250040440c904040e5180e9004140c500041881e0400818600c8203078081e40442c0c1f0226005404545400c00042c0d0243c41521011103181c27400d400e003440c2e0356844203400700940011400d4152003070766803800d051030201d20400003400c0c03005c140032101200da40017040b41c442550520344030008040c80141507a112818001c02424401103030204820402c00003410202001c4440880b00e00e000d102090080281e50600c5c0200000c1ca101d0741c2c41c28005103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 87626179 1250 87624929 87624937
    0xa0b090112051219020c04060f030305030615041d0a0c05040509042102030d060504020301030206030c070609022106100503071e05060f121e1902070b3d0b 68
    0x480030fa6611074500d200000c00ca0f0300489000e00c5001c07810420075a06941000815031a40013500c04002060a003010380c030402030248002810000000005446031301d9105c02c8810584910b6035441d159529049404201802080507040445003100020190245400303180c4a0301c01586236145030a0500051220b16100104283c0e00420101070340783d001da50340f02c001e0f2036520b030a501840d1101d186a6681c0241c1e65554841403080d8010320043c00542d46c1c142c1100c1d04a241d0076100703552004180740c1000500b140301d001a50180c00580904407065109011a480007800001c0e511035569450311480d04041c2805419010341c0154030a0100c1f00007018015100e2440c0c2c071025204940e10400500164000b90060f01c54150101d10004030000d00180c041c1c01c41851019403135081c407507000c172032080b0800915002d22071900b4403d408000100e80d048a01c041e81010400d462860031030407042480115034001e0316002d10298114001d18074081d211a948005646111b540900d800d00c808000c0d04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 87627429 1250 87626179 87626183
    0x3120c130b030c09030a03110f06190c0c1502030105090606031314150c070b010501051602060901050702040e060f220210090f08010506040c0504060f0c1e06140a0b090112 75
    0xc01040000801d503170400001600c03500c80d554400003441d400c2e6190703080000603002c0038007603840101805058800384030354030344407800d0381c1c00050301054a0388110740300034031040040c0403840041004002800b65400070340c143c52094072008142d40307561003031040e140310442d0140c900b0080c4054034800120400d40aa04241c1e5040803105049034084501580050642c0d401d024804000795810422034140d07a554018882400c10700d040c000039128000080498090003031240c04000352a0401d0307030148099425440d000f51013000290030100c012541e540095a0880040c581d0300f0029014801c0e600d45000002a100f011030f44582d8940d09011100d403541142d0740074402c8030700002c91030b0b20259401030014452140045124100b10b000d120440f01c0e045424410844104424000c003500a22111500200c0e07143c084201009030500c2e00f455002e00e00700300c0d090140c40100034240300c0d0580009901260000341c170340b4a601c411111000300d5000110490704208030340c0c010803c0040a00b00c0c606801c2c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 87628679 1250 87627429 87627451
    0xf0606080402030c190b0d050a0b040b01080112080f0307021e0c010c0b040804050603090618070b0a050a02010e0f0d0206060409020a0e0702030f13170604080301140301060305010e03120c130b03 85
    0x5600c0340030b8000c0307c0c1c10521032040308039920400c01c0014182e07030043c05041d10083d00c041080c0c1740c00380002405042d05004140000242003406010450b801c01150810124545115100e040001c0b000307481d480000c18248800c0c0200750790644511f0042080e0320001c0050315030100142c92a6034090345800300800c242c03000b0405010003d40781c0c80e0600118841d4484034040d101300c2c505141602031441012030702c2c0c40303503601141060042034520012a580e14505080c05d507141d204608003240500352803241c40c0890f004031920644100300000f46d070500400550240c45480c1d646000744000c50b0450710000e98400c03c0d00c0400c1000924a0091725009076462060728030740350009a26640d1640000700d1040015403005040140c02d83e51070481209918143c00b6001c18103041e1500482d501040c055040e0348085241c4481e0250307070075400b42c0011644000284002c18828524030703281d8110b101c0005660400000180d00c000c04401101c501640041c45c003071071141800144d00158100030a084648 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 87629929 1250 87628679 87628729
    0x703140d1814030c040f060518010605030a0b040b0d03030f0e01091a090a0807050604022d190f0b0904180b0708070c0b0411100309030c0212070b0309010f0606080402030c 75
    0x242c5950046d0b02c900b103801640866440d140c80c041c0026413491130040d0825180c0207005001d00d582c03200c21250412622640800c0508488c0e00103001001e0620410b03a011109410510805400d41c201402c1c0705140c8000300b02281030900c2450a90310b074803100a01c090b03501c00040c010300c2c6184020a403c0031194085900d07030503041e5500d0b50325030b01880094600d6071280042000314135044804010140007242c144020200c00190903c0e0b900a603d29188102c1080103002c401e04585542d0174001c0c00901c0001d40490b90f140c0f0340948550260043c2d502650078008035140c0c03559800c40709469250303c00d0b011681aaa200000c2320045000350801003001a401c1c0500301003031008080600030f0b4010005003601ea40304400b0448182021003c0760305141c2041c48807808650089030001c2155015a00c15080b0f40d001c0c0394030b60509032960401c0d80651004000d00001a8055010407412040001d00b0054140ca41c1401c1d600d00c1011180254150720110b02900107090044640b01e018560f420789442c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 87631179 1250 87629929 87629953
    0xb091003020306010902070507080f030903121c0e032223060418020706020f120f10030201030b040e0109050601030311070e1603090204050a0c080f0103021807050702030703140d181403 81
    0x6101102f4990310081e403010031085034600e414800950b0107c04407020078038100e0488940034050312481007050320959200c05000705402c00344120b03000c0480c00030801c41100d40410808180700c1c04ae00980d04074001100c1c260300d200501c64070500c91000020002814149400c841e600341010071400e008a041d020b001c07080000f00c82d8000307032031142c019207081c07a01c071010702d84031203100320001780b510a0f004659418460240d03032401c040e0042c1c0340c080c03034080f54009090010501030560840003200c1980ba061620040c0308011503038506a038801e99682159410381c1440540d940d050340605e400a11103071000c104960401e4180c0c2c18550401c0c2130110354461a80c00050455004441d40e5205640310341e002c0c00c803190320041c1c01d540194a880a110154110740202d0f08092044a809203200400b20100d1804d5000c0c400f550728050340202251511501d0740b9000011452410308203089200c2da42008178403501489180304136140a010b1094200d1502554a03800c200c942080c076050300800c688140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 87632429 1250 87631179 87631183
    0x90d0c0f030803070e030a031b02040b060c03030403120b06090d050a0506090c15120601030209120118030e030303040b0402061c0204080303010f0b12190b030d030b09100302030601090207050708 85
    0x40114011030b4a95201d242c0b00c400074045101015000e44070703400070740382880001e400104461100340c00c941d0141a0003814404500180017480880d50700c284085108070b031852000000b50b110340d1090762500c1040f02803503144800e459070040b440c0c0d407001d002d02080d03001d42000e40c0141c7c50345020358100c40d0101500c4d00c2d0a820003005545858154011811148640c2802d1448180301e02104029601d000304915000c403200902a154504240d00050007140940d1100ba2182040d54000000c00541e48a0611024a01001c1404402084081103614064540881030342d2160f80c00c9101044241d48682c00c1000303651100d8a207480700002180c0c241915880c0f880900b01601d01c02000303660303950401201c40a07441c895401485080e02c01c2003540e0741500d02018640d00324006403001c6c0c101800e42d24505001d0f252904601c1e803d0700c180130115200d00d92642004401c8041505c0d444055158a2034592100401e07010294140c0c3c441d0b001080804560781c01043c566001d5410303510080c1d141d5203828 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 87633679 1250 87632429 87632459
    0x3190207080d140c04030c0b130f08071401031e0e1f0905060901060303201504080711091501051305150301030c09020a0903080c010f2c030a05090d0c 66
    0x6420b6555032040710008840512155401040c000300701c9042900c0c660300c241c100340b131f0703809848041c041c00b2490900300d40d80b20424a000e030417494034403030700d2948543d0003a660b6a09403040c6200050010a43e02c099406480b4040111a5072060081d0003140080843d02a18035015625200c0c402c0f401611940b120b00c0401c001045600301d80070900101504150740307800000b901410240e45485000c0000076046000c55551807090580340c002509052031140c1070052001000004100a070100300800c1111001400001e1040d80c4c00d101c40084002070041905c800c5400460850b40b40c941c0e210f2542c0500d000c6c1c00c0e400301040c10585500e072940b0104509042d101c1e421121030101000620402902f09614006031424400850400b441404001c00d449414840030309407000008a8000c0a102900300506d4040ca051040c0300d0300e8045076412038102d8020641e41220071002c101480380400c044211081d102041e174600d402c010401041019922956070101c0b070035104d0364000222048030554078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 87634929 1250 87633679 87633697
    0x403030e12100e0c040608010209030a1212060312030c0e0a0902090418140d030e0706081f06080601030e060606072301050c030403080106020c010c031d0901081e060c0319020708 78
    0x81e14132160950103000c259441508641c40ba40d00602151000740c600081d003507445604071682501900c030714801a135080d4008540394551504141c03012040c01120b00c1070310001c8480e40e41c104201412041c08481e62101da10700c00341e01c045029000c203c191000d4028040c4608010800a149004810b00014042c4628012900d4810030030206101c200140a50840003000c1d080a1028050030fa03601034a0741c445008980901003498040b401905c0d620030000c0e03454503401c1601c40c0d8180c51b000050800b0204545c03003030000f81481100030420001143e454019900549068100038440d0780d4445640c1030310a10700e03d0039401c807041400c0d000d400d01600d40111412101140d0341d0825080040074104141c0000041d540030080454290b64400155a611901443c10b2441154989042e281c40a0060480790b409080c1400210355803902160520030381801c400d1b500303118281001040e84901c0100c510600303544041c00000c0c8003606a419100c18a10f604c6001441c000031a130318402150401050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 87636179 1250 87634929 87634933
    0x1b091309060609060b0f161401050411030c0103060e01150c0c0f031e0209180c151201060306120602070809041113060203092b021002030a090b0403030e12100e 70
    0x8200240e0742030313100705406044400c15003464080700d0108402d1510503500c410907140c1d101c0b001e170742c148002c0c40c0041440c2000780340280090b00b03250405400c69804640460300c64041d0001c110040d41c024802d10084441c0d11000d501ca9030301c0d1994000035144900c40176414001000b00807000202d1003031414002c0c220001c0d200040c5400c6080c845140c82c800703000c0d58250142c1c507500002507035442c184a40d10804200b128800034114003140d03400c00d985140b5540d04031069078494141d003040c1c44050a50036899000c507030304a030b80c0d694040781503803c984038912412000c96422030120b44550000c245007405107040518003e4010b0100d400c86240c8040c5e51425200842c2c00005a2028001c1c480100b01303501c000c5042118400c000b500010300c1d01c01041000700003801d0001d681a1260f071043d42d0320380007018100149070515019450707070300103044040001c0c2c8064000c5842c1681740182c4044c0d0f601a03841c0405061000240301007084401110341e40d604c11703461030f0f000c881c403e4000d0080312001140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 87637429 1250 87636179 87636191
    0x80c030c121e30030a02070204111c18261e040510030c02030922020307020102090901060908030703030507030f05070306081513020907050408120301030b0c031b09130906 75
    0x44500f003d0300484142030b5410411004035681c0000d60382601d400c642c034030400503500d4505200003002408141d0b0040e0741c001011904214102414042c55620b14031070130180305040c01c99960152000900c030004000c0b4a0f0350303200382150503403021710200078001c09017500d00c3c1c4120189144501c2c1080070403602c2000300042c040c84542801c045c6161403000b142002d21000401d4207019440340a000c2441d40100b5060300060035145510b41c101170340800480c41150380b410050743c020f0207540020700050141c4501e030000100b442c03181d0154011122500081c2d41095080d5034100c1c0900b10252054040644880030450701800f41c0c42282c1c0554010f84000803010700e0001d6142c1400c082c0011680f03000391003001c100c08410304440c07051106604072182c1a003507544140130740e030340d028a4214801a210f4180c41001c0e00c410003008506803401a2565040c980d01c4c900103030000c0c44101c0c0c24a40d03005526660580c0d107034410024040c040b03002050082040707902003101040780c01000c403e9415a860f00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 87638679 1250 87637429 87637453
    0xb0a090c080105090c120703060f0515190603050403090503010c020d0210062607080303281b1107050303071505010501030204051f02011e0b0406080c030c121e 70
    0x1100400820711100280f0184c82c1c00b10758103860b07010701441203001e0007181400004011081c411000030316408241045845482c044040040c00d040322a0121241ca446224003d450410b00154034401000408659241040000c40c09000040c1044050085010340810107940a000d0040803503a55801032682d40b0074040024603000c080d07138814000c181b0b0a001400b00510510000c001000c1c1101100c0369400390f86100d500d01a0b141d40501010301002c01408080c5058400c845103842650851142a180040c205021562200c110705882c030b10220030382c11101d0040c1c01c9c030284410341300140c503100f961b21408641154842c0c1404c81d0310059505403404038400910030f481c0074207420b00c0e085007003074140f002240300d00f0b0b85c4541442c41074001138080c0503014401d41002e80e8411241620400110440840e140035248211000b48140d007803400c0804c0140c0002004016414010014090900600140800b954280c64044141d0144020782000a24103002420300c0039070020040441079040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 87639929 1250 87638679 87638693
    0x70f030b0d05100f0b010f0509030703080a050c0f01060f0512010605030d020c04140402011b0804080709020403150b010909020f07020904030804030912020d060f2307120504080f160b0a09 82
    0x7213880d0002035854600441d030300b640e0150f4a03030424959810300c41e0f41c50540800180c5024210b5100038401e0500040302e40031a98068090080c0c40d1070300c001c45484240c2d99a5450030b1f5002c5014020440c5000d42d010002441d1483c102d403602e5040740000644680c5980100b818020811000409030740102851007040c00c280c401c0c00c000a001c0c0416107101c1c10903078002002c1c0010031410031344000341c8602003404c2c803e042d41140d00824005003251508c80da59850344019400520050b941043c060011000c0d0711164004c99202a005a64007560107051004440080d080070105440800e824440400141c03075020025004034001c2d21411000e150901e0010290721264001e0810403000320702c40340c0103803240e070101405640e1042012070a00241c0300600010800d2191a40c000d2404500190400681c80a001e0040102c0e65410300e00f43c40e0b91040405031441950024a982c0040001000390900c2601615080c171181000301e03004440c036101d9403000c00050300d806021954614100e805c210007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 87641179 1250 87639929 87639941
    0x60906070905030f0606010c031806020a03030509060f010303050a020c030a0f23030d0b120d1d030c03150a0603080403050d0206071103070303110f0a0201050907090b0306070f030b0d0510 82
    0x480007809509680c0700d02c11744481700601020305000340c3d1503084080501030f021a1000b1011100082c40741941c0e80c50095079081300e82d5082e00840e01d00400b2464441c00400c10030b11480d000d1501c076949900c0e65800f01c80b00d60040e200c01c4114024045d09075000c0c0e07802e003c044c50040c011650500701040500b031501c08610000391a26116a00003e0015403800101c15035843c01ca41c040300080005607034001c5100003e91032407100301805182c1008172811782012020b00350400a00394810a13503c00fa0070306654034419400207a241e8404000f00102c2140c2001071b0303a102c8125080402e08654a40d0380900b036820035082124243c00001c5d050085660420207145d000255103000031443c15140c0556849105400e00902019101e080b01d60410325020101e400c0c00c105101d000da540c088000c002070003003109a945c140d080c081c01000280300c007118000c0c40c0b41110000c0c0a0820798a8410302a1030b014034040000081c9902e0710a04015982c4000c2c10b010181d02035000303800c444244540d110100d40c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 87642429 1250 87641179 87641189
    0x50105120d0f030e0109120f02060702010501120f060b030607020321060906060c070810090302060c2a0115180c030509061306020913060810110f0901030b030609060709 74
    0x100c050403401c0e4040e409880c60307040e1145820f0008004001072a058054840341401404104241c81e0341c03007849900c41d04800010b0302c281c0c03c2c2c1d003540c2c03601c82d000c80c01c0c1d403400e00c101428035012486482c0071418440700020264800c2500151a071a0100840d05000048035610003603007000c65140e1170303a464400e04501101107030301b50140520306500095403903d0041c00b102e001e00000b091b814070b00c0600b0442c5c100500800d400301c56400040302070074000b601061030700b10010702403c00031400d17501c01b0341e05640071015a44001d140992204000300c01038100213400381071035902c1d030355090503800803007a00700041c207086103914022624828a01003540c480410f01b00c2050302c0e2070204505900040b0314150003058481c400300210f040d90904d03030041e01138040101c0e070103172501900d0450f0350340580c0301e1012500d07240c1c107a40b42006099190000c403501c01c040d6008121007084000414030b40c0100402c00004141400140b000444010a103820b20850350240250700000078003001030342088020300149 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 87643679 1250 87642429 87642433
    0x60602151005010203070f1b030c091404020d0209041b060801090e0d0f0503070c060e0c03010b03060405030301091d0d0f02070803130e0c070b090703150902010c03120213080105010512 81
    0x90b1400e80002e60324820400c028040030a4030408038100000b9403031305455842405c0b41d1440b095240c0c141000e5809440c86026152894411800c00c041180100244525001071040c0c90128444e000c1c0003101000400072266240f6910b0603000300c0b0640c122800c043d100c25501c0e070f605503040c0251a0202c81580c9a061b126901102510748600d60000101e58802103600d8007945a13150020b003030301d4011300140f004002508003906004035010014102d402c10f40101e009004041000d000c1c161503000507103010300395405c02c1005026101071500718510b110100d001e450304800e0055511806c280900103d07200040c140074948030043d40c104004800b50400c64007071071811030300d8101070301031040d1842000d043d003240c4000141c0000444098440c032580041c034415a07440d250018540320480c50008841c50b507040200c40002056520501c0c407205d80c1138481740e01108042c1c6080e1a02d00c40d0702c400c03101d159020421044811a00c608250092516074000314003541030008001d00c1c8815206081f01b25 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 87644929 1250 87643679 87643711
    0x80a0305040639090b0403051005010b0301030f060b031f092a0e0c090301060b0c070f030f0602090f190611150705031506030708150a0b04140d050106060215 69
    0x10300e9200f03054440c48181c19040105041c1c030419111513030540d12807035603250007003400801c1c09070206003e0303004021804104041d13a240c0b06842c0c120700080c00054000034282d20f401c400240c1c654000c0c60f2078100103007187c41c6817000320001c520003140c034500702c21510b8440401200300429030a103044450041e607148007820303400d421103d1442c3d01c144035014211180f60b01192100345d440c8200e44031030070301034001c0c080ca83c7c40c0c5125a00b158000c9180800f58460103130009035079949541520103036584104a003e00ea64513071503d0004e508922035040d4003c591600d0044103648140d1360503601d0800400c0410441d1411802030080490301c101d4108981083c21010b0841e5140540c055020400d810f0158a9441c0d2141480303510700c104001d01d40143c00002800703402a08012100d10845902c60000300c0040400144907200d103683c03044043e1340b032003480240300501c0030700c43c0c050001700080d1401c0607103011903d806094a0881d4080700242c1c00401c107010381002e803801c12551045035141d0004807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 87646179 1250 87644929 87644981
    0x30c030705010503131b0306020301061107060c1713150905040e19030c060203090601050915090403030f0209060304060e16080a03080601030e03030f2403060a0b0409080a03050406 79
    0x1c2448001c0c01d145c026844816000204101c0308011102c40000440d104102510303850700f94025030081c058440482c18800201c4c000b82c0d40064901b040c3c50701c0baa100d000003031403a85c0c0c1207403000108180d0300301010284840e156812200041e400207000c0d81030181c800c1d8140340390181110032303d904901d005500380070f0150001c100000c1c00700342d810b0840750140315440703444c202240c000f02e008034014140340c000014821030200c002580c905a41d821952600c65444032441450301c207000c1c040d140d4220034010700240120b4001c0c1d116030319480702420050714180312500020041d5104440440d429a03842c18282412581005001d12209d414102603516508100c002079907110101d500408101401c03000405a900c41c1d000b2003075074035903441240d843e42000c203043c0e04c00c810112102c076280f50b01c00000c221015050f1819000c1c00704003501074002c50b00c664840d031024016003070030a43c04c02d0b1554005030004001e54000c010f00c000a0340c2c0007034030303051901d005000c0d00d40038443c00c0b2100240b5655190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 87647429 1250 87646179 87646187
    0x50d02090c09030a080d0203040c050a03050618071d0f060405040f081e0703030b1201020310120204060312020d08010803030c160303090c0f0305120414100e09070e030c03070501 78
    0x1420600744010310703803a4407425000a181104003440100001c1010440450020b032a0b00614084c900c40c807162510b5546400a111810300c00d072001404c540d10070400306100c59450821020120200fa0540365010b494120030f55050301d588156001404a4400300590040c1343c9280f56002030044500b0300040c2402d0721500054552840d01404d0840700185c10350b590200e5000601e0144240c2d110180c5440382410302400801d14440c0e5140154901040e140840c0d2040c1300b03c0380700f521800c40003012075041c000c07100806002803400b00d070481e03038608000c07010809203098607817581e07001c0d0300a100c01031200710300a00c004010fa1111120b540b040c0148840a0f4041055515640e11202d01c00c1c2c0341911810200d026100a000280496107080030120320905150260000e40b409a0200d401c83d207810b4007929081d2045100e5241d038a4400ea401a40f42d20308040913412681e1540b600201c45801d180014411400640340d07200400c146105a9105041c18000219000c0f4128040c1000602d4000064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 87648679 1250 87647429 87647431
    0x30f1b0301051b030703020909010f08060f060102100e03040b030109050702070f0501080109180212100b06040f03020d05120a350601050f121302033f1b07060801050d0209 75
    0x1000180200005403161b220794169814000010400700c0c09595526200c504c044007800341c00c241c0d0040b03170001110a840304500a001d510180d00412203446407201800040001d03828114050104020000b880340801d0040c5001c0c20254800143c2d07400c5c9008007a1425041d079120540d0b80807820801c0000341e0704140385a0440d415102c0115800400001d0a24030007400c11000758480091401c07190701030400920b206450f40607460412003010881d040002602492060070101001a1001e00050424502c4000301c00d200b00c0840d80c2c8120b00c42c4007001d1981010440c2d40c0049c248a510030070151880514507004050b41009210b03c1c108103c501c461254000d0400b0f040c808000b03540840400201c040301ca0440c50040c24142d01c0c01c240c2c9840074544c2034024160310900c01c00c1d0851907401421002d1440c005208400c01e50b540c42c101d080d00e201c0a54405105442c0304040c804107031034101c0350036520300201c01c01b000781c80010700705035010301034480c182c0110f0702940c080c518000058036492501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 87649929 1250 87648679 87648721
    0x9050904030503190609090f0201021207050a02040f09020604030b04110904080904200a050403060e0102121305010b090c0d0f1109010c0602090a0f08070920030402030c030f1b030105 80
    0x150a0004200c1c0c2603001a101950083c81030034a481c0b1f040741448102e0101d0003000e8030036400d403a05209905148035140c082d980000c1c1003500000d0000d801850982c0c422066580c4510380480c3c0410f494000500c141c000398410384091160340c1c100010044041c154140316001151001081c0c01d160311030044900404440e14010b075034070124200001256420042c0110281001d113544901186000b89103170054481160071508058455501d080c040c002e65400d1030014400d2403d503620340042e00541e000b8810252559503861008081c1030b01d920a103d44038011040f080c6540f402c1c149000011103002e401280d03e007614151800e80602d50420403944280c109207080c400c000d4141c00d01200900c00c07220400e601190102c0f0000c2c010340030381c1c1c0c80000c64003501c00f0b070740c4060768400c0c3d18006e41740d031030080780d0151310010320a0700f0480800004c1c5070807a0000e0f048800840d0072801091626100b40040c4003280d10511075180c614a0003c410034500c1816002841541070107440720000d441c0c59600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 87651179 1250 87649929 87649951
    0x302070320120a0201020421030f320a021b090601050702040e0d020a0512030402030303070c05010e0106090b0a060e06040501300209131a0405060a0503010e0303060109050904030503 80
    0x4640c0450748104001c1002c4a103580ca825a00d800e0428080d000750f10912420544901c4800e00c6d0005082e031202000c0440d425441d181001031200d1000c40d842243e454a113883e285180740321800b668041003c0e2240140c4084103a40e590741490f0010307141841c02c0050907283e8014460055403902c500110350f030000400e08040351280854400140901a15034030070340305103c3d13442500e907103e074001010304c542e50107501030b541c5010000010418920080381c01030340540c82000841c401c14401c90f505550709006400000380d0742c20000e012425586c46a2000743d04a46030b06e510340c0589444c5150200600c118200f404000401a01007140c9010390f204240c140010700358030003901030340e00c40c03071089144076040e001c241c400b040c20702200290055a20503000c4c0c03640303100129102016100d50400c070b41241455884c40c2ca600d10400c400303080020310040c1c112500460024080d01c0900074003181103042c1300035503202e14008000515403917865012521480e284024000842d0300941144c0d000102401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 87652429 1250 87651179 87651227
    0x1e030b1b0c071a030622110712090501080c030601050a03060b030a0b1201020c0a110a05100216060e09130201110106030c0305060a0207030c080c19080a030b121005060a0e0f150103020703 82
    0x7a100d0041010807042c424514001540c9230400040e034811380e41b00310781d07515038496007910382c8011926050f00300c1d1184400c0c901007001c1200340d8005e00144c00a008507190201d0695141c0d288800140c0080e900d410701da946070594144149824540b03003444403032840c000c6081105480d4003940d611300340c45000d40368440c030350483d035080e80321004114094100680800556a0041f50095683c41e05a83e5500b40d4a8180c001240c41c42c4500500720501200030020f42054607010303221480c0e41040710040741409404031071880c0001d002e0090703e00850250305807055591850130440d0405000807e0002c0389841004410300081d0842c580008075a048444680c0b06c0c118810603030b01e4260f0740743e02490982050642101008060b03001025034200c650340511180d034602c020301c101400310f603402400b25000401101110446580810752000e00140011006503071052103603102030007580c500c10102404420429240c0305d16005d003106110030710b0114500405500c00400b001480c03982d101800031280 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 87653679 1250 87652429 87652489
    0xf0a060f020903060c0301060e01020616050307020a050d0e030c040608030304030813021c1a01052409040f0903180e04020904020d050105090102030603071e030b1b0c071a0306 77
    0x241c1640d450751070242c1211003a0501941e4910103410910401c0d0025242041001e01c40d48085101070080015401085140c0047c0c04140e9882e00300614000c2144240e01c020000308204010212000000d515061001844030043c107050000c0c0840e4540035a04191080091038000021290b0203034151130460b00740c0d200c4030f040c031070b4a50481c0380282d8020349000d2196040c1a00311082c1c08258400e00d00fa94029481440640d07110409115059000860041d084140c4e82000b403056102c04119500e40d2802d40264001003c0b50300490350034925954440c80a02007603008202c41844220501c400c0d03400b10320701914a5000f42004100032701980d4060007103802c41d111a02003601c1d080d4444001d00091410031450742c004c1d002120481d11034030860000040844030400f004400065504440944030704603155908111009000c1402c03421541c3c460340d0300388031110044c0001d64811000707040c1c0d0910381161109110a1581c190340c10072400c000780009955112000d1030b1000700d0141030702029401c0e07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 87654929 1250 87653679 87653681
    0x40c0527010305060f0f040c03031404031a010302040e070f0306020d060803220603090b0606090a08060c03041a060f0405060a09020c06010e0a02070f0f0c0902070305090a080f0a060f 80
    0x180010310020610380004402c201021803198481e034400780c00300c6400da0b5030a0480302081000e0b00d0150034808000c1040c0301007440364100d018022814420b5901c1c06030799581d04101d500f80000d040200441c0301d0018000c6103441d005500300031a010001309501d904007484030320803150621009203200d0340000c443e082040541c100748001d00c6800e0a89885112483e00d1450190110402c0c51a120800b4408a4000d000b44607191859030485040551542c0700d00c24041507074801c054075580204800400282e0b0642007049521a04840381456101d081c145040001050b000740010b10410809040100315264074603c15108141118041840e859080103d00750358021b420808901c1d00020380380281e503a00042d041d04235145c00c0006001a600c94654000324055000d000341f001841c80e0309035000c2a10502482c12a90194407407c003021703aa8100c442c00c07640545000c0300806c1d800700320f4131520328085000700c0003480070300090324510643c4040c841c3c54843e5a08018411a40c1d007003803045100003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 87656179 1250 87654929 87654979
    0x7180b030a1b02100b060c0304062307031707170c0a1103040605070309050d020a030209040c0504140f0906070f030f110a080118021603030c020f0a0c081005040c05 72
    0x30542030442e018469072002910b40180d0800c500f045410800001c540341411403c4640301425040590306180c2040e074129056801c510786001540e203802c103030340403041c1c15030b0050102d01c0c03181d2100c19001c006002a2002c8070700042090f070034840759609014081c03c01011030350340080c07070b1904035a585220b01400d860141d28600031460500c4045000314035503800c10010140d660280d110710900a0382c0b5410400b0030310f2503080084d0041c0065100b0401400d0040c02c041c1c0052055054030f142548400c00b00b0101c074022003030891254080030034070429810310240a50012000701c05007a46180180010300714250882c1150200f40da983c03107460b134240342d0b6031180d40100d15a051060380c0b04215440208010428040c0740c0508640c0382404507941c4047c800c03600000c8109004441080c11520250001e01c0440d404e04198090600c1c01d40b4000c03c140880c0e03000c01e04c910000c40d18681010b041c5442c00d00254000007031240340c1428880880c56154a4100b1901d0441d9207040001841005140d1a40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 87657429 1250 87656179 87656201
    0xd090507031b09150b090607080f04030c06020a021011010b060304050703060b1e0d1a0a06150c0503091c02030601080d020c060f03060906060f0c060405010507180b030a 74
    0x1408404030810107154400c0c0b10b0151412811030b1155255180f4004880404001c544080607900041041030203a801411001c8002081c290510060382c440703220039800b074244440c0c2d0180024003401002205140700740030300b20900c010901e4440390340c040340070103400c42c8040e4140400c511300700188441c04d420540c03420074007a00030ba450f414545065a82e450660104544241c10702c034081400341003000c0c03140b44a8010201d400c0e5091048400d01540442c04034041c0c0b80c06003107100c0003945041034030b54603004503007081c40010382515100a180103000741002c000200b0107042d4899001c508008107540d500360b82103418541000551080040041102900a405005030400026060303070120f8a84120780054082e1000c0c048501c0821080b44100e8814011100090011a549040c84244582e1010020f004646420036a501d9110a50080521444107601103c100702c200102805001e402000c94141800d001d030f100c03040d140c403002e4580a11069078402100084411101e504a00d414013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 87658679 1250 87657429 87657433
    0xe060405031203040b091612110a031109100f140a03240506030d080a150b0c01090201020712080a050c1006060c0b06090c03010911190e0901140907050d0905 69
    0x8200044410b001d0f00229803d580c6151288000f403601280440c010800744000300c0e1031b0000c181040c4004c004510501c205540e400459103a040c1a615034603d80d07030145025510303ea03038070342c40d6008000746448010320b503200e01540500c00700400c444005c1c0400540e4400795500995040304000309655190740d6102810106060040c080001e041400c28811540c00394014400b0350b07103143c28542c0c1c0352810081d290026a00c5000103070315414030f511402504914040c15100680c0da06d076000b055400500e11070309140d40d100c0d8180c04660301000705030001c01c034000c0031001e100060b031900c40c0c09006204042d403e1100004085000d124213210398145d40c10103200412a1903151100205545600700d02111003d518801280c2c06140012800d8422135280d500c440ca1a82801c40071009001d8002c1070002c01c03d0240320f400c212804645088034499101e03902c2c404400002000c020403010181d000c00c0d003809843e6290703500c5444400345c05502c4840b81c28020350710200d0700c15150082c51035440260240c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 87659929 1250 87658679 87658693
    0x3030610030908162907030903170106050a020c010e0a0e270d0806030a020f01031503050109060c0305070f050f13050306070c050c03030c1c23091e060a0e06040503 72
    0x38800300400d50a03000e000344070088041e0010f46400307003001034018041910220750000031b05414800d0300300b0320001d0300c00d240000307100442c4000c82c8040802038001c8004180081408444a0340c10005445240c07400d181c2498030703102200100d0b1440c840b070f01030b00c020700c203083d000106064040014030b050107480d600d500b0840c01c4521481610303030101c0c840c0b020004040700081440b0303140000e001000190001c004604c4162840015002884c540b1080111218041c0780080480c00070721036001d595029040c04120020f00120040c22101c004041c4003c0c02182011404031544c050251940400c0b09808590340e0354100b4220050118540d1296030315115080c10400300a80c81250310070b100e88a8021526850948001c045d01e0340968040d10926601c007007a07110a0b0a0701c505040038244403828507450072300585c3c81140c600c0c0e030f1192940c101d8840c002403298043c1405003070403925020f00d2842842100c081c50004050788140f03040d0b00200054000c00312103e65a81c4100c0d0002c10b001030403102d00e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 87661179 1250 87659929 87659947
    0x309010e060a0e010c03060e0f06030712030203070c06170c03130204060810060b0408031c0f020304120f080c0306060309010608060a060f0b12070f0e03150103120e0303030610030908 80
    0x82c00307400e100d0f010075500349119504031900a0003200251070440f0030399a81581c030b03a0a600c0448000a106551501c130b00140042d21116510300481a1f82c0243d01070340d40c40c42541040151031025902003000c001d600c42220414914440d5403c0d008210030600903569140c03103010b990407100c4010069131007450190005000f0b200042c000000f190140c1c810700c122595000035240c2c0e4002c0740b14140c2646c00c00c1003079000f042c1c1d80d2a032800581c80d0840c2d00252000361115403100702d81040b02c1c00c41c1d080c48250854603059030040071500c00c0c00f440b880c0c0260746191428951045000180c0002c1c01100081f020032002075081d00720304090140c640455070740d85854523400015011910544040d206094408680c50754a10b08a80c0d403c0480c0030410782985800c80100c940c04a0400c4981c1042152405540a95000c0c025221410b00001d02a88194154249004030b008001c0b1490700b44612003481902c280c901005a82d8040421a0340d0040910b03892001d50182080007001041030324000382044c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 87662429 1250 87661179 87661181
    0x20108070c170a02010f1104050d020301060f080303191104060311160606051c020901290406030911010203070f02090c070c260d0e1525060c0e0609060309010e060a 72
    0x40050180c2c0284251800b051840e030484041f602010107180c42000144001d003031004924010b1480070b4000142c640d03803500c203c05002816080412241c000205000507141310303040e00343c01c0c4179601904007c9061a451081194440c074440c580074940c5aa00e45241d0f007101600395000940c81031850344a0040a01c1e01100034459405183c0c400c5255003030001071000e4188010403200d501030030b550480d1742041d0780d80c0300d54071a003040c0c10250101c82400f002c03613403070540141c0000d180310307200850fa03000e491510408040c0342400c07060455006201240c00301d826820391a0804d50191a4000305494508074050184074605015240e08000c1c0d800090040032254417600b0428039080d200010308480a045c0c3e00c83d5080c1e00c003000090040c40a80f0003601d0b240c115012000108248140b5208008604200d8290140350480c00d0340030495400e014010b0a01400040840c1c52a11902c01d110300c6c0001041401008801402000c001c0000340e46160254401d60000f902c0307400312042403601c048040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 87663679 1250 87662429 87662437
    0x9060206010605070f060506030703050f0607091d0402090403050c0a031701050303120c03060105040e010303020a0309081f0f0f091506060e0a030201030b012c0a0e040f020108070c17 80
    0x1441220300015595200f003060f104d9041e4000c80080c0350b0130b01c5441c0d90340944405406654107010f0394000000080c4108400e0381506c00343c1000e0800c1e8940780c9000703401c02400307034408080c0040d000c880103110321309941f443d60b000d0307411a80d9081d10340366030604441c00d00a901c6084454420040b4400a1541040c0503030324900341c041201c100c907a06e45091685034015a0300400340600008041040030782960003850340140c0c189000d44c2815500e40341d11a684500382d02c1600580c1100c0348440c01e0590289000340070341070708802410050040c0a24103109503242d8122510956620070141010701a034000d0b500700c0da01d0380410310281d1420700b00650101004003103a907126140c00c2c800102c5030300a090b07040d00200000c1c40500d00514540042d0060301096540c0c5040100c501c280328011420031010114040300035280180d03440c1020140151a016900010351310413003042000300241011400c80c8000307a0a280c15451500c601c80251087c0e000403c000344001c0f0080403000c00d45110201078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 87664929 1250 87663679 87663689
    0x40314040f030b010911030420040204030309210203071e0b070b1e010608011401031b02060109060e04050309011116031101030605090601021e120f04060801060f0504090f020f0a09 79
    0xb106142c0d1740c803040c401c03c592441c2c004a10082007400001d010551501200c1e22645104040000449071000024126805030b002100071985284d02030060310207140d030125103444100b400501c0c0c44134980000342d9404281c41015241f004001d4450a60151500c0c148018110b41590980310040d178036101500395411551030031104031340740f50412001040d0208504881c0c09840b1248164201440407840b001c050785000d0500d07461780c680c03182d04135407101005802c80c6590702600f03040d41080d2104d001d0f030300071368030290300200310700188404079001100300c40a4603009d003030100620030340a51080c1070440c034807840d00c00039642007000010b0114144418102d20b009903030400900f603c54040003900c69007951140e00503482484503009000c0701e44840011030100c80122120f0002c0401070454a60059140e0614154041070030016503800c030800501410450402d0316180348245001025130040c3e22454000a40f1407400720f010002e10381c101c0f80c8200c011098a0750b01c12816201a040751418807030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 87666179 1250 87664929 87664943
    0x80a0209130c0b091503040506060901050303040f090203040f0c060e1306060804020915040603030e041a060a050d090209040609110604051e1f08010f05040c17040314040f03 76
    0x1031061829001e1a40d0082d034030440080a40b82440d00000c144e800c22001a9009612070b00020005405000903510641c814002002c0c00e19200090000e21203041c7e01a501a0340b00b4401071052000c07402c1810140c1705034400058a075038890400900c922850310010f0006120150007181007540310000000e8070348181e400c4442c0300c8540140e4011280c080c40307081c00207280c220109005140a040f0b490b00304441d10414038251081d540098116141580308601090711403000c0e05043c03c0c14054180158245411858140c0801000c01c05601ca175805510400c14000342e2800c90310131941c00a00e10329005080740d10240f0b01850704c940180810002501c8840d0f84440107005071030324400700d0b001c0d42c1c400752510b10304001540785176813440181261954030091140120180d40c04c00c83c0d031010038100c169601c2d542540b500000c0c14900c040c5800150086040054401101303403c07102c140350302508503001d541e2503500c038142126050154499480c8001000500003038110000049405607800303544 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 87667429 1250 87666179 87666181
    0x2040803041a0405010804150e030318011503051e030408060c0408010b0405010b0a050706020d02030a1d0f060f04030e100f0f210506120303040f03110a0201120203060a050a080a0209 80
    0x1c03200c04940903502c2001d0014041c0c6c4001000212070400426555040050200e800a4244641400c41c0c00c100d5040c00004900101c41207140c6003409500650100103104c082d0390782c1140c0300c031a2908030089000740c0c01c2210140d000f14141040048070010552803041e9240d031300340040d02600540c8a40328801d0550700f00700c0064242d20f0b00d03124a504032485a0f403058036221403420161801d0b00300010035103035280d09101e03880c0300c0021400117611a8401c0c440c0007403940d00d40d0040e01e03229440d4a902c2001903001c3c0541049680001615542003c4017494510a581d91490100c4450900c50f01d2280c00164078800d640071241c2060001c0401d00e800d80385c0d810140c0c1c03ca0710031140c0920281200c504051820442d000350511644081e402a4026100380c85c9842080c034607502d141e00a650840c0e09400c0c42805070700381948000045d4000510f1809410282030fa03030002000c03001c2c2500b042d200c60f43d0000c0401c40507903d05440700c00904010b000890b407540d4448141e900c820085030143d0040d41e40704 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 87668679 1250 87667429 87667469
    0x415050f031014010f090915030503210c07030804060908041706070f0e0306011203030e03040b090a09020406080a0515030a0b09010b1f03050a06030b01080a11030f2505040204080304 80
    0x10911615908940d0740d40c1da440c0c42c048005c0064110b43c01308c200c0c0d1800c58100031000c9401031008102c20414254400000052807214a030440c01c01800030084003020302c400340000740d2081d08150000e0700400c0c0403600e20b183c2d0070000e02a12440e408642ca403601c0340309900c4658000310b60300703210300a142c86150601c0102174094800091440160340e16401c100014061940516821102c1e2030091800040c1c6039072602c2207a16580c03040d0000018081c000c61006000d14044850030081c2101c00029818145032031409040d148000d461540001d4445001030282400c8001c41b4401d41c40050480f1280c0c9041c0c1060030340c003801681c549065501707080e000784850400c0c10310fa5030307510707100200041c5101004004500925000e070407082010b0311901d0010106079a41010340c0030f440284050315020a051800041031011420018060b41218440000c602d4022804941003040a080f1032410074032040501000d500356003004d40e215101082c0421059030000240040d90036138002d81028017128 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 87669929 1250 87668679 87668687
    0x20d200a20120c0a05160609180b0405070507030813020927100e1510140f090a02030f1023030102130305010e12040b0415050f03101401 60
    0x44001440421202140c500d541e1008000e5030003121603880c180c0314015215010b5003007507440304842c0600ca5010481940920206004442071000c20000441d2103519040014054404d05e116500c0c0080102c0320004140e16640c005154a400c010f108110518040c00082c0a0360032407407050380055410000580410f2440d0142c10085400404a036201d555005005801e405220328040c00c4441000e510070940310b041141d17101c03114440c0e601003860780c00c52910628050050403880303440300302c21040c020b8816418072403c050710b1500b0903a20018030f9842c003150811240c2e000d0541c000c410a801c000c1400240e40c0911f0280d81c9031039140742a520340320381c010440c000d00d02401450111000e40359501c0c40130b01030440c111300d0000e0005401d154040007000b41c602c440e42d2050300c40b41d4440301c003101d92440500001d10303110b000c0e020541c1828100313040303604140200d0041e070355080303a40038036441e40c1070180d0700341e6110b84c1c4603510306a035a15004803244082c404500c10240401d101092800c940c0d030103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 87671179 1250 87669929 87669937
    0xe03030301050312070302070905130b0f070903080c030f033105030d0914030706052a04031106090607080403060507050c0d030533030c0409031d010909020d20 70
    0x801002040c04d10707241c0461402543c030041e8101c0c00c0d0300c111200041d2903061400b8039803003143c01560340c1c0c040490b10309040101038070040060000450000420500c1a000030b0714100781e9410210450701c40c40c400f244c1c3c602e14402c00400c2c00c60034501104100011401410303903030702280000c07142403010071564607985a40101080051584c0c10502644400001981c8400b0f115802a68190740c3d0010550710313035055901403e401d80702580c07580c0c104041c039152440c043c0303501a029841070014001e4501040d4281c041c42c08018078052444031111911b59881c030503140c4005000b401d5955a4402d803a040710b581e03000d032004582040c149000034032514003074070556a074046a080078203140c2c500d84004034002c00d0700410a003802c0541c5048a01960b1440c003c4514080329000c6080d18140024205403815090300d101c2c0f44114105420000007039407068860311407010200820f03c001c04e4940040e998045181c101ca04681e00c0450f2841280410340c20904e0400c54403d201e1310740420404106401c0d103e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 87672429 1250 87671179 87671189
    0x10305160f03110604030819080601080c0909090312010602101a0d0212010f15081608070605030703110708030402040b15090607061b020601061205040b060418020307030803070e03030301 82
    0x841da001000490079000c4101d210003c010300c85841c258803640d400c00e90781c201695110529840022002440d0740002c0515040442420030b802c10345803c0329010240d11401c903585000e0701071507003c14044d980800030b907000c010140f240040c0d10f42c0c44080007541c07400c00340100c900a0381049404104200c2894900c00d02c8000509004003480b81a000c0c4040d0f0076211442c24419981c4480a000c406070381d200714038040403401903034a803540ca8030b5499450501512121408000d801c1c1d41004414800140741c41200c9440c1041c98803503075490f009500815452820084d41c0b480025141c0400981d813004502c01c6100320b90410208501006203c0c007030000e48041b0700261800c000519141c60980054510302e413041c030021416010031005040001109a407107000b45c1d01203001841060f421840003000400301c2e4404100300d241644840404034009890140555581e00000b4210822001081d08240e0058222015030b80d4030324000d001c0d03902c2180d424001407060041d908092401001300c034100e80c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 87673679 1250 87672429 87672449
    0x210050a0806040b01050d050709090e03162901030804030b0c0c0a020111031b0703030201050f070f0305060f1e0a0504090803010e1305100b090f01120b091f0501030516 74
    0x1d82d03024140802008034044d110705202c0d0900a1951080c1c0034022584100a0b0381e807820000341ca0026144240c88902e40c1400c080d070001d0100244425100d5000028940c0042e0a901c2c210b1484800c50300501d041705840e0841c0a04070008000c0c0f1400000601c01c40c0e11651002c505a551150302000e03e0240c0382d07000703001b904409400c0d400366204040e40500d81100d01e060b68a849150f00d01d25200301c002d04484c64185d0042e200420a00d40c081c850194848c42c12281e0340c1c41c03886e000b98001d06040841002074241580e87d4041031458480e401004251003020b0b004603029124804040b40c010140395105204181110010845003403900030030001c00e070300c03400c22401e590a2400c0943c0d00c0c1401000002d26444903003001c4c01089003041381d1071112041a00004002c1500800d1120388031005010f05952642a40100540740540b11021101500803900a419454901c030441c1000321840084240b01044004003680484c268001c604982c0b0400881c1c0d43c0c007400480c00381c0070035000d12a8081d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 87674929 1250 87673679 87673681
    0x4080d120b010203190e040213032001080c0d060306020304080d05010b0a0918150b0706060b04030c05010806042903250506031005060403030c141501090e01150303020a0210050a08 79
    0x880020070703242c000b010346d00b00f00e01250409000b1508a805c0f5607060b5000d011011810006d000489488007085245100f0307810301c1c9522940040c100310400380034a800c03d400041c0701c0391180003507807041c1c3c043c5600c00b10a650340d00385810b00f20520b400c444520030070345280100019410280c042124840c07800d6840c2c022000703107041c4403400203840ca540640906900c5c2c00044141c3e1003600d071044003500803442a0b64840700d05007014811554550006101244c0030401403010800200413041290000d03c0c003044c03941d2b0790001160150012075480071544071090900c0c251090a1a0030f03240d1640194100c445103400d000c0054030080800800642209103040f0520080c01c0007002594030422918103032010343c0e07860300800d03080da220b40e00c240c1c0040c10034220f900402c40030303080c0301c50054500c4005040003015026003000400e03042c0b003142141d40d541d210240502d8029004102c520f42c4094807000310315500d090294030346029900032440340790600c4031101c020b40600c0949105998075580d40d56070f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 87676179 1250 87674929 87674947
    0xb120c0f1503010f0f06030c21090f0503030928030804020d0503040807090615091401090503150906070504030c151106151201020708070f020f030304080d120b010203 73
    0x80e2032005205400200c10500c0e00480e4145a00550003007031126080e441e01c4e0f00d003d00381041809150000410903082030a00300314541d2041c1c1e914450102410003c00707884541c12503000034902140010040c2c54480240d406205020014500c80c50500c8161280c0340c0e011050041c18040030351000b402151001c8844001c40d01c155403565200c0d101400204400c61180c0344c06243d600613502850841d4807201d820b0000c030741c00c1e02650005202d11000d000c0c400b505210702030314015540c02500c1c5115031013891186143e1080c0382d40c074010480035041c0c51101e00301ca61700310740c000000c50340f6880d14419000881c504911800440d404c594020b40d0802480381009120100c103210f03201700d602000380c10201925105e0050000d5801841a42503140da5802148103003e080e03c002c86240d4004d91040c0403a00c0851107541c11507020341e600c20302c0845021f0143c40007a41034001c215510b50544804180459420400a24900680c1e06a1980d5242c404544e11007402e039014005498010b800900c08000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 87677429 1250 87676179 87676189
    0x201020a20070b120403030c0507051e0718050a0b0f06072405090a03020f030c0d0e03010e01020301030309090e010c0f080a240608090d05030408070c030c0b04090b120c 74
    0x41d03000380160541c1e12440e6200b00c0d8121540165001800d8011000103210415815100714031b600350103400c201d414424191200c540319140c2c1e41c1c404a00c4a0b400c04030700b4101c4410301c10312000e00710041503689000901036010005040481d801c01c0204d2602001d0301440c64030104000000c540200160729200c1c0c80d5032250904680c40c00b90a50301142c80e102216410041d004062040505000a20000000d41030084c0343c0741c42c2c501c1c0c409180e0410054842e1000c00403c02003951482814020345000406c40840d00400145d00510b00551010002008050b0300070504001c0b80c007005000d00c00d9040281e8120b00700d5514540d90382c00300310407141c0c9050790f5000d0b0034001d0f4001800b0500040c2001c0d4000d0708002c00900901449124210110074070459804ca030f402074200501c400101031281c410302c4007808600c40600701502903200410304504001d80b4003580c0c409181d01c004071405060b80c6500260154200c0c2c000e94452a00b80320205205080500000c40b074500320100422a01101d402441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 87678679 1250 87677429 87677477
    0x60405060d060b03183a090b07140d030209030d0f0309140102031b03011a400e070e090a09020904050f070f0803070204230a14070201020a 61
    0x54041c9848080010755200d0b20000303180318826041038044141640d103961401d1a52241200781321140301081c05545103104c103e800c100c19440c860001a2051218040d515500303d42e01508407040001141e9041115a11200c800070162004858030580050301c02d800340c0c0606611aa0103502842480c1810b40c41907280084081080c10002178180440d150f00034000f8200c03d6006084e90000301303028800d611801c000000c8103100b01c903541076506242040321071700202c2c1085403170310a0100d2282003180780320a10020000c0c00f0000c07810319012082c0e403e0281c500342e0307401192440c44c0140c0003c651000603c81da108100e02e580d0b5255101d280420040448005414000302c00d656910744c80c01070312212040c501580c0150010840c000c1d42501140c41d0491540003110482c100b4141007082d01400400c3e5080e050381100c02040648005d544d1451449810072501140851101401880a00d9030b020800742d011000d0083c06a03990040700380e0a030320a0802100010710b0900c1c02a81d0008251001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 87679929 1250 87678679 87678697
    0x9030d0b0d060c0e1903051f14011401080604020f091003180503180a150507050a0606060804051006060504060309020a0902040605120a050402093403021206090606040506 75
    0x8400c10200d20707102c410403035075600796400101e15440c00d008103e260a444001581c10f500072100304241c1103990f015180c0e403100c2d201440d1103500b44601c6d059a016030304035000c10380800752149807a6a642c110f0305d030180760001d040e50100c0c5019011030a03a0030b280c000c50f0025405070551501d010383d07840038403818540e549400b00070160b90300329010388400781c141c1c8551442c0c0a2002107445c1c00d07200d426402900501c244003881848800b0703041204010104040908080c2410241d88402d501d0601a0400445402c01081c2c1407a107a4003240654021010305c1c0a03e001d242221031a00100c0c000f001103a80034000c81d004100d09020410196102c3d8100d581114805401802c00b2a0b447c0d05000590f082078004a0101e0404191362002201d00030132244d00c0212440184a54140341e00030510030710000d42105103105a00c40c1c1c0c9500070801d070328422800d003480040f4030032010b5046030003402034000e0008043e410751142c2c0882c00d24078101da10980100c8000b40700601e0503250608000d12039002c1508 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 87681179 1250 87679929 87679939
    0x50a0207020f091306050705180a21060213030b01080c03150613020c1917030601140d020c0d020f0d1110050712090c030308090a0b0c0307030f0e0703030e030609030d0b 74
    0x7044e8002013590280314040e00d002d88403140c6850385410034081e06013480b0505405a55660b2080003260b100180401150f00614502d030002c42c01410b0000c041d01c80d00c049084041c0e01520008100030031a1031403412180510261462403242c02d081544801c11100046a46c02c0f011001c900c0038a082c8401200d020b0303181500610303100d0721280302d0f410400844c00c0280c4c0100444141403d008070001414081c80354412500c3c503600c2d040001078003030040c50404e10403c0802056114644105034100c034841207440341202c904028054009503a0b0a0610400080e40240400812880d0113040f0700030810902c50060164080c0c075400502c02448010302c00020095500840da0400c0e41e1445080c61003070040d044801359074198140907140701070241c501102c0d41e100f42010710104220000c059001860068a583d5075102d0724402c4002d8052400c00c10710701458180510142400001d0910441744241c40c0d404503200c640e410107891310400c0b144083c10342c0040140346480303000d550003613019450041ca = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 87682429 1250 87681179 87681211
    0x50d1d1e100e0105060102060105030f15071214060f03010c0905060a02070509010602060115050a080a15050301021c0501060e01020307060b03152a030601020a03030509010207170706050a0207020f09 87
    0x44070005071214480902080e035503403010f10242d542d06000003809008160000c01d0b110711242c1c50580c0e030382810041d403006c08441d040441c003e02d100700c5034000340d04468001440503a002c00c05044d04c83c002611058490b0401207107900d000c0c00c042c000c41c0103000310303600d44000703a500e0841404070030350084511804600541801181c665070b02e501541c080c0141d43d004045a6060641c001d410846011103002070210070720500c6007590740a03400c59400303407090030301007038840745500030643e0380000703401582d0b0550010038003040341d200840241040c058030390003d02403641e80c1c0109440c44440d0600c01030042e08100f1411012800d190425610440050105e9080c024150104030ba0802c1c151122001c88192820314000c994140e00400700c42d0404011142c694140b45001035601c82450030000d0900d41c0f100700241c00c8603020340c182d8684581101c03a072055217044464001d09540024001c0302d2292030304010410600061090394034183e0b000d0f12a291907551481080100e07840244400e21103100c0103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 87683679 1250 87682429 87682453
    0x1a040902240a17040b130c030611250302070308031009020d0209040c02010e03030a150f0306020c0609010506010903080702060c010908250f03030209010903080406050d1d1e 76
    0x15846030340c0c00490900c40c1e0300c0301c0040c0d00c001c050345070340301204006941c00c3c1d00f44004a4982c680d410340054400c1c4c44400d50405924281d904030141e0385c40034007500d2030000c07511128566240204016103812401d85c0315508150f03d22030b5007108002020b001607114180620014041e14001c54201481207103004c91a03540d02d1040041e40e008209847d0019004194280241044d0240c0d001c2078181780020302c01080b10001840d030741d020080404081e95140ca110f001d000745040720f540050b020103c84038500980702c0c10b0640181d408015000300c980f044800092003240103120b00d60040005030f44500d4031520311740b1007680c02c2d0010901a60b1110702007114486011003407107600e107054460b000c525109c480e010a038011014040d142034100e80c50607007104002401e4211080101a4981030040e280e0080000413039030b500d0150001007541c04005000303c0c807160000007418013050307000780601900c0725012072007580003520042250075038407121802610a0704003a42d02a201c1113007088036880740c102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 87684929 1250 87683679 87683719
    0xc05031605010c030b0414040b0c0403050105040c031b080703031206050612010e0a0209010e10170c1201060c050d03111c0902040b030c01020a061e020304060f0f1a040902 75
    0x4000304031100da42d60300700103076495010f00601c5d194050444007080f480c0c90110390784810f01d400400051104449600090308421444265400345030080c008101500e0f152400031003c204030b000c1901c031109210880070a0806401882d4190389800d800380110354a15030741920005070074072070898101d403a928081055102c0c14041c2514403c480784468840d40741c440c00c0c4003803060140441d4080d1380100124069660403500049403c2401d550380d047e5500080c80403a000354131a005500c000c0059000d028511a102018060194100c0102046a640c1f208140d924640704e0000404035003224a0105995000354070188e941d00c0701c14440e528000202c104120b030f108010b0261000d440d41c43c0c000005500f81841641000102034008000c21602840080c1d900c41104034003c2400e529003000f50888107148040511400591209540f00d04061a0090141c541c40c200d403030b2140d14119100200528a0040701c1c1c1248000305e09101043c0f0301410700c4003a11031000142d07003002c0c0e600e00914160400e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 87686179 1250 87684929 87684967
    0x30402040f0c02010b01030c0e06040506070510060e041101230310051504030302070f061704050a021017100b030c0c0c03070b070201090609030206040501030b0d0b1617040803070c0503 81
    0x40c0c3e0740002182ca0b044800901143c144190b4902000050012a80070f81c0ba400300b101d06450302192201d84480d91803501d185031000107640060314500381328000031b1401209900f2030266114141409206405000449101d07900c046102042d08030111155803001d00c1c0f0008640040320b01c00b51200c01ea440e20046841502140c6103440c50740d400040410a150b07040c030100001c0d0070440c1c95804414944031004154580c010986c0d50380d100850007007420070200f000345003510784d07001c2c1950419080030040601030b203c07009466001e00c0540d00004558003007144404069500c00120359056450395803d20180c2e0700000a0400390340700d0000a259259420410200100a0041c240782c2d41e4000e480010000c0c84964804000d000e0400300900041e0313500015201511420319002a9405a00c000a803c0c00890320340502803103840024000344216403808103110715255250540c0038100040d1070307440b1100489015080da2018004100c0c500e104c0c1d40e07840b0143c2d00585c126401c2400305c1410414203c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 87687429 1250 87686179 87686201
    0xf0e06010501021002160204020c070f060302030f0106020d020a0b150306010806011e180b040609140601110a11190b0301060504081902060a0804030302130b0304050c0a1a030402040f 80
    0x100a00040203590b07810801024181d0030a6015420003503680000c12079588415002841950045a0040d41c0318003088844001d08800b0001c0c14520358940001d40254400e0320480c03d030b400c0d28000070941600018020385c040360154010104002c941d210b0000c1444003802441c4400d82c0d5000002c05c07940e0400806001e00b4030403000d8151540740c4101c9020b260310f1450741c05440e06125008102206818440080501c2112008a1a1105240018010101500161082403501020500c10320103281d42500c11903082e00c44d0b80c8000c005003040e503652107048000400a010405802805007400000b481d04030280d500504001c2d510341041845a40098204000140c4081030420002c0d0303080210307041c401d080b40e4154548410070323008940c07280310700e100400500008a02081c00c242c403070360464424010490217035030000d449038001c0c200340e030050324192414400c0e068140407070314042c903c0000700c2d0000d4560001050a40e030103007020390802803069901c00c0e5124000d442c034072a82d0055000c500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 87688679 1250 87687429 87687433
    0xe0d050d0507020708070303030f1b0f020d021f0e0a050f0a03080f1b0a090b04090c0306050402090a0509090a050d0e19080c0d06020f04030b1803070507030210030f0e 73
    0x480c65440312012514010510011540070500401100070701013036202c252905860041010400c614000f40903100c07078010141c41550900101050036445161440c030080990300741c40072a52625001c03070380c55000b0540c00c0c3e140001c01100b24000750495009841d10420081a100c1d008920303103400381407401c0c4170702c01c0010360404e00c91403040650003c80203522160401e910269410040002803003501d11244016410000007001c51609002d215040001c0189901c456525a211011a40a0301400710004003103418103102080700e140500a44000101c0500340038041841c0c00b04203e5940005840c502203030080740f0b40c4502080e41840100310803500c680380d04402605140a1203038803e4052400e28160003a100d0a0003403c4010440d00d101d044115900010320146003003c00085c85082448900260001000000c1009000d01940705808800c461900c0d524590305d0716807a8403a01000a00f140c102e00003d20051404400080481d441032500250310401001d1510465981000c0c01c043d0b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 87689929 1250 87688679 87688687
    0x80106090506090c190804021807090801110304020d030f0c08070803060a0905060a0312090b0c010b150c0601050d080f0c060105090a06060c11061c02070309060804050309010e040e0d05 81
    0x20f420980c40403a040082c02a85a24142c8841c9420704500040d0040c0000c03c8031210210b419551080303941c5200248107050312a140c180940060301c66402d501c80c10b4481e50902c00d10121141600090300c3c440c5030094003d4008003041c3e0f6040f02c0100d0010781110130700c0380c0900c8201c0410450005056110310400c4066500d050003c00c00000030f0003903101110050601d02001040d41350302c0041c1c800c5a40c0305c8184981c0017060002560075101ca6002120050808511a080113905420aa900403030070b461113661401600700c0100c46204c0c200c441c0b101c80d40718100402c07032410034051600c0b055028854140c1402180350031030b01164881c00010400d41d01035030041c082850446025500700c072020000b080b1862420300040d080048c801c001500d0425a02440850f9403521000c84d0f00f6050750307401c1900c0060a47c6400002504242d1041e800611020030204807903000e60b01c0c060040340c02c803000394204800b080044903050101081c4581043c0c58a00c2d190011108014a80712a1a1507d4054076 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 87691179 1250 87689929 87689941
    0x60216030507030206062e0509121b09060114090102070b180301062304020906190903030f05040614071104020d0c03050a060e070809160b030601080a05070e10090801060905 76
    0x217091000303031005e4402c81c0b0702d921a0b004159402064500c0c080160002d00403408401000ea64600480d80c00c21340203011105031010f0320b07202242500c0e0140406500b41c07201c00e105018014040400c4601d6804600403450350800c0031000b201a1220300307014411140c1341c1d525010fa05984bd08403000c4040e40c2081050605c286190a01803580604a0503e006c41d020402181d45010316011035003060086500152440341b070380314841102c92007482e844000c1d0813441526402000c600041c4800d50014004bd070400c01c0781882101202c0484010b0f43c0da944450007c54441d040d298048981254030421403e000c504a0302d650000d40f1650a00781c400007596919024042c0541d0001020456101d15000301840f901b0440e40031650001800d2405007410754030070305e10174908080385914004824070351078006201d1f40b0340070040d84103040c2070340e131148a9142c441003141074410554894010845070103014900d41811804030a0000c400c1c9001ca0303002c0c0d034802e800c0d421141a90480f00e5025141d01c20004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 87692429 1250 87691179 87691183
    0x30a060b120f07030b010516020109031a0106092c250801090609061809020a0e090102070218070f05030c12090c011b03051608070203100b10030605010c0f0602160305070302 76
    0x50f001c990f6003414081e040c04400000c02c1442214201036008071648106c0b801e5911400e411030145500c8600c118000c88075015440c00c13040d00744107207000110f11b040c000c1408010100301421295121881c0c0f910042c1c401804060140c0081115106140d00b407810001408011380c141c40b10141c1e5242c1018550420220409a40180c3c0101d50503d003440420406255441d608264400b083c42c0f0001e10080d01d0320000d07154254a90101003035216200600c0034402c1d0650013804194401c131168603030828010142c8401300012180700010030024901c40f1601401007008562191b204940c0500d80382d00d0208565181c903080c1c4d80d4880950040707640f001e013940c2201c242ca000d842007580003284c0d01c64a41d0000d0140c0b08100a6110321107610345003104006054003515440b80e401029100010000c0b264900140007103101e0a105100c11100440b1207030080c4140d206031441a9660126100e2035292052910642401203540c5582005541c0c625144088090455403090380c1c1d5a0f542c3c43c0c1420024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 87693679 1250 87692429 87692431
    0x2070b04121d09040605090102090d06060e07030b060306130b190e180d0e010c0b070302130906050f0607022b050f03040e061926010f0207080a05030a060b120f 70
    0x300752000d0600d42c2c405035407400002c5070b1066004002103420780c1c440d0881c1e400ba01a14004940103881201454208080b40d00300707030240c51108081d441d00c3d43c0e410300101c0980700f90444280c0c001004102161031400c0400f03c01d040b02c2801d2002240700c4403440c003c40c5990000318002081005500c8045c042100c1c10981c070f6070821b2006140440113050804003640301c0c008130200405000501951030816405170804402140d0000c800c0c480c40d02d0040f40207000395108490030225101324410104100113188034a2080d200701901c0c01060a0034001070081c00c2d4400041603a0003c01044940e424658211070008200108c507200d2100e0301c118541a454070740300001c01ea4060304140410300c010810340040300e50150003280c02c1548203c400e84103842065140c1c1050040c0100c800c007659501c0c000c418034404840c40c810080112000194007a0f040b4000d07075400030000b08080103110400340c451000303150045040d00000450940d14003c248140c0d101403107842c0c4c0510040100188051042d200d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 87694929 1250 87693679 87693707
    0xc0b0c071509050d05070e0109050106081303090b1c090c05011101140c0919150e0613051216080619140403030e030906030405031207050a05040b090402070b0412 71
    0x10000c16904154050b00a002c01c0c002c09010f00c001d0749812060103010040d04004141c1e007050074205503111411030380906003d0107110041404800440c0680d080740c0411008150180d6031800090304003014000b039036001c0001c50755120011440b0290300146881803480451240602c2030040d494a400503000346040a658000390745489101e10f1307980c4c00f182250380c0c4030301c068068942c0e074004c210020b5003504822001d0044240c1c07000c404644c0c22408540048c407074010b130322078880311132900041190380c2c03007200252010890300840400c400e0030500c00b05805000c10009542100311486540d8580303400c1c540c000411540308900303112050031165072244103038041c11000e2100406000d0307040004a00039000500309550b9480b1507200b0350050040e1200210014405682d90815003400c55607030308045000b042004070701001c241c14902a5048039080c0495490743d500f410300e880358084640c0c0110b00d003190069020000c44001800e079101c500d102d07038880d4000c0d00c0e040040c01c100804620040c424 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 87696179 1250 87694929 87694949
    0x3210806060304050606040507050d09050d09050301060f090c09031403130f03030206060108040201090909030e04051e1302010207030f080c0c091b03040f051903020c10090308090a030c0b0c07 84
    0x9020200d1008a05c9991200b001e0310042600d449011003121107100c0c1c002d407074004514004825042000200c1c136001c8003166a903410708001d0b102d0b8101070890380c0300c4c815420300700402102003214014a4210b846910f04504000c0c08959407a210b0441001d19a01400302d11307000003a400030034a00f04140c1c02c0191442e001c030b21a20314116600a9603514001c0c11450500141d4400102107a00c261360312000b0304a040c00c00c0c4145586441d01030210003081010521942c1418002120803070884182c00d03400c120303c400920581ca4139540210207261480742681180204180840410f188a0f4450f10700780c13054196950b514001448181400d0090b44a5803040b4020018080080d031030111206c1c9000c4455103140d070340e898601c3c0214061445a10042840c000c00500016806142c1d006c0307030a460198083e2142d0008a00c200200d8192243c070f0700c00421000d03582400840c08070009071207240d034090f180d1f921180d107035290400c1540003540009008030000804c3c0e450f050341030003103000070b109480c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 87697429 1250 87696179 87696181
    0x30a090803070305070803131415090105040b0c0a050c011e0b0d0302120904021204110a0e010602070e0a0e0f0c0315010311061e030901062d0603020310032108060603 73
    0xb0f4010682d103d1100007400380c0c400400481d0480881d0000404c40d568000d07c10513009024103642902c4442e2604038440c0a001100041c522007018011548520b03442914031110f5a560914004a600050030f46010000117004507501d0020910411a5887c4841d0300140320b000c0660042069641e190381c0580240884002d06000030f0300055580e402f50022040c1c03540b1a0001c401003030007402420911044100750000740028444000c10850614005580d402140703501d4a0189038040301c280310305c0e130059020241c1040404803a0100580100c180c940c0855110310b134101c1c0d42d00d1301450406807c03080d00150945401407030200540e603801d41c000d0801813501d614544505080032012a4900c4c0990800660f091503041402040c2d450f03162400c1d8266128106909068003d2003d030080c2029040701a540000c51605100c601a820062010740c6482d503082600c120069080601400002032980d0170100000d41e0361281c04002d4403c07003405030071040340000020011980a0031090040780100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 87698679 1250 87697429 87697433
    0x50f040905060106030c051e03060111070f06030203070e030a0507060201051501140a020109050619140c16020f18040c090203010b04031e0204180b15011b020f12030a09080307 77
    0x2c0386242c11210f80b420001480c001d440019903407403050700107402082c03c43e00d8a00421200850156002c1c42007aa9030492002d041000c2d60b50310380c2140241c0d040a28072940c20441b05100760000d6a00c44068034062609259040103e85822420101116a904245020700c40c02da4240320f41a80001d4100482119000e6000003801c049410143e068500b0340008580d103015000350444800c86130b1001c1204d00d517140c800b003903640350b50070300c2500802c05042080d103510807002507104500580c2e02e100140e281029130390a04516200b1068101c0e04030300000413083c55030303031403481d210301d180c1101900d0511387c07405180444e40410140c03c0750b4107880c418001403000100340000e907000c0e2603000003c41c403115218190805d0f040c0c0d0808c0000d60150903d881c44510302d10150000094038851007003128680c860794030a030300781d1203813400c001c1c001581c05204880c0070541a919080040c0098000091001c0b41008541c0d110b500d0709040c0c1c00350340002072981c14150300c401260014075424015500741045a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 87699929 1250 87698679 87698683
    0x203100b0a0605071406070504080d140307030b1203040b070b09010501080604080706020d020f0421151a030d0f0f050f03010311060c010603150627020f0c03030106020106050f040905 80
    0x6000300003c10602040300020041c0c00c454090450010800301c401500d03000f9402030950b4443e006000c1d16028484410314001d000e85801d040101111184500b142c1d030b101030441c020094098004d90203259061688490403050004101500414041d5075442c8a031b824400300f100400f07443c81103280e240000402c180140480c4158100e5400341019503604032074100364010380101c0d0701040f100c83c070010303e84054020b800c0007001141c84004480300481900c05d80070003040007121014010b0b660840d05007845041c0360340101b031034840c900390001c0b2001c001400300c2d10b005545140c4101041c00203886030000354103c3c008001581261a24a1134025110041c1000340410b10000f8420900d07804200c13059030300d680039240301c0003030003000b040301581c0c03402c00507a8906000a400d081c14900b040c04906000c6142c3d56033400700d8a40c0c0007101c0348804580e48802903000e0408040250303420301c4000e146041c01d2000314000c001d59400440ca043c181820880e101300a079001c1072185d85010180e000107040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 87701179 1250 87699929 87699949
    0x30e160306050910060608010e01140d1103280b0f07020309010c0c031a0a050c070302030f130b07050d080a0b01020c010f0e13021b0a020112020a0509040203010e040203100b 76
    0x10000002c202c82d103c50035014508003950100100c0242080004900c6552101805040b0765081d04500300999840c85d082c0241185056181c0d040120201c01e0750114041c890020040d28014044800032208544071040341301c40d050340c040080e0407440c00d00062101810362960000641e110b0310501c6d041401d4065643d00c80c8060141c1402802c040080034000c41140d0b600c011504203000c941240c462082050001c0d10890701c003d1140d25043c00319260140700d2059407803841e0303d900110324041c0300c0c1e0411003141e00454030f1860044482c4101103030128225000e04100c074800d40042460b2100a00080c00c0c5500003070002110701d2030a510a4a01d030390002d00500d50190a0800c0240290644c1c003c0300d14808041c0c00641200f8242c00c804c0d54407035648d00624604c1c00b0700c440203010403d0070710f044e501c42c184990082d00113008600709207a07405156000303091044486c10140e281c01c035400041801e0303030002d0f4426131404011108010640c2002e20082184014081c003c200303d00c804c0001a0790021 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 87702429 1250 87701179 87701183
    0x405041d030a030f0603080c011e0c170408040f061806030b0a050f1503130506010503191e0501090305040303120510140301020c011b140c030f0304030c0f05030a030e1603 75
    0x14407081d04c03441d00d8403294000b1000d141c00401c81d40c2e81d400b042000034042c00c03034a25907010781d40c009071007018240e0090ac100c0c04038688641e24807420000d8060108a4140080c0003039424080c10400081c8440100c00c419006045a45440041c8141d041c80c074101c2400640c0080d003807600749140140c1c6a960f5174540f0081e40c0007140c80d44407a0509002190314030710b000c00511201c403000810b010701c4000f114048880c86104404540407a80c80344145071303d500c00b251141c000d01845a14102c0011703402c1280900441c030003400840d607070020b500c8013030a46030300b18015804944000b40600a241d8410480c181c0048102018481e90405070281515501944105442c0da22401716111041d41c082d0110345c442400e42d402440f00440c112507407912026004c2c003410106001d03447d2104855003080595000740c026101550070500740c1c2001c8003503540001c00c00c07020001011604400074840c15280d000b040d00540086031548443c990180480c0c0d2800c1200400d9800003003521641c0d2600d020b00e8041e26 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 87703679 1250 87702429 87702431
    0x30705040f090f0305031603060302090c220e010f0801091205030901020f1201060e010c0c030f03050702060d060602010b0604081902011e030b010e040e2119050405041d030a03 77
    0x4214010403500818400c107004000d5000c50b03c0c1c1106255003e0083c5015800420203080404040081039045901910000707400416090020303900b400c0e1200604110314810b40c0383c0301c0b00214241044c24034030740c9800120312070443d41c0040c445404802207542c00303410200b0007041510460740321a6008074808680d003041120002c0080c240c2e0b50b007901520702c20407000c03c07155106e1000710303411812140c0c24025200001c207202003400315584540da01d103039200e8012580508150030750319820542c1615060540034880204401c100585942c03004000b4030b4800140015000e0410dc402429030b400c0400407441a01d06202c1882100d0002c140c00c403140c1441001d8140752013444c40140c850380f200004420348003044040d0f01c110160560024655164260f80b00c0d26248601380030001110801c040311003d507400525022841c2e03012002c4801c100544c0e1041c00c1c20004510b4540c0000e5002c1440720300000e00100742049170342064003451040303a02c0c025040305070b00759110200da540e01940b803e0b20105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 87704929 1250 87703679 87703691
    0x1704020d0302030d0603060b03010c03111204020409120201020702030f0706170604090507060207060e1807030c0210050702160e07080610030f0c260708010b07050c030609160603020903070504 84
    0x54000c00485584134503001c001c4c40240d07602d09203e0300609112910030f0095081c03030b600d000030901ca0310941700300004120085050600807810b408102400810481e0030070b68450062010a03814800441c03064050350000d65229101e10516040045442181d0940e51100d141800f10b01e80001101484d200560440071082d0394400004003d030072401030141c118050a000424166400310b02c1c0819683c035911022a81c41c016014031040c0805505182c0c03101141c4004917800340c1c420380004454038064412214072020003e0007008852003615550056400340c0c031300c010440000d842000c02055694030440c4a4a401c3e440a010071100034001c40c070070f4140c03241844200e8003da1001e94034808154082104101034032018205184400b490070008102844080c01c40941c0c41100d0300c1081a0b545895103a464086002040d400840c0b040703485000383c00c0861099102008801c0c4226071400c02401500c503803100c0c000010000d608541d040600400641909403000986407084940c295000030784 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 87706179 1250 87704929 87704933
    0x906040b011e2304050d0809030109150c0e0d050303070311040f0603020d06120f0204050613051303030510080604121e0206090c060405090c0304060608030c06040b071704020d 77
    0xc142e6640c480164400140041c0c00d241c0e61110004810102d029180501c4101d8883c80b06507500503882001e5200d03010303042a0000500240250081c1000607001144044103a941d10a4800800009080d06980c0d82842076080d6130050708400c08203001d46d600c1805004d40c0e02c1305500c03840020700e0300b814180c07240401c6401c030302c00f82d04a60081211042040e07034075455032030003000382d80b00e201c100c2100341c108000807803103808820081c0e0382c841c3e00c8640281240099405d100140100a2581d5408bd1980000c03c00c58030090041602c00c488451044040103500e140180840c3d04c058403012074400301d200c00380940c48000803aa90041e411000c4103880955040f000c603034904000b070302d5101c41c2c0c0030403030203181150700050001e0103401c6000a44601460180c240041c9000d54854075521207800c0020814070300e2500001d540083c000c4101140180d00c0303840407172559010a50701c20305903015808120520440040c20340e085804ca1400b40564424407009501034480035002a100b60203018480b01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 87707429 1250 87706179 87706187
    0x50a200c0f0327010f0c061104090207060b040c030504150203041e0f0b0a0e190503090d0c0f050301140105040c0c06110406110c03030403031b050a0b06130603020906040b01 76
    0xc0c0d1001e58421640d603070041d484980c100e02a04090380710f0407407001d100300301da641c041c151442600d04a03583d40e18507030f10070381c4507107028100c060000440c4407003c03c40810314440c1800241030f03080c01444003084003e205801d00c41203c0300d59003100105407500b01031000180800c80b48515598940704007584a448030305026803c4484010a000e025401104400410060201c060b80c11405407142180d25078030b50350391605680c4804800d0340e264015404500d080b03101c0030b101c54401f9004000700c9081c82c0c1c490001c61206c24001509072100c28001d10100660a9000840c20240900390001c0c004c22201a08480244a060044d03c0c490f54883c3d6688a41611402d140700d040c94200d00c0900203001d5015031846d8030b501c1801160002040003480200d00c10300000c4401c0b4045000d03004500d0246181c43c01c960a12050602500783c140061084010400401c440400d0300e01500356400d0504201040100c003210304103614025605003c02000503a595009035580100c042d41c020510103e0113004072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 87708679 1250 87707429 87707443
    0x3030c02060a091e05090f0411100207030209040605061002010b0a0302130213150e0f100f020a060c031d0c0108040b060f03190605010e010b04090908040e0415050a200c 74
    0x800c3c1c91014602c020009404d01121022250140c800750419100c41c06180010700003101c0c040c00e0190000c90000c0c160400501c81c07070420103144182c1e4840c9031030354005110690240c4050f24051303164401c0c0a00da180110300100b5580150008002c0400310381c002c85c401640920001e0302c45d002d2165100d65240c007580444507500043d40000c00c080c0d4440001c0404014481d00d0076000608086108031541000c5003224110a03009140b80c1915000c0e442c21240c0c2c45ea036a08080442c041c1c0c0c8940000644540646000d401ca00d032004030385001201040400045841c00b840d1059200e0f411151141e41c0024041d03070060f8018050211990740c0c0780200301082000c0c61450307018070034004050118199081d444040901c2a5800e11259a9446074550000400c5c0034095032443e0400003000f04860030340c01807120380e1144003000d060a595400d080c400b100c040307030140c03820001c2140c5188820b440b8400c031940416079038001c120700000506a100868900d018004501c4000030341220780318010043ca03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 87709929 1250 87708679 87708689
    0x20703120e0103111b060c070812040602160f050c06120f041e030201050f0912030a15030c1503060e1605070507050301020a050d0605090708070f0c0b070216080703030c02060a09 78
    0x9035585c2e1400c0741e00080418802c1d2600507030f0740141004640250044c0c4200c600043e04000b02c20301384402440c60042c20360016200310381040c0e081164181c000181d039010b0140b03d010f00580942c101c00c505050b803c00340b0701a01c0900c0f5042c20002e00140e159000f40359908005806040300040e95a071401c0f02400c81100700f0b0040806103e00c1c1074040560540000c0e21544007040e842c0619111148000c1d03071045e06a10b5240c10a200b480040d00006681d403001c001664202103a06001c0d80d01d45a0719080720050b0060780360030900354004450142c05000c0c1d0b0009010509144c94503290420b00c41511200800d140010000d000030490103015080141c2e9014180050003195603206024001e040383d803250560100450030128001003e2821090840c030500b034984500e03681e41d446200850f040e5206a0306a400e100214020401082401040c24464010b135001000c200510010f0400d0140031503100b11059030203203a0a00000b54000102c05a40f503050340c1b25034660012420581d0010910307081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 87711179 1250 87709929 87709961
    0x30c0c08030d02040611030a02060c03040c120605040204051006081b0d0c08010f09020304020907030203130f110328021210050907050f010c0b0105060c010e12070302010b01020703120e0103 83
    0xb02c4011001c055000744110303500d0351070780818030404c68082501e90190002c50f60140e00420001080c0300c400800443c3d12610170390320541040c1d100d029201244101070010349059581c2e0f410001182060701c6082d0308842e07141c6610880a191040081070014011b10050400c0550005595000412070540d02c0b0840f100d0801e1000c001303034803c010500c800910600200e0125090000b0710003807103100300c80c001d980241c41c074949661080015001303540090260000d8203803e254120105080c0c00110709020b2103000c4141c0d4503249682050316104032a60f1201000448500c0351500300119903407a034182d036040d40e5024117101081c180908001845028003003442c10001088180c910115501c0700b611340c12240c0c40d0620142100441704c000e0100402000c030b060540c0180020b140c0580070b0b0407800c0031b540020408551652100c2c1c18141c1c00c42010b00f000e4808a034041c1015020300400054040a01c000c200d05403541d29404201007404c0b801d442804009961694646d100b500000b00c070650800c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 87712429 1250 87711179 87711187
    0xb0a0210050a050601020c1806010e0f0d0521040e0a18050a03020d0f080f0612120a030501050f0103090302030304060b0d2a081209040509033a1503030c0c0803 70
    0x290b64083c000480f42c5600500031114004098540000c0802d00300c1b9441c569012255183c1c0011b5480702007039801c2d00e60003081061004100d541e950301c02c0352810300c160041d181440c4e611281405400140385085580c41d010f21003401400c61004015501c01d4600f200400c44040c03442401d01c4450b52b211000d0310a005001425084c150001a1600380300b41e03554a40b6003121204200b20750324181a50001c50741004500454001d00e840b400303000c49070b012042a24000908003010071042c1d40410919408031b07454400402051526a83e034290801c3d0070700b0144020051035600940b80c0c80020030013040195504486c40190300c0d200907805125a024050710007640414154014030303503542d04120801240b140c1d020809041c007050b481c4148105200c2c560400b50031100300805480700a0038504544818442e4080190b8050340b00c0c010311201e0603114a0300082c1010700c680000e031054104461504207410004814908036411041305d8151402e408802402c1c0f910744642d84047d400302146201c00305e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 87713679 1250 87712429 87712441
    0x1106040e01061d0102030a0801030f05010f1814030405030307140f030a030212090705030601090e012702090106140708030c0910050d0c1e080712090b04060b01050903070b0a021005 79
    0x62080c01642203a50802d085102e40c3c10700490b600e10030501c4020000326048010400981c12040d020000384c8a007001291540540708194122004800d514240000300e180203028040b18421103526080040007961403c0e04050200c0d80d83d12428038010242d560b010200e800c4420700780034501e140720580e41500e0b650002c20400034069004250705084180a480108119510003d1050b089a001038003408403a0f103001d6603035000b801e80444480f90b5540f00c01e403600004190070740711031400e10003031031907a100b07056401448002c0b85e05800c24014000005c00d1000620002360503500c14640c04019030b9078a9541d55411a05805050340e200d80180b0011032034102c0640110162070100d030700603010807030749802c4281101c6801c0013203144407402140c0c0c00081940340c811605154070a201e418000c0c000261640c0780300c1159081d0000b0b495440400d0b0610041100d40c0c000e01000c0345007468214100000000001d495021078852150807030307000655101158001e0245501c402c00e40e0508010714a007030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 87714929 1250 87713679 87713687
    0x90a0204061203140903030d090515070512061c0203010c0305041209050f0609010c02091f090e0c010f0207091e0608062202010c0206040321020f0a1106040e0106 71
    0x500200c0c8114209400854100c2040e05605241038040e40c40140c444400e03004516a03500150095800d0701042164010090182c000d06080794480c60082c8004d0f90052050680600054000c804101d020090001888010000c2c2d94001104403544c3c4200310f010346080d0541000369170001d4165080c03940400031b40b60950300c22845076014844200801f062503104507403410f03140c010b445d0b12400c400d20070042da007811000f82c00c0104040c142101030010540004900d07060468015840c5241a4240f0503405810140d00c0005d15510105000ca02c0b00031904a8449c1c0c462082c0301e0410800140e2014194820040e100041000503401c20101c901007150500940e0720004250700d0b1800c3ca107000408280000b25188a0351004542ea44001a1102c8026420f003c8000c10b80c108560703480f01c00e0240e59180000d0004611070148504295040c0b0083d403e2990a41343d103805540102040a00910012483c004403030343c001032001255040c5030000e0355074055a004502040342940000c1001c0c2d0304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 87716179 1250 87714929 87714943
    0xd0806061b01020d240e04111c060b0a0e0430020102090f101b08040e070c050c10091802070602040e0609100f03080d09050604030917011103070c0f05030309 69
    0x921310b42031022000c1007008028040d9030b544004082210080d0800002c2d80c01040360381c00c03038030a65000b200e01c0c0411001410f14804682c0ea2110ba10307011100c441000706501c9000c0200c202a1001542280340c000841c0380e40b06c0003040948031201611080e40380f41c00c50540c0c2e0740d40c12803403c2016508496010000d000b5000003203460302480346400c0300105403a094980010300011643c030006030b480140720008000e0040c1c9401c46400400380008a2060f404050862150f0140d9803060302003102824000d14010120500c28040c500c0840e50501e4140d00c800d81e501612400300b5802d00c22611900321400034405c5020107071006202190100d400d408840304a4000c5004a0390003646884403250300c0402c444604c1042d42c4424181000c00000c2e10360b90140561020050340019540307d40d0b142c4c6401d0810841e41207001400001c001e0151000c100048641c40140ca0002c010b9030340b10081c4122548009020403003481b541d540d5072020804070105070124554810240d0b510303130400d5101240c0d1022 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 87717429 1250 87716179 87716197
    0x201030b33120105060f0408190b0a18140c120d0215090a0b0406180c0314030c06011e0b0d0b03010b12030702040c1209200901080d0806061b0102 64
    0x12551100040c040c0c441000e4034030b03a4060280b0319507103034078150800240e64080c41c59480c80b800280300000b40d20300c007407000710b1000060020a40c0080d1051a041e5503201c00140458100d6241c00e03c14903038185240d9011b4410780e4400100811085d104103246d203416003072071440398040202d064401c8200c07c040b6282a51802c0c6030201ca903103400360279400b02001011a00c400003035001c030072200c2c08a003201091541050080000288034110303800410440c29201000743c1d160524804100108283c40300c0c94442c500e5100003450400046040c540e440e10410b11850b0100c4081110700e4030781c3e0720411402801031211070105035440b0340e4200110b019009403909244203518100c402441401e002d0700e40d4041542d2a00554074140080d406c220003091168803681c1000240f00000c05030803501e10428242502410682580c00f40f000740503800080c0140031140508400c1004000c002c00000d0076000e801600c1c20000050f64407140401d0701800340c3c0c4041018410031701c103400103100040d8020010b0300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 87718679 1250 87717429 87717499
    0x303050d0b060d0e031804050f07180902040b1c022119020c06070306140603180708071707050d08190c050106090c0e030d081803120103030f1209030203070f0201030b 73
    0x4081b92080004882c01100e002c4064100000002d828a01c201c00b90f88030009484504592030381c0781c05080c012a04250410040860009583c074041064110880d890380c040032019403606a90318034030504000308202003800344210310701080011042c00080700722000000002c548401001d1900c40d92018241c0e00b0f1804289410000700342c2121100340034240200180c0130b5072454888603028a402c1041f82601c04c054040c045001c5910300007030103110010503020b143c0c9400c80c1902c9140a050041d958442c62040900015480000318032900756407609110042c580da8208542c04c0556121680800050031035207000d2010445940c580e11584408004d9914907103151074801c203241d46c441c461000003011603c8140042d82416100d60f4021039144a1003d483c00c10361110201900e50030280c0084003c500d611024850b038584c4420003409151140c0e400f444402e40c1a20041d4503071090b010003405c030388920b041d41029640242c01c140f1a0200151190809034000840c180300720780c40c401c01f41800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 87719929 1250 87718679 87718717
    0x20a0c021905190501020a080c010e060901020309070b0310060320030f040b0627150a080106050405130b070323040f0b090721020d0803070903020301150303050d0b060d0e03 76
    0x700303c00d450001602c0303041e001000390901580b10800941c00c043c8a11000303640340c4210b03003540d18050103028041c0303001c04009601c90602d030750094180719554020b40242c00c014020070450000381c401c02d004858481c02d001444911000d507a41d0740164007039010070200800403d0000c0c2c01300189203544168041c0901d8007268540308100060707141c1400c1d01c00808041c5441a041d1f0107001c3c10708503046492940c55000ba15402c07004201c102c40598820304859565180c1000b29051a0041d0717603001003c041c8083c0080c8040c1e451620140c0090f062602b010b42c3c510403c1c0e02d01581242c07041c41015402d001c1c1449d460a89001e419070480314104407810f85d80540071070442030002a002c4103079694807111100719005a01104110b0020140c240da004810090300d00124070200004e45c0244425940d80ca8403908500506095030700f0b0a414050304882280100040b90b44031098403201e10072014003241148282c80003810034000d140c482c807907081c0b070010000b101200c004001d00390589141104980c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 87721179 1250 87719929 87719959
    0x3030c0f010b1c12050417010603060e0a02010206041b030614070e15040509040f060c08181204050103050a0605060a030f0e01020405030312040c1e0914061003020a0c021905 76
    0x2000003284007400c10b0000000b09000013894600200d02c40c203450702d8210b040c6903448000121000ba140400c16290359101000d100340940c1d8013a82d101054120010321000c0804d80c0001d41e104c0c1c0082c40502101e000c02940d0b6032551600ba6600001c40c5c00680c1484a00360900742c00020301c1c420743d501d4001c01e5181413107100d1401c0440d01c04400d51160710312541001e28010a002c3c076601c0092085441001590b0140f000800611549040c00110355500410745070446908042c44851600c02c8425071140c5a20700441c0711141c111804d03180c081c07030b010803103843e2205071002406094000e0340d0303c68070119a00000d260b16038411411085100c206010311802900c906080344164002d240c0c0540003081200961566005800e411601c1265014810b9540e00030030240d040344220311f000301c184850030402c0144064064140882c100540c00c0388a030030070100046000c20b81c1d00d0040d0901d50041020035045018880b40000700341c01400c1c4450410421840e17941c140032501801d4401c0b108000d0b1068 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 87722429 1250 87721179 87721189
    0xe0f0a09050c04020a0203040b040b0702030f0a0b07260406020c0705010c020a031e060c2102030f010e0615030c07030207080304030302101107050a051606030c05120901020903030c0f010b 82
    0x185031600840a480420404000c2c48082d5001c040084150320040100040d891040b40c001c0000301010402141c8403c0c91f441010b041c0110790b45007444a40c840b50a0703201041d50b52a0746070300103010b800c1c204102604689080190130000e02c006541d060058108414000300e074008181d00400e44081d510340b15211801941c9501030854003075044001d242050000681e204807182d82c110440e50881801001a5a0344060b113a403032909400250301065400040621038040c601d81001c01c92095045160003840c0c1c00012005219100116100001041c0140c44050b5620035100380d048801e5905c1c80c052440401c81d038000700b811401440b0700c00000980b1100132003a00c00340c0340c4c190f020300104a0240040c001030410513404840c480c0d000c10140c00002c00030004420440e12030070107004066103001012040c404143c0c0500d0905080a500d002c1080c2c0c031400301c5030039900802c01d904d05a220b020195009014141616170140b0001610f000c1081e0005604000c0380e02640007888940c1c10b04003400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 87723679 1250 87722429 87722441
    0xf081204020411070c0e0a0219110607080c090f190306050105100f09060509060f0a030504110901050105070609050304080a031211040b09010518040c030b0f18040f0c030c0e0f0a 78
    0x20342945141801440000943d543c02030700b11f104035101500700800b0701c9840f0058060108a400407580441265080760400d11410303900c07060f94100f4026a191200403100b40c2e102c0e1501c1244103c0d403000041d8013942d144a140170f05510b4480481903425100e181100041000b070180c6403160f00300070201c800c1d0301d01c10550712a0444180c0c0d04c480781140f81002c1610650400759455900074802d0212114640303508000d0144082030740e4000c1003c0c101400c044210320445850075000d004881d00601450344c101d41119103250b0b002d500010303242e9860038000c1c00c501075600081c645e809544030413070925a11200005107200b05880800012203281c00c4165203101380d100d28241c0c100b0a0110120942c01003003d442c0440d0750f03000b400e003501200d10000c3c04591301d450b02e110100341c0e04c074000443ca003071440c0d022282c09410f50b078102682c2d054a0b001e80f55090002e0000f03041d1300d0950514400c0204005e922001143e00655044c04031343c07030701e1041460742801c4519410409501001812580300341c0291 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 87724929 1250 87723679 87723683
    0x40f0b010f0c0f0602120a47060301030c050946051612091109040503040801090302030a0e0f0f01110c190303030b09220f08120402041107 61
    0x14118180c140c001d44503106582420f03500410140190b0000c20344030700040440b24103c001034141032800f00e9100c0c08650864245503d00c8201c04500c0c1e5007410111241c1080680711188401e0250542044a030484400f42446030001001f10000042210190306207082d5101102d44603015603880010319000009480046456880e41416400b00c0c40c0c80c8022081822080030354110392240c481400741520b50036a08403c0d4003100c024095000c0b035020000000e0303040c0300030061101d1419030f103c01c03018400000d0f07a14480c4104201080c10002c04101b183d004195180c024803e403d840e0070040c2d00c80d084486002c020503200c600203230700c51074100303515400341400910141c040d44950300115004012000141030620401140c40b2042d6500036203a42005144054840c100d030a500e0b0040c20b985010100b03900031502c000910a440c50421001c8a0704090000001c0000c0d04500300b000c01e10744150805003490030000f5800b0070400040e01c905e4855402a0341c10f1005001200110300544151000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 87726179 1250 87724929 87724937
    0x71d0f070c15050c120f0403080123090604020c070605030103021f080a05040606050a0b041a0306030a03030902150f09040c0f020a030507061b02060703050906150904060906020c010b040f0b01 84
    0x101520b00079240d10603600007401c401128101003401050110a410646041d02c06000728010001010390210103035015000b0090f0088426603650781c00340f4070180340025141300390040e000155454907198151103580300b150741141c603400c3d940c0348050041da10a00082e030107500c6468442040403c40030107610300f08020390310204a0b645403d4440c00410340904100c03a2a030b12000001342c16a540303580b220107006d001c400659a039150210041c100c010000328040001c0d0b003481003100c2503030302144c0300402c140c041c28049035428081c030004480d4040ca406207481c2050200e129050008a9000f0b4210300d40c0643e07041142c01c6081c01c09481e4030b07a4920707917500142c0c00310100701d0000c0d1145000d8581c0318850302c40460742c2c0d0f40c024411012000c041c01c00c0c0006a00c1203041007802c81c3d06004080c0c0004000d00900418104011104c1460f424603c10341d009030105004a01009003c0e444041c8164204400715166000014414043c11840c2020b521645c00c044107c1c04500759446142c0c00c0c8001610b03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 87727429 1250 87726179 87726203
    0x809030a05030415060320040e15010501080907080601060306060f0315060c02030c040e0312130506010902072109080c06130510050c011404060e030c070b0c071d0f070c 74
    0x1c2d4134800080e0718400304070b81d15107840e4000001024a0ba0349401079018001d00c0b80c400e00c40700248422070359800c03a10f12540e4030208081d8400d00b4a440b003135040d01d4003880d0217041d83c1e80c0c4103046860726000b07070300c240c210b4800c4500026005900d0f030b001c20283c1ea240c1c2da401d1422005070b40220282d070000303d4481509100c243c2d04000326406440c40c603480c18400340a6900400c20100060100c5495840b007c5480c2c01c0080c0c40640440880c841507400f14208002101d80707100303510f82c166911414040e03c1165640002d02d001806400c01d401e80c0100c00003210000840e503400002003410265114802d414800d49920b4802446d020054461011044400051507441d00c400c00000c080400e6840d02401000c00680c0381e02c20003801050300100d400140c0c20050b00b054540581101e490340840046904148120050f40381d01041030401c507004810030316102c0707642141440c00d19110303a100c3c04c2c403204000c404450b000410340040c1d100740080d03004018266640c100903240c1c1c3c51864402494000154 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 87728679 1250 87727429 87727433
    0x11b050304170a03060302090103080714060702030a120e010e0f120f0313060209031204031205040302030c0d0201020f100e0d0206070c0312090b0a0209091f03140a050a03050a0809030a050304 84
    0x1000c3d21040d84607241c0810020740d00c2d0042450440280c1054a0300000040d8580c02e00040c4440c2d034150342d8440c0700070b1160b4541984000c1d203070701549000c407080007821110395132030f61881d4210072017096606d4020404400803807540c5507a9489031011010038003500c201510380d4205402681d8080656010407071071aa121a0340300d41c5100c0c17804040b40c446030300f801800043d17101080b0b40860300d0400501296120300f10b080000211306000018410404100420701c0162004103d402001606a4001c0e40c0e02da221b20051b410301015403611203a0b807082403c80582c940998001e2290408004c058402a1000041c100c0e00c68504644400229101c3c01380180000d119a10240c0385100501c000108140d00340c1e500c03102818140d0705407031400d402240d11100c62604100c4242c00041c1071403107503450406c451582035109420301c8040d00c4007104401010a07000c0901c014820035600c18207807415880340d86009841e80c1c01c003014400010760301000044200c1c8000003112104006920345506594a903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 87729929 1250 87728679 87728723
    0x6010f0c0809270114030601050604290c0d08100609060f0210050406020909070921060e030c01090c060504030206070809011e0503010801290108070c080c011b050304 73
    0x203080300ca500040700c214000e404410010a00310082c1180354483e02d654581503205806603d5801c10920980020004200da59104d204480840d619003000c6001202d50201c90041400341401c1a1104000061051103051010035412182d0341c4a40314030165480300e03003500d440c2c40c03058050340d004507070800418000107008800a11070440700e4411101c81000054210f01660403e49007201d28030340102d80c1d4001850700e0808164400780303a2800c2c0420500e8802c0958450218200032035284601d8485070061266a8206083c981103a0003104e03510306100048600030480020155039441e403603d00880d00c180300c0d10488040b030307400800c51402c080740b5803a07940e0581c0c00200ac9605101c24112004032411680c180f08480c03d2a540700c1c0e680b41c0d0302d005082170950b10147c000310103800e170114101407468400340059440b14402e20f0400c0c455a41d1020549594920790b1000d031103883c3c007289144040f001500700d03000303001100c1c40c1d80e20340010b03061099415001c107a90082104a10b4402250300c9006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 87731179 1250 87729929 87729937
    0xd121e0902030307050d0e04050f06090703020a020f06040b10170c0f0109080a030801030606090c14031f0e100b030702100b06090a09060806011202060409180c080102090906010f0c08 80
    0x2c1c20b50740303460010b5454502d001070a1948501087c020110b00c40f03d440c0c1403084030340c400500d5114810301c2c5010703c000780d41840300a0580c0c0503d030b030125410344103e108110000d0684085c00440d0442d080500b40041480f5044402c8034a10300c81c00808901c003032083d8103448266424900400011031303200300304102c2900e8201443c4c1044046200041c503c0750070403494810502940b905040d950542c00c02805454003a0015951f4130705040d410030749141e1100003a01000c87c520361203038403070b10740c0b411440001c14100d80040012103001400701e00c0c000c0764140603004402d0140a0b00c071840e83c50980c1c8aa9002c1152070401503003094a0101c50000c0c140c00403182c4501c010003840c58002e05000040c0614100c0d009a100381d59100c0083c0075880c02040800c0c05800100d001c0748400180760300169903441039000360340c2c003562900000c131034030303503200c0d40d4040081d90100004203410b480d100703814000d402c03c518980c030824184012a1036075000b11107040c0340b042166111204c205007510f4100aa41c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 87732429 1250 87731179 87731183
    0xc1c03022b0f02070b090c0901050a05190801020304080c0f12040504090c030803160905030309060307051c2a081006030b011202040602061e0106050904050403030e0f0d121e09 77
    0x3480d0388040400c146280300074605580704c5d03c45c004240c00d000804500e0400c50b401c04034085e014500041c881a910b00b131028084603012507503241304140b50300c40a914005690b1208480e5030000c401d02c000c0001c004040c00c0c00b400d030002100da9010307004071110b0b41c480d03040c0451429403404200502c02e034200394021450050254004000a95407a510000507a104440c810100900d0481c0ba044066001020300011f20f0101e00840c14031071034100203001c2d1320000d8001d106100c4005038625405107044004001d01344020380070480040c0c900400d048414003023302c0444680c010030340041c4103014080e4035008442024043c2181ca08102095008048c207114550600c207400080070a402068001400034000c01e5002d4a4542001d000710b030b5103843c148203501c1c616490480140409a40a030a41d81e541204507404910703a1142d0405030010030f000c00028200f401107200221460070001080b52002c040f40c1d642c3c12181910308401d10403244843d0f40174400101854119070542c85941000c40780038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 87733679 1250 87732429 87732431
    0x1060e15030a0210120c0309110405070c1401060614070507090509010209130c08070c080703230d05061e030a20060304050105040b070903050c010f02030408030c1c03022b 75
    0x80d50002000c94007142c2c4200e002540c1044414140f160346c0c000c05214002e541418021044070795152450900658002d030b000740d6850000400040c0309030b254108064100848401b819503008169000e021319003c0c00002c10110404050140d41603022a0102c0da00301024140103818802500040c00001d04030005540d020b1204003407139a5003d00500550803a1480001e1524220390003030001071004000c441802036032150300d400316000b4421111401d03807610b810040d1901915940c80800d224904000007194041141f0090409541c00076015000c1156211040b01c0c1c601c030380c03d602200001426415402c0f084059001407000102142c5c002102c1c2c0c0e160140c04580000305038250011541a00d60340e44071001d00c01807124014406812081e0ba191003245242180c8559a41d49036000a0a0400c812100c2c0000d42ca0720a2040d14054010034050340d582e00d00921055503524021ba01244034490003250050146019200301c0b980e2800c07418940c0d4420341e1007101d25000c0789032040004002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 87734929 1250 87733679 87733693
    0x1170d181e030204060b07020604030f0c0b0708130b0a090603050c0f160c0603050c09090a0f05010f1e060e1005090a0905240f0402090d0b0108030a1101060e1503 71
    0x49081c036100410420714801c00303002507441d41c0100301c15a2107507841405c044404110150243c2c0b05c010844003640d40280030b041b0031408a20700420f080c1d141e584607001c20700c8042109010001c40d08010141801c65201c181c241945590250f0142e00c01c205400010900980040000602941201d640054a100721604140784040904800c1c1c2c484650094010700c1c00e01c00d2001c10120b0540c42024082c82e15041000303150544110080c2d224850b0306500c20071074140025010081030300400b00410f0690760900840d6500c60702490040c0c01402a09540c2403501115030207401c0321a41030080b100c06580d2520f06500745014440f90b0105400d801c02003082c01c11480100c0e4451900300c600400070410005400d20f004c410045844982400c803c0d04d481080b01c0000036a5601030138100c0414080f100165204003120001d800031010030704c02445104460b000190160000c8068a5042060746aa0403c07010207a04070f0300700ca005004600001d400400440c0c507404104c2400c815280c0081c00301e841d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 87736179 1250 87734929 87734939
    0x307181d090706090501170405010f060b0c0c04050f040f0c0909051f0b01080c030a0e06040c06020111070f08030a0609020c010f0c021b120a080406030207060501170d18 74
    0x910300802a5038900810000305104040404110308402001e4900d0407405540c200701c00200042c41d49400100400603840100302884003c0d8811034420030100001c1048a60741c050181c01c603001805594040c1c09000070b004107906260150b103202d519420143d50941da41c59031104145401d041007540c0e403268192012465030f9240c03088948440c004d500901d440d94403d007a14580e51110842c20038185d0030000d080c00aa608000c0294016880310861600c1c0d588225100d0020f00c0c0f0051070b09070512809042c0824048030a11240c141e50040e8000e00c40b0091594070310005110709000142152103820040022801000103990052030303543d000301c1c43ca075444289200303907000f451541d403003651340c0c20b03000145600030b00c6541240042400030307000c07440340c0d660300c5841d0803004011f05004080c0741c800880384000c14001104c0d680da0109045441ea61580c00080094000e00e5089076002d1604001082001b2012001d003c060b00040050503120540b0720100d5106070300c070203003d9424000c40d4011171 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 87737429 1250 87736179 87736199
    0x90312140304060b0f0a0b07140c0a030f050c040e031b03070c0e0711010c120f0204090507090303030e0114071107030c080c1806010c0305130905070c060506040b06030718 75
    0x20040d4080c1e0b201113132640754070040101c0280c880b5120342c0315030301144081006001c03507002c2d034440d04d410081c0e0302c0400d101a0051401c20310124091948904071440200400c80100c024001d40340c003810440e0108a4400244811500c0e0840942c0c802d91042c8245208101c6090848689030100c60a982c10900b00e40d880b1525100103400c0b4014001c290360030001400d0340700c08203404140e40000207201411010b40c010308403129a500b10f588042d12000004c80d400d00e50b404913401445000d0040242d440e144200601c0c800352400300b02c0000b814004000350202c3c05000d4100c0c52000a00440300b1b0307441b00441600e8140281d1045501030151030000408a004040c0b41c200070100800640402018001000405000f04d00f9907404030340c0150030302c41643d03072007220601c51603450300701155500280c10041c80d44050a604c62420541000300300b203142035119510080c503610401c418401600c4007410841587c011582c01c0d0f4101600b40001100c1610400c1c401010300a5036010598180c2c440c001c0d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 87738679 1250 87737429 87737431
    0xf062c060c0c060f030906072d0516110109081c20011b020c01020f060c070309150e04060602150406020f04031509120f0f080a0e030a0201060915060903121403 70
    0x5003840c4c0c030110030818407540034000d03164003011904d0705052000b1405d104001019080c5c904081d26440c4002c011a024021400c54181490000a40418002c10301d45004041c1c1800700090005201c13420014501c5070004810400f42424807440500a1200504840582d0b0b400360300324807604400085842103500303228800310450261406407403071a81d45c00c00f03445d11044004403411507000d1415601c140764003186682e040b0035410f480b10b41d100031038101110201000d820805540070408c0386d06580317603080480c0c5401c240c810b90f02881407650f107c1c8103903200c01505400003e43d006040c0024002007003503004080c03042a1303018460811f51603490314081c0c4007051412080c035950700c003003c1060000c2c01460a00e1006a0300c2c04000280c80448001e0070401d240003243c061080010100c1d04110040d00400f8480c1e0040b800c4946034041c5160007800391000d4480c65903500e03c1e111040600b032000d00c5180c4c0944040b0344442c51454550750310a090800351a42c40f0003001088817114080c00c1481d4011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 87739929 1250 87738679 87738697
    0x31003020d03120b12060f04030c02030d0905130e031204060612050c040e01020c1002070606031a070914030d14070602040308041a160303020a090803040f062c060c0c06 74
    0x11454011010242d8400c80c4c0c07030750100a1003885001c2910010316400502582e000d0f008010050b0705448525050740e1690261000950500a100a0007100c81e8003c404608071401280c82c1450003034565001d004941402040f51243d4004000d00d44a02e03029102468005118000000340580e40305901d50400c1307980a0b007250300b500000e1004030139207040d004d0940301d030255600071480c3c420300c29180381d41c0ba0500740141c44595004110141402410342c00030000303580000b03041c440740210110400f0803c1c0105c0c0c00a01142e10303120040b039a414604494000c0d004080c0c01000c1c407403600141650f0142c03400c1d82e25500c0010400c25100061100e0001d4401144540805a180ca0030300d00d582056520305407040120810a000c00c40704510810fa45294442c0c042c1001650b0302380600b030440d020001504840d42da0300c0005000280c01c1075001c403e030101d031841d83d00c000c808170180e0b0b0342d1440210482e01840340e332100000e00007454907003c8000c1503401c0a420440c2c142060f198007141041d0005104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 87741179 1250 87739929 87739937
    0x31a060f0901140c0c010c03030e010c0302030601021b010f0e0d0c08030301080d020307030905010503090a140309100201050103080912030d05090a0312090c0e070302070501050a150e09070b031003020d03 89
    0xc81849542c0181d242c81d00074806400c210b00b00a050b5a13000e03a1010f14100c1c80d4108900c03684040103043c003907404003c1e500060300003400784030035425014029500c1603400d41d00501c10034a054114884090107207101240c143d541300070b1410024811925041404030182d48495903144d038200213102d0792000002171100c8806185c8940c949221641815040c1c9101e4055410401c0b03e8400aa4000d0031781003610030900b4002e84980314007500c0792034000e82c000010a80b18865109408205001010b03010300d2004842d480c030f1500040a049082e11000c0c0b1008000e50428025080c0c18680300d40351303125000c00801100c1c01c0c400c1d5598460142c92040d03441c000c2f150080006c40d018507a002c20b5100e0078800c4400240415a5a0341d65052004014422013841800031004a0800e600c40d4040b1404950458004e10041c03c001d02e90b40d0003002486d0810641080d00c42000480d4000322000e98820360b27040300645052858241505135550008001d503d0200b40e6035008030050340c8200c48980d10a01a41e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 87742429 1250 87741179 87741187
    0x31e0c12050126030408070b1303060203100906090b010e0f0303090306040b07030f05010b07030c05030415051903051902031302061c0c030b0d020d02040f050408180105030c0703031a060f 82
    0x814854a2049010325802e21303001000140500f0400040c00c1c2c04a51180c0d040c2030703550324100c0040d9035580854100802960001040c00207010f070b03070301458050b00e0800c08100015075407101c90b00c0480e460135607440d0100c0c10f03540e100449443c008040400c01603018094130701d8480e160000900381001102c00322a42e80195051140702980f500ca4100c41250794002005554108070b0101000d0007101c0005007084460720440303040100520944004094002c891307800c4a9021034041c1c21038024000c002480d50b01c140108100d10300c6401068002c1c03650040c8100040800003044d0080d5200914003856100b00f41d2460006813110401864680c0ca07820603116628228030b9101c007a9200920071400701420961500099075900f032070b02420b90340c122001d005c000701c9031000c40c010740050680c2060302443e0004100502111100400112030b40850595907070107201c00561351404162030001e0f04c014240000e80000c2e01a51020142e10f100103100303e40742545070001002a80042484032100201007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 87743679 1250 87742429 87742469
    0xa09170c0c010309110d02150a050405040b040605150310050a06080f090609061f0b030a0b010f020307031b0f0b07030204060e060702131e18030f031e0c120501 70
    0x8030091070755010920b41400700d0840c1d92100c81d110840545054401c000c0d1110030360440d52040d00c2c000d11a040032801c0c0b62681c58460b4040c0a58019200d960f01890a0458451952401d4803d507419118028554840b0001c44003c400403908000c20803030a12403640d0003c1074030350315600c1910050040e0344d541c0322280b42c4100868541c03900a0b100090301d520550512409140c0800c0890b404900b0f5445804410a1220608004040e585c01800d41110000500032160f0498000c2d0034070007401c1e00d81404058050b03400320383e40d215035000500003070f020034400c0c03c03407110f40c41074010210f000b094600c80d4040e680c0c950b9030f09024296260008a64001000c0111641000814541002c11108036060903002d4000ca006030400380b242c0c501c0140d0702c54000d01c828a114020640c13050007d05c04001e00000024032440c0041800b1054010415a9018030b244c01d01c240602d0034043c1c40c0304000b0104402d407070f8800c00900141c1d0305103000e01c410300078480e916508038880c042c000c1000014007a032210001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 87744929 1250 87743679 87743683
    0x171204091a030c030a06020c010605040e0a03080106020304060f0f030e01020307080f010801022106010c05071205060a020a171017030d0b01020309100c0218070201050702010e010e0705090a09170c 86
    0x56040c20701a0f00102e90190303499801281c0006255040038025950704466980c040c0100955042913034098035141681f1200c040c0040e0105000d4440c1d01d0303420260b6222501a0b07507901441c4101130004043c00003d61146d8411412400016460308002c00d0b0251320b0f08401c3e00760b802c2141d195000500b11020040c00d0642148140e0043c181c000007180340881c00c142c15940144075151081c0d0704050034000c109540d20404010003000e41041c1a00c1d68551034086006406114482c01d84083c80342001060a6600d64405c940441c1090b88440c940d8507800a452400c418009001d101c8001e207403480010100a80e01c0e000340e504403600c0145643e5003400000008030b070300d907105150440d401440b1001840d01c514441d0554800c0505010003417840a10000e820800d0f0681194013030040c510074050441d805400c603c0c003c5076590024006207405407056822502c4810183c80c0941c0038000820403801c160503401e410a92032070004c03504148940724003407145d1259144c2030401d00300048107503c034042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 87746179 1250 87744929 87744971
    0x120c011d0d0f050a050a0c080403062d0c09030f05070b03010b0a09080102070218190903030c030c0c0203030307140f04121a0105030325021206010f05010203031017120409 75
    0x2d0600e64140351348294000c0003030040c0f40640c4107203d200b05170b80042c091010180c90080d5030040040c0111a0045420381019607407200ca90340c020b545540540004c0f1306070080700240701c01940d032204000d2a41e141c40320300c10b5600d00d0a82d01030142c04c402207140c203202c400840c0a4044642815900c60401e40000d003a04015803102403181d20500007240165203c0055810745101d0103055000740e1141b800c03401408800c94148501d09140541c68003c15070103822540442d44982c50801400f403403080d05030b46d01e400c00706000b54944c00410004800f18000c00c1000080c0e40d0400e00b103402d0850040145140b584240c00c0200390003414031404c1d00300316a0b43c25408500035000c10005095150001007a90ba028510400039903924100c445561441c18903c1c20078071f660010301014400c050780d1b01640c2c0341c5000780a03500600c0049040031556500002c12280500340d809001480e00340b074440c8240c24030030025004109800750343c0e465801000701c403000d4009003082d207400140803210b02c0300c94035a40351 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 87747429 1250 87746179 87746207
    0x60601140c070b0903120d05160206041505070c1712010f180504110402120109050c0a050702100e060d140601030e0c0d03120207050a060f020c120c011d0d 68
    0x1504024454040d07030045812402c45018034041c40d212840c100c0024140000c0f21800d440ca6040454400000c01a0f50462400381c49003080d10310480325100e1003240c8030302003200d015296003450b140c0c50101042c0d0b41c0c031180c0c2c011418504041000c0309135581c4d0034814851090a9001000030a485007400c5e20aa0341500424440b191004c0c00343c40c5c1003850030408600311010100c035a845002905100c0740283d4003c1c0c8410050003196180c01944040c00a000c081c0140c031011864400086d04940e440c4044401510f5217464030703401c0c1030040c0e08200006402d04c01d80010007110300d100c10707100c0d1500009880124a44040400c01c0e013911050742980150090a050401d414490b03c1481030101140c151000d400c01c1d154803824070544e04081e11040360a1080c1c00486100003115014044041440120b95200d51810300611201c1800c11081c0d000700030328545150000030050b0700d551079000051004a030100c00104080f41025206013201010056030007550700440e00038400b0715445986c0707880c604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 87748679 1250 87747429 87747467
    0x204050d0318120f1401060b0403080d050c0301060c150f0207050d080702030a0f03020903280317010b03060111100c03050414070b09040207140a12120501030203030703030b06120108060601 83
    0x91071601c0c4c59100070040302c030103006a400341d600c0100b4030b9000e41100d0041d000c0064050354a55803460721081503401101a540740318a4038010402d9603aa81017224101c40c0c40355114404640c7c1515000341e00c44502d041c440c2c1095030340408084540c4907002512009010340003030901c580c28440003400c0110300400103400c6400800141540b01d401c0103250305c2c0c01c0440d00e40140c81d101c100000c24a0010300b12510280805408101c040049803803081e50104c80c40307035882034810ba502c080842c540450170700803098825414030001b0900d510078400445184120011a1001c9400000041c2100c40c07610111002944807003c2006101c404c0070181e00c120035010003080c2140c500b5886a00d00c0c000d201d00c0c2481185c0004071030040c0416450003d09200c1a4025920148030780d2408010303180d424159840462500160441581d010b48175140c1245c0d0046c01a502c4d250baa55412030080501c541c1e41640100c0a000341d1807007140d84145a8040d0840c8001040e460034200005040742d14412622900c2c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 87749929 1250 87748679 87748709
    0x6080414070515070609020a03120921020603040519060b090123120f0322060507080301050d060612050a0b22140102041e03030917060f0a0204050d0318 67
    0x5910f8100c1510200d00501410640b18440d625110000d42040e8002960140791341c039010040c040e0030b035000d5074030354060380750304000d0b65580e1109890007a1040070000030595078903a090160030070300000d41d402440f400c25a101c0c1044e4403044070490b0f580b4a400e668072543e480505034507040c542ca40c0c81c050000308113403550012510300c5106090034001c5480c1c0c0101e10511418141e608100302840c1c8860710b81040e2603d5002d501d0441058a103414031202900d03000c00c400040c0301d40104100c40c40d198015041e980381d80e081005010b409515041c4c200c0d425035503a1400103800300c00009942c4031910034005000c0c020b110f410203d010540241446d04e441000c40f00e11489603980d0303c2082c203080c1c6d01900002c000d80e0300d40001c0b80203006907404a1146415008000c401180e281124019640729440380950f00e40c03248013070021b80d01d50104103016540a20041013501c22510342c200d50040d040000940ba183c0c0b82c602045481d10b4603442107021500304030000301c03903507000d4024401412181c05040d1103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 87751179 1250 87749929 87749939
    0x507050f06120a09060b1302030912070203030f0306061e12010f08191109040b01030b0a02030c04140d0c090b0a1403060402280b0a02010c020f1b0d0209010608041407 73
    0x61500152900f060269510040410000541c00020880000403d08240001c01080d407101950044903820018002e0200352a40c021002c41070b101102c0c3c018000714106035001483c080079600c003405442d440b5400b401b240c403440c1d10b40024103d881d5294140d030341c5c49900940c3c034803040a0060300300c0c030508030032004184800b2100040f0b000d1280204e99081080f00901d003410541d01210100c0c9507009000d5800b004203000d120300703455040b64400c030160a4503541f05155101280000d40f035895070540104130803c881341c05840e1000404100400b60711920107030b42e8134000c000c80b40b907000d0345005441e50502c42551074003280900041191026003012603140500003500c034940144000d124801210160035854003a85181c0c054007150f14034602071685420341c021007a0000c18a0750015809c000040130010f1001c01c106181102101c0245040c0c0b141c4003120f42c034030740d03001c28003500132842900f030001603544d03240e03d07500070020703074943d40900e04003070a008894080001940c42036500171201045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 87752429 1250 87751179 87751207
    0xb010906050a0509010306030c03050c09070305090709240e07031a0a030605040311060106021c05090102060115110312151c030503061302070308091908070b0903160507050f06 77
    0x102540b5240303001552681200010f8005114a8102800c041c528905c0801001f000048411840c00704841c02c0d1015981c2d001c1c00c800703580b81113075120065081300108101920b0705401800c4014802e83e100f406154000c80b40072010780840d03101588042541060182c100d8261140d0055400c010b0b018a00ba02c0c40440407468015043c44000d0220750b40c0d000050506214030400d01000c41c0c1f4000380c58195039206c3d002542c91b401269660b0101c40701c00c40020302e86000e003003190346401060b006041542e20704400c41c4c103c072103a01320080070b101d42c0181d00090350300140000c0203aa1000e03e407148050404156005e00c0e0358032640524000d16001d00b503480d034944482020040a941441c2c0070343e807561000c0104043d60040d01500da0103030700100d4007008140d08030380703010303c280100c030308440e2803c8000090446072204a2009041002d0030003080740460010021142c0c0942150122031504818810100603220419429901904403c0d070038066460f0251041e4181d6030200c0b2400e04001d18104011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 87753679 1250 87752429 87752437
    0x15061c080f090a27060b03010e13060b0303040e01030b09010501030b0c030a092414130609080408070f031b0b0a0c05010f02030a06090506040e0c010507031407060f0b01090605 77
    0x8001501c001c14000c0080d95003803280707406068500001c01480003442d154800d019071041c10112010b08002011468000140559041310750b1aa40c60b0300742d0315083d1000c15843d100010986440361200c1c00149580c070100010002000c074001240c03101d40c0345003003110040030040c02e040f026034100f0004201040c10092065000f40c03a661003541c1c0c0c1e4950903140e000400414000800540c0c408140c40f1500904254000fa00d25040000b4031060794940d1a5106000c0c085490030f10908420700c0c90004200141d12074400b06100b601254074150b103403a2502d10301071365603208088409080c00c0900401c42c01c20200d07103030184c20000d52881c20b420504034441902a1740c0200080000d401c00c0141441825084a003500c0f9421908564a042c0022804090002400386100725400c2c130001c960b450034640314079011f40d0030480251414480310b200444199028030f1041c0d04103c00c10702001c803544101c6004040640c45000000350703003140c030100201542c03560400c441c14032070f02d200200031840d0008103c1e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 87754929 1250 87753679 87753697
    0x1104050403080f070203090d0c0501020c0d03020d030209041503050304080f030901080601050307031415030f07050603070e0a03170304020a09090209070f120e010b09010819110103090515061c08 85
    0xb80070f640d581c4900300d103980070f41c000e1254003071900d55800052200010122083c2d5a00703074242c8a0081d41c080612480310107001e4000c0040c2c3c0905a4081c030188030364003404800100400100c1c5a06403030801310080c61139078000780c9050308001400c11080d0b1003003000700820804003000c1e505103c0b180340040c020010082400d4113004000000414480c4240e202000428a03140100401d083c5011002c06e80b0090006490107803042d85001c174000e05d00051100204c5200800f01803071344c0e4039407d04440c400c90b1400381356007001100f100400050300c0001d43c2c2c541c1c002c00302048c685a142600400900f461b40f903001405091038030540350003507202e14480c1c980c40364541c101250514401c200483e4800304080501600320301d0444610f40b00300c0e06401494100c0c0d0101c4500300c45036200da55064484400440070104032480c200783c0400200c14145040c00c10b90141400104180c4a803501d03410300070720782101d03030205d003005080040e5842c0102e03401c1600071000542c034040380c0f825600e180c403900c80c00c0e0381 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 87756179 1250 87754929 87754951
    0x90a02010e0103091b08120408030d0b0d050f01091104052724040c0e060303041206060909081e0a021b03010b10020d0e09060a1202031018110405040308 67
    0x10100907406038100340b6065601c05403802844004c45c1c074138100c19189009402403401001080b010400101c42550103031585480614608010030b08000300410b1036010141d041104011a94080343d018811031a43c802c0001c00850111a10302c0e0014107441514000f5105a140805110700b0810070340d5840b07112107861154504000040e401075242144141c0319044650419000e2031540600301f03d2140181c0c41491a042015280c0218004074441155401d4040d44140000c00604451000780c1d0b042d0350140000192280e160740440b420f030345040c2001d840c84440001c0791003242d400f520101031404420448241081e40350350009444012025101a20b00884a101a00c0ea90294440b0311004001041c081c4005e0708400081d48941e5006100c00c08038110110480d10390134441047c0d481000d0090010441d903003003c20208051800c1d142c26030301481102071322035180d0380911409400701c400c000380f4420388040789090200000c0007250f40c2e010b1400d040500c00065040300e0015088280c00c24 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 87757429 1250 87756179 87756197
    0x2010e010c0c0902120a0204051503070311030705030619030c05121c08060a0f03050316030203120c130920090111010213030c0b030702100e1207060e15090a0201 71
    0x101c6205001d2940580312140c00e40c800a0780f0318081c3e0003042e4035201c8030100c044603030f2003178418012400b0302d01c140303031f00107500c6114810081d101000840e4041d1b032a080002d490759480c0608c000c107400403514500410f000205210692806040b01c1e01c0b40c40c0e903070003010082170441d50f40742c4200d2190320030a80030340078506402021074003d00c410341c43c1c0003083c080020112403401006005500c261201d074022100d10201103800c40342175183c04240c1b504071004500d402070720310408071003030034004040e8111300040c08400b0740749402d50b0f20203029070054075000d516030100780001c001c502516070101088500c0d01d060035007810700900c1d52000440790040e0141d1511404801a503000941c41000f0b40d81303501c001071068400500c4410901601d000700707411400e1544540004c03080c2d00c01a58a0310240c0c1c042158480010015080381d403001d2101415a41c00070051601a1640d8221110440d40207407680e600c170314010b00402030071020206510521001e8100b0b5817083e519109a140043c0c10041741c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 87758679 1250 87757429 87757457
    0xc0e060903010b0303130e090d0206150a0306050403080702010c05090312130e01031b0506070206031906121a0f04080f090102150c0711060a050a081308031608010816030201 76
    0x940180e640389409410f881ea14542950242c9a190b1580100d21f15800e044012a54106000179084205015034006281c9030700d50712144450340000080d4035074800c01c01c103c0170000480da030107201c0c000c5200b5151074140341030450029095600d90542c1008021003481101c1d0f11740e42c00030f90081946283c00f00c8a680707601c0c200740d403080030500313030040e540100240000104024040840c10200c0a0529001c04c2c0f203a240e10402c4224414a0000780d440402407001c28120070701c0718030300300805e20110000112640d0303900d00d18514252110064842c0f800b1403625006040c5001443c80d8002e40400c00b04600703103055030341d04606026445940c540b401c0301040b00b007a035034020803485080e000041e010800074941100ea40745940c1c00524100c40c1c2c0010f0381c05a58843c00c10a05540d0b84080e030741c45c0e0a0401d980300d40204d42c1410000e00301c0154031181042c60003c507030680011809055400c0b5680d5401d110701e00301500c0c002060717000c44015488490758090001d090340088081da035091800403000c1c0104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 87759929 1250 87758679 87758681
    0x50a0f08130209191806060911040311030c10020c04050609070503010308070314070f02030d020a02010e040c090506070305040e0114010c3305010f120b152b0b0603010c0e06090301 79
    0x200504d10203d6103014200380d035a0414111216000303209a5003401101d44480e00c1d00c084d111004848489944140010310014084000035202c020000e000c854440d41c041001507030703407030810301c01c0d6000da0404400501d850501e40202c03580a01c044d980150307542400b0304000d05c1844144400390080001080c80800c00d0304c185810540200c3d18031007940c545180e801c0942d59180f401000f02d12a205145000020034008034140324940d405031900802c514007481884013403c0c1d045849000c000011001241542e00c50000c1c10344503010340e450310f0700c503030401c10b84a2200c0f0040e0450b28224110b49807091141ea80000d114801591002802e4001018000c00640450510444541e109005204640d00121640c401da048800340303d110110f040c0d84500c40c50300d80074000070180214801e0400145500b000030b640c5050884054035495200d1902c44011501d81d010021012031170680300c80c00300a0000b0080c0590700f000d000c4000b000540107800c405002c0e440120384241c0145800310f030340c1c409c6a4003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 87761179 1250 87759929 87759961
    0x90a17060406230106050a0801060206150f15040e090c0109080303041b0302090702060a0f060303090e0912030c030406050109050c07021e030a0510230a0b060d0c050a0f08130209 78
    0x3c89050f00030113507113684010f440d03030b0410a540e1300011034510000500501c000350060007100b50141d5007a0001c1007000780000d41a103164641d800000701d01900902c00481d6005200804c4000103c501e00c3c1800b1803010305000440e5402c50400c1401c103018410141d000c400c40360800d900403041c44101c40010a8000591043c1d480654000012410414190b80202e24a4800c0003800800c0000c07403031403680d00c4d04079007650001038001808038900b844441c0080700242c0c0c10038070040490b8440e0801c61412482c550040b518a00410740c01b00034031040001c24040c26015003141c11041c002d5150110f022911806003500107441803058400d0b45d2880d2185082e17a066007040278050716417801460a10a07034801003502425030746894420036054451003410400801031160000d54144e0320b951100c02c01804401c0307003066010f4000c004a41c0c84103000c0c81000b18603100394650076100d100021014114480b02c500c07040901c01d1480c01c020444154012014520f6812191940c0e261509048000348400d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 87762429 1250 87761179 87761231
    0x12150a051e04030206090601150504030611090d050a030806010306060e0405101a07031b03050406140405061215041a1c05010c0c050f010603110f010507020a0b090a17060406 76
    0x1002000340300c203055010404038486c43e4503000303c602d41d07640c4600450400400e04c40100002d10b051200b4400240ca941101308512202c070300d00d5041140c0000091b101e14a50002210903a00801c141c400b00354024217483d91283d42400c1c00c100c0c26103001d002500c40882989894440e5623650700054044580c0074403030b40900800421003980940c0c1d1218001c85a0000750107601007810f100010702c070385440e010540310450b4140d680a040c9480c140f01507803682d042d0111810200300900000c0303501e07110f40c070250070f10b015108502c1700d00781040d1801c900c1d11a40b071043c2c1409203061030000d40071507660307210103a15240309a80c40100d40e03040e0301c921981e140c15010020100e500305050078111a910030304118189001d80c00f9628030504102451b401c030b80852000611807001140128050f1520107011000b401041c100b5a2070601c0c0f43d4009121b00d0166000400321a001060f001247c0c24895681c20185c1402c4002c2240c4107a100d407803d503114001040241080e0301c0301c2011240b60940604081f20398 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 87763679 1250 87762429 87762481
    0x60b01020f390d0308071b0b010f05010206041106130f0f0f080f0d140910080f0612060109020f040b03040303021804050114190f0b0912150a05 63
    0xd8401c5070541c84001c180c91401c02410301e04590300c107030030703562410304140c0b40040c100d50400e100795400b540e01c40d00041003401031101e26801d046204100a21548110784071b04256a0a58182050040c0c40c034010307048541154040c004202c009140c41084041c814400c86900c1e80369158003405401010058000000700ca001c5100004d50408600c400c80580d002c2c0084042e020b616144c820f5a80c1c000009132440642c82600d110104034054880d003181c2081e40b401e5207140422000200d8040210350b04503c0000c0c0041042003000078501c0011900001c0485002d0411000c400c001641c520040c0a11420300b0340c0003d0410300e595003001140d00801c41c00034041e8880c07503d07040c081e000390843c41f10103000880c24852503500380b5040c840c0c1810380300400c042c4070711034803160180000c000200311441c004004814010540103403003042c920081512261091341c0d41600b1050201b6204040d03242070a80e40f060950341c810440100c1da00380d0251141030009103544e03a80800c04020307403811043c1aa40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 87764929 1250 87763679 87763693
    0xa0e0c0d081e090f01030c05030c0c0a020402031608010803040b0703050309010b0a060c0c0e01030c1401030f0f06051207030305031603091a150a060e0609010e04050903041d0601020604060b01020f 86
    0x341002d20b01070200c2d104210b41c11080645000015016513030000f00040024034100001180517038000b01400116254504903034505001d640450203c0c0c9c0140e60f441c0d6801007800040c20000e034090119409811071401440c00d1610344894a841400754a5000b810f0080200000d28400c0c070943c0203040303008000381404241965000d0191100f000c20b80252117440c044000404d070007494001d4070b8120789c0c0c01000050b00742d292800c2075aa103c12400500c2c105510742c4022b4030050414081c6c1004111307230401c0050260320b040204904c80300c0318003d200e4130340c020203001c002281e00f05080c6c076801349170b41c0d08079051300120600480003030600d108014041d0341c0c2d11640e0b5090501c1018114898022102e0b0702100644140810003030b00300920405000440e51440c02400e424810054149010b060400104500445000405076002169025210ba0010504000301107020401e40300001c4a641701e4121402d00c1e100007925a05d0003400500101e4880c4260740859201300410f002d0310300349034266045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 87766179 1250 87764929 87764977
    0x914070f021e01240303082a030405011d0d120908091912030801060909090f02150c07030f0201030b120c01083d05030705030a021c050a03030e060a0e0c0d08 69
    0x13802076603000680015950380b0004401c2d5041000302d800f82c16280c21641e1880b06202c00b00000c3d41c0c401881103c03a9501c91422800c031405412403025403900010250520100e00e44004140d418640310f131a0203d41040100307400310300c1c2007045442e0440140c800a100c04051010b44c054943c09a00044c24480300c02880c10501d81d002c0612070682d10140d4070b00001d240d41d220000240c40901d14081c100d51210001d540042c40d008425004d549a1b034580c2e50704080000019504004079540192250300741020000210340c0c0c144282640808200c5262034009450520a603070b0b4a0403144945c10b000d04280072680a0182c50101074284040312808880305400d220a040340c070344131004040b00d2110420022441d031602203907605c03c4e140041d00816400c4044e80802000c2c2c5c40c61b1700d0341c421408001d1450004650103104481e00742e802514040385128958860500c0c10f0401404001310620700665102401e00104541002d1481250b185940d82c01d40e0a100d4420f204980c2810b03410380303005102e408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 87767429 1250 87766179 87766241
    0x30f03040f0204050f0603100c030e0f150601051309090312180c053a050303010303090e0903120c0903010605190810020a0806060a0306030506010914070f021e01 71
    0x1c41c66109540a2210351101828603424003c16542c0d660315402044040b0420301c00e50b804000401001c0c030300032800d00501d44e59103040161120b14110150881031004110000510140d50402c200b0720340b4030b01d0030130f41001c40d1095492074001e078441e264654400c01c3c2450321501e900800d0085804c0c0c104131046210003000c4545c50000c1040f076440d00351550005131071070480003880c1030700c101c401c88080380284641041c180640310342e021910300c40f12195240104d0030400286002e14031986a983c00700f424200000c4034500c00a24000d40c42d801000102110034496454542040e00305001070380380d59001c0d0000e8098410b640000b81c00ca40c0c00d0302e40000120240510408580da880c00340c664a03401140900d09900c24582c1400c04616150082491400c106c40244491011403500280c00b980341c2c6d49180c142002030307100000c40c42c0c82d82010121684d600e6849034100310176040c10f07030038075503d4240a5281c184182d420724410b1a00121410005400c0d006090000d03240d0a92501c8003441801001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 87768679 1250 87767429 87767453
    0x2010f050403060f0e0d110c19080706020606090109020414060f0c0d0806040c18030809010c0c06050d0608060402030601140d0203030304061a150306130605210c061804020c030f0304 80
    0x41e01506c11900818102ea01401603410311f40c1c0740d100a0038030042110280b00c00d0b504030409220481820101c0010410401c2c0203001c0604444c1d40a08040c0c1400d2040003500c54040e000900000e104000030441c0c0718402c0041d90181c20242c490030b803900783d9020035000c180200b151418460040030740d9210019482222a48940b4048908002c0b03514802c6084550307040d0030700d0074442c504c50400d043c408100800301810607002c0500d010110130041e5030f55228290310aa0100f03000c0780c00400e00103610711550040c0400340c848030340103007a03074a03081c0c001aa5500040c421001c1c03901908619503515211074002086491f0050100c5c5e549052516100c002490f1070200c00740000749100d100305c454501020814092001d82039440e0640d190082008502d1030f8070104100c103595140070011f42900c4c0d140400d10b907030509442c0010300c031641c40411401e103840c00c801640b20398410010351940703502920b0004c0140c0400d46e00181c4507010000024514805c203070501c3c0c5401d6000c0100020010401400c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 87769785 1106 87768679 87768701
    0x40504060e07030b01030221060f0901020d060815010504020f030a0e010207060603050a020a080303100b0c0c1503091902060706090c050604060f020c0a050d02010f050403060f 77
    0x640c0b0749032080e44122113070f40300000108150301d0034146c1d03010681184501070f0450401e0710101034441c40002d044c45099500d0340c5c0030404514003503054441c40085451f0030014141c60f4000169240014101c98140c51200000030a5504050003a181a44e1000c20600e045850f8104014058031034661549c00c550341c280b24600c00b0807180d000e0203005601030350140c0b100203018014400e07050100d400c80c1425500400030700003201081842c01080ba54032044407512501c0c500029801c21440c4c0041c9948007003c444002039001c400c500941c02100220120742c68100d55484c0c44c1e48000ca14078029502c00d0302480100e0201d1442c0d0041910b4502c9007459205517500da0340020303982c1e00705400140c0001c8800140840c2d0a404000440c0c510404440c2000c076a0f01e80b0340054120001c50310002c0c10441d1200203031312514056004d03180915407040007070200410300300b4144c004000c20488 = true := by decide +kernel

theorem cover : BRFrame.Cov 87589929 87769785 := by
  have h0 := BRFrame.cov_init 87589929
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87589929 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 87589929 ≤ n) (h2 : n < 87769785) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
