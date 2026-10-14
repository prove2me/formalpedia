-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0420
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:43:17.985318+00:00
-- url     : https://prove2.me/submissions/cddb8e53-e983-4fd2-b779-3e214772fd68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 75359714 ≤ n < 75539570 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 75360964 1250 75359714 75359723
    0x80105010305070c030f090512010515010f0c0609020a0506132103090e0402010e06030c09040c0f1b240b0406090b0a030809030c040e0d09060914060705070504050c07050d02010207 79
    0x7922501074800310368801e002040300c0100181f54500164990310500c1e040e0070700c0300c58400055075060511025030042c15001040d414021b40403800d0040940060030f481e0308030f411141c045440300881c170000d0703800c02e1207800940d0721283c00314503c441007071031900d1344007602c166600e80d6035a0040245200107501003884000e00003410f00c04103102400c40503c005e40c1291060500205404072200000c0103030304126028610341c10082410b064900c0d003809405e07401303045420841c00240340c084000700b210104405565201c0c005142c14420000f00980d4100e061102d03501078910003005100c50800307001c0504446125900b003c00108001c0c0c2103200e03001d400ca90040104411a196541d00d0400703810140000b0b9150040c0303205180c039034886005a060300b0b4241c0024120402a05230003400da0606034012200304558408140070814600c80c40304034240d0200ea00340e4507200d0b14500140f03848216082280c10504140601049016074400303841154030a6041e103c0301e04001208900300d01500c138000c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 75362214 1250 75360964 75360977
    0x3120314010f0513112505240a0e0a0b100303020c101b15060b030105041d030306040f0905010e0a0312020307050406110f0115140a050f06030601020a0b01030305070308010501030507 80
    0x14441c00c0d0710001c5500c500c41070172400e0803501c0c04420f01295100f0641c8969030110b101d117104000081c400e45501948190454049000a41051500803001001c40c07000300d64440da807034003a03d0104100200d0643c0480059594074001c03000300d4140721580300482c09803241c0c1408080341d261052030072014000b290b556140c140014502c0ea400e4080c0b028061300c5000c2000400e00d100c1c82180a000064842000c030280d072549000300b4801220306c2001c11a44135000241c55100c0160040200ca40040c8100d5020074060f0030004050001c00400c10020b209605e004503240c1c4424000c83e00e0f101702e50007921154881c0c03000040580c2603100840700100040e03001c100900166008400c121f0304690103900f15203503160b10103060350859910700007500030400300d400100300d404611601c5030541003040d240307428082d141a011030a280281d40e4500c0c842e1102100090460344208952520745d41c00a60a28007543d5900700680103510891007036000030591000410f440d4000d02503540100707a80c1e50b885 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 75363464 1250 75362214 75362239
    0x2f01050c0c01031e060608070f02010c0909020d060e01030606090c05160b1312031d0f0307020d0204091e0506010608040b0a0510080d181a1605010603120314010f05 72
    0x1100101313401d11202141c0011500700200700002449814003a02e407640312005a0708014070080d184c10301040400045a0601d1141c1003010340c03081d0150101c0c1c0010001503207a51840740c5102c054031680e001f085400da104400041848600e411000c2100c0014404008007031051108681600c900084906000c1200312540000380282d04495413101d101d080754282d00c0e219035201c806140c0c1d01520040026150200810800080c00c80c44500c1140c44000b01902c98170603189640724041c402c0040d00c12018082c0c10070545d1a5078000114072075012105262007448003c095002c0741c004001a201841060004501240507180300e5000b00d8101d590090305540700740c4140090980240040159081103c0001d1501002c00c600f5509aa103515140c0c034042440c04905c004e08101ea108401032002c003c012040b904070f200880751242d02400540340c0c0748016003880c501400340382c1e02c0107101c00008000070044941c182d1100581e101240c0d56821207036030301c04090300700c1116402401e61120351003045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 75364714 1250 75363464 75363467
    0x150f0a0303050d09020405070201090201120203330a12060506030105060f0d0c03200117010b070807060e10060504050709081f1806020a020f0304061b0503072f01050c0c01 75
    0x3d03041411500d02d003c2180c01055010401303444003681d00c00050b0307448110800441d81c200c0040c01030300f545c00c8421070861030848544402501501c000310400c176443c44591070304c0e52132007180340380054004d040350100cac1c0e50381e600a0201e542e40308825950689010701003a00f40c64180105070007030320000d1490b04050140c40070808032000040080318084654000000010800c200700c0322284208018441d10205690015240140e01103000200c014114014852410b2030f505582d041900000c006071035200514140b0000c140c4056101c1e600d204102c8000c00c01d480c943c104c541581d40541d03080c01a511118001d4031803003001e024902c5160058140f13404595000c00b181c2c0d483c80300c0c022010800da02c0380085101c440001c54130644071280c0020341c6d03000c2680c040203150b103168014130003140340602d00365000300743d488205101c030350283c09102c80405220040054071955604a51034540c5803500190361100140c07400c0c000300c188039a581d61104d0395805041a40da410030382c00003402c12521001c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 75365964 1250 75364714 75364717
    0xf010b07031409182a040305070b0a1715041109030d080a0209040501080a050105010806010b070206070303140a14060d03122307020109030311040506070b0604020903010f0203150f0a030305 83
    0x260b0b40000e80150510480e2000341801401007444143d10620b01a030010b605c3c2d120340328502c141a0180c410001040007880001340e4030115010642587e8070f43e86521070494000c0305040140e08401185400e108060502d07400080803150300b16001c110300754400e040c03900c0500603503840c0c6a160700809210350b59580282802544014a168018540f1400c440098210340003a000a201644928138280c00c0050074450a4090040440142015807500510220038031651100900403840460380004040c020f40020075000d42c1038117842c1062501c480200001c0c850040880c00420610012800505018103032000c040d8055a40c1c101d0040c80303503020030180c0501302c0c0e03a8105100c041d0f004018000700b070701130038001c500c2070780040360b50b4509044c01819691440c01404001c03600304001c022903075449088452481d0700500a1000390381c3c40d17001500a0040c1c0d0a4150103500b0591441000b650590095100d0b2907040ca207005030005060a001245010194242d0011407920007880464007480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 75367214 1250 75365964 75365977
    0x903020c030f1b030a051b1305010303020309180c0a031e1508010f0b0904020108061908030408060108060103171e0d0f0f0c08011211030102030408030f010b070314 72
    0x44441410901020030320700284400d4562640d00600c03c1140100c03541240b03601404011001095442403907140c05454100001107410241d51000f803646042d02c40032030584034000d459200b00515030b940e080c0070f0b440ba84901070741e03071003603106621138101c440103080014082e001c00c0d400c403800c0c40408a402c0d00145034400480c000c0080381c0403410b00b10582030003440d40c3c1580c01100362428500d05035079517094a440e0502494000d00300b86214401e501c0d441191640540c091900301c0f650707103441001c03600303c4c41180d080c0e0040c1c0001400c0812140d80000c003c2c42240c90650481e034035a07a0710070065403100005e020003800e207891614149211142d02003c0c00703040720342c078503110150750803948410829442070800e03071032058813003d00b4400311041c0c1c03046c040c007411840c0c1c061005510715400101244014000e120818104c400098117100590942e207454413800350086669061905184c641a00215070314003032850010008a030300d8131444185c5140aa143c1c8480081d440070031200c1c8529000390 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 75368464 1250 75367214 75367217
    0x60311010c050a051b120c0f06030c070213021902061312090b0a020a030f0e0108040b0702070302061804051003080a080721060e1003020f060307030e060a06060206060d150903 77
    0x4020707840224100380189070b0035141c4803003c1e000c4a0191801c6c0703c4004482114005603410011030b20074540c984402816610004481c240d5072540c442c0400003890086600280d0803c01e900109440720003568003e000c202c480e01d02c080d10300b4092103401c9999010468054086800390024840043c082e4400050041918100529490788030241158190062040080140c0c0590a0380d41815002401d56000e02d49501e002801c18120342c00182103000007a000030952110040095042c80c428081c0c600034660041c1f4003559100b90130b40d6101e003080350f80b001900c5980f030880807030a95035140801004890344002c4081c10840c81d81e0098075007200c000c05800a202441e06207080e0b03030040380d03200d140305030300040700282d403504011504074070f02e20080c115003000c50032200c28000369403080316004982c0c400702c807c140c0c0c0b5610a0402c4026280a10345a080c910520b4140302c3c80b5012900b02e8401e41d1103940c00c4901c10340c3c80000300240350b0724007900500415104e600809003040207400882907a07000303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 75369714 1250 75368464 75368473
    0x90d0303061205060106030f181b0b04030803090f060105011413170105091204050307090e01060918050105070806010c020f03070302030f0115050301060b0a050d0b060328060311010c05 81
    0x2d4100030040c80c1074000040720303241c00010040c0045900b6100710710380110041810070000c0c0468641c54000407103400d01800c09401c810f0700b405071a1804150030003924180d400580c940d540d9103000c020a42084da0036814501031004240300703020700020081d0495105a51f54043d500c241e41002d0203541c082450421481405540070441008140040e40c041503030800024151400e20401ea00307100c0c1c0c1c18000340e110b040c104401c000e140e40004156087e1138041c0400245440d40c5000d81d80108441c7d44441200380c242140c407041858401010483c250140000380001c9d504d151040b540070f0021201d081c00f04001d0044030000d030900c69541401d050028040b200456183c3d0006881c0811140490b00c56a4460001d2114038080c4d00100000f07100540090010300d003854000d411074019020108200440030444800001b0240c100f14440c042c081c00141d603038144105680354010349150940998003030320003003204d002060302c44c0c842140d17003140441e84402c02000c01101c4160300d61070180d038944036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 75370964 1250 75369714 75369719
    0x60b0412030e060903061b09060f0c010b090105130f1b030c0912080301090c1b0506090f070302060301031b0b0a030605100c02130c030e0313080c010908030a08060a0e0901091b0605090d030306 84
    0x109c0c034000b40f645d900c1c8840020340700d1040100d0f003403c0d40c1d4420400c1340a80c208000401c00d0303850741d91100042844007a004030740000f5010041d802400d03000e1082c05103107603c4000080302d0750180d02c41403d055559441c030008540f69201c0c100260044203005140000801c0100402d525680c0450000040fa10340300000070030000031540a52509c1c60142c0b407541000e010701084040402440c1c40f169040c1020380282495600060750501051102410010340c904807101d03030140180400d8050b1180f20611910344660803401402003c030782c02414054200074142052840c003c0350f03003200c070300d81c000c018030202d181e00c0c90004060510629000306054440e0b4517018a040c09001514203101c48280e11082d240c90030030001c2c50304142e18005414840481000d000b4002c000c002c03190a40003508113522185c8400000c114070200303d034072810b14901c404040c482c0a44040d008070750b41d02d00030b80042d46c040e00403280070240c40c101c1d4407461020403000c016440c483d040881c0140003450090400250f0140d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 75372214 1250 75370964 75370969
    0x6020705010c03110d090e07020a2001020a02180406050703050103050c04111b01090b010b0a091712030403020f01200d0506041401060f03050c030402150706060b0412030e060903061b09 81
    0x10030490003172000c0780801d10103000821091a000d82d0010240c80281a062001c0d101c800307000c8640648140303800c4a031402d0b645c60364020041910425030160480e0544448090600401e210a0381c00300e4401e810300000c076028038401c0c021507069a4004001e013070322420302d404000040c90301e0b10354191101000d000c044400300031921070540304401c85c00045814250740c036055046440581002541003020320805443d6a402080141a01c41c40400f070703021403070402c080501e00007004130550001540001007004065001c108006010182d80080c030542410151200d00802c4040c42ea59403203805204040714000d082d00415041000600005100440102c2c0b801001c0400d8201d180420070a810308401c182e8140b180c144c0c80411410f48034118181680000c07420003540c174488030350410200f4030405000107640719200502010501a542e0303540c481c00300c0710007846800305402044601038142d40328201034044a9170804001c0c0584071079550703031b00c02c1006070b80d001c0c2c001c0d02810010b120711021038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 75373464 1250 75372214 75372223
    0x3050910030e1209030105012108030a020d09060b09072c04060302030a0b041e210509090a0b030706030e03030a020309160303210c02060601080c0c01060f15050406020705010c0311 79
    0x80041103d055841008009060a60307606a001d03001201c0782078001d003844100011210480c951001e0f11580e00c0d11022200c00c040e001d820b080c6170400d0f02c4c244d043e03400c104903030303000501d05403003079403016865074881201b80c5064100e03080045031411501201d50128401c10b20301b43c14a400180001603090712034010900d8140012000c0340e100f0a00800d0209000e80d1251900c0c148088035081c41880045e0303a03d1051104c5400e10140c0c041c02041d04907006540a80c054508400025210911038a00600d40300060595285018000d0140c1d5002054051080c01203c00c0110748500551a40d11991005e038002c0d400204100d92900075100540104046a82801d005600075034694200c02484491005400041114001101d02c3c000036142074030f8001c0f6040b58418400d00b4907042a50714021407211a10a50081180d41e511f400380200e45048005c148000399200000015030640c10b54600795402d100c3c5008030000340e8450360080049611500600119501c2880c00301030b0800c2d00080140340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 75374714 1250 75373464 75373483
    0x7020111030f0417210604111303020108011406030f091207050c040f0c020607030b221e060501021504020a030b0114040f060609090b060c030712110a03050910030e 72
    0x10446580140070031310020110420010300c0f0300028524080840b03a00700e818180e48081e02012122500002e01c1c02d95450b40001050002c00b00300d41d58a44120f0780b5180c03416042e001c01c0740850b01920001c64400c0c4580b03500989810060000d40ca1500c5807012812183c8004004106034824034540c100c0012226001c5d0010600c1000182031803401c4d03104210640300140d1005448516184211307240680c0020020380003000d60070300181640707030b0703001040e01c03000994161448034408240011018040c0d030f10007040f801c0444050121001002045011344603a4841c1da03006030301622031041f20041c0405581d8100303100800541e4125983d640d80136031118241c1c0f003510400c03010300d224415030900e0f001744648410102e070304119030703401c1180245c07000610340a0003148643d81c00c5000080e444c0c1004070b4485030342d0f40d01265225003d07031501c1c1202003a00d64000c00001c2904d00348406036100020603000703580c1d06840e402d083c0403e240a1001d41c1c2c5115004c1c00806440e04a560103222044c000e4600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 75375964 1250 75374714 75374731
    0x606040302041814121b1c0207031a0f04230a0308190510140607081617040f0603020304061805070603141003030513091a0f01020d0c0b0702011103 65
    0x409005034281103130f2000609000c030146400c040a0f5120100c50301c8216400d200045c1c0d0701708904800c46203a00c1c40d001051200c68020f10030b20b01c800c4441034001804e201146d10070380640b4a101c0f5a00b0904404101c1520708080c0c0310501400304d000142540007045160b00c04080403030800300b40e041418170f0040b0815007500418558001d000107860440101440c64680600034030030740c2402d40074800001954441d1485c2800b03165071030100781ea52442140d03440313500004082c1d100c10b0010b5440f030360030a21036400c8455011410804c0e20141503481628112400c109004540524240095010b036000a01c103c07420340e5039207403c94802d030103541210400c5019000030a60981000d030080d003141c10100450b00e0300310000080015018006504505896142c6051600d9080ca60002c8090407407541190608508000c03282c01e201300400c4440c00f011004030390880c4803454617001640c45100540049001030308904052000c1440f001070326401001d50310002507002c0d02110034010703039001a542d001e0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 75377214 1250 75375964 75376001
    0x220308040608060d120807020f0f03030a0b0a0b0306090a110a03051617010b130b032e03020904021509040207031d090603100c020102090d03050a020d1d0603060604030204 75
    0x82103502051042e4000000c2d03131461140406910750f22034100c05550900108041000011241c038400d000d560105c000e020101c3d400c12004c0f01026071250004c8402c402901d103030007041c0890340761415040d07044511030b5a5540c0b9503200e40e41070008082001700f80c9075102d5100c40c1c0010b10003140c28010101000c0b1650005081e04092090610091208034100d040101d0113190084605d51410340e20b0440b000210b509980300c0b604648403080c444a9804924968004002c101001c0c120980c900c08401c0e07100c0300e0303880c4140e107003101145400d51400040d401c00e205000003001414200c41c1d070328040001c0c01010381000380380c50029080c1e0b4081002200008d1807515403001440440c1c2003ca5408403c903000b000c1c510740100401e03034600503003019014460302c810104147d18000c3d41203900b685000382007401c1125080c20040e15680c0a400c2c180018400c041044900300d00ca9028002074030004213849002e00c1102e4200142900087c158a500c1101004000016130f518410a941580c00d0340c13070301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 75378464 1250 75377214 75377219
    0x6060f0d0c0c20010e0a21152405010503040c0506160501060612060e0c070803040c0306060f0e16021207021903060b0306090109020108040f0f0c170f030903030d0222030804 76
    0x117025208161009025103150841445070382400d4007210100031000c016001015550706002d41a03500f02800d85d81801c1c80d15040c8081c006442c0d48250b1410300107103003200d41a55841c011141723072104580160140c0401c1c0b005200c0c9103400802010740c80c44070b64404803001100d40710203007150119401000801c0d00015640c403804103500480b0028500640c07190244e10306050800140d20454000500c03001d80003000a0030080c10030b41d14005150840c80811a03a5154280903032400f80c1401600912007100c00080ea44002e04a010510004140d020344040441d8440d45580c50300100c8040341c0c4219420700c500e80c000507602c1210020350042c040400e0084c0003100b030504017038000d0b180c44040d904040760040940d0300213070000d0b0400e50184030300c0c0800da00d50034510106101480c1c000c0031150150350004203e00c5002034040a501903405030794400081c030350316a40e00d20a00301d10035050341044c031140307100101d140d011342008202c01c084144a16602440f03480010a140c00880300e103c40810705 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 75379714 1250 75378464 75378467
    0x80609010605010309080304030e13090501090b09010c0c020112270311061e0c040306020304030f111603020d030504080a0f20010c0605060406080a030e03010506060f0d0c0c2001 78
    0x12007000340000e0a0030000780005480720091351000900103001c0c4250200b603891a9120b01801c649030021000303041091110a2810710f000e4544070500b61180c00100c00032403004201032182002081d081c0e119806102a1640150b494905014001c0400f9a8840940c0e021120040604841891907041302c0315204140c50080c10038802c0c80480344660380200c1c208a41c1c05443c1c0c40e4501c10300e0340c1ca06031036415610030009010354031454000400640c00441400109030300700044040030340e4151601402d03500d00280e0f42c3c1c0d503a910320400c13110075850307032400304017504104c4a140d030308901910301549080d84818041d407410003400c10403075840c00c42c01c00341d109101c0b0400c1d201d03107200304070030304072110400c0400000d1038680d04501c05032940343d5500110381690b485034040001448a0001d8442040c82404c010344100b10049219001e07500b0107000a00390720b0960216041c4514000745282080a040d5040000740f40045510060224041480001c5060442e45983d80c004070341c0c140d00c040c1d905100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 75380964 1250 75379714 75379721
    0x314060106091802090d0f03030507110607051e1201080a0507091a0111150106170a02070b070c030306050904080a0e090411060a090509010f06020d1409010809100608060901 76
    0x101d4010401000414003403c20f01403201c10086014010141c0c60705545c4000810b08090404010002c220300e074424002c141c2c164108610401e240e0f2246000103849110040d160001214458000ba60411481001400a001c40140c0e805103580c0942020f802001c00c118120007a00149025400b540d00f8404011040251802030031400c001444540c5006191003d184c0b0f42144280c10300200d0200305080300c80c1002481c030785546201d540c4000c0e5a44c2c25002d410050260303d8410301c440030f01c000800200982c021602e02e6548044141c800c1d585e00001110041d070401c000314101a2600400150350741d40c04c04081c042c40c014045266180505072000c0d080354000340c55a8046d070030081c10000031a98021070081350303034404e95489503035200200c4121104610f0381c01c034603401008000086240e46021030014243e540070380890b41c0e081c800000950f820754882c0c42c0b00380103400400028507254412041d141d000041001140e0300840a80b1801c015a00c0c0ba400415040e4050700420407111002d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 75382214 1250 75380964 75380969
    0x16030207050c010806030f06011403070801020408070915080706030c11060f0703020f0c0105010902090a0812040b0a1b060c030617060a05060105090316090c0302040503031c0b0a03140601 82
    0x1011032034aa410760755140c86001640305141401a0800040c1d03860300e0500c05020f00c1030303444c411f035845982c40380522410401d00c0c0301c105000e849041004a49144148225400c1e1010310300140a603514106c0460080c0c5600e55060b40704a00b20340e0001041d038020000c2c840a02070342d4502090340e1607544c000403c0040c405003a6801c80c0c0c0f0560a000901c8288a0b40d140c2000c41c46c500543d440038207894040c0240728000080c08698a0013000040e0001d50768058843c180b0100c0e03d550120365541c0c6082c0e85c0d800240e45881010740104420030010f00048024a006d5a00c0d00349140300841032456003441115504050380c1c02e6440d54003003008240e2512422000e0803201c01446440c0f0301c40d1030740c0703956081e0080041c0201030360f4101207400360f8010320558600100003002c65450072603180650034100c1680c810600b80700c0c00c1a441038401e038041e00a507410340700b026004505090300c20984100c810000031001d01225910b44000b245516500c0482000e0750058000e14110b41840c1406403410005a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 75383464 1250 75382214 75382217
    0x70f0320010f030507030b030f07030b1005090705180402031e010b161415090a1406060f1e06030a0606090e04020603040b040c0f061710080723100816 66
    0x110002560b800000010480300245000505550344103019001001c010343d00507031602c1040d10004400303000081060035644162440300b040d88510f505000070b15840c3c050a42d0010900f000210110301c00c5010306800f280140b8509407080c4036201081c120303841522030740344000a855405194229a8208034010001c40036513516202c0f41c10b6030440101c50f6140018050520788104041034801001007120041c1d000d5603400c00c90801301c5480d0303929075982d102100d598146100c01a0800030101da02071140c0809005590040000c1c0c0800c05500d000c0c0c501040c00001142f4205003603214003014512690b2400070001e0034500300b41014041405590082041080d24420840140c40b02410f803074204d07a0103912007400e5165407a00d4a00c42409805c07644141007a0700000501d1644084c2e0700d4010013800404401c0d42d00e800240790504450f9004075513555204d110100301886d4081c40300d4001586a008038540301d800382d0005801c00c2e0b0307400d0b1040c0c001000c54091103d40002c954455600001c20b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 75384714 1250 75383464 75383513
    0x215070e040e03090619020708010e03091002010f0e01020a09050a0b04030807170c0109060b061204031103070206040b0a1803170306010c150c020601080109030206011503020903070f03 81
    0x948002400152142026401591116042160100100281c80f0600001807016856501d4403a000d170001d1400a18400140b090610000c1c0404062051401c09101c03440691314100452091090f030013406020002150b60ba000c1c03142074a4001e01c1010060074049002603541c03241030340001c2022074941c000a06c18401030500300201d40c1d514003200c007101d5104803d03644031796060400c440100a0106110006500000c3c00c0740201011350141e60a107102d41004c02609802c1c40074800540505020b2040310024a000b00d40403d0040445031249140101103900c0e00a403036000c90090780140c0e001440308880865107100154100c4000080110a2003001d038501d45180c0745c1d018428010401c04441002c000081901c903445050781202c0f25400440d48010703400803101d420000d0038a82c2d030b0f41005010319000410b0005042c0582110f091300b40d03004207866400c280d12030501e40700e14041d900505900708402ca250f9241071144a008240410314408c44900d5400c3c001100d010341d50303141e02c41100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 75385964 1250 75384714 75384721
    0x801050414010c030b130905031207030f05010e0408092803150608010c050a0e04060f030b1b0a090e0c07020a0b03070809030a09060c02040603050f01020c010e01050115050c030d06090501060215 85
    0x9680d050010f1551b426000465001141e080c010309504c02e107000314004172040300c01c10901a400d500011110074030a2403c10440c0c0c0d880d2944001c0c0c490039180105440c00400c8401c1c0c40d803400c01e21030050300302c50021102c50801007118060400e04298000c54a00d94520003010a0001c0751003010001d001e240024001541d41800061441c45030b01c40d0881407000042810752561a07503131003a0302401071007808942250701c2e42410026954102c40c103d074261081203800e16080ca4800640b403007490951a44101181001c40c0c0a0a06600404d96107150400303104403005682e82000510050641d045010b40ea0f040c041401052948018000216a8010062400d640f98014114000c42d03600749008036111040b403000501410185c2c1c40541203104a0303210420f84030043d80100340100d80f2000030002031800c04d490509840c400d208401075010001d16204440c1e000d5001884800300340e500b940e1074481c1d812035031000c54041d07400c01003c03140e8400c01032040e241c0421000041c1852240074400313516 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 75387214 1250 75385964 75385969
    0xb0a0506090603100e0a0603260318010b030a0804031a060112022508041404061401030c050c160f090905060118021e0306041404050705060a05040801050414010c030b 73
    0x32075003031441e0080714004005181101c00c2202500a00a407505003050350410000781340c050079680c00141e8510881001c8c5079881200c18050f0440c2c52140e001c1a4250364501c488103690b0a08000e181c01b440d5215903e01c1d409603070a004036040c09120780c540d00c3e200d41c01c40c245154400b12804180389881522014895a41e0300020a6040031803a0100981d42c1c40141d0190b0003d40200c0f0070814040b80e0a2911004100e4000085e009488010b805070b10404404801c0100703840c500d100320a04050340c1c6903034840d80d51080d04003082d00f822034140f45260a01507900d041c54034a80040d20700301110441c80078000c100c00700c6a020b004110040342449407140c55201c9a480b0030040c0305403440040c0480b810b00d85000d8540540700044240d151007111070041c0b4000b0040c4e98030440d80d07284554640410300e12844081529203000d5030b00880105403190412040c40800d03448401c82030180882400005060f4009004103885a03219500324402d0085410341c8900b907404002c01241403508000341d002d00c07038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 75388464 1250 75387214 75387217
    0x30c03060405070e030d020706080a11040b0d090f06020711300f030408010204180e0d0507020607020d080903120a0e0f0a03061d0d050a090303120b0907020a05010b0a0506 75
    0x54001c44001905032100f040c1a501c0c03d54540f501c6425002d413200c030540300c41e00030881c0000c5a400307448454096544021030811900100d07200340080c0c0f401e000a02900d240440580351018040c9000035540c041511450f01281441000b00d443c1a00000d0040811200710321181c2c480ca4103581c408401020070081e00340100d803010003000c90606140b2040c4032203204001e01d00751400d451702500d0381d40740c850b503c1078003039072141c043c4e202c0000d4810403004030410f5038481c4800091010016040c80d48c0d4210084030b990303200c820181ea11072000c0c40b4000140e40c07484640b00702c161095140555466a8105040c10640506c66001c5904010322050810039001600c0700a543ca0072031360703034202d2500300c0c000030524017541e00003901140c90001e0b01d005a02c04020840314140c1910211080680c00845c215090312858901c0b40c00070f400b105041000a01494000b560000d40c1c4402240f0465a140400c4040c03404464880050740038815a105100084c41140400340003654054621410700001c112103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 75389714 1250 75388464 75388471
    0xf080714040b011e0f03110a0503010312031517060f0405070b0c0a05011506110a05120703030b130b0f060301050a050f060c0f0a02010914090c090d020d0807050105060303030c03 78
    0x102c0e1600600e40382ca0f807040c0000901c00300c2c0c104000d510500c6800000703240200301088807020a1030300501440c0300c140c06068480c0b000c0c0c659a140c0c6103030b0039070740c90700304004c10541501c052685030030701c1c161407803c0e100800b0064019005014052000180c0381403401401414005c80c0d0807482c001d01003c00c4011417050190f80001850660718966465590b00c0d01a4091000d01503500e08071681d8404216407000700c048806d15030740d030240e00c00c561901035150030304141e0051084d0b01070500c01c4542500780010b0184140203044c00900c400341e00000c91005500005110101c07992103103a41254034003140c5101e00d0580c1a22514159030402c00480c4040000d07004031403107010100459410740e6070300000c440c61a5030000648002919070721500741c1d58840d111003207020601505010900c0359520b28800100c0d40c0040445465840c0d00d1030110709c44c0c1c441400140c03c51268048400961501c0c000744071102d20483d6083c4d0f4408403414501d0860708041c08052080e00300700103015480001d5800c1e41d41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 75390964 1250 75389714 75389719
    0x907050f030c09010909020f0907080105040c0c02040f0501090c09060210090c030503040303050306090601080f040b0601050d06141003020309100f140c0a02010605030601061709030c06040c0f080714 87
    0x90391515040001d2070440c010581c150b02004481c000f00d00d0415070340003207004603c2a50040d80c00d825070010418800c00c21540c0700001010a00100700c14a4079030450548180c8500340380789180c2460300410142c1da402c100d030381c1020fa01e44004002e59989403041401c01c40d41d6183c91403049040103030080d04c40f0030700705042c400d5540f00d80d90038050148000c01c0d4801194004216a55260341703240142c56030308210f454900c24070ac0c0f203000403102e500412119200d03000220031100c1c20754843e0303a015220600500a141081420b20030b041d040d250603c28a0080d04114100d489000842010401003120903082e11041500500922044040010341c2c04025509054082000480540c85400900140d03448102d0080c14006103c0b2441d110030040c03004202030f6000303101190f240c100b41a9500420312404000a5011810400b105031f0190580d80208036a001d40740741c48440982e5034604030081e541601c40116501c420080160f003460028001c2c030004001d803002901c2c225000b24404904943c060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 75392214 1250 75390964 75390979
    0xc010903030815270705041a030910061d09070b1c0f05010605250323040801050103080301050a0e100315020702040609050916050d0201050a0908070305010507030c08090705 76
    0x2890002e0494407400f5082000d80448a090300c201c000248090840d020452044202e00211312103078800e9007210260b0341c00301e40070f1490070480c00640c102540300400610640c000c019171014461854024100204020f250b900000348501d41801a0a000074107a0391180e031001004101d4034069a052302c2407609644502036407802c041c003c0301c0c05405010004041c3d07074644000851081d030480060510f40300103c600c1d1109501c00f1610300d83c121380e0340c007024003c03441c050300b403517900268545a0a40240d20601e028185903a0307a00391030946000303810459101f080800180203600f440300c81c400080c04804e00d19100d03818110721300c00701c0081d6804080c0008418030300c42c201d4070f201c6404551310554068410000140c3c2d0745143c400810040c0ca4204d0306014020307003440000c3d2901050b105503031000780302c04c0c002c105540c01911640c1c0040860300502a60b2000090800414400000154001e000102d0a0702e40348800400300c5035100058418400b00b04140403040f03400080300301c280d88040d2180f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 75393464 1250 75392214 75392221
    0x30709170d0f1e02031209011802040209130504080403110a060906050702180a09140307030e09060a0b0a03051005040c0512040804050301020403030e03010c020a0b04060902010e04091101110c0109030308 89
    0x403900050002c4082c038801d00f4505032a400d00d50300200911801807183c0c0385c20750035118041c4103420b80f0a41d1401a405210b001810b401500e040d40c02008502c1c40103140b03542d2a0601440b46003518821141528000300205040003848880f00e8002401002244c0e85080c6904081020b0080e1407203026200400002003908011500e8040103254107070010380b501c540c245040050000030b006103000880d040900388072070030800403001081c1c0341d1003685520b49030702900030729048c400d402100405160380310311049800035890407004002e00300c50070039680c0800c5a1a2814aa010050103a4072180c0a00d00e85a4499805544441a92000f0070309c14003201980d00c607820602c50600694001d03a5040d480020008201508942446940c3c0000c0c1d009002408072950141e0320f030003c14001601050014000800003011540508800b510504040c0f0346003400d000031504071480404119080188003510700300310743e044400240b0002c40303100282260107020000a18071032103440011b0078080c00c078020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 75394714 1250 75393464 75393467
    0x3030503090a140f10060f05190e01030f06051f0302100e0a06020d031505090714040308030c0702040506030136051009140105090c0d06021e030709170d0f 68
    0x121981c1c50f003018040c50340204150101d07441d40c3c0c469001c603504c0c0c418241e5810f180a00c0d80607900856081107403900c00300e03242c1030a10154103009005052040c1c2042d4011480c000d20030074082c0a140150038601003000c2d80d203004021074030054804030f2401d034810840c3c0e442c5590903c500055941c140e071a0702c8d00038403086040d6140b02c60742600c00d6200c00032000c04a0b01c05d0f800516619180c21654083c00740d001008515080c603415030141c1d9030400030500001d02807a001d070a0005107000b281d05034510300341c0c0e42d44a6018641081d0380401d08400006214000d5240900400d500408100e0080259808114003140c056947d01d00074495000c41b054465101030840b6a2228071a070031005071050800c1c46400d2000a06182004a842c01415100301150f0356051259920400448004120b00c0b0741041c100180c0f0451190115a850780800403c5456480c132016421855a082e04098882c2040361010b40170041940241c032023402645422490302d03600003407210090134103051500400e200c00380d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 75395964 1250 75394714 75394723
    0x20103020d0c050d0f14060105090303040906060302070c091a0913050714040e0a050a081c0e0d0806040207080403060c0309080f031501090b03070305060604080106062102030f010303050309 83
    0x40007115a00d8140741c21242c5030801c0c014080d09102c3c032401c021500200400d4400c03601c250644000c13803601903000400e107501500c0141128180102164240707075441c031000c8262842e54001d50000f94012800a00300406a00e03110080e040e040c00a019025590b00c0070f01c00c01d030003120541d100b103483c60b001c600b203044c02d021740d20301d46500305065404c12600d51001d404d100b1030801000e0300440c07826004000540002c5860003841d94404041c011400590711051840e400c0311070507404c2c4528076203095a580f001842106d80359904040034201d4007510040c00f621003000108460300442c01003040700005844101150181c0c0d5214000050405420008800070140504024400d0000103007050301401514040c501c100003241d110300402461000440f03488501e881041036030303802070010500840c007030b070003042d84030b01c015100c0c90a0a6a6504240c2540d0342588101c0c0417070840700345410042c040c0082680d10104072501503145080c4001100508401423002401304540400894000e030b50602 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 75397214 1250 75395964 75395977
    0x90b070807050901120f060e040b010f0506030106030b040204091802010201141005010c1b031b050402040b0f07061401090606030501080604030203041701111c052526010f0509090705091302010302 86
    0x1c004204060700c41c231522098007010303907041d42c1c1c0700d020038000140f518040192009807180582268156442d05000344c000d00902c07548103038030540a0001040603621407162441000101004440c2041d81d0300000e0308540c80000f050380c400c01c510b010000f18003000301806045407402e1801c071030f415102c0e04041c0300740c13040c0203c00c2405914292001083c032001c2940d44c210380807403c06000d222661003040100b24800c905c914440b04c0d0060200c443c110710107074080c04000f80949030101c0d000034a00d50b203c030700d20401d0700311031005991100c0c28010558544138542c050305194000340441d0810340c0b030203503a038003841c030406841129503080c0b00104682900030b003040c41500031086032116107074903413401450780342d81050060901d03000c00146501c0101c4400f2140fa03000114002c1a00c141410031100384500c403545161040441040c4000301c41450140c3d4007c152541a1a1500d801d01c0108060010068882c150f03950010b41c00303000c5662a80d081c990009000c10809881312024030060f0702030301860 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 75398464 1250 75397214 75397241
    0x1608150f010507050d081909020102070b0d0e011b0207141c050708010903210504030c060b0609180105030c0a0e0703021b030a0807030518060406090204090510090b07080705090112 79
    0x217040440c0d1243c201c44d0b000e00130807813082c20440042034a1400400c071540000c0280c0164001d050410008240030001c20300085c3c1c040002c40e1180051040f1400d5400f940100c400400b500ca6141c3308483d81400502e000d0805850f079811310541c4040054031841c50292000003107415140d2210821008104030130003011088000d00a010040c2000f40100e00d19401c1d40003018503a0603442c80d90140e034071806104940c5900c601e00400056100d0030b0090160a0f072041d0070080400c54081c0d0f50f5a0301b54900700e030454800407001e00d5070400e0705240c14501010340c828012440b2050a1040382e41e080c0d081c1c4d510414138500182c898940980d40070082c1b41d905100185030200140c00002c550f44014818400c030101d44041c44241c0300c80342e040d510707244003e500030460382160b030108000640030380014140c240001c001103154001511a50704040e620011401110350303c06060041103000420103030b0007241410410040d10341544064010b01c29001e400c0c1c10004851008c1603c44150751040b5486d26a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 75399714 1250 75398464 75398473
    0x20a080a0224010504110a0804030f02030913023408130302060d05040317010f050d050a17030f07020604080a110a0804080705040605063103080307081608150f01050705 74
    0x303242c1081071560003801018083c07410050200c1044440c201190f0406085a49030745690780c8a803030442d404043c000c2a02d0460000f08444440340d070b83d808058004030046000160384021440107903d6140700e0144400000b00c0030440100101025009811400d4116084982e01d11481c140b01000f1001500300940c4074102284444803000e00c1e81c45a44154032903154699034100c002c03104459040240701d1401c9030094580140640e040c62201004158460b10864100b40c0e216940e02c522038072100e10b0103d800401104000050144072411030b001181400940b400d400c02c1d0705c426000740b007001a038038113200b00101610802a0200070303c038002c54116038000d4446031220312550701e4103400d00c5618415420400040380501e480c00494007020b8801807000e003220303480c075400000340c42c0c00500116101a00800000800d03220002948a5482e40d900c80947d460203185400a4002980040301000360700300c1080301000c5000d007180c040c1785084550740303c5080c41c040121440c0c400c0d4100203129029 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 75400964 1250 75399714 75399763
    0xf01050a05040b070206040b070507051002030702030a02210d050408070203010f0b03070806010e0a0b0d050a030e1e03070905090c1806010e01050c07050103021602091905060a06020a080a02 83
    0x880d51041d8000c9100740c0010100780c807282e00407a40c0300320545003d460919080045030400780981e00800a00b4480d209498400118588450490700200c2d0a0b00141c0c00c0020441d01856061001c41c1c03090700148824203410346101031942c2e0350f0062598504000c0c2d0b0b0358001c68140406041542d803126802030003440701c0081e805181c809001c106014900a1152200c085031050780850400d05030b9140e807000b00103954402c0000c1c0050480340322026007003100e9100003004150b040c04803c100600030340b00d0591814548040c81028050300b569007040428004805015580200e8030701c04603500a040451641c031030207080c0e428268880083c40d07212008200d9410348820540c1d1b144c3c46004240c80b030b80c1d1001081d40041d1018451a038001040d500f1aa00c14006036011f503002d00b4040c1034070054100c00529590103d49542019100035901c5015400c0c910001030b480d0050a41c010820b458610030140343c4200603580c0c05000c1801000c50401003040302c0003500c00c1041c2c50020900040c0b041e130100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 75402214 1250 75400964 75400981
    0x806040b060d150e010f08101a030304030303060e100303120e10140f0109020a02030712140301030605060a05060f16140303010e0106260112030c0501050c09010e0d0210110f0105 78
    0x40c43d4410268000907450001804d811541c24020448400d58043d10b15070209048001c000c208036519901400c0081000019544080000c0c00c0a1752094500007502030610240c45d0601000400840c0440748200007440005e6201d5084014404ca50002080d40e1480408076414a0000c0e04205a031a19212108070b103540004a041c0c010b00480030420000d9880e500038405178480c40651602590042060a00003440740a4400d00740d0400d00e4030040344140d0180e12041c5600a0340240c480b02e031101c0c1405006e2521583ca100106800c03201c5600e02040d43c0050340103401240242480049501400001d0081040c001030b002c079041410740e81e40e5078446030440c40e4040c0030b0151000043d04003031340c0380400101c04c042c9441403807910b810b4055a860880042a0449903202c08c50401c8940c1d108100099003d002e4280580307007600402e03032100300580c0010302c410080c1d04583e101c0c0340380d15820000361300c039282001d0f146081c42c50b2030018140c41c0c0c400180340170301d00030080c1d44641c6080100031814 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 75403464 1250 75402214 75402251
    0x8030a0302090f030309011e03020903011a030615030d050a0509040e0102040305060c03010b0301050f01180603050105030c011e050304050f0d02030301050f100206010e190608030d060b0a0806040b060d 88
    0x4810440791002d0307543d030310f80c103142c2e5030701a502e861800f207903a410002c201c050b0748030118031010f191481c4c05407410141401003400d5600d46402c3d0300c1900040590600d55250502031250300000c14000c19690071150320000713517209220b41c42801408400160405560720890484012090191051082c100c004400343e0017035205120559060040c440410060403446048a0403a80034800c2142184d080c4800c1000090300b040009040c0072105d6081600140311400f140d006241540f400640f0350f00d040185400c05600c0811103040141403450104101e440c1d85401e000074585140070707612959185015880e1150075141070085101c0c01c04000309081d400001581612400c6d244c551070544164240055058102480009030b048003005000d0991700040302c0d54840300c0700c112a03849134010440c40e0111005608a0440da401c00189840861564002d40c0d000780404181d01f40b81c50002c4000a00701e04015000600c01e039102c410050f42d42c1d980006482c090005654100200c003055403803111003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 75404714 1250 75403464 75403477
    0x40b0301060e12030904181e02010807031806090f0507150f0504080619021c0f050f040203070308090d08030702010f061406070807051603030807030f0908040e07030608030a0302 78
    0x242d5100b0a5003907400d214040203140c9240c030000b5801c1c002d0000400014040c0d05000046042e0032503006400308034500d22070305280c419841161042c010030300004010090080c8100c0600d401c01c103011341e42580c0307501000403658012a000070b490025107031241a65400c1c24000c5d1242c4100c40d404244450407800c5842030500302e84940c0070b0f03081c42c0c0d4415a4140914843d25a16400060004289996039420811292007082e001403600c02c020001c1e151403415040c002e82900c0e40e80000c0582407030103208030f9400001d0300c128956145400d90009a6405243c0001083c1c00d4011419842c19200e502c4503501e12136102206549a1602c210024024103604c400d0f26051401e040ec0091032100e0400004503404000d0b24041c581440d44d151206c15130f0100c0c43c00c894a03c40d104400203000c24003a80030010b144aa0344010007403c0004000702034968238120580d405152581c408000f5007840210303070031140d0300c04111040b50f4a40006400038005584040d07214080020b95401481d03041e80103152 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 75405964 1250 75404714 75404717
    0xd2307050301052103041a0406020705221517010204030b1521030c010f0b13050411010e0a03050105041208090105090d080601030902030a0803060a080c030c060906130303031a061905031b040b030106 87
    0xd0240ccc0d036004214402c40110a1a0001544200c2045011242d904a0700010000303c0c8030000c45981e43c501e00703182610303c4030300d003150340d50101d01031040050060003581c00c25500d0318004880001240025141c94400d1400071203981d1580084403441c44c03d02c03d45120131b80100007001510030803000300e000703004a9102c0510884810303444139070403140e502c1520f001d030b6007009260707034040603000054403840031503181e2980c86261b00500000040090052a12841c4290104010f100a0180281c17004030041c00d11a01030b4100b104020303e100340000d5003443c600241c58070404075180c8a006030014410110045c3d0140504141c4405000d4036000450095409803400303e0b91039aa84003c0382c6030f00000398000d5040d0800c140000941c90301401402c1104401041140b42440c0007814900079600c5600807000300e503c2d40005140f2459510310008000700c103030348580ca45540d81c0c841c400392842018020061020100100d20306801a22581062486003c0300c55551900d540700e094084c0c009101c0d400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 75407214 1250 75405964 75405973
    0x140705040b0402030906160504090516020d050414010e15030412020c0f0a0e07140a0908070b04120209040c08030708030f0a0c0801090e030d2307050301052103041a040602 75
    0x601070a02e48200c900c55200c1c503014148a4880c0f0503039956441c42c0c040400100541400045500040c1e40f28440c090140b201c500c00440840b0b03000a810010102d10f4201408000d000c10001d8800501223000c96180074a00074001580481c002401c0e020601e07000100900080208402c000618422080381095a0200c5810b02c9520303081202640d400c00a560b000140380320100f190940b2003040580201542c20302c9000c0e80114000e201c1340d60429111940028001041000000810b126420180c07215a052500d8541801c14202c0394940400000340199003c1c00020305120400700c4110141c900d644c145c03a0384100314144074990b5001600c1c0740c0040c0201901046100705d40e4440d00311034400d280c07604007540e847c2c018860000d0218030b882c0070603030100f001242000d60702c80c883e24000e01d04103040b0411070340e0882c0004410000040c00c10062220400050005544451000e030b1103204143c43d10841c0d0a92080d0241140aa42d001100e00900325a251105040c0d0001501c02d40c0d1041d801c66 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 75408464 1250 75407214 75407231
    0x4060b060418021e041539110303070308131406150a050303070203070312050d05100905070e01020318010504050603070801030b0a090803040803060d0b09010f060e061807090314070504 81
    0xc8603131140303121b103030309050484c0002030300c0501510b800350507442200c4030050b0b6071074501e500f80c1c01000c400d08151250717001c115074841084004403091100038810b03130003181014120f0f034002c0d2810001420840c005983c4501800402c625140280c4c8407045800c1503882c1410300b000c00d00c0142d403a00d015244114000400400c05050001c15107802c0303a0010010184d4602e541c56096180d020300c03c072507003001410058081d04035070701e00409010303203510b8000c0d90f5501c0c5030420700d0003200c60181c407032010044800c4201a040c1c0e4000b09440003000c1c1040d0300142200d086c401680c091089038403c0c1e40003100030003005200740d040381c83d15048034000d0003807003459a120350f00d00c000c598a500c4018502c0600303101007004589003002969228101411005031441c49031a0303011416803c4600b84190fa44800004071440c0305802020018801003201030160304020002030f41c0301c1505508800001114000941d1407480384a0200007950400184aa1003181c1030780d0b99107600c1c640c080c090007039041002c41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 75409714 1250 75408464 75408517
    0x60518150402041e050411010807051305061308060c07020102070f0e0a050406020c030d0b040c111015050d05030c16061704050c04230105010e030604060b06041802 72
    0x1200c90014040100314041d660301d80c20003000340450100540b00303001043c40003080e05828840c0314003a40c050702d54010807102c0c000c0010701d10a4024910401c001050003059100b141d40700c10001a03940440b0900c3c0c640c0c030381880c0050700c0d000c1c1c0e41c040e07221441200b0501411a420704000c04030079000b07070b080d2044542c5410140c491100030f4801c040c51028800000340084100d0f41c40542c10920580c005450051700c941400e1440d00862000403200ea0b031381013201941e103014458500310310240c0c109401c1d640034200000c0c2d107405c0045040e205207500c40404c20007000300e850302200600f200420903c410301c203c0c02e006640360040500c40c1400d22851006500003065001860308544d245d549100141250100072008200040c0045880b4855080700d15020b0b9039a00400341c0e04007824aa050003100a00101648a101a800a0f05000940d415890584c40c04558580e006404c294007040f1124003c000c03070310901c1190b0184007840c8c0203d90480402c54a034000b440144045403d41400b004034000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 75410964 1250 75409714 75409723
    0x303091205130608150d062a020c06090f04050705030906072c0301060e190501050901060c08070f080a0807021506010f120f020d020705060a02070807140c0a03060518 73
    0x700110744510300c42c0c04000c0c280c49a5041a0300c0040c0401400e0701d0012100424062070008038103c0e010354440f00b002e5684069004014001104000302402107411103030080d46420b00100780b2401280b0001c0d1460707090315400802510202d018104106510700a100104203030400d8410303095034002d210106a21b24400c43d204200e198220300c507800c001e5000b02200c4c82c00700884804035015500d8503000a13012104000e814410480c2094802d0206850b981d4841110f105810951140641741c0060040c19888000964029031240c5141c0e0345120f603062140c41e0b00c0d00b800340100294000189401c481d64440c80c803074003510072a001c4600106503030740b8054006408680c03090000b1a0101c01034402d0740b2683e0141d0746580e00300c00028410074a1513440d01644e0001c00082c00b600d070009148000c11400300036443d40040324000441c00d0110999601005216050b40070303081c1c00840c20201d0021000703001000000c54001d100c91006541c0b840c010014000445903032140001c1c503a03006010302c10104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 75412214 1250 75410964 75410977
    0x20a0f05030f06060a110706030b1005070c0e0912030c0703090602011a190b030a0218060f070f060204080303070801150c030215070509031f050601090510030f02090307030303091205 80
    0x641c0000d0590740c3d14240a10303900071240500c1000000c0c1c80d200c101d50018001d0780050072031a034001c86c0d5081c0c100d080c071110002d00c04a100070081c007000a0b03400b00d04c4880c5501d06482454210340103544801c0c00e0030b8909083d240500f01803100020511100c6e08600c0000c12901e031003512801440d50740c40070b041e4200c0d030f85c0c0315451200440f4020880740a2406c202c010406d00410b41806040641340c035001000c68100300e454150b810f500003041419074150060706c503414501113420b14a01020862106414018010010702080403442c40408224607501904c1c00303020501c00301ea469180c01000244040002e20034445880906120080d0144c070940c00c40b40010781580041103d0290141c03501c40020008050b8002c100c814000e014507603a080c840b00f11300c0e030340600071041500c229030017500c04c442006e06194180079003007100b000b50703480b4807096045c440064100040c4204010103004082c0c49204610780d494010001c02008154042d03006d070010030300402018030701c5c01803044151290b20940 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 75413464 1250 75412214 75412231
    0x9090b1806040b13110301180c0c060e0307020d110906010306060e06091804050a0308010906031e060f110418051017030c070306020c19030e0112090b0a020a0f0503 72
    0x40040c41e0750900350050f01c54100c01500b0a0315000304100310004403950140f80c03001101c4000010008004034180024031241c170701c0b1007000749403101c140c00b41121100590041c180c98691450b00d104060501c1514409500a00302540301c0901d407500c400c0c6500071030501e5101d0b140d42400b08a05510030b00c10f03141640c0c400d480d1110040c1a0604011032a001800610782c403105180c1402904400300d621640998407e8004000c0304c0c4140c50302074203909058000c5244140b80c001c0070808a2021400c60a21071144005003410a1039428202c1c05000303d0b09940074a541400c01040d001022034006000b1201b82142d1b403001030b640c00120714141c0b032003620b209a8940306520309120180420410140d480f134894220303071a1040b05400241003100750361041c0e0303400fa408600885103410174031040d02400c02d0848040142c4803107a401920810300180b0302410440f2001e840042d45245902480781e031604416814140c2c0342c07107d65440650703c4940d004000400f02c011484103180944c0981e0f000d40c800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 75414714 1250 75413464 75413509
    0x30e07050a0b0c07090207050321090d050a1e020c0307060c02060f0a050c010f0b0f01050313080c0c0301090b0106030b120712030e060309061f21080f040609090b 71
    0x18400e602085400412800c0b0940c0a94907000400c22686c0c801403910350700c0390300a5516168554800c4a00031a5014001d80112098003000315808020409440c4003140b400c10640783c1040e07207400c0700c1c20511114600c41d100e00c41c41414566a400145895000078105d08403800107031a00d070100c9080008820013500100c061004c21702480d4041d0281c028a0514a002400c055114012900755017103a19040c803140c0d0703500140002414035032043d41e01c0300c1d000c1c04c225295007049003c07440f0f180303190100034125003004281c3c05d10040040c03202000c000c40050007440440380d141060345c41c4070002c0c0700c0c500101e40350400d4142d9074100480352805020206014100807032814100d50025003070316004a0030003081c030300002c3d8507a076104003940c09085510020160780c9800d84540c2c03112a030040f10296902260340d001c00c801403242154010240c60503030707910034082681ca40281240112036800c0c03100344020034040391542d07001100c00c040b07803104001031040680440c180020170101d20041c0e20300084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 75415964 1250 75414714 75414719
    0x7052e02160206071a180d030603030c0b0601031b081005030d090b030709030602040b0909150609040b0303210f0703060e0a0b0d05030a090602010b10090312020708060703020a030e07050a 82
    0x1885000341c190580220b005c814880322441c0e00005401c000c8400c003072004207a46076840c034003c00b04401080712101c0d0608014250a5031030103840d10845600042000308a040001c4269100b500400400040c01180d4200c0b00343c44c00c0040c05002e800c59150b0058003640500003458603001a0095072002e003516003018840c280102002030350310048c050014000c07076031030010000714540300500041008421107034070f070b03841002000b01b80680070341144030f084100c01808096a8491044809182084400060307039004000882d0960284c0e0f40d0004200b50fa40c80c208203c00c4a07031210900c00c0c400b081d05805140e6540d0001c1d012211640940c00c00c0154450005104030346a50201c855200c004240c0ac40464443e40c0c4c15103154051809080002c5080c8410003d00b90240030b00c154401c001c8824088500071018010203030f154500c800790400c0c00072203032030034005c1c024803050000e4203800080c1c3d000d81c90114805000395106400d01b10000745480b0800343b540030041035a5055500007406244182e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 75417214 1250 75415964 75415969
    0x100b030402120106240f02010c0909020a020c040f1d0a0c06120b0d050d020d031806020313050a050a030e040c09090b030c06030405070e0f090a08030a0207052e021602 73
    0x40d1421880e0031650341c0c0701c0700440c8001c4600105552841d8185d209440b00c86000001040000f1020072181968141091000b906411610302c03000d5400c4d5900050302c2d0310741480100d142c400c181c10015003092620030a800c040c0901d03000000b02202d40c00407050410300085181d40c0d6943d46c0c820192806034000d00a2012502c2007080c000c00d84032101001c0b400d0301c410340020786440b4800b84111035950040001d4041c2d030b5014411000c008581313040801c0000512113006c0c6410409541c02080b070759000000851058840d80400c4001e1342042c1141d1055107a8a410b45d5100c001800640c04221425000310b811718040c0a18035030380c21141c3c2c51141d0030b40341a042e400174101c0f060181358580181d0510032401d03114500950720850051006020390781c6441050011030700081d2010000c580040104500584000340c1021074a502c180c41683da030381c0361210300000b4010000c000b040381c0101c8141080d103444920000352010b0b050a5842c0700c441130300b51590102e1003038540c030000700030518000a0152 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 75418464 1250 75417214 75417229
    0x6030b2514030609041406250309050a02060309030715020d0b091e0402060f0d1e0b030d050a090f060509040510060917070816080c09040c050d11030607020102090108100b030402 78
    0x1407040d150070071b000980002050410b04129051160410800c00b24001504212080c4200307604504042020070440d499050301d4040e840400307070154a00101040c07030080200100d4120365040b2200c2c0e005c440e02c68455002035480b1080110840e8106000c40e0071300d00d40446514003444558808010031883c2034410300031000300a0050360310076400d0190b410b00c0d60480006100d032a522410029444030010100002c0641c02c2c010360825034940050544d150701d0001d5030090750021401c0c62921b072032103400c00f1100d210362900b01214940507a540080c41302d40090181c00380710380440b030a11650380d0346c0441d520b12810702d02c2101d0014070891000c0040c02e5103a800d02451681c810305690210b038941039410b03c0c2405036500711000c10f1508100300441d001c00e2001c80d13200c08044460350b0440c1025101c103d980d811500810340300740c040d01180d50400a03203001c080007072200501910fa15162142029000750000c00304680031440301c8002501e20102c0f099004203035004c040104e800d54469400b4407085 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 75419714 1250 75418464 75418471
    0x507110a051f170703020426061f12080705011d1b010c080c0601171204170c1005032d070315030c08030915090108061306030b2514030609 61
    0x144600700051000d008183c240003032044003161805030303440303242c42c803201003070b050110080040e95400c00116441c114080b854681064860328104041000c07030140c4c55812030342d0b50001d103004023408800c0c130801c841140134100c000c0c0960003c0028440c44246032440d2001595021b007150055030006100400f1801e10307803902d46040c03521081d8582c0f103503642c4d826035110030701c3e0b1040741d070103d80100071442e0202e400084910a2801034080242d09141d40d101c0c50089010301303442e986011001c0103014100b0062214844001000380c00c110940000160140d442a182d02c0c0140040690700301001c144030401040b4480075041450890740da07207500300e0040103600410304200ba070140c0004085400740c400800500402d8001e19503802e000c1c0c0c104210700a03851604101c0d044240208140d507038000010342d034840b40c01d80d1603214003c601011940104120b0300010700e50980f40041c48540301c04c03480381c90b0a2690b10a44030050342c051450a980c00d55403074580c8000c076841000040d559042c1141200d82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 75420964 1250 75419714 75419717
    0x30c0418061404050124030b070e0d0b0f01050406030c03170702090106031a09070806010c05100c02031309090203031b1603030c02010905040509070e0c0405040203070507110a051f 79
    0xc0344555940c501c0180c94001c24031903141e03041c030402c0c002444002e104001851407410441d41d0394448004030003400301c41c130f488041c1001c2c910800052060b0701540345540a032a001708405150718051401d00e00303c285c140c2d51401ca441c0074600200341800c10340f040406a0740c000065034100d91440d40da0640382503040e10304814400062003d000142c0b42d0441c0e00707002c1c140c10384001c034014400d040100401305020f000103100e240d2103800c2c0144603401c42c2007140c0114003860728000045a6050541c505010a03459480861420f00e0044040380d0110140c03002d0500240032400c850340d20f508400c15100c5c1c80001940c950420012075180c0c2060640800104451006507080070340f181150421408503a4002e5000c50307003a0400300215039000080f2009001c040310100924182600a255110702501440a140c1801404100341908103001d45004050040c0700b0f6682c0d00c4c20000041c40b503042540115450a4845d4107030645107051021034045d14806060400207440d0400c40715002c041c007248240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 75422214 1250 75420964 75421001
    0x904020904020f040602010c030204050d030c02030a05031801270e0411030105010303030914070b0a0e01020c0904140d11100b01030f060b0306030708010605060702091803041d0114030c04 82
    0x390140ca56001030401c01e202034640700c0c1c0300c525250010342034801c1804d2400c00c041c030400050000d13230b9450740160219500b5103840d0201c3c40c000d10201c0e20344200098040c003039100115240d00402e411003840f044280b0281d036401450403d440c1c94010340301e00e82903943d1002e0000e4405201114003109400e60003070007419241035038410340c00804e00711a001c0e003060700040d460304c2c0789806200c04a0103051801260100808006160501e241024050070505000304015500365516680c0b0802140c20001801400f140307076404d05107061241d034280c0031080e550a020300001404400d00910010b510008030502510000040c0c0480e4002017040881c0c2d281815604e040460318144144500c0c00580703d105440c135681c1c2881420540341c043c0980c08101181e061041c24030203a1107010588001c50350603a1900c180f512420940e601307801c0b04405040701d80c800410001928043c091400b904a0091400d0406503626446941c240352903402c0e440d030f0142d001d4102c400c03041c00c00394462034400716000c8064 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 75423464 1250 75422214 75422227
    0x30f03090b0d0f0c0e03100506060903071403120703020607050706060312030903030e030c032a2e060e061e0301020c03090310050601080c030402030a08030f180601050102070308090402 81
    0x11102038201203540c81c10070760f403444816070340040c0380308180859180f03081440684020388000703a9034102801c100c10a035074480000c1200b5498a07815100074a000500b594105600e41c01442104040240c6c40c0784a4030490401c840e801c02c10004507041ca54044c0d02038641d40d590800309035401d500c1900c04a91260380e60100001041700391501a40c510301d03503a80030800d00c2c1507050080966401c0c0010a543c0d0b0810402071803032410000466440022043c9140c0403428600c1407480d44406c1c042242ca000d0048641501c1101c034954404002e18003000314003410307009600c1104040750240d010303450f50b0114103004a0083d21300aa080d10313400c1025550022101d809601182c00c0e82c0004044070700961021a20203014034051080088005503501d0401151a080000a100b610080e0810055810000100d429510144580081d094104001e969070741490107540381241c604a41340d251030030a078907803640d2080010510b1812104140d0007000c000342180c6461889503c02d400d119130045d8204100b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 75424714 1250 75423464 75423479
    0xc07030807020c040218010f02030c0705010804060f0603051609020405010e0d1103010c0c020a15020303010314071a07050f072715060203030106110109230a0605010b030108150405030301030f0309 86
    0x5000103802e41e41c121170b85004400c005003003142c20603485412764100380030365540e01c0000658682202d40c2403070134901070388460402000520f032a245510007281400804400d10000103215131190242002d41010203540b00d0307021040340900d0191314001240e18400c0081442c0003400d1240243c01420f81c065030381c003048000303800c66046007191008031704a400420305514112900000070030306034615a0000c104004c000351130781f105020080008420240c0e1b0423071407a04002d204054684107a403c2d035004c0c80c94002c000c0a801c0044102c0e0309208803c0030b2400641c0109104080b10040684094091807421184184a043c146003a80c0196074030400000703401c1a6580400902040d0050b5aa84d4100701c001800c03900d50b15040c40c080d0381454014000101c030000138200a0140303682c1c00d440402580f4446080101c0510081c0c56107051600210b10310100718015412a2080c408070340d50301440c40214030201c10200d901400a40061004101041c00400341d080c90502c81d2405181e6952120503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 75425964 1250 75424714 75424717
    0xf032007180e07030b13030519020717030a080105040b040e0a0b060a0e0c0d0203041e060b010320030c03101205010b04051803031b0d0908090a0501080c07030807020c0402 75
    0x15418030501d0990031a00e858031038901224480340150400a0450700d03069904140036021110708000003e142003072610031401c3c0c07242c5c00728100a140004a50082c000c0d82c0e1182400342c02c0c4c0405486441c100e1030980002220419001e640701c00b100d683c030b01010400203101130928290030648400305c90100030000d001c0408514400c190304d420504001003440004d0400380c115964a0711040f00303002e810341c800000e440e0040c050b5000507a0382c0e641c1c0c1c50712140d00d0500c605030b62a42c04400103980d0401c20207411203070a03210207903004c214001c41882c07c04481144800170f03003260b00080010a5610f4005801968000c00d0001607074610390341c2d00000440d1400100c0260b0b000e13503489404440da81381901686410008041142c440c40070110450360f221f21000c0c00040892188140407160480c1402c00e07a04102e09800b010800b420140c07c01a4640d480508014452840c2030000704141d07004d0700300c9600820032521030508182da5549c0c1544d070118064810400d43c03144030043c0506a94500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 75427214 1250 75425964 75425969
    0x6030302011d0705150304021c0b04050d0806010e01030e0a020603012417070503040201020a02060d0906050105060f19030906020720040b03060a0c05070204090b0115020a0f032007 79
    0x1400080d0034580c0741030032100009085100ba0300e6030480340040180781c0c0e42107080c24082d0a40e2280d56030b69210340c80050800156052000306840e2003014210910a96000351031082d4068429541001000740040b945c808040300d00501003500410100340c1d0354443d0b4481000903001c04d08644403000c4680008078103400990214032200c802c154015420082305030003484c501510308100005d018421441113001800600c900c2c01c00c00c0c040005401c1da0720801400c030342950007403d10396503403490902030005410351100507540c49050000000c0c0c0f0b402c188048940008000c45101e0401c0500366184501c0d004442450007015221005200411458401444682e2046849491ba12168039030101048102e40901d4400ca2038803c5510050710041100b550082c510a800a0752602c103640030f40301402100c0000e03410503d800341041c2041750340900b0754144c481400003105001480c0d8412607840070004801408008075030030210010340105445102100b214404c0c1c0c43c403484100600745444080e6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 75428464 1250 75427214 75427217
    0x80c07060e0322150504060e060915130501020a021f11060a0204050901050f18060a0305010f0204060206010510050a0503072d031503050601050d081309060f06050a0f0e01020102040801060303 84
    0x300382c5000c030010f609030400600b0300641d858040c44ca01c0c0d00140980c0142d101c3e0301d003806190409001317140d41d080c01301c0d82e503142c008001c40c030340440010018000d41c001c0480440c4a051703010300850250300020b107a03614268001e182e1094064a0032500b000c011515210f001880360303210141030303401024050f96101d440c000c0d8005854034a0130040025100c030603804240202038a0f408511a45c0750021102008070310504035030850703107940700421513210041d80090401e500c3c004608280b4196a0014012910306e68200c0e4541d90700e9904110521400801b0200130407002c101c0c0380d24090059010750391200187c10031103945040250380e8950060074010045111411007124103d10750188900c841036500d03182010006407c5680c4e681c2d4400d81030007a240f08100c071003001003c00c4404001c80f044807103c3c24125a10903520b4403094041d000500640343d0070080b1240101d1030741d21901c00c0c2c80d8043d12a988003450307080e4142040e10382070901d1403440d0441d5020040450310303040901451000718803d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 75429714 1250 75428464 75428497
    0x302011b0c0b070807020d0b0a050f160f02031c02030103020907030203090307060f0605090f090f03030106020d0c080f07050d020601060e10180312050d0509010228050c060f010806130201080c07060e03 88
    0x35400d003040b503034020001ca29000c0d041d000d1020000201e100c0f200cc0580340e00744400302e09110413081e03140d4012910b44010b061a070103107124000003140c000d907040300e10958061880d40c80307544c002c0e016800100d0780700da03469005000081c042010b80d00700610b580c40084d00050340719220000305a54007021174210300b9900720300f8180a88543c003000211001c019a034040c504550602c41c0081d12010783c8200d2400b08501e05408000f4088404200c912403620aa0000d030740354210f140042d2101010078902e07000d405214000039a85014036000c499200c0c0c0200342001010980c0b0085e990807000146580f1031100941001c00011503800419400b94040d13100c01b40c962a44921440598800502455a80c0d00600030300109000d0b504114281071442d0140940b20072010608803420300496400c81c5140c4200410300040d0340041240d1030607100d501c025106180d85102070002201c4100c140240001d400000107030b0b20660100280c0b40041c41944d021a1402840320024a95008803580c3c4492540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 75430964 1250 75429714 75429721
    0xb070807062c0607021605040221090c011d0105070b070e090702060610090506180102120a050d0501090b1f031503050f0601150801050609040902060a090302011b0c0b070807020d0b 79
    0x20803c04140c0c4900a480204207a0701a000d107018540194401d440c0916004658481c440100c8600308080504814600000d80742500034079545000c0f800d015800700c0c5540300b40c903482d020305402d50101920181c41c0d5030b16105440d591460b240c1001062201080074110000308141e0b00d42801e00d000e104203500030100350802108105400e40005d99100900520030420001c58482c81c0c107440146650b00341000007070b898400140e081501e0f480e0003039070b00c01e00014601e440756001005400c1403108440c0410203030ba00c901c24027044034514450150f000041c05201d400328079101200090300e415514000c195035400b220360081001160b0000c42d035642041d4141155040700b006a00d0040500040d0f1a44d1040345440140c065001801454000c2d030000810000d20340700d03500040041da40c040c1c4925030b1284010b1008013808504d000490010b200c8030085200c48044a01440c0065001110310790304030715015003050203603c40c2c0011500401d06220a0f00507035203008080206030700404007206c5504c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 75432214 1250 75430964 75431051
    0x1404030e04060503030a0e0409031103040f0e060427050309061b06060d03080411210102090301060f0605091c05030403051c02010510170709050a0608010f05010b07080706 75
    0x8041c3c0d007182d0b002e64000d010080343d00c0c1e8000c0f441c01400d5800d031000100fa00560600710382103121180c40c0403071803100160008161a008118804451480111200702d403901020402540d418400811300081c480c009560030342100d01501c500c3d6031240046903e04045007010864941007042c0340100c01c1000420300e9842c01c800e102c12640094110340308114060301d680c0141140307101800c00381072075102074102401921056403c240c5100010050413081600c061054040d510080e0480e0083d400d2120000c0c80e8004030585601303585098a500303062005801c14400c5188400002c4642c3c000c0041c03160010840600c02040590f009074050702e00c07944a078244111505a52a18004580c90f05081107040910a00300c207042c1e5260140503a0b03421b01c02d5249524194054103c0b820741c0b4a00400d001204200d40d01c107600b2a4841d00c002c1c04040304122980084480034403442d40c038160104280800114200d006200240c440c101c00115102030381030b41c611f03403030203019101c0040d8883c507a4112180c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 75433464 1250 75432214 75432221
    0xe0901090c02100b01081311031207050d0206060303030c181305100f0b0d0b03150702010e0f0a080a030c0c1e0b090307020d080c010b0409080a030c020601080307030c02041404030e04 80
    0x903561000b4400c0c0d041301000240405001000c0700702c2c0740e0300c1c0300c4010100b00c02e0b49034195443d58014101c6120414030018074959a103c240f04940d02d1041c2884415801d0010892510641c1c00a000e54115954245481a03640c41009000042c54086403120b00035510b40701c0002050380d41c1d2070000760915100008511420b41d607000507154900740030041142c100200c0803500d40585040300450405071610100b450f00c0200d5002d1605503220f10200300405a05500c050240001c50040b24220441243d110362203280b00f40014110000402051075468041d4010741c503e0940b5242100380c46100f03440e407500d91550445160344404141d928030742409001c881c0141c220604002841c5400d407641c3c0020300d0340804c0080144914008034920940040039440301c0410800904244055142c0d40340548541e4000a03054001c84e19058500707100c03504c0080c80a0688502000562401d0243c1d01c09803804004100c040745c0c4617031294a10814443d42c035100070b008178842d4131100741c400d00150070403054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75434714 1250 75433464 75433483
    0x50702071d011409151c060203041406010605090307090e150c0c0c0109050102150601050904060303080604050f0105030a0b0a0609020a0302030907081218240d0609060b0403120e0901090c02 83
    0x2601c41081400007a10318600e000400b1603040f07841840c0c4406c0c6d40d4803005c10b03070903194000d00840d1000c420401403050860700c44881d8021001170300d00a0b07807101416a0540a0400c4580d0960b002040038850000301d603000e401c009a800c000ca59500031600e10030b1000603000c86140001d150301040d0020404010080c40188105c02d0070108002c3d418100003c3d561103810540300b90f040340038800315186034011000c8a0160700042c1082c448a900c906002c0c01d49001aa58130780200e01e0000060b000c1034000181d80e0584800401400c10b6a80607116000c00d100040c05060110740d1b548800034042c01c0e00e01c002c01860003903840140e03d80c0b40c003040c40c5060101d50b52200c515508015410060b00c035032a4100d6184a1f4000880c08072021090082200c007081c081e4070b0416001c107004490249aa540b025054004010713005008a40e20351004c4011b0310030510403251210010300c41800002c00500a10109452a00d0010342502000c800100016000ea1040b11910f650b1031880c80181e5051100415 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 75435964 1250 75434714 75434719
    0xb061b0f03090d0308070315090c0224060904030e0d20010206040c1a1905030f010b090112020f12010e09120906070f0213020703090f0e0f0604050702071d0114 70
    0x804100b040416064100d4820090070071032810f0002e5000341c000d07031105520b0840c0204102000ba1507030b8890005044405480001d032280d4000000444083c011f201490613130011101d4460b01c84609004e440f58019200b03e0074000010400381860320380010b503181c0f2502500d902d50310344515840f0b500103814680790060454101c0c4040101050003849038904907030ba00101d24504041480c0da07161079018510140d5419024000c80c10190f6a1110245010341515120020300b66610454a141c03031044a42c07072400700d40350707084c031041c400343c1503001d042d440907103448080c84d0030100d99000700340f200700740c224011300c2102c2c40500c844d01d04100900003064030300e142160b00e010380300d10006641d03024a0300c1c01000c030462a1449002c40d101c00710103d17001d0507008810b40d2030718500d18000d000b02c0954001c0f0400f41382d0301c40001948403e40c540c0300b03010307244400000086131a040203020190a00902c6001907214250001401d608455800c40c0c645e0420312074041d0950401210000c0c8282c021207603031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 75437214 1250 75435964 75435967
    0xb0f0a0c020303040f17040f080303060103060b04081c0c05010c0228021e010203070515041203050103020609043c0501050a061e031103040302100e0714040905010b061b0f03 76
    0x160003c1d0605043c5d074108844c0340c0032500521807240c151180d42c0010020104480d000140c0280000141d40110f00c00d0700c0900107503403903444d400164010703880f59403840d0740007455010040442e410150940b800b94640f071940c52342242c0743c1e242503562160b40b5100590081c4030300240540d4040b103050500b01c290f06046001e040603000980c203014150030780746403c80c01440c112400e038000c1003102c032420340c00070684040070101d4804103021001124107892118000740901241840b80c070655050380d60091104c0e003170451142c1480000d02c21154403017500c140760490302d00f2113050699008407880f000c42545144143c005c40000550b02c040e0300c280d0154504a80030721400703401c02040c170b05601e4219040c2d1001c1c400c1d85000c801511000e180b0801205001003030009060740410001ca0f0740c43c80605c140000f940c00a007480e614040351081d00b00c400020612550140792507000881030901420000c12512402c01c0060000d9005410900341e0750710302c01d090b004075030060203100290403c0c074001c0c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 75438464 1250 75437214 75437221
    0x5040501140603180106121101080403050f07060902061c0f02120c0a0203072108090606090106050a09050303130f0902030103020303030601030b18041514040f0209130b0f0a0c020303 80
    0x2401503158079031141c800d00b00800080d40e8000f1682494500841c4400241b1816940381e1103110004a507010580d2041031819060f02254000c00b00c2e2401140d141e61002d11742441c2d05021583c64000d2407040364001d072500c10300400743c0e13205000b5055880c02c200102008130500c0b1420800c8130007082c1c40040c2280140301041d03140d43e210402c598400c9001006580c0c410b02e02134101e0440c465001c0081034224104241d06155a855002d149012076076250486c56131680180c196840303074100c0c4c120390301c00720f400300500202e84101c014100d20803513030034010451070711034000905580044e8450400000007280411100c0481c01d5080000d2922080440c030395410364000c49c0d00c902c0001e1606040c10744074110041561148070401c01c1c1091350034101120707800c0600d4544290341405d6090100c40b03090120491407400c0240c100783c0500c1e44500c0c64070030340394140e007400301241004040012110a09100c10085040c2000841c0300e95803048400040c1e1600413400d800b10b03a24441d10400319030060040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 75439714 1250 75438464 75438479
    0x2070b030406020f190203120702010213060f0201060f08060a060b07030504032006030a090506060f030c04050405280506010b12040f0809100206010906140904080c010f110702090105040501 83
    0x1201d4000341c0001c00541c0c0c4d0320042c10510b801e8410803400c01c0d5039103400d10044008503404130103850061100b21290742961590740c0d0890a074080d40d00c0352002941c03c08dd0801002c2d00406401d04c400041d0b00012460aa482120060076190707030788020100d4103d081005040a400d12a900141880880103400c0100640b03009000340101d00008000c9550303c5400800c070300050640c00000072005059a903680360480a480183c42c01e00f0003150603126080109100e4a40f800301460719100c090000c1444416101c1044050900540190b54074050203500480407890b00c00c00c0f24404500107564443d0071f00501c0c095141c0441640400401038013440240185444028502d801642121403070342e040b81141050300b83d910038010b4640d4002120b80b0300303032400e0703401080190403240c01040402c10348e6510218186542e003d007070480c0e4004407600c00140028410f00160140942150000400b1103d4440310822605001c1c0110352080b00498041d013140f808922040c050f04098400744801d5140810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 75440964 1250 75439714 75439717
    0x80d02030a021b0f0a030f0c050a140402030a06030f0803091204050120010e06130b0603030a020a030f020a0b0f0114150a0c0516090c090603050c03010e09030702120607020d02070b 79
    0xa0190702460b803400d410300c4903135400c40040c0d0085801010008032565034a0032940312108001d040301c42c072031480c000140601e0314218040c1194141088214032180103800c000003540300404880802d0b03a80c000100218401c901031502c2c051040085d55500d0800204451070148202803244a00500300010f21030359910024501c07020210311036903a01c030800602520302621020422002030303c1102c0421440c000d03402c04140074280110352040e07090315448d060580ba44240daa892015901c001a141d00003882041440b50340c48141c4195002c0101c1c07680d0b0803030003c50030395940010f000000c2c0140b00042c40900140020081158400c1040c220302e10708242d14001c8030010710a0008500715482482014043c003449180c44001d0141c0058540d43c02000511082c0c03403ea00040e10440f004c0f0380c150085c894103000c2d1110100c2c1600703507868021110040300c2e0040c0001110b000078084580140c40760f079803040f05c946a017806460301d4500004000e20f0102500640e0045500060081088024080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 75442214 1250 75440964 75440983
    0x7052805130905010e010605120304030c0b090604030b010b030402010806092a090a08030d0b03030f07060f0e010504060c020f0a0b010e0604150314060f0402100e01020c0604030c080d02030a02 84
    0x60741404079001c5040d810008003a0744030040c21550030309440c0705038048194024070694004031500b82886007629050342e500c3c0100c0c00000d2910488684c240a4bd107001c1000c0c1808403030007040140303090b8690ba51042d80d03110a9203c1d032050760000c810300c401c40d81c10009040c1e10440503212001c140ca00300700c1d00003a070f13810300f048041e1298910400d00c150580c3d0404542c4050f101415650030309030358050b081c1e501e90005000881c400e2401c4030040c1145008002c880c0302c949207000090400d10203844950061000259124600761f0381c1c03048148460b42030040d03034462030150f400001c6944071075030041e003000100d20442096800c61401c10000a0000529074191011080800880d0780c50340c0104d0010105480b100b08000c1c10307040c2c00002c200100c0c0400c03401c02502e030250f46058640200d0500c00d00380640c0c00a601025101410396203a2003101e00c6041000c0510403103005c0101c400204502d0381c883d41080c4d90000a6000a1040074030401145000805034070095242c00c241d03000081d1a1500764 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 75443464 1250 75442214 75442219
    0x6050109020c0c0f0103020d0c1206080c06041802090a290f070f020d0206071b120f03030504050c0402160201140306030c090411030114150d021c06020f03040507052805 74
    0x46901342030592003517040e0360303d500c5140c208202c41901030b0700241c403540e40c5140092040e1f080c14000f0508040101d4107031842400a03010720b041a05001c980100e4100074803511108030343c01e0159400595410011a00600c060628865030307040000707821a0044c030f24800000f011204010303000084403c8d1045441094001100d001108524400103015020380d8202a40c041c0d0301003a80c10610901a0048001d000c40d00901468159120303145085e00038502c001501c040c80c20100703500868041d4012542c803d201ea015218040d1964000508903040001403204404800c1c2003501103507040002407000010303012000c1d0a5240c1000042d9507044200d022600880c08800407608000d8480034820703034154014000d00001e03100c50403c0c0031651041302e0003c000c4208a109010f682004c251a01030180c0140c003c6101641080000c11026054070085406585c20003121000411200255020354413400c00360150504d00070810031f0340d9441540c1c007a02079101e015006a640c0502c4900000c9a80c00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 75444714 1250 75443464 75443479
    0x6040f090b180a050a0302010b100e031f1407031a040506090a09031407030509041103060117180304080c03060c030f06010f0c140a0c060f0503180102071505010306050109020c0c 78
    0xc2e80d1a03420581220001440341c82242c20040030140c0640000107000780c1a2408850204000c1017101c0100c03403040ca05416800c034902c001e5201030b616841c8840c0d505c0c02e50000c18401600e928002d8582c03000c46101000030b03034411144054400c8010038440c2c7c400112401d01041c00c040d0001040390802500344600a5515400b03001054052800c0c00a406c06014010b40c035460b10341405020703a072110400a100324506400c5c03449580041e010341340104010b0303480c1c0380100d0b00380e104561039010142100000c140d2044820076901c00400040c80540500005021544950f40034140b0349000074054410b02c40043c0200080b1807200040036611038402d00e0314054003488401e003510708904044011b001c070b0340040945480140c000610b1000544110f410304902039036858116142020007410304000754040000c00c00d00080400710401c5d07a40f5840006152500c6991103406d4200c1d0000040135084e02d5000401c188800b92081034018a01e070201980b41c0002071008607200d04c0c250600742d128445 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 75445964 1250 75444714 75444751
    0xf090b03010902031002070506010906150809070b04170705090405030d1505040612020906041e1a040c080907060e0d0303050a1d0102370804060e0601060806040f090b 73
    0x3425009240103903005410340e0398180d082a460070282d40724101c181c8031807041c100005039441c5184a0345040700e13002c1e14900b11010700031004403101c4102402000192041210208662035094000d20003072044c1400d410004401c000500d040c0002944640e104013000070400c004200040b04480721524030b020002641d6201c0f0f02c07001c2d84001250850754029240280129641c100c1c2841180d5940c002c845c6000316984d44010841a41c903002000c603100c40c011b58400350900c400d5004030b43c1c001000f00701e0745000c1488101040490700c15810000001d10441d0601159083c01c2c8040d0010705560314081c070302004590041039151489050003010540d4034400154150401d9102c14407400c0850058065044c103481028042e4200c84bc0d001d0b00010051012a011030508500012020340115400607a2840220607600480b0042050344c800c1c1d1183d646400c0c503541400503034081c01aa8071030300d595040020030b0008640503050650b01a03860000310784c02042045840d10350104403400a4090441c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 75447214 1250 75445964 75445969
    0x509100e010b0303040302190b0a030f0b030d1b05030f030906100e040c03110d060e0706030b04021608030603150708160c05060c090604241103040b160201050415021e03040f090b 78
    0x10443d80c801c2000050220784622ba1396815041501000880c0c2024842034103810101500c41d800e451259005c1074405044c2c550311900d42100c1c40c000c134007510680741031100d0b208641c0c940e81d00407240136013290000c100700071442008036551030180940300079100c0030b858140e5a055074001d590001520621210280198582c2c85007a12800190303c100c091000751800d080c040d80d02d00d154004c0c04c02081c24500307054034a090034402c0d503001c00d04511820b920711035903844214060740b01a080e250140030780b010303d0303a40400c401c51040c0241c50721755070b0203400c2c0350249403000340e031030b11035842c0c4c041000540002000c41c0000422640100d4100805551404000b0001e90b0a200d1544403212300e8005205940b82d46080c003c0010307a5074600c1d2100444800700103000760300e03441540180403429409000044500d0b030001c8052a509106060862502d5265483c05400c00303060150300005038001801c24841056244000c4400c002d21402182041d041180700400920f0b14080e50150300e940e1200f000070717a03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 75448464 1250 75447214 75447259
    0x70305030904020d060305100603050d0e03191e050c09070302070305091002071502030d23010b03130b0f07181401080a02040905070504030309050307140d0c090509100e010b0303040302 81
    0x21640101140d230050180c81a04004e4103140c8415242c40c0101e07810801c080e0300074944001706030380c010058050302c065501c40c078400302c44552059071854950703c240c80e500c0303200091101c01070340210000e1240c100d82c0c40c02c200d440140104401b08150040c090440000d42090a40d1402582254030200700d101e2041c00720700c0e00e030340344c0d000003607041040d21090001342d0040300400c1d0000345240c051220400c84071201400041220b410304007051040c0c01003080400200103180c011644d610b43c040b0000603030303d40b204444001d0b95801400b20024042c0545160003002031224070021030b400486040c64102c10f481715183c01300c0c1d020706120085000800e0010b0701e41c1124080d0643c44020003a40c03c040c8801001038002e40000c40100c0d071102004900c526001885004443d9846040c43c110b10502041c4000c5040c03403101100c0b412900c0c240421410428000d41e44a0410b400007040c41d0000404117600740e1b40392400f121080d0b4500b404003800c5803004000c45081c1c0f5016102c400160608204000d00c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 75449714 1250 75448464 75448469
    0x20c0a15020c03030d0f060f082a1503070e04140c2b0e0d02030309070506160204060e07030b0d0218040c150f081509010537080609070305030904020d06 67
    0x40c000090303000d40c0007a086c1c0c880400030701c084c0c00420025480e0400800a00c00c070b07028048180e40651071010322643c0024102e4140314850044011400807135011032000c4a101c0d6101c40030135404001c005410342d000b00c1c0d5080700c090880b814060354002c94100c18070b141e800b5004441c464800a0800c0700c52a0400d01080c500b420645030f000e16481191180d0014001d100b81080b0500500c0c09070308a41e4400002e9901540010000d00101450601004415841841d112030510058150000981d84c0c030701c1890010102c43c12044414074204c0170040440c4d45200030688101e0b0400d840c0d502584030b501812901500d400103142c4151114208512440c1c100e91041d420140c6032081d420030641d000f030004504502a0300e5202d5140c0712243c0f8150b58105401680b80c205484500401c280e02d40381a179040c1c0e0b410b80080141d9190074640420700e6101c1181c00508210605940c01c0000c83c2e8104005a030119a080242c87c4080c00c41c3e407416228494440030b1885140c0210707600560407180c1d44500700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 75450964 1250 75449714 75449719
    0x12031104051504060e0607080d0b010c06050a150503030a17220305091306030f1104060801060b040807270e01150305010c020c01031a13110307050d0c020c0a15020c 72
    0x810300340104031025581d00a001c2c500000c0c0c4541503102071750070070710300b80c541c501e0f4883c0f8000d0400c1409460030000300b02884409040020b802582c101041007440392501943ca68600414146500d00b60440310340c540b40d0005009500c10800304140070b07486807034043c1c00c2032040090352140d01c4074141c9038401110004400316043e10321420804041c0c02c50300030b0480382d20a5400d400c0000481e00d082080340d4880c0310103401040c1c44803444002941a41d11010280d100410000f405074941740c486084030502d4004108054002070140039018003003008500a110300348980c89803250b1450045503c1c4880064404650f8441d442c504444000f9006454282c2c038075444245038607503d080c450f000c2c00c07140c05000c0150040600184003944203010710586641600c401e000700b0b000c40820302803030b10403240c3d170410040d5490400120b03c00e20f20004600510039a40c0d1207446010f00c8406100711106508401c09642c012032400c0540d4883c009200102c0714000000c249000c98000180d003400c4180c1c400c13a5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 75452214 1250 75450964 75450979
    0x6040219170a14010603020c0a080408070515040807050d03090503011e0f0501030b060105071110020303180106140d14070306050109060b0c0c060309160f03110103091203110405 78
    0x952607020070589000e901154a114094444154040032607101a00149180740144010321980b400b940082244031550f500301e484002007526100c00300e41060300b009209811040c000c101d10301e000007a47c80351807400e4140503e024600f000960781c5410078403038a40036407000e00e00241894003c912801c01000043c009100000d030308800340007081c001c2d0881d030070443c1c034003015108518020700c43c02c1c0c181c0f6440b46216600d9250000159015048048102c8030108201251045a1994121428040da6030303001143c89060984142a020b251200c020040b43e140800810440046907010064007606660006400c412800d001d004015022030b00700c01c610521030300104015096010604942410500704145629502e80d00268428060210102c1e4401580c412151030f0070030046400040c4041220b40444070402a1104c1102a80c8100400600c980c402c105122085e00d007881310342401d280811107090b050761000d194072001d5845100300b540c0c0315080400d07020203008990203031070024003c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 75453464 1250 75452214 75452257
    0x10501060306170c1509061606050105030f030313020603060111060f010305010b0a030308010e061903080a030b011e0809031c060302030c01080c070803040602070b0702030a0306140a0905060402 85
    0x1502a101e01d11418001103d606840c40401c2008030304044c0103100204070f844003220b0b0301c440401da6000104146d42c000010441035901084a40a10420910801010036550300d890105420140c00c0c000116080c1c108000700580c4108419503080e1003941100d01e2074590b2154030040b00c0a1210410754482d03480f52600b4450420b401c40300407412a8440c800034021a05020180146241e0901c40140404d8400380180039200c2c981d080e00d40e0001c03003d007110380403600c010110002d4641d80c0d442629540c0b00041c03808142541800b8098829000f800d04c02045514031a010410650300000c910401c1080300c04544000000c0c0308440006601d070800f03a0302e0500116205000b07106511080380b0900c00d8103160501540107840d074038880c1104200c064101074880e220100c240e80010800c0b141c0950800403038001a400e00425800f55115034000e6440d80c14003400a0103c0c0ca0680000307041928040d42800f850307450311189420388844180c040307515100c03400420003030b0084400c44101c101000c0c3c00e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 75454714 1250 75453464 75453467
    0x71b020612040210030204080c040902040f02120a051609050f130507020f0115080c0d03031e020301090c090e160c021f0f09080709020919080606040608060603070909031101050106 79
    0x780b405039008a4140841188901c0250b04920851080d8000c6408c00d440c034034240d260503401000c04d5070014101051649221546008980c00701203211700034040c85040c030008120300c3c49041c0e80007001c0004840100d2100a0140159602c1d129180c030580c84060300c0012a210310046100146404400f0702c264204840b0280d02c0f0b141c240c544c40815031a004402c240034112a441800b210300040140030a03090301b48c180948002040029010b058540030610007004480c481a41132859014005843c0c3d4100b02c28401a1002510340408000510a05001d054026044182c11151082808481160154080e1846429100b0203035220140f0a0420885505000c81500328402c81d0381e003003015004560700303640035100d9004400e0b00781e00c41caa040c0102507480c3d00074007030800e00400c4440d1001500494a80e2041c6035003007030fa00bc0d00000144101418280698005804580060520751410030b010030754030038042c42500b440c2521840c0301d205141c01002c041090508442c001d214a40c0c44000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 75455964 1250 75454714 75454747
    0x30a020d02070f050c01110307020d0b090a0507082404050d08060d020402040905150d0f02010f1403041b120201170709170d08060f0102100c140a0206090c1206071b0206 74
    0x5e0603404a030b5a0100c001200901100315082d00b40e008100a00b494082d40314620060350042c44444181b05a4a1007000301c6c008129010061084600a14500030100220402c800041d1034280314400c0c41018000060b13400f0541c2c0c8d061110300c0c68555001d40d07074100003801d148001030010b074004e40f000030041585009600501e1007500300d003210142d009000014401644040301025260340f908225100c0190b1085140d003903684414904400100d0380140c400e00c0c540e00c1694101e4030b072390384050090018440c603034011005041c0c500054000c1d0800b500060300e010000d603000c2c08118001000160018002e6040b080a801000242040410711440c9542c1e1051a541e080001c5241040020000d24280703074030f4030054030107902812801499100d4040030700b811101c15028042c2c0c80c1041308aa0006001605a04840e03500901d000d007070207040641480902c04840d40600a070350b440301d001d0b120000d84590441c41b40c0c900300240045006948000300760942d0029840000001c12960f21042c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 75457214 1250 75455964 75455983
    0x30e1002070f170303070302030627040b0a020a0509040f0e0d0c0501110415080601030e1015050d03050708071b03150b090709090c0e0909071a040b030a020d02070f05 73
    0x403211411243c950107207400c43c0110754110b8905074000c0002500e041d01c80d401454200c4001b0700152010100300b040101c50000320320440d07840050700301c1044280608059010b40008410400314907120210300c00034494481c0103c1240203a03111400700812540d598000c107030444449040d5066004014130051424980c180151450b6080440d685044140342088070100c500e00b0340d4041001400c10016100c414000700000d043c55640c0d100184551001d00042d0300003801c50400092214610034107019190464000c503000d01010b070a1000069004030803100681d400030403440d2104000e144c00c070702c1c10010110300641d1100e0304400008104c0180c40c1c1c50ba070b1060420301840111441e4080c401c0812007260302000154118000b002201c04543c80340300900944d1030040c2e26603e000e004102c400304240c90312010390744024020040c03108201c214030b4603810361401d098a4245040140d92241c00082e140e00803032680000e801c0038210080e41103030307049540190380f002410401c1c1841d1782c807a007004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 75458464 1250 75457214 75457229
    0x2d030f0c0709020901050405012001050903091e06070f080c01020415080906040b0414030915030405010c08010602060f10050d030201060306050a020c030f07030e030a1103070b12070309030e100207 86
    0x441c0108180c40c0700c0c0241e40b1845410ba503404c0c2024541401141d03015404002542e600d10b070030b56031803842502030044d14071407010200110760359a905800c0c001100b40b42500b04030540300ca5000c0409035503d100c01c031690103802000c8050590501d00300f0388141d10440c52098480d6100040001cac50340e1100c01c0d1100c6401c800c0d1501c54659032020070203070b2034180c00c83e0000d02036003002000400091200d15810180c00ca900112400c1c804d8207004140c128441c54001d03040c110010007040304004003401509007201503131602e040706501d040380280d40c880f4040d10142d052000d5000007055080300c00b018000400008281040b4481c950802900901c103034081950348a0a000c005109000e8030700031508190b1b0520700551401d00304009090158210450840c100403190fa5080220b5604114420455004101307100c88403104130101803400201d64010403409200307011900c1490746102e81c0070780c4181c00381004170340303050189011128454002c19280e4440f481c0e58205070850740c00a820004d41c3c0701c0c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 75459714 1250 75458464 75458473
    0xc06090a021f050a181a030603060a09170d140c03240d08030603030714070801050a11030109050402010905031014010f0302030a0201050d060513090201202d030f0c 72
    0x403032441d60007651440b82c000082501040840340c6244146440180d900500d4800e00a03261184110806080c00c0c0c61111544503002c001c1c4507151805128107500402065010003a5020b52350760710040c10102c06c80382c42d620384046200c0c000100b807a0440d1010000000c0301c4459458114125070071600305482c0001c160781501c3d0210500f5104601e080341004d40108203859440310355858010940c0001c1c034442d014003003807207400c00158030303800007182c0c240450014100c0039062019082c05c4130f0780180b00c0c0d8421801c08403050444043c10302241d05450400030007254960312800143c509501c16800140c152041940218429250b50f22401c4441c4035800d0300311141c1d984400345c14415041e0301010390716420901d0f00200540c0100002d100c405d0b4249004503005584000240b0f80400706e4242190741034913100554115a400031000c0414141d040c100c0316a40c2036a110503903101004986c0d4607070790b505081c0050000c0e8001707010b80c2000d640e000450b40c2d600702407101c110158010f0340219446115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 75460964 1250 75459714 75459739
    0xa1407020d0203030112050309090a09050609010519050402030f06041214030c0a03150807060906140310031403090d110a050d030509010c0f050d020d090506070803011202060c06090a02 81
    0xc003040780c10005010303a009500b141d0a0146a1010350126017048036076210821801220361a8198083e200301008000019416641e007001424042d0040114000d07901d00340820040d417010340340c030320f101030008103000a082e501c138400300e0b191500220440f465403048408000c1004104c044076004100701d40da600410036000d40503100680019138072550400c000b800210416882540201143c0c12800701c0022015a41ca00c4c1301c0c1018060303082100052a020006c5c05000d4011180e000310700c800600e443d140d4904011080000201804024955014010003801464080050f03c1d5041c2008103d241c1043c100e01e0311662520350315801c1c90080604000c0000c4c28580010001074042d05a141d940ca0102c401004664140c8130400031517850721445006008250200322080300e050003600248081e001c0c0000140400400d0b502c028416001005a800011109800d032811a0865910028400d13058800a00131380100c2131001e509205203000c1000080000414101050003691200c01041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 75462214 1250 75460964 75460967
    0x10306080a0b160201060b0909131205030108011404030e0121060e06040c0c03020a0308040302071205010507090503011107080d0605100c030305070f170a0f05090313120f15020409050a1407 83
    0x140c15104c0c2e1f001911042c403005203642400601c3c1c65001001d45c645110030b00a90340c4035480fa4461401d100c0c0012808001884141800d20074031680f050348c0b0f00203000920740b0741d6000b890714201d900014100403030100089240d54040400030304403907041105100c260788807504403402000c1280d240303110340c1c00c061000c0080c0d4065141100100d030503901404040c0c4031a00c0a030703005840940110110f206520700056403600d6400480d9070703103200740008180303400e0480000342010030781e400640c82a40b400811590440d031400484283d5580708944945600c1071a001000914450380a00e0b0801d81c1c40d200103c0c01e42c1d218041038001440303070f2010800d076214903c0898444180310903440104917090000503000c0300100c4801d600900d03855001c00c1c406845c803110400e540781550080e0360340d4000300d16100c4031480380006101801d40380003881c1d225045520740f20319004800d103028158050107411448402c0341a01164094500130400b44414200208524010005011a13102c4001c21501089805 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 75463464 1250 75462214 75462221
    0x109020301060b0301060503010506180d03090e1807180213090501030209070306140909031b010e150f01061407060606081e0f0a05070903050f0610170a0f02010306080a0b160201 78
    0x1c0d1b4550303491606589c2003909218841c0d10004050803801081c0f400302010f0b40c0c1e1303c40c2400e0114030a69412a0241c0751102d4020100c5014141141d11742c503100d0302405001c8002a00000c8800c0c0507901d02c030303a40521281034006d2140c111b13003040c0316041000114200d09150041c41c12a803081e10b803545683e0300c01c03408a081358924012840c50503041841d01d9076629101420a400c00301c45800d42c0c0c82c0105005400d6041e166038400800b00d0303515540c0032040180203001c4040c078010711303503080c0c40c0c640381c00b00700b0042c0c0c501c05000351400e01c040326051202805c1c96100781c801e5603900c0a03081200548401c0050b1404204580403403100c40100507420300c5100103c10700d806692800b40580c01d0b915401600d8028100040c01c01e000c00070304840c00000701d40c040180d4807040c046500601800e0a00702d05100c41054682c0094041c42140c07840080000ea0000320405440d8100030041a440150b20048003e44050b62100300103200d484040e00a001c409441e030750203041d04520f00c032525050604164240d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 75464714 1250 75463464 75463469
    0x4140708070b0901030b040f02030411010f03140a0e030405090103050f0601092702190b040306050a050714070302031207030c092111032103040b09010b09070c05010f0204080109020301060b0301 85
    0x10000070f2000e003040b54040d400801c103580000304086802104d2070346103001c0741c02c1250156519520700c40c0c0c884c2a540c01c19003040c1c416019103000d0080c0c041d28501e03110401d0b0003500500006603640d10360701d5050b109205440c05010000c010b5802542d50781081d541d0b0b0103450444401a00071080001a10699881020020009140e003422458285c2410080f0800c0c8180241c3e00491100c00040f48041c00c40245809000f0400744161034a0640c105101103420081505104038908000d10200d42c0e08110601e04140c0c2100c81c0ea980c813034030351604904600903024a000350010281c14403084035010340118940c20080d41d207614900e59200340311050a401070110300600d1405a00070800304950f2403070720820f1007010b01107620380c4100c3c000e19071103148195000600c05601005100411031030070b2409411180e10340080c80f094010307000183d0b80110203031034281400340b1000c5240400000390010401580100c004649542c1d803100041d0190203201d404920a51130400b0100300c4038090b0301034905 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 75465964 1250 75464714 75464729
    0x6030a0f05100e150f1506040b0703030f020906031b0c03120403020c030d050a0f0512010308040303090b091c020d020d1101090603020316051c061d160806041a090414070807 76
    0x142c481c0b0485609500e40540303601d286c04585028260f054803484020b00003401902c000f00c0c1e680070706040080450700c0d0076500d00d000e00d0040020401a999580580b904588540f00413144110a100c1180040c481d60400e0403a03404041100c2e06181c240e102001d103d503000f6001d6580c0c80078007504040d15018581c030303c80d010500500c00801013500c0380d0003040260159050181c035244102e0310b0f50404031401d030b0040320a103030000b8050082640c8030110000600800a039a4249100c03100080c0d00c1d030420b00f481c0c5000c000c2594204082d580c0b550343c0342d060580c02400362000b5a4403428580000c0315140c03c118046040c0000000315180b0902c00c50f44a40364454904c81d1103642260200d803140d000349800764110010700c20903654520284101001821100321801e80c0c4d900c05a000002001c00421280e42c07000050307030040383c0d1508100385035481403007240e0010300c984455202c090888100700311280c0081c1d00004010070031220f211201d07441e02100003203507000c958440309180d071a01c65018151 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 75467214 1250 75465964 75466003
    0x8010f050c070f06180c090b0f010c030503060d21030507030e0f060402060f13080a06060501050a1709070902160209150d0303090606091109040b151206030a0f05100e 73
    0x4003144440d444107020703140301e6244004155070340d186e140142d5515004840d40c269940803444552905044d0310003500028204400c01640c6602c001d00301c0d00004000d03e00414522102200300080d20b410b4001600013604401c60b44141e11700d008000304011202c0001003860070f0a8041c08813400103088078645040402020b05035603c0e428032280d07810421000791011000d02c0803658050210140e00082c084610080042c1340d40b6003081ca0a480456000d0390600104020207030000f680300e5a121038100c078400400000384c560400181c504040d51b031204640510200307070b8240d410000803410310498002ca034140600d0b101ca51880c0002c001c5901c1c01c42d4408284070500b1b001a0085c2c00c00684140540400103c403541d442507441a41d0482540b011400800030300501140350078455100038140c103030340350000350780b56646046181c032402c07840789540300000002580c159010060450802d44c0801340980f044042e01e0300d565101507008104c4903940c01d000c64800b54100c001b9107160803003113100100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 75468464 1250 75467214 75467243
    0xa031413030f05010f052d011404051504050c04031403030105010206010e07020a051504050d17220204020a030902030601120809012a0c0f050a1d130c08010f050c07 72
    0x2240c2c04035004100f12865520341e0b1100301c50342c800384a001e00c0303100900c03440110034440360103400701135248050a0b03401c10985401446030441581c800484100d05440004035a11007861035071440e451203034000e902606241c200020103002c0d50190048911601403000d03182d80500380c0a40f00e020901816006911800041041100d03801c0c040350450901d00555003210425200c6600740541900035403911281802407104101c8104031048a8a00720b1034001e400400ea26441d2100180150032203440c060070f0b48840c0140404141347ca03d58a83c024421542c4240700c03130000e0094101e290060703119000702000002c00800d074800b1803101e603500048c00c03840c00b09400c005503102e207102030300c1c074500f40200344052140c40341030405440b069000301140188980b800c035011450583c1900014001c003400b140c20010718240b080e182030b036900e244143d1000b9940315214485410b80b1800040c0814040000001c0d01c040c040d03214508100c4d07103080a010350340e00c0c4003203020a44140440102030041e6803035403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 75469714 1250 75468464 75468473
    0x30b031b0117070f1103091f020f03030a1b0206070c02041a030f010902120c06030a02030406020909010b0406080a111206010323060405070801050603010603020f040312020a03141303 80
    0x290300311008141014801c4102076050b800a54404031100c10200b164001c03416040e941103c200243da0191200031880d005000000ca0b5494150b50111000380a40919454480b4021710001d40c04800507002c0381c2c1c07a840c4c0484104080c2c158654001625000d40d64621041c610109a203403240c0080e482c1d1440040c0c00303900b8040189246a007000141202031012200c5940a01104454246c2c00c000840d440b0803600400492505414211103141d02070802140c0a0700c0e25000e80764411400000180c4a544034100a8043e100d1700c2e04090380502100000f089103040070300a0004e660555841c481e01d45e484000e0402100c42c103012142030030b001030014060040c40c0d170390229403040c818980420030b02d80409005850081c140100100c40c03a0b03410420484d414039202e025408942484e010203254917101c0032035480e2006004000c10150000b584004500414044500035940b2048003100081ca4200003500d800d90682d0889c0000c4100c50701e1402800f01100b518640e1380300c0c00c00c040c3c503240355a54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 75470964 1250 75469714 75469753
    0xf0c0201240608150301090b041a33060d0905030403151e0c0c02040c090e0a0c141e03181c0522090204031103060708090a030c0807020d08040503070501030b03 70
    0x11985d40c190b48501d0040d00081d00c40c13410a01581c0b06a0b101a01420701c00003610001c1703001800090031480410800c5124411400e0b40c402da006505405d00410b04050003284092040309101405a0301744032040041000000041c01203c0c010440e55031910580c40d00041034441a04c0c0303501500038843c00c8170304025940d5100a414644504111001030303040e5020400b035805c481c103a4004200150f00030051388040441d0540c1c0030102000c10001004950700103080e284424603032040301180803440a407109890155000003007080c00d440790b182d141403140e400244690751205d14040c00360502601051200382c1d403003411030b5887d0f00d485042c1000b504a40c840f82c0100084040d086051110001d114078880c8000c0001d98010b002400c84142c1c1300007410303d00140a80203000700000c80b401c0010094012407106107141d407500e071404400d080f6003014005802000c270060f500c5100d804a00c820006003500410807244186d06413100d40350780d140107404071003c2c0c0c404640c040c0c010510036031442e6007891 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 75472214 1250 75470964 75471001
    0x81c0c200312070810050301020306030a0311030c0a051608010506100311040b0d02120108120f07060b131401051009170708030703120510050d03030b040f0c0201240608 74
    0x30840c2d0800540802800341a8801d65414012544031000d20030340307442c1201514050712003a0029861400c091010075600d640c139420240400010710815211f050b000e00484100c0030f0b14100302c4001514a040c200d489440044417910b003490711080010f481801802141e02c0307090000c04050348040306146c140d000e45106000751781200c1042001046e00e01c580c0014041010a01c0e400603250f0440540d0300e120450181c00c461520b44c0074070140002451204201c8600c05040000551500300b9480c045014100118a050b4810b00a02030204003204680c41158041910310040c41140d0780ca10a224906221001d46800a0101282031100f003c1114043e00d902e02c404048a0000c2d6a9108090640c0c000703a1040b80080c206014066902c00c5502803603420050030701c070303a550142c03400b00050380242c2c40704401001e054840500e41d0240c1d481d80e002c1808000f401c502404918643c07400240207008440445030b00d460b0b600c0300700409542500c81c0d841910f14607182c4402ca9203905c24011106090759 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 75473464 1250 75472214 75472277
    0x5011d0402060307030e0f070b070210030209060414010c06020a080a0f02030c1b0a020901180501060504060512060a03150c0908010b09010608090c04060b090906010c05101505030604081c0c 83
    0x10610441f0720790400c01ca5000308240070000313454506602c10484512101300f01d01c01010b0050100c51101e5a4460841c1c04032140000840502c0c00300e00d0043c4c03560b07000c004002d0410b61010070f001e040c080e0406200d620500c1010750421440040303034410802c0740826107085140384420b02480d82146042d03501102c0d1543d22000b01c2e907034410380b90300081180b0400d82041904d00113011802c071447c40c40c0d010305405081641000d90525080610042c9036009070780802c000c0d00c1400011850369100d090415002e036800c03820211255003895103240262809519030360001e8215100024100d030b040c032600313000840003801d080b85a4640402280e0009020341102d00501a400c17208074643d940703100e000000c112207680c068844949400f00000d0080c000d2072603040c0500d511101c0001078012035961044400e00a00154003884141907010007205900680c3d00341c420f01d0306202c184810078010f031000d52a882d140d0545400d650215a041d0b07148175072100007250349024460f1101080314401d5410700641c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 75474714 1250 75473464 75473473
    0x7060609050a0b031507080703022d0a090504021c02070c09020a02060402040b061c051018061a18010c06020d05040303060f0605120f09190605011d0402060307030e 72
    0xc0c0c00803602221410b82d40d1041499841401560a0606000d8040300c2c10f0400c10005040c1b902e070b00d018217881c000030010003c142c1e000074070300c21500c07000c03554100c0d40540803414402c21205042118070742c0d122042c110041510b40e04001181c2c64240212903400801408402d4081003011100f400703908034201c1180c044a400e180030031a40c0c9a817000c1c00e4805560390080040b1304150040c172041f82d2664803028018401000b0800480c419600305c000030f10140c400018050b81ca40040036008502e036003307007101202040c1600d40700440717500070005440c0004c0c0c1d0301c6102000800020010f00c00c0c0f501200d02c0003603000c0c51800075030040d48400b0049019100c05440e112268090504407601150220701180da01c0d80103015040d02c40031450041c002c1d038203000d40342009161501100031001032090000d80265070005055043c203209454034080700c484890541c41c0c0314505140545024002e680422240800e802c0556014800d540e0040f40c01510a514507207444608401420f5640c4401403503214 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 75475964 1250 75474714 75474719
    0x30515010c1202250302040c030603080304140f07090e060106020d1d01030b120102031803030c09190905180c030313060f030e0715020c06070314030915010902030108010b030a030e06070606 83
    0x2034241044e05028044843c11891811403040008450301000c10300704041c5410001e00c00945a4002c1302d4000d604403003145000d40c0c3d41c200d1a4642490224810382c00e00403075000241203a000d4008440c15003100040e1703150303680c98101c00c0380c0e140f0909006100040807083c40044090040032445c1441406241c0460080705e1100490424501c1c1c280a90300c50391300004100f0507a0501d0080340006403c00c02852860030308500c2440a40110500180b00f0207001c0c03a098080640d00460b6402809203e500307120074907003000245441110340c4040b010500840d0240c1115140210031070349074102900030480301c141060011110607610320416011f05603189014810500100050340080c28500b0007007050f0750800400900f8180c60160b02c2c0c1c05a101070080b000025004101001580c03415030b0b034503880b56900c020712032500520400d19103072000c8110010402c4003103500214140d4541d0402030041c0c0341007409041d81c5003402880a000182c9504602c40301d40350080c0180900d5005078400703d40b03e41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 75477214 1250 75475964 75475993
    0x201051b010207030906021504080d020903070513060f17030a0509030a1a0907120812071202040801091703040b0a051308040b07021c0c05040c0516030807030515010c1202 75
    0x2800460203130046140303040c04121095040242c0280c080381d8000b00017150602da41d070716865008204007090440d8004c9100050303503e003040307800014480141110f4400345088241c100074001c40c01905a400003c42d8081000801250600110168000118542240500110b4a40d00b001d1181031b4540034251940c0003091941d0203a040c40643d6105400d0301c0e0a0124026251050707030390208035021801e07000c40011410f00c10950340500c103069400401642c1301d0038210745240070080f45408e054070103c0c1c08100d0b40310540c0801600c52040d500c000b20a00700010700491400221001404201e0480001c0d804010582080c3d80111308486e100500b03080c3c7d503803840000c0d003181d080880d0180000c06e1030b0302940340100b0303420131003009500c0f03044107860030b5211441309038000d02403240195141c50040b000c40340b254088642400c8607000341d4103000006d00c1c0007031950784c045c0e0718800041d00749001720b000c11444050030352162005031603540941c5856580c400540d040d4916034400d40c010100c40e146400b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 75478464 1250 75477214 75477217
    0xc0803161806020c0409061d060402010e0607020d020d050c0303040803030603010f1b0c11060703080610020f07060c05030c01050f09160e010302120c0a060512011208070201051b0102 80
    0x80c1040d4141040c00311910328001c05295164080e0007803010440ca042040b55000705501c2c0384480140da010601d03500a0504070003070403003013036940010346900c144541d40e0000483d0040c042e601c00d03a11400c0c0d40c04140304011082c020713500c0c081d6001022000400c0145000480360b02c41510800940d150401443c0003e42182c101d5407281255400020411405107002c1c03240382d99000d14110200610f000b14080c0c1c1d04520140c1842400b840003e80120003030104000100044420081c4500d036512010303c2d0081c1900019a08207002d44200f002d0303940000e001048400c15405100020440c00d4503051084403240380464007500c19000810255061036000e000300382c1728011001d170000304c5050034000350f850304000b010060002e400150043c00b4040600d80984e0440c0d404a0311500307105408a0035a04020364085640c0e07101080301c000151807600300c4042c01e00803c1040c0170a1580c0e070385000c1c0101c5005000300041c40ba01080100d0001076000b8800f405904200c130b0887c2d00142d101c1802c1740d08a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 75479714 1250 75478464 75478471
    0x2011407050702010206060315070809010b04020d1b0309051f020903100603050601231e130506010e0a05030a0605070207031704091b080c1803030414100503091005070c0803 76
    0x40c070001d054410340d6010840d060b00644254028991010600c640008940e40a85000d00f00000d403800304541c42001d4110280301c0794014004c65440060420720401060038420000368100451182440703d0b00030b1207004260f80e0400b0140c0250328166000f90840c42a009442e1465942808890540c3d01c0c01c025604004c0000440060400d041d0304003d031912105030b0100740342803200302060504500c0702c5052950200160ba4040350190343d8880901c0d01f5071007590756508094000f03c00e000e000d005400c428040d02c1c0c03c2e29502207445043c2c4c14070808041d140030b8207800d0391018a40d0000510a03a10084d0300400034410b030317403003a42c40e562111580e40e03800e000c40041480c081001e120a00c068403540d41010904890744151200b18180603203405c0f070007400d00d9182840070401c2440301890028420301102c0040580c5e946d540c8440c01083c4281d868451a03010f84e000c0b51051301014003900c22039004900d9880103190004100940c003000d804000e000300c0400940f490418002684400a10300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 75480964 1250 75479714 75479717
    0xc0e0114040e310c1e03060903020615040b011b170d02040e0606040305150405010608030a0504090f27150204060305040303150518101203020703110603011a0a02011407 74
    0x4036500891900072803035100c50f10072002d450303910564030000b40c00c1013030749003107604600e4485c418a40207003100000a805501c0584a1800d00100104156003c1540c502c59080520081060001c1805000450b425020f1f801d012400420710001d440498000b19810107225000398003180000d012000010780008101c4070311a0340100d0b061143c01ca0032060540c1c00101a940310341400e185440d1580d0740c412201e8a80400c0c49000d0110301030140c02c1d04110058114601225510341c42030000030419485840349103070b071368075000118003200b20078000c00a803c0304151100d080c807940c0448110800c4241c100403544210495003108250450340080c0008bc51103840000d4207180600b03016041d6203580740030310400005110144826a5480c1c0c010803400490441e0b241750365600440702145044035000360040c42490000e00007010790000302901668031030751220f42c1304400c0c90301b4007001c0d00003801448081c802001104040c1d4011034045d00440406100215414006083c00001000103456200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 75482214 1250 75480964 75480991
    0xa09020d2706110304080909060102010e070f0609050306091515040903080f181207031803050717010203010b041403100c0306080d11060c0a201f0c0e0114040e 70
    0x405000d0b01e8801d543c0da052603c0600c0e0310310700c0c2ca690303042d959101e26145180b041c40c90502017200d5034800d40c00344414410f8103007151a038a07210341c41c1c9243c91150748110300c00940d0520010401d820701203103003400744404100a081c8881c421411902101b00240b2090550030103190010301a038030ba00454a40038040c3d1901030081c00c0004101c2424913004040c000c10640c40707005441e6081001a0f21242c40c100c50b544542c590042e031404403504030300b5480344020403d00e51408000e001003c226901103440d4400710241e954840740800e802d0b40402d1052003080c0000344800c010b034562009540200071401010f690982c82148042c2c81114014020b0307100007540c035803060221510403c1315021900807410301c406000010301c0499a20747c0300a00a18008802050303c1d550180a2000c1100e20380c0720315080c10001180340100342d500e030701440004a03c034004401c203102a80c2e01340b180070103a80f00c070341e5103092220366040155000030b9030780600c50300b40d002004001381042c0340141842c050301148041c2e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 75483464 1250 75482214 75482291
    0x304120e040e0715030603020301021b0c01020604050d0e0105040915140319060f0605100203030403020706080609060108220807120801050604030b060312030411100801050a09020d 79
    0x10424010300515900452a02c406540b07028400141c1e00d04481d40b00d9014503a070041540c084001d0030309680000c1d059800401c0d8a400c401c2e01383c4410680da18154101d4034681030724401203984407800c2d200504540c00003404002d502d803190342c846840101c107042551905035a805848103d84001d0b5100b050882010028852502e0581040b1071803502100100156040540c0183e031810780c0450050500755211069440040e207070304a1001040020481191b100040b4000303901ca50003218110014024071501040e00750240e480c0741d009040c0500700b00401d584000054422041c041c1800c41c451041c4000c008140300c1c000090204c4c9403241181944458540c68442d407041c1c0d11401b24014814a03400500090311200e007624100d0b034001e01190304544405c001305e13003028580c505900f01d104000003044144040a0516003002c00e068840400030800c800d802c45008500b80a50342d88603028010401415460390050604095811300000c0c2100c03d107400c640548650456240d040c61000e42e40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 75484714 1250 75483464 75483467
    0xc0303020c030d080c0906070c0f060804030e03070e06131b0c0219050105031b12040b0f280e0c03030301080f0d080c0403080a260a0b01020a05060f0c0d02030412 71
    0x903040f10079542d0400b00ba1030f0806071a5140213002e003240c03050241c0c001245007002d10104d919080014950092a0b21001d80c81c1e1701c0090038414100d8081e008264841031028241c10300080d0503007218010601111a5185c01c1c0c204580c225821145030310300c1d500d404611034903c0344401d10551403021030b01c404116996070300c1408000b41d0100024014841200b604206a036080030071664041000200004d04541401c08600540200500e030724102d800c282c00c00080000c40c9070715501444840f03030346000c40c0d0b540d00d00025070311000d507141643c14000000e20060b40e01c4182c000510b0700340e03d1410303500302070fa280b0003107483d5400992011400b0742c403a194841002105020620f09030081e032030a4020303840c04e030804002a10903440010000800011a440d09074400d24840806000e203d030042c0c5c151204280201e092401070314170a02d010714100031482c080d0f00000d40c0080c05a800005051141d0381d6101104070031a00410100090b2420001019034140c144000c510980c0b288074642442c1101440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 75485964 1250 75484714 75484723
    0x6020309040b030309030715050f0d0c09050f100503060604180902040e07270209040207050c010e06090904080918070305011e0e180712050703020310290105070c0303020c03 76
    0xb1030b80d000c0d07002044800500d440101d074100a607042c2012902401d035072050225160f103e400480040480f0203c0c102502031a280c10810074000b050361030f956016140c104102550381064030340340c0d100d6018280c031011580104051640007000408480c01c20f5a0340d10f0030303031611019a600342c0707200f580da040c110118a010302c13502005074012001880d41c0d0741014180124145d5260002c0c4240c461201e11880c042c065030106d9180d884054415925003400d0300e0b0840ea03c03504855424003207116005880c90740d04001c4155040c640c0c0080c1903410a40301da488100c00340d802000519004100303840d008010f4004d00280c030b8004c0005a400140c5d640c904418210311803030300400704580a02d150020408110420240c40c1c00400f45100d4200004290b20300c01d10702021a4400c00e000c0416000c0001400800718110342280e000fa001c1e43c00c4a54403030403a4046815018001c03501b08900384005200c1c0602c45080c82900c04103040c4a07152124075111400491036a502c200d0041c0e1055910080b642070500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 75487214 1250 75485964 75485981
    0x1518031c18020607061107020a080a050d02010b010906120609020a0507060b030c1003050a09051f0e03040812070c0e0c0a020c010e0f0d1502030915090304030b010509070507020a0602030904 83
    0x80200180d001c036800a0720030f1103080030240c03a403612802c045001c0d41545080300d070440d0b4020242038503950b03039440207600c50b400c0c02002d4544c2c1c013807070007c0e0100e50700600480d600190140e4400b00301d0350404e8000d880c01d100401894108030390341c20000c95401610f1001b80040e860b0703901d42030341320300261400d4804e03141d00148250090f0032880c0d0314a01764503014407103d80100c040c14003240710b94070010008000c000421001d481480380c01c3c00c0300b0010101c0491910203181e480000e1104940417040c1d00c0d60381c403552003240398940c0000f5006500c82c10101c0502402d038070403540301c56150758600030350400c044d01b550128194440001c1006000e03804101e944280c140c282050b0031501d030320307000150002e03c0e152020350080c00d080b0403982c02c0200341c2e41c440d0750311803140c40110740700d050414841e80e4610520010080c44900100401c851160000544085a0340302100c0c80560b800c1c1418000340c900e001c0e001d002444000e00101c40140d8a00281e007010309400d6000b1520348a0107001c100588000384c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 75488464 1250 75487214 75487241
    0x30c0603020406020304171f0b040f06031203112701110a0f080a111005010518040b0103030f110f01051006090e040f02031c03050106080709081518031c 67
    0x100002c00c03c3c10740101c240c40448015000c1c3c2050403519124503414014031039425020118801c0c07110000d101c5540c0400c03148002514100207100c03681484030100e4031b0500016006c40301500c180e4240501c40d42126401e0424005118201907504510002290f508290781c2c20071245400ea08842e940c0c802c0750554108480c1c401003c010b5119140c0480081a0482c041c0201c2400660828042c1c0241305044880e40a90220f589414040c0d0070100141420700440e4032480000d9174402c00c6d0780d10007101031300403904440a49003591071a0740941d80b103044501042c09014002d84c000d880d03000103001412800785114008206480e104094190008854212806010043c0703030600c443c4042400845d4029400000d203d003c1c50240002403900300b2a41d60002031300004110a030380c2c00d505030031050482c1c2c0b040d01c4a0301c00751980c0c4800d5529000d80c0c002c2c510154007501801c220008102016600181c0080721800b0110b10014020701319404207a0b558040244884144080321403440b403c400701c03008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 75489714 1250 75488464 75488467
    0x8160203190503071805090a0e0f030703050904051e0c0d060506041203020d020f0a110402070c0312030c0206060d0303050612070f0503060c04030209012601050403030c080a0c270305030d0204030c060302 89
    0x30306c0000740c0a020090218006542c1c0d07404003407111007040020110700b024070411a500c804035850300a040b03512404516004500340000720340c0203030290310350100c1e42080070b5007000150307101c0d0080c440d5900a1000d07266000d81f01c950000c1e203901c40ca001000506100365030740c80038000700d0030040d00d0034001c44010405c650104040b80c4001300b01203803680450b40e200714803001d25204940050041d019045010b0501d00c00540d00000b080f038030480214030300704030b0b450034031641c60b4084003607031214012140c003504a03100304085000030f032107035126661280008010350a00c3e054405241d01d44600c1c0d4000c10001a8003850911982c0b604020380c660280d29030028a24040c11039000c111200418890480803e018603282e207040a440c815031000001d455000f00024503190800401802a140c1d508022842c0c0401060350f03c1c03070a0040340007902c2d444c2c88512030505000c00e019051003040c2e243c00c00400c0303038180c00b00000c3c00a00081440c00c405080250311a400c0d07083c009a0300140380d008c441407620 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 75490964 1250 75489714 75489719
    0x13150e011a010e060d0f02030c0703020d0203071104050a0e01090602130e091513330b03060609090111040f050901050105031504110c1c031a01081602031905030718 72
    0x384107443c4500708a080d00e0850b160440011182c0140140c200143c03070050022041009a4510300013424010b800307582260303280340340000d003a41c80b482040d1340508994401c0c90788107000e0829400c860b4000303964160006840c010800410700311001c00c40220b41081d00024481c03074800b04180c0b100c0250081018040d1503081003510265580803600340e05100442807070000340c511840b002034040c200d400c84100407060038010200c018007400487d08a400c4894920012024010342c4204d4000e901c014000b04200c0d241c079003c0002118004043c0c800b550340341e00804030b10704101400382004008454082d4142e5040500308202180141c0119041080034401c00c10107040f003038124005030314143d0340015000014142904240b0a0010701388203803207030005250f5864280144554811050ba03000c0003803c202804510350926940b0b001b5001500724004504260075402d001c0411007414011280b41401a400c150200600503416501048000c002c012201d9009500c0420101045c0b081400303160 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 75492214 1250 75490964 75490967
    0x3060105151206010e060403050102070309091109010c0c050a0b0c010b0306061008041b0e0a0c0207050f01080606040f0303020f0606040612030804050703080d06030507090203010308040e13150e011a01 88
    0x401c0e102404000b00c5070007040c00c0d64014480001d114002404d542d555035142d0810601030f604c002412400180c08000001e0504898418241900e99400c4504c0c504008100111860f1142280035a55000062000600c0e40c3d10800341030002c0c00c0003030750191650015000c290031120000a558020b400210420000d95280403080c5820105420201c46a40326410120030840035a07c0300003950780e148002040c44409034000504ca4484800144140760150000300e80b148a20b02c107141c0c104d40d0520910b0040c0d07001d81d9445911001c05400705050503503a19100d103c2c910b02e0340c41540943c01c04054200101c10034001190b028801b07403814005c10780380c070904201c1ca01c2100c2002d0204800314001c01c0c10410f09100000046070804601504c800550803000700421151008072014420308000280390003840c003e603412280c01042c3c10b420f06140440014140f0b0b0b0040c201041003003100129000a0b1840842210b44854090f0014001110b23145c2d090840740017a2100500f079400d07441251140e0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 75493464 1250 75492214 75492217
    0x7030506150604051e09040c030b1b0307031802040f091205031b0307051b0d0e042007020a090504080310050d0f1211061302010f090e1b16060b0306010515 68
    0x1120290744048400d4072680741c4205005d401034000d6031040d01c01041c0000e01c44030350645404d5074040c09903c90607444030b141d04181c0540750305000300e81d80002e0001500c100d000790b0004d4164000c03804a03400c0058164002022502c4800c400440d00b079603562400280440e094811035030b003c950600f0341c55070070480b00e039254401010080003035000700000012072240c1b0400a83d001c0b440c507000e4151021000200c026280c0d10400a114002044007650b0300345840c00e8000e8510303d00c186860745114010708031039611280d1060f03a05903000010340500241140303551156a20030307401124203039200e040900000c40c408070b0b0b6030b1125105107000e00e500c902084142c0e0300415211b40c030051a030007010009105450054810701912500d001e10303005c024010380c0452038400384600c00d0b6240f00d58685040c8056520100501031055500a000c3c00159907203010300c207514800e98084022800d0400c001d40c0900d0b82c0311480c908458280d106c850388141d03402c080203018050300c2d044803601012540b0400b446480e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 75494714 1250 75493464 75493469
    0x1201240c020603040606031401050702100b0a15020c06070323070b060d1e050a02190303021e011514030d02070501020a02041d0109081b010c09030f03020f010501060207030506150604 80
    0x207640e000004c542004000d03889070008540c400c3c1351072943c0c0c205081c0c1c2d900814040340d03d180903004035044000175503103a1280243c4030342d000740900441414604d1210030701d0071110001d421b51050781481c903c690303a681c3c00340a0303c0d4400e596200300c205c50300c0e40d4504109640d04602c41c80c4401400403000003000c6202241e0300007415140280040100e0500f00c0489824a08040d19030410403440303c14050082811541070303000b91104490700c0c0e0b100455050320341c41c1d844050f00503007242d0042c0f09400c11802c44500b608c0410400401e03020005181011010141c0d0300c020b641d00002c0580402c01e040604c140b0703d60000500282c40c03004d19000010b521016403207c001c0c0b00300e64644018a60202c1d440d0481108900d481c0200103d160724980703060943e03c403046201d001450300171880820392050007054601c120710754070941c0e414610754829005100b6440d045055000d86c1c1c494010389042440b4890003403c50740e0003410503e00e5814050b09011010b0300314013240b2004807480e82d80d40c0392107088504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 75495964 1250 75494714 75494719
    0xa0c06021815070203060618130501020903031204030e040603030f030c0519030603030809120f0c01090b040c090e010e0c0f1c060515010e010206061002070b1201240c02 74
    0xd94904003602210690110001e01d54000204078460b0400a88800a032400350b02c02c3d003c41c0c0a5490748403c000644c5810f110244401c004032001031400050074807001c0c1041e224000150910355035500082c216000455150f041103011070401050560146158180710300603641049401e0541e2401440240c4020f0602c00303140c1c94401341d04101c2e100314100c841810440700d1021030b5a81014004000d4280b81c4000d074001442000400c005910225135440c0c1980754421551a01032440480e00c0309421034084030406541e01c080c00004200f03000304503846203215419144410b400e01d10003034103c4a1081510103a60300d000c445c42c209100000d840c445402c0c0c1190710b11403c9007030700c0008440322818034800001200d42c0d51020104520303600a00e0081406400c1c1409644080004445003001b070101140140c0c05180400d01c039003401ca03103c900700490341c81030750f8040f5141c0c400602c450380080c00010340503201c030f80100f01c0f201440c52240e082001c4410f0007840d4009454004240080f105000791 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 75497214 1250 75495964 75495967
    0x2030606040b0a08071508090f030405040f0b040e0601060813023f0f07052209020301020f04350706140412060902030c0108010f090b03010f020c03040f0b0a0c0602 72
    0x240b42d5a084041402408560202c48074140c490b0b10840b07240300c0d01c41c1c241c1d002c940000003084032801c0c0030511745040400200250b00342481c0c1010003003d400280049068207903603c8802205072918020680c54003c90300060800354500300c802040b8a000401d4003800c84030302050140142d070386c0218030411403484c201400701401c4406080b03814a4080391051012140440d0012810030041001c98903411a44103907820540d8500c10300054036408201985400d04c079801c0c02c140d80d006644501880d500140c001801c0003001d070400781240c1d119421240c455070300144a1000f1400c040300f41491120443c03203000001805a901030307924980745c01100240a410402d14508842d48030076070303001f40941c08a0500c0c0c0036140c18030350010024003c00b0b034001d005090059140e54001c201680c101c4541490488450385080700784001040102ca1a82d899502c40146540ba20907030b001070720803a0001c0e00615a1140741900004d0040305a600070021507400780844103150350405040502e0a40081025 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 75498464 1250 75497214 75497231
    0x110405040b0f09070c05070506041a030405011506051c020c070e0a0f06140102150106021207030504090c050306030706111c11061801060b03010302061b190609020108060d0203060604 80
    0xd0303040ba2400c0c55160407031000002c0144555124201e25206800781041c0e501e02034030b400503c82248218091034420200f4000184040d0140900031036106006200000b045984031580061000f1254404c0e4001103011480c0344006005035480803141012600842c0740074507414649460f41d01c580304408031040d008001640c5014a40c001d09184d840c0c4840802245860380399160800c44a900c0f49401440380b24020505c007501c03e0b2aa5050303c00c43c0d001030995094030190010281d0260704200e003044002c3c000002c1801c4180180c2810310015202ca039164540035091600d440700560104040041580315460841130200e50b030080501602c1c4080c1e01140d440405454028030030b08140f000340304c2c14080144800400c103440d0054103191000703002e0036a48001400c035a0100f804080e40c88803042103400340c15128841a100355080d0b0100361031030f500f600c04903c14010f2101c0400d6580b203881d1070019003103690084500c1e40c480001ca50140c40b0400d01c1c1c022980e1400c00a0100d40a25500d2505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 75499714 1250 75498464 75498469
    0x180e07090c11061003060b0d0201080c0c01090b01120201110607090509040809120105090105070201061a030711060106020d020105060904030c0609020a0504020f1801020c01050a05090607080703020a030909110405040b 95
    0x211503140742550211201d6090280300c02011313510600c01611020b14244800b140c5140c166031440d81035030141c2d1900340701e4807180e01920310341c0d20510510206669480c03c1c040040da2004030340d4000d00440198000740c104900015148480000da1502d040d0840d10801840d540c0140420040d5002900c0110725070307a582c0362901c2e080c801c9210003a4400481d05035803020b03d030150400c81c0700c1c508202c0244000d40b00c1c88810382c00c0c0e9403540210b0841490b002511810003209a0103158482c0803454035428407401d009410b07042c01d2081e08881c0043e04240002d1003481e809010350b50b0401015140d904240ca82a1401000500381403001003005803599003000035541d8010031340300039100003401150703a01184c00b01c40314158050521a80c10303510900303101203d50300118941d00c8205040e1511450107441071002c5405a10085046601007002c0c850b05001c10741440107040c0d0302c1c0c8a50010180c2d0307001030a024210706070315400000c0c000d040040c12403000380c4000c15038003243c10a0784c0100d20031440303400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 75500964 1250 75499714 75499727
    0x90c120f04080d060b0901110304050f01110c04180c150507020d1a0703020414060304021c0609080406030609050907051c0f0b090705010f0206070905010f18060504180e07090c 77
    0x4483d808107080c1080820708845100060020304000d80b100130700e00d014846c00e0341e01c0e4001c83c818507601104143c41512254001c00d6403031226182281607c0c0011550700004040b903040d8414207183d014190907120401c64041300d00800740192000a00010040081c010450703c51080024019403440244404010600307900229410452424039454542440700070001e400a10990300024041d00c01300c1d82e2400d1560481c4c0c041c540141c04400150740004c0030487c01d914014088548a80e03800c0d40001040040d809480505015980841c031507103402122400e8032000341c81409290004c0750100290358444001c1031070510302c4442c1c040c04849d90300300000300d48910720010b402c404040c2c0c05c01800c90004607543c400d95a00340c0320b5528940200700200d035204400c0f2550400310390300c120288001e601941d442d44400403145814044141128107241d00d02c3d91607404940842e0001c20f040c400000d19100c418000c0c03038212401c01c411050401c055948400d030380302e0264165618011107060521a80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 75502214 1250 75500964 75500977
    0xe12010606021605010c08070609080c010204060201050609070e0f09151e010807080103031706130219080603031201031106040b12040501060e0402090a0f150602060402090c120f0408 80
    0x14020005260344950107512000520f500f0484669051000300b0250b005032102810039030011012810500550b60b00c0c0011b01d8024000d48a0348828048c401203541c0134001000541038550020696050440900450510244c000d07804e100444c0300c40551030320b4420410220580460b0b0400f8641c55039076148029101800f100c0ba007103031807a6504848214603070130b109044030003a80d401515642d6214125000c80c001c0c00020002518000c40040c200d403480e0441d030f001700004000c01401c403c0361b0480c00c12644410300300102420f0380000c4100c440d1b04031160302d50140303080e005075160400104090302c0003041404010101c298200030452a81c4403030b01070f40c015200140000fa61070140c40da50035a1392030220b800700c13072560900b07001040c0802d01660280c09598040c20f4103205850b054840c3c1d011b0102d00755540d00495070313035030341c90203005808007501c0040c003158001d8000c034201030050010020b0010a4802805001c00c000d0f65003042040400340d022100400443c6503840c0c91070804000d20441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 75503464 1250 75502214 75502249
    0x10603020108015105070b07080108071502100501060c0203010e0309030c060c010905030c1005162c04020f0a02010e1603020d0503160606050f04060f060c060b040c0804050d030b100e 80
    0x321300d0950001d401000501541e4090317603205400fa605c221007101c01100c240203a00c005d070002c042c108154140f209000f800e00070223005845080d04000b00c000100c560980c092000504800f10840641c203080c801e04035120400009580740100e4040841d5a605682c4401030041754001040791800b20300f9806a103185600905403507413402081211f60303880c070107040080c220503d40300103e1226a511074204a10b0320041c0c88141400186100c07609990314001d0380304413681d94080c4100781d145c0e10ac3c4001e024500c200e030161074640e000540000d003100c80c0c030300b11040c042c1e00c440f907401c4225541194840c101c942c1160301d80072000c02c2d40351080c15405201c43c40c44900303109202c0d80e802c2000355081501526415107044954082d1901000700340e0b091840340041620720004c4c00d0240d035100350b806181080c0076010208401d00d0360b002040c112040302c0d0610002444c2d10051008011060100c500b00d0261844c0a01c603c1c800480001c030039020085072581402800c0c54500350319180c20045680f400c011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 75504714 1250 75503464 75503609
    0x10c0c0905041b0602060105010e010809030c0a12110a0b010b160b0a0c08090303040209010e18030d020d11040b16060902100309050c060f040905090f070801060302010801 75
    0x2442c203c03403040b80c0303180c0080341c8054502c80400d9091002a03200e0407180305a44070520060703200010b580100003d0070306805030004100e401c800a0080100c00c2200c0d126055201ca039070b400c1d0324024081458021f41c282190894907000000ca10b40d041c0c414195005442e80d10759550212030340d1040c8280100004100d2469441040601740d0780364806140c0010326192116191394080c8840d489120030ac60013584003103a4030052041c4294143d01d1070703205000360750b01c8101c0086d240242d4615048213400c21038158000450107440355140c041d0038a000c1c07009040070b00b41411f0200c4055240901003401c0d4038100700138800702c03c1c0000c1ea0460070040e40c0107881c0307806440c0d8800004024102045042d101c0703101c4d0341800c0c44c050074500200c911080e954001c450809041c111000064280a00202c7c0c040c80b4031620710000d00c00600008008009101c00040c84030b26520002d0141c0034140d00ca584616088003443c505e02d02100740c1e01c101081445100e2580440c079200f04281c066011780d003c40120354 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 75505964 1250 75504714 75504721
    0x9040603021801050306010b1c050702010e151005010906050a0302030702280204051627090e0601091803090e1801020a0302090102100506010c080307030e06160e0102070305030306010c0c0905 84
    0x6822160703505031813042e8246c80c80e030380c3c0b58241c0814600c100400507101c40c140708a04a40030403075034440354122510307100106800071070b10a43c2d481c040d4032010352074503803994100703100c0e8440c070107090500140000e080200d02127280200140042c09108800014035400100240c0500d01c00d0010803603103e13060803030402c0108508506940c0c003003801c83c22030059141c00080381003141495945134180c0d110342c0e183d0708220410f036045019040e540781d030024030007800c000103c0c042410380600b40c0c0b2142c00100900b415850210385000791401d90302d81e070210060140030800429444110030040e50781054280343d0a0700c3d60326501d1b500c400c070b54001129a510100c0d486001c07541c917800a1040c0c0409a0803105082d0100b6880b40486105a0741240171482c0d000c403041c0000c00301c1014513840f48050800080c00079a1011560500301e0883d00d02c8001304000d2100c98180e5042683d01075800000c0c401040e0450559440d19030700c1c80302404140c1400507000044041001007989403001c0c1003034040c107008505 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 75507214 1250 75505964 75505999
    0x1515050f0c0a2415150201061d06090f04020d0303021c06080105070207140906010305071103031005151206190302040222120507030209101203080708070e0303040302060904060302 79
    0x10300000c494040c400c0071801c285060792080c020340365107154007402241c1303051500320000c0844a04546040655480f1000014046000022507203504c03074030300078020140340490070001442c80040c2143c4100e40d47c1d0082c4030240e2265a0508155a814107006030f480341240c1c0d5144141000b0510305040c90305055010500001c190081d60107240d0f15022a01d009807900c80421000190101c1d040c0c100c118440028144d42c8681c20040d0000494203142018215034100302c4d04550044503040000c4e0420a8200940d0900e01c20144040000712040c40c20401800364894a0450140c4414451b6000310303101f044081e00c0c0c0040c10011030b0b000700119650340701604000310180f003403282d46005035002034000400c0c001c02d404d0110042c1e4071201502000f402c1d90300b042980c1e5000b501c1003180400c0032070041107600209030040360050003900c50030311600e001100246900c1c1c1c01440202000108401c06905440000c01c1d42c0989078100c40903a11071007540013180081c81598030103540442c1061468002c41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 75508464 1250 75507214 75507233
    0x30403030903140c0c061e0301150207060804020f10051b070519030519081306020f010b0a120b090307080f27090619031211011515050f0c0a 62
    0x5034840e448a02c0d6160300403d01d031005015002e644005070b000451404410300c2e04c2c60040201490003030560884c1601d60b40c000c0303400c0e00700b60080035482096040d00d202e0660100505001000d003854048404c0c07600c4e501007002221b070508098024820490980d01d00b501442c00c0e2041040c041c200c1071080c41404500d40d42d0f40c0480e1195a0207000440b0000241c0000064900c068039000f000400001c680c00c03040781d000700d1541c00103541c1110b06014164034011171002d60b00017401245c3c010000c00c9841d0f48150b0031103191601c081d2080c21f540104109010300160000c900541000c040032a0340d6a5200300d500350311650034002c01060001812a60540101c0701600c184041c0f801c603448450007100d10303250711108007020079901076020800241c0da49004e204031040340c00181c61004100350703255140161591462140c001060b66811034207104882482000b0b012711544002500c0a81303409c1c0305090340e0840b500b114003003003000565003004040902c101c80e0507088010840b04c0707178001c604080941 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 75509714 1250 75508464 75508481
    0x3130204151d01030309061b020406060314060d0203100e01020c0106060903050f0609070e0414060708011d0c0909060a1d0703060602010b030d12090c090203040b060603010b1213020603040303 84
    0x5000903a08201c5014540c007a45506a07503140d00c480742c00a00b0540c1c03c1d10300c11140d041000320040023055200042c0c03958080d402c0207040c1078601040f600304030401a0080c4400408031409a203110080402680d000038007660403208140f00019405d00f00d00c0e045001e8458404d10304640d40c00c0c24000205d00c1d40c0311142004680c083c0c4199151901401965902c918068400c400194444581809120460507403103810611038083c514200c0002003981d821300d1422901031001c900c1040c0104041010202a82c00d201541110964203240130084200b29024a081c0c00e030080c2070710000500c1d15110707201c10801500311014000c1c2c0c80a100f21000324640c4e0120b55010000b802c1040000d0482c0c014003443c4400c6400a0280c01c1c90100b4000441d141c2d0308234502010743d1512011100c0c08200040c0122005d8240054096564503003810100340c86840945450b00501c000c10042200e1545407055881858001d034091000343c80300407805054202d1080043e50007080003040c00304244d0141e001900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 75510964 1250 75509714 75509729
    0xe04052409070e06010e0d0606080f0a03021917070b0703140114010c150f0207021503040b010623040b0a17010b0706090c08030403150f090f02060313020415 69
    0x6408029285003a8550300a0301c5040840d840540140241c4039a10303412a4852010701d003003020792582e07100090441380504410749409a9400b0240b0442c030040c4440d16281082d08002c0620300b031295402599181001d00402c000c1c1c481d4210201000b800c40d4407408041e0300c80503038a8881c1614189240390080a88200780442d140000500440043c81d210b42d048540c0b0300b02142c00c03c0b02c07a01c01034a0a500c8040102c4647e03004141c400d50045151250300101c0a2281006031190341e1032042c45184074800d20f501c0341d0002c041c4200400540710a0010781902ca992501c1504e078104440a580403880b0480081480b140204000c100159403038040c080c016440e03680c0300782c0400c140c1c40307101c000705080c0180f0322074820800240020070604d4000b081e010380314418214801d030703a808111342160440d0f001140c029405501c811b503034025602914402d880a00310400c91545a9039882c0443c4da000e0350024090340b000301c00602c08511004485404540203803050041400a90b070000b40303001540203201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 75512214 1250 75510964 75511003
    0x2d03120207050108040b0a0c0e0a0602210309030421080316080a091104090f05010501080c010914011d06120c19020304030b04030c1403070803040b0906060a0b090102070e0405 77
    0x1803551300c101c00250186030400803060b090385614442134042d110084410060040f00710483c540e503114902c01078020185a4040d18091030010003205152543c000f25410041040c41403242140000c001c803411038105a40840311040301031030790540001c81c9500a0081003020082040440c00c4880e4003038040da02e551250816034030595060202d40c0495800760107800324949000c0035051075805544102d001c2d8140c555598800ea603000d00703640c0c00360801441600032030803ca0855810941c2c0c0c001a20680c103010684141d005e000a02080031484600007000d0341410700c030318980f224421036551a02843c40e0b0580f5240141c992400b6a211092554400806507001e01d03080344040103542c03d40e0751004410746a900c441e1070803a07400300703143c50030380d600d0300d02d4000340c0c000820400047c003610340725408254a83c0780904040327035600c20040c0008881d030801000c100042d95230380020025102c040002030344603100003004030b02c0d26480b600400c00b04000d4409100078000006130290f01d071843d424401703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 75513464 1250 75512214 75512219
    0x307030b0612040204021b010501180516020606010e0a030602030703060302030f0a0309050f04020f070b070f0c02060319061802090a0609030c0311040207060f021b030c03042d03120207 81
    0x1200d100701540210641c5070400070900620341350300101f0282c000190900c518095a8031550b0850b202a8800b0414140c0d00c420080d0000e01802042da000380007405104c5c01451034030007e0340780c03c0c00404080c100200b540f014440c60f0744040d14540070b035820007011500c034902503d0140046c42203000503071091080500803e0500800203041007400da00da51490086440c09091101c65000d118004d540f0980a003d140703031082c080d1003d40380c49401180030444c00d092060b80034005494428550040240307041c204409038480e4400c482d00100403023036a000c2040680042c000800094101d00c008028080e078980341112150007074907416404440d0b204d07003aaa94103090f00c455841e8400102040071040c010000b04942200e8a44d44e41e0018002601d00b40f116901e0700210751700209030494444d400300d00201280b501204100609400c000190f19190031004040e41c0c0f4000c0f4032030101810041c52891464a800d4001041042c0103480340300415516440d0458a601103442c000d0014800c51000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 75514714 1250 75513464 75513469
    0x90b010803030c0f03060a05030d0f0e0406050913022b03090e090a0212030c160905091b062203030503070f050406090302090408070209010902130905040c06030e1c050307030b 77
    0x3160b0080465400843c40d0401c012803004481d0001806c00354000b000d100d0004035514240010703041d10030b06070f640030381440c8004005003040f90900c102c1d5024914200c002d00c1603845603480c154015504111010f1ba13407445200254198003d0350002c1c401010700c403a0704081040e114407240307100c0d100342c4400c4246074071100007080200040381e1448507588015616000740c2420b4181c80f403440281da00340d81c90200021512454400c8184003403203004243e002c104203445103446003a810071000c5000d40340b0329042001c4c100424092400e858071071a000074220780506400c61220741d114413a416002c84036550303804c021b800c64000300d54000c08621b2071466004024401e904442c180c0d455a1106030f5440d0440d024425020740041080b2880e5400308a600050303a560f18586008068034080544d4075200410351381030000c080d034050354502d820030052100099100d86d054068800b2071800140ac4601026260f142000003000810280c210254081d856036001c0019846440f0707544062100c0d002d544203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 75515964 1250 75514714 75514717
    0xf180a260c120304170a120c0215011a040918020301180312020307030204091805010f020a2003040308070501060e150d030e0102010209030d0206011508090a0b070c080706090b010803 80
    0x71444410b030850500ca40000d0101e001a54001e40900076440f10300034001072081490b0b00015019011460386448503d800c1e600317004900d0501c001c0d2010b8540340b68130807184041560180201c0c40741d036003a00c0c1c00c011454185425907008040b284004e20021110b1002d036205004092420303400795090540300394001c5900c03a4120110355150b615108482007640508009401c06444031003096000c020001d00c140079030241040700350200d070103d80e040d070213803400500b160200d44414580d980140100d010340c50304000300c20000761081c10001503101514091500310720503504014401c0c00c020400c54180001540064180c80d201d00301e03100180c9800250310020074041440b19880a00329144400207407080c07030a1218031606000141c284080701000a0038804409944801a4040d40c0100485000741c605409025501d044c0013501e82002c0b00d01a899403507400c030140000015001140b0143d200e001c0390f4280e00d40000400751242c140c0c1c581003002e050002d90541d21180040300100300c4950110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 75517214 1250 75515964 75515977
    0x204110a0e0f0612011e030212060a05090610030204090c0305011503050c061e07022e1202040b0702090c0403060204030804030b060f0609010c080702040c020c0901060c05060f180a26 80
    0x440208445e80f0740003001c46c0f03451040345c5c1c1c050040030260002006844505960100038069006866145040d805290841d90020121390256200c0804d00c403003035000d03070783c0d84081d00d40540e03001c00c40e01414148007405860641c0003c202d50310340503501003000b49040282054922032815141d804d06944204207144c0901204840240c00101e565030341182c20301c00405641c6e02c0505950f800f841001c000301c608a1740e6607032400700300e1300c20b06540340519400030a10b000d1091543d01182454101400c2c0c0102d8014044024001e001d050042002107200f0010b0701c0c011a48000300703550303d075140e2814001941040c4000c81c2c01c2c3c1d110b1000b0130110f02d03001024aa8412002e80f00314100030000c2d0045070300094400b8180c2e1840010020140507071110b00880344585082d0300149041d040c0b01003445450750050340800100f0180c40c0b24500041d002103036030b54001d038005080b403115480d403002c044d03803440074407600c07000500c100a41801081101050120102c0c0410500003400035400720100c140c1c030504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 75518464 1250 75517214 75517237
    0x80906011404090506070f02010b0a0b0316090b1303150513060507030204031b050a060203070b0a0b1507060608100b15180a080115051e0d0204110a0e0f06 68
    0x480060050660103600032801000007040410190b44540360513040c03800070f172580c00c00900344108440c0c14035024022286e00c4802503588800d89031500010290300c3c00060900001500e20301d0100d03100070320480c9040d000c0c0c00d2600f200e0b55159000c0c9115082174203503120844900c269600303442155003440c0708141c405c81009040a0710b462241e9200c10040c034004101c130041c150f00b4000480861040c20068001207603c1d810301c0040da0402d420456034404551091007154400c1200d040041e91800d42960881803010020943c406810006071610b142e99090403408840410410f060249075040342c012502020140e03920301c0c503990b10140990b10701d4024213800000105076802c0100d0300f0001030900c00b003908080490042c1200002d8841600ca80c4043c010b07a44405900c1c00120314030340c0d49001070800300d40030524040803451150500c5120103200380311b0640cac00420425510f6a0300b101208407206000943c0d166079070380c8081d1a540b40552247d000c1c00402c05948040d040850455264000d103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 75519714 1250 75518464 75518473
    0x9070f0b03041b12110103060f09050603100902031e0111030c0703080c0c0c15040b0304080414030604150510050a0f0602010e0706020c1302040f0306020712080601090530030304030f0809 82
    0x1d0340c61701ca030102e034045161810582d4524001500d8000750609002a003a806800701d02d1b4149401014540042d10a603800c1d607500c0c1514260059a0004211484940015803440342d086098420ba0040c0b000180d01d044080001040080c000401703401808200d101340c4660310a600c2e02d8802c50507a005034000c074001980040b048001b503150450341c040e05500c107040030510781621101070700748a40007510100c54140001c00c00340000c000e0080980c0404400780c00400c8c00c0d14190b1510070f03c0401120070250b10560741c2d8040341c4017990006412000d80720243c01041d086a075142c585c2c01c44842031190800651030143d60a0710000040780000481e1926401001034101070400c0041e5021003010084245900308000603080001c216010015405040010386420b024100988a000782c0d03240301041110100c2004416a00650a00c081e1401910303514442080040c10340c220500d640001c030450540328031011242c640020045205511a50700e40001041a260983c0c0000c000d40c0d0f000015000f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 75520964 1250 75519714 75519749
    0xf05090601140111030c0a0501091e0213020d0f09030806040b060f03070509011206090209090a020304020306010611100504120207171b01031103040b060109050d170309070f0b03041b 80
    0x45280d5502024130400282c914180042030310910b0159201c6003110f035651600800d03400d1100780c0c40e40c0c7c2c801d4601d110b002c406600099001412000030000c0310b06070070350b0204203d9541d40980e4081e0104034101034040000764042d060141048800712070399403180e8142180c0000f1030a03d1410703203440340310310991503003141c403140380c2680c485c0c004c18007050421001816541618080703005200042400f80700041e910201a800c0c00942003000b4a070b82c081c03a00410500c00141c800050460440358185403281c110f0304504060b50030100c002c01500007050520301407009200c1403440c403141d040703550780803201401c2d03079103a104101000c2c4e43c82040103504035400640d40e60449000d0a9400e08051400145044a070703003900305143c1098a041e10b00c490769208001c07003942c22902d1100940012a41004a04010303a00c85840c1034800700d50046050000c400300d07029800c100b04189c00707020032030403850b9915190102c01802e80c10464082d10b40700c1c00ea100c1d04201d680030030b000b0419141813454001d40c601c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 75522214 1250 75520964 75520967
    0x6120305030a20030106050705010b040902010c06050601030f090503090405060405090a030e1302041401080703021e091903030206040605150901052e0c0213020a0207050904061506030f050906011401 87
    0x4140f01c050f1600041d0000ca0302c20038039038200214040d200c0c60315115201c0030355050260841d40030043c0340e0b010314a00070f440f4000d40c1c0c200315140040d991281d40403440380d480074012806070411017a621111030170024071404201e80407029109514040d2420009030707841a040105485050300d90b004103402c4002544003080c81000a1201c4050250024070001000341f10742040360700c65482003031142490302e0806425030f44961b515411850070b1400703504044210094843c600000303600007044007400140f11070b103070302d8600040c003902c54640f03034201d0380d00ea83c2d0074040d448402c2180c1c2100c1c01032030200043e2040e80c00156400c1c4515002c2c1075002260708003018002010303100030050780c68a00c00d800c40c03c1030010443c501000808030f0794070400b0709020b502c1808503a070480060190102e005209400642c0c1c0d00003441c50842c0e0048414000070f0700ea81c14408020f101e00c2c4101003454680c4007000c1741c0b464144d00001d18404103d07000b00480d50300e4400075912010300b030194000b006109840c075051036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 75523464 1250 75522214 75522221
    0x605060f1608070b01031a010803180103110403080903060a020414012604060b1008010b030f130b070206041406070915050405090411012307030c0c03020402130906120305030a 77
    0x115001d250541c10200749844020198100c0b00040b81c00c070707a442d001402000080d040c2c1c80700185264441c0d0401d035051000e0551207008400401005055044509085030706ca504a0490b8a08008290303507500c2e242e042c00b450300d0340702911700342c020700c10040841c1ca1083c0300c0c421079040310312501e800c08440510800460314a1740c02c0b01700d5401c28001811074a40302080010b2240924411540080c0301e0350341a0030322001610300c200400503c801d00c8010003020148804072030740211050304910860f511403c1071501c903442c51101a00342c8100d4800c010b0043d400141c9540514010600ca00d14a2008a41d199480e8000c070b815000203140000200711b26528141e1750079074000d0604100b41007a8407040070490a60084409035a0030351068000300c09542c012100107540240c0c45110100c1c41d1a1562417074003842a480010300f0030900100c00001d000034803005601459000b84203566980c0907040103089d0221501464000e6840c02c04001004080b690600c500e051381629201e04554401c4070682c000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 75524714 1250 75523464 75523477
    0xe030708091e120f0d0c02090105090601020a0506010806150609010e0d060209040f0906112119050702030d0e0d02100515060c1c020a02150d06090507020304080609010605060f 77
    0x3030800368140d0750a503a50080800f12101d050002000303886801040145401400c0d04100107000c149140000503881d10743d140350558a0035203580b09591a00c1c00101e1503c0201d190260090199a00114407090b020990a02641c0c03018000702039401c2040400000703105a80d40c00b80880c0102042c1c5286040031342e0303080440340c0070714401400c00b014040030600796500d00403160b682c10b40d40c034004e00070041e00e4445c10b880020441d58403810000f80c8014601c10021000801c030b260011100000c142880c054001f059140c07240f4001e200c0d5003410800070759aa00250000d110031411b0451200c04c0c001c0000d0041c0c1610740a80c018180000d0603c4400010140035103000010441c3c50f44e00c0c0c0441d01c03514018005030f02040004d00490b880c0000760540100b122010a046401c980e40f140050380c3c90f220304082c0c40c0324140e520b669a40c0400e103200d00510352039018000c80da04120070413014940100c0540102d840400959150745c0d64000702ca400ca0b0010302900740e00c03c030706000b900c13510340038003002d86030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 75525964 1250 75524714 75524749
    0x8031b160e1504110c070e1003020a0b0c0c1003050f09060702190201110114010e09010212060f01030e0a080a020d081311060708030114041a1e01230c010e03070809 72
    0x2c2c00e00704c1c5075040741254020400c5240680c4540403c1000941c00302c1c0c40c0d540040d1000711100084c0c25a800520070303491520404200b0740000c00c854800c00c00500c01c08100c690000c000c9081a503c054002e0060a012551103246601c5200000e09210000c14818400c2e0070f19405012511039406a4043c4009007544c10b90400c0504c0c1e01c2c1c854445000d02c603482e101044070300303090020340c07400c803000359404e000814400c19a401409200c0400701c1c00340704a031300301c64211104008d00d424440100e00401c0b003220321031210300c9148003560501c2070010050100c40c001d50b003a5241c20034820402d42d86100e003a01d00307845a0752007480c05030121361a0301001021070801480146401100d88402c19590000e800c125569042548520840d2400740701d8803001030039160031820f46860f590002130200315403000030759049607041783c0009941c2c0325807512841202024072005200da10307001d119200b50044144c60700250319002c3d180b144620008245d0360001d43c02150245030070386200611002056a68000e407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 75527214 1250 75525964 75525971
    0xf02030f1206120706050702041107020613090b01050c0a080309010617010f060e01030506070c0c0506040e04060b040b0307090207030e090405010f061401121508031b160e1504 77
    0x21110103200c01080010980e490038800e6040c50802c020002100c2c192504a607403200000304201034110381a155a82d804540008607144103149040c1503114a1344000e50269001801400c80c0f5050b11140050f208c00c4041000303042a400010b4541c1d00c10750a00c0c1c02c01d6884030000600041e51100150350149a0500109960390303100e809245011104090407210b945844203001004203a100b00030040071665440b03400385d407540d01c030503895a5018040c0c000f000030b042e50080501583e019144010310002d007085664590710030390001c00075404d5508450280c10b2916140c91132800c3d00492540040007805840d0091805074035100130750107860b0841c05c0c018025503040c003565030200070b5403080307004400110b00c0003030070b041e2201294101e82103070041407014000101103982c060b0400400c2070030900001025142d2210814004041c2e034481403240c800029404c24840901c680390703416100c40c0c000c51b120003280d80c00550a0980c240201c0d1002910440042c0d00c503c80c0d0b07240c04047d48000341000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 75528464 1250 75527214 75527227
    0xe0f060f070503040f0617071205040203010b0a090b120a051e010b0913032d03150f12050d0c1703040228060f11120f0d020c0109020f01050a0f0f0203 66
    0x2420344c0c03c1a48100d2080c40d18007010800c4c2d581040100328011207a18143e12589040785000c0d05210380782600100304c81d42da60000d400c6440960001c1802040100ba1084955581540c4000761480f00031040c010450014800010140011010006a40600501018900302403c4a05040300c002840419034a4210b22809611041c02c51401111b0855064107800c0b250706000d000d8a049503805160031540468440c4480320420045e61050050f150200c0d1901c07503007400d15172911194011030542640325400042d0701549817160440707d8882c0064a0345900403060550308000c01600c041c00000302d07442c5162000c0c00081c0250b500c203100500032030f04040c000d01140100da200040410a10902e0103050003495000340405e988040070f0324091100e940010f50290300e411240da85000480c1000c42d603241d0703000300b007029035400c1d04013aa01151940704510615020303003003114042e80245401c00204c155544200100c91a1002585488140c201e4000c0f04641004115151074118081030045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 75529714 1250 75528464 75528473
    0xd03020715050c07060e03211b030c0304020a0506030c07030c0602040e09010e0c0d0203100f02041211010f03020306090609090c0d110a050a2403020412060e07060e0f060f07 76
    0x24035000d031885030800c58540c101490300004a44a44006808540c018000e00307401d000814159060000e40e2908c4034215113910004240c00303035802801d400096004002c118080302076130065842980211400b25a04e6514010b000c074904c015103047c43c550b502008010082402411503994240c0704590041c90640d072610b40c1602c60f4070030b403201e880302d9440e03c1c010030540f4810860b440310410b0032a41c0707481c41c14013a0300080c1d170381e4220000c1c1c6066640f0f0f003001048440300c0c1e0b4152001054071882b1000301c040941307018885009002d210502051203000c01140441c8640700740d9100d0000a00381d01451b840e044108180b03020028000c01d19031003048994000c903142d8520903204039200e100382051a10410b01080701022060704494010450400201b08a000011f242418940074202c0902d10402c00c4a045003c0c1c840d580080d0342c0794815084d55001c03c08a680326510010a00d004c5c0e43c0c41c5511107400b11903111700300180c180d21000301c10307080b28640b038864001c01c0304002e980e500030f141c00540da0f503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 75530964 1250 75529714 75529721
    0x207090e1c030515040606050909060d1a07110d2a0519051507050f030703140709151404140102160e0f0702010203071d060d1d07050102010605030d03020715 69
    0x1c01600082d212014080485428940001c0c0000101c074140300250804000801d83d002d2a040203101c0d41c6001c0c0803070b40c20745034441e00c0c0c12850340141e0560746583c01d04400b074003080825200540010010501c020300c0c1c200101d41154605640d40d0350900c0201c1516450b061f0b110b590034500003812150144074000354041243c4940d01a0072034a071214030480d820700600f0400c541524001790b0384a4820011120342c4981110180b207441402c1c5034032505c40100031070090040d9044031a00342c4101c014000015042003000086a9a40008000000620030120f07488903a440354844000c10a010a100344040000380c82c29010040c0f0459144020200c4401290842039100916950101c001e0180c140c007010807980e071060a50000350b00e076050000d4000c0c0504140c41c00d075401440101203807000d6a9600003143c42c10780e068441817042138100c502d00800f01c0c0b08040000058030640c04006205c1d401030040e1070032a0f0f002800381c0343c001003000094010354820b10b0100c40c8440311407800c1048030318621 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 75532214 1250 75530964 75531013
    0xf13020402121006030b09060f01200712120e01020703020915060304060209010305070516080703030b03010e010c0318021806040617010504050706080c0306100509041a100903030207090e 82
    0x118188085071602c180981283c2c0403405450047d41007104100c4107807200311903210f0640003881c0580c640102c0c400c1002c0f03020394242c003030102e41c01010000103401e0052030f00750003040d0060341004c000306404e42080d24207110785ca004a015030004c000820251414240d01688040c2600703008203180c0b00c580024102da4011039003110610340c00301d500305503541e1510600303a101031141842403520246080d10340150184200041c000310f40022298109486a0001703034546101600a10042440841b0280a0310a600801c00040d2502c81c80e1403030b00e5800341030840c681e500034100b45450940601013100190004141940050b00c50714005924180320f50350350000145d200002031203007823501e015820414254403030401c01204a040c0301944000008076a008082103c80519010001000b43e80c540601042217600600d0400321811000031700b100c4040003c030031203c40c4444403d600040d1a04099400080c0060784007074014850851140d204103030207805601110040e6007504050b1013801d0784c90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 75533464 1250 75532214 75532231
    0x4050a030b0a1b0210020c12030c0c010f0c121d0a0b040c0801020301030c05010e0a03080301091a04020f0a1103040810020d050a29191205150f1302040212 68
    0x1c1041100b09240c4540399141c0034100c0381000d20061142d00030364500601c525024039940c00170390010051000c1200c1d0304c00c0900300f20307000d407030b441c0c009095281500210501c113901e5082103505036000c891403054209a80b41d6440380b014240000a40c00002c040200340c440340240c260300100d540c1c84040103c1d00019214518061049c60716180c001d00c110034030750064205030b006000502c002080241c060003075400030300e05501d01c4201200054200041c07584042c2200d50000000b1889540a800c041030501100008400600c52402840100d01c00e44032041000d010902588151034443d080075450000d499044a00f000d46862034103040120051301d0015455000403502005903440c01001e900010041c010000c9021071407100c8200610252400280000c103900282c46a440b012100d100e0800c16100502c001e854a0b40c20281452400c0c0981d01c83c824a40a800140031615000d071280b5514414240c442c0c40c0c2da908201c0c0c5049e07000089901580a0007900000784018414a1098200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 75534714 1250 75533464 75533483
    0x9060f0c051009082208030904020c010b0405040507060f05040e0a0203090f0f030304020901140123040b040b030103020420040b0304210f0f0c0308060d0204062102010816080a05070504050a03 84
    0x1d001c2160741102d500c080c0d031642007605c10821403641c1c0072040d909844415100076035540450b00f411401400d02c042d05981c020b24103404d000c10b101c030000d2000251480e42c0c0391354451540c180000e46040c000c9100300200700104400048030000780d5000341d50042512821100700e1851000c0c80c85c1490031a50304441c55601c0481004150314090f0103e90050034111000101200030ba00000d12040c1c000e10b2351580d0b80c41d411708544100c45c0901c2100c0003401401e000701d440707a4858101c000d05520a210583c8100c2c02c0102c42c5100c0f242640381c0503440b003032103454180b0341072600d600c2c9085600020425602450402840002c01b000805c3c1d240030103000c2d907034160003800d4848005c2c01d0078002907140020404611030180000ea04240a260442c00848034a0071500300340c400a0007503c245d800c03d00402c030705592401e12151445400702c2d2464800d0f00e030070703003256102d1460802041c4d40080500000b2880000309404401c6176100d5a00888149845881c0c01d4403900400c00c07880c955441201c030f400c90b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 75535964 1250 75534714 75534727
    0xa2c0f030f130509010b070b07020c0a03050115270507090902040b07050633061303080a020f0d080402060304062904180201090303080a0e0714030d09060f0c05100908 73
    0x16100800b0300a0b00782202c0e401480d5052600340d013094028600c0080522031050041541c1034020002201940380003001d01c200183c1700e2030013034041d03d040490070984a12510000c5540c00c0c69010350100501300d45986404111031900040207031002510350b40c14049a590045a4942a0700003000a416001042d03940c40780d003850214907000d4000d000140c0d056a155041c01c03161040c09a00341800c040f505582109031040000483d544079503142c14000070401003001042180c2000070b081e11281da6003d07524040c84051405450b01c0701c04030703228002540107000800518020010f980c00501031080000e58900c10425a0301d6860a0f6403c00525600f0510552080ca003501441901044001401812084640c0042d0007481c0ca404003d040c4000304000402d000c000303134040044030782003008440440e0b03039500c0325041181c58038032400d00a010b41e482c0452058010400b5030100d820607030720354a0104844208483e40c22800e00101c4031402620080030b038108040c0541c0c40c40c180102c2009075543c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 75537214 1250 75535964 75535987
    0x207060c120c05270402070c0f0b0909071b0f050c030d0c051002031305060103110f090f07050901050405060c03040f0e0712050c042402060a2c0f030f 66
    0x80d041d00450464202070140310030035448400d8402e000f9000c104460711900c041070352994611480c2249400a10108403181030004c1408580c00b01c5034500412240a6266100072103103128045907150040c1903240400d4005124400100407a101106011081000c0390f54824507010702d00d0054900e0751206680303410915040c0a01140660a030811501d031340d865581e0030380c496191032164051180d0120006110404504a84902d1603004095071519a1070b840c201d2007009101d0b007024081d1700800b805407120b0070f00602d880c3c041d01e00089102000e58600200301c07031a80c001c18006042102c02d2100280d42d4072090043c00c06441604081e41e2181d0400705450798a60480e0302011032000c11100380511140c01114910001028400100c3c03a41e9410ba4080c1c0a481640d0000d140d03c5e13003503451203038800903020340c0c1d42d088000d90b82a6410b81d110f50b4240000d40b4401110491003003003510480e90720030552100000841442d4040d1818510307110384260030354100341d103040582c40002501d52841c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 75538464 1250 75537214 75537227
    0x150306170106300b0c120a0207110d05031e030108010b03071a030c040b070b060f0a060e01111c0c050c04140a1802030d0f12050402010f120605040207060c 68
    0x9185440200882890f200300801900031105505940c4401140e50b4040007001d624402c00303d941000343e010040c1841003042469500c0b000540c2001034404003c60050190b030b000f04c0d402c2c0307a00b18a1070f103040380f102401c1080070038070807104807031510041040a20440d052009080084080781281e510fa61611043c01d082d64960a40c00e403098101000612000e020111a1064000c0d001c494549941c0e8142c0201e5091107290000441e041d408980130040041d00300c3c401b40305036410b0703402d5002c00000342c0601030081410300800c40031494190401055500c00c49540c102c801c02007040712100079601c0100649020451064800181e28603003090a0040070480180c2c0914180d030700304901d0b03046122401c00000c0240816001da80c4461041c2061103901c0c10000f10141c000f020340b05440198000a01000b00000510010546440b42000d1010040c42098032558068440e03104a841d098404c031160b80e0388407012000b40b036403a10302144c3c035241c52000e40003241c40350500040381c090b1450040e009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 75539570 1106 75538464 75538499
    0x903070b1302031204061205190b01020312010609030302240118090b070305010f090204030c06030e1005070801170f07170a061e1b0c0f0c150306 64
    0x12a0b220303c018800c4900315116052008540750104060f40c4d4109c0d0315400c42008a211040f201e003c54000404020051060328a820002d845004002d1001c0e0004400202550024000c00d90104011501009488100303002880241d403152003003941406801d07801c0c025034041e10680e0103103801070032107258460241c0035a4030342a030b0003c0c01000240b2402d0300004c40d40c440012003110300d108036016a6000541e560010341008800d5020b45100650507000d03100c4c0f00c000142220040c030400e4043d60603a5107901065240491000782401c03e00d403030440c02c8d0001088500300401c002001000c481e80072240001e002d00342803e0b0703824064040c074050410b60603d840c440303545075030328144440302d980810108100800390300100c0b0700c2d80e07101d0281008038a480c0c1c0b021010a10340d04895400c0c52203040c8400b080764503207440c2480b03000c0010700c210101f5188c03002440450700b45880d4080 = true := by decide +kernel

theorem cover : BRFrame.Cov 75359714 75539570 := by
  have h0 := BRFrame.cov_init 75359714
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75359714 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 75359714 ≤ n) (h2 : n < 75539570) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
