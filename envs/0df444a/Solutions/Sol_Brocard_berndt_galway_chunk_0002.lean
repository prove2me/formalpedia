-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:17:56.129855+00:00
-- url     : https://prove2.me/submissions/660a667d-3311-4b7f-a589-eb5647a6a27f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 179864 ≤ n < 359720 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 181114 1250 179864 179897
    0x50d0809120309010b040608011505150c060c1206010207030b01090f0b060a0903031803080301030b04030309050d09030b06040507050307030209010309020603010306050f01090c140a020109050a0803010504060602010204080304030201 102
    0xe603441c092441c0c01c1140d42c0d00e000da10a5009240400d00d45215501e0031501143e00da80510508013061082c900c0400340c582040704101c120f40d00400042082001000013881281d030602420b80501c070b4640d2626290ba20348a000310036428006d247c40c2c11903020300d2040000c41c8402d15510304540403600d00240c1c403c80203034603502034640480c1054020400092213013859074000303207140807680240d4804503103c1c0c2c0c50b03020344205a82071102806255080c40103001040c960010790b500207109040014048145270345403400c0a20020507200031070540c10081040c850410030040e440501260104500c3c070b0006d1020301a400003401c50000c0582c04294100164025031001c801a40c0007420a5100d6a49140c14005088100c0340c441d00041d281d07000161165981c00340c09104000350b15078210b80600e40d241c408542d040006e40314110741d2101c0c0c10b100071650610840d1409400b940c4040c0c2c8d80e6041009010980b0003a5003c001107a1040008010055001c000d07241600e9091800503c82c0c40a00c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182364 1250 181114 181123
    0x604030e01110601030c0609090902030c040b0105040905010306020301050f010503060108010608070507060204030506010801110c0c0105070201030605040203090c010e0a0501021902060705060114010909060501050d1d01020703020a050c0301050103050d0809 112
    0x110301010f44030750700002c018425403d07194000c464142da28600030701c0d1200e00360350694441c01c074020f40540c0036180c1112240f5054122880f40003040c034040381031541d25640007041d50400c0c0d2040e46c00542c004014010b5050902c015041d819017070800c01c0c65400c0810000740601414400c0300200100f41703004c40c0046200d68122500d0a401c800d0a540344c1e0b8407030030032548400c028810264036611703026240414100c1070302987e07120220140a0012040a0801504c450b8480c1030202d04250359400c01107843d5955202450143e122a001030007201c01901c0090055411050218070540188008200f140c5e40041c3c040d02040004040c19040c14080c40417841d24082d0071001001401140b001013080303c20b8000c1400300348400d84e07904030f4840e0f40c0c582030421181540150b030300081040194410100c071036000800c907506111004128001321400b0300e130032070704400c00440040c2c00c007840803418014100020300100d44110020410380d499a52040d81c1c501e140003900c003c0c4076002c0d0019060b800d0601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183614 1250 182364 182387
    0xb0c0d0903030203011502060103020105040306050601140403030206060307050105030105030a020616060c08100e010b04060302070c090606020a0201030b03030a0503060904050705030d11010507030b01020601060507020303040906060905030708010207050604030e01 115
    0x80052282a0552802601039002405040f0300c1d0118103a40320186440010161f04894060315854a00f605513100c0002034203000388042d040c800801d404441400c2c0300002000114003c0d40038091a051500c2050f04011036680000c0c1042001d20060102d5034010680e15034640d8111070140c1d8624611501c0a1215869000540902d10300f885441229801c200460b00c211100c084580040b502d41c1d180100b0102c0a005108101a0a220600126000703038000c04d40640903541c400400f41d910823460b01501e4240e081400140c2021210708110b5130140508003101d28110041d60a182c0e910724000d101d400f00030002c9225440030004501030010511821020303110150907103046490700382005d80f80c61030261800b011076184c0710000ea84940b20748221051302c07505a01420b2241d280030001c84e11a081045e044c1c2e4940000c0000061101c003610404005100d56216914030620380b0f000c05050204039400003650340d00401c0000001400402d440d41e00c240d040c14140f20744912100100d8a81d0b604030b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 184864 1250 183614 183637
    0x41205010b0a0803030103170c0a03030504050309090108010209010f030204030f03030b01050708030c04140907020606090603010609050a060501030c020a08030c0304080702040903020c03010605030c01050d02031503070611011802010503040b0c 106
    0xb6008900039034080b0003103058034060b014403c5030010180003c06107100d014030311051904080001c40019100341c0020742c10034011400c0b0303810a41c081d0000f5840c0003081e407214909039030000b0641125608090804522911801c3c1141040e00d50784a0080a4035a003100400b010340e12604004145c0c022000e46000c00d07009030405880f0300e419103200341507900c24000c034080c000304c01004084d6807a044580c0d0380b16081c5070740544410b8913001c0074422000c0c00030700042e80c5075480e000041209041d608c5007900c00c6540c5240414040d142034009011549110310030030454128240791004901c03508226a0407040c3c14030410398964640c100500280030722500258400d0802c4a03800605134001080c1c40c052070110000c110103070340d5004160303440841440b040c1c00f15000b407020740040c0070681d0140d58000a00b2244194a4a0306000070f0b04004090300300340b000c107a60081074000300c4801d02c910480140c80d03044201035041e00b500080e0040c040180003d00c0040008001206400c00000f03613500e25850 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 186114 1250 184864 184879
    0x102040f030302030d0b040207020303070308060103020c030703020a020a080105010308040b0702010507060204030501020d050a0b030c0105030402030102040e0403050d060e0f0103021002070302040c0c0506100303050304020603040c050603010303030c030b01020c0105041205010b 121
    0x40740b6000b03440342e100c51107aa807000d05001003d8030502d03140c800c444070180d00800542c50100c880d0f4060301c0c00d4000504050505074240003003600f1610900003050018440d03409002c54505910405c6421001c42c1c0102c00c03240e1614005000045a0008450944040c0c4025644a84040c40101c1d01e92152002c000c0100340082400410040d0540140682e8002524180810342d00c4103400da04407200031601d80e0b0300d1350000794a4a1994090380040d80c02500140015107400c0e103030504130138480c10a4030218006100012178505902052081d40d0160a01605000e0740d4240020f45044414042c01301030320442d0504a100b030ac140c0200300d0a0010766002e842031210b0076604502500384520788406440034001c110004560241390340e800c0c02076a6150b2905810750710b40341c00380b1040381c000801c00c884180c1d5443c0c004c507465442c02e0246008622a5801158444140798000e0a44020303519041c155400007c4150240c0e0f000790944050341d85208070a080140c0320f04007a0f0252010080f0150003211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187364 1250 186114 186119
    0x4030303060501110d0212070201030902040203040b0103020102060a05040201090308090316060f0e03030301050915030a05010207050309010306050409020109050907020106092301050907090b030601110d0305010806060303040501080a020c0102040f 108
    0x4241d0015400c48400340c8485141c42050410351752514040321407200184c01600200e0843d03640755025240d014018500051350599039408a402c030303841940c050b140540450010070866030b041101c0c95114010302e809024030b040960018100c0204c3d030000502c00303c004510540c440c3c80402c010b50850300681046004c0b25070354070b0040d00c040d102d580302c1710000358041c00c256603a06002003203a04942025001700e009039502c080e0500140b4040c0f200a5060141d00b0350701e00480d4003400584a070a010b4006180e5440b10360002604581940e80b22030701850800c40c20101503a002295141211003d554051760b5607188842207006141035044030503190f2503c0b5150518134000140c17007241100b141204421640c80e141045075480c8115031003800100c03029404d01c0664681405550424410304041147c0d00f0f40c00801c5091860502650b40020358039001004041d10410145d6000700040d1f020318039090804000a04001c8001c0c4144152a000a5803201c000d00c25411a0b00400c0e0154120341c1842c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 188614 1250 187364 187367
    0xc0a0606030c080f03040e040507080303070503060a050409050303040204050406061a040504060602030f270402030c0705060a020306010507030305090a0f030c060f05060609040506010201110c07060809030f0301030b040503040803040303 103
    0x1140340015900214082d601103104200007403d000811010401107040c103140c40400d1150100080003180c02380514a00010f4032201080610301a4041d070300c62036143e107003510a020080b01c855001607c15420304d50b0040100d80040304694000b60182c8000c0380750340d900c0c24a5400b070071960748120b80081001e1186018002a84040e10584504843c1400101d9071903504a9580c091707440c1198a02c0c108118680f010303c0808032040c0c0702c2c009680c807585580701020000d41280c1013142c04080c401d50000301a0100b01d01400b2140d1320100e00030b0f0840c02c40c10080002030503400780c1c11000381131641d5a0081003a403034040065504140e8040410f81e01e4074502d2900271314001094800710f0300ca40c00c1c111404480e16580c080d0270f104150241950341404076a00411029000160582d410f556030348806004020b0800020b0070381249490003040f00ea440c0c10ba00402e130354801841c01c2c003141c00a12680495100c07401c101d0b411681c018030103044030707103403400e00d03d00310304c910383c003540c500e2000280010805 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189864 1250 188614 188621
    0x8060703020903010e0309010f0507050a0602030a0504050c01020703050c06090303040801060303020c010206070305010608040201050d02120702010605030c0609090105061e0309010b010306080d0206010303080a0b030102070501020d050606070c05040203040303020c0a06 117
    0x182c0c000c0c0e0090208540c0b00c50340d1a917034020400b41070f010907181148180000d04c00e101500c406c90242c0c00f10303510044c0030f490308801c0b80d00955200518a40350380800051040402c05205c20710000e100500e61140340d61201501e40c9a80024980300e0341001405030b1309a80e040060703e0207403148000801c0110341e20700e4040e40d5a44a8480300d8090b004040020b81c080c0d0291090504071030446d11510842c2d40c441c1d004656590103960501c25466007448181c03034100603455030b10710864041d0000030300030b41804101460b1000e860b050500c03901e010403c035000c40c0c07921164a0b04507242511200e4070340300014003c4404103840540040031103008010021501d005402004140720282c03810000907403503420a5850b181075604600c050f030712560040000900c5103d15aa1200b0701820000c2d008180a0020382640d20081003607640742c0d00414070365840c041d18400c0d980c010404880700ba140c8540d5640f5000c09168511406116aa0100018040c1030180c0c0460702c0ca000350704190364a010843c94001d005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191114 1250 189864 189877
    0x10207020a05090705040303030c091d0402040501090e030403060207030207030203120301050f01050405030a0308040201020f03040308121f0306020901050904050406020706050603120d0b0609040c020f060a020f04030305030601090806070302 105
    0x7a1408440020322810300d400003d000c0c0c4d03519070726546802c0c02c60310242c02a005503009101045654540011200002800143c01c9000846419040c0c1024010401650010f03041100c846240401d020031543e000011281166403200300581c3310032550a0503030034003a444d07201035014003400903a441c505170040b00071410390f07500700d409a0301c105c50040111070714001c6005280e015808880c020000c2400b5401550b8003601c148125540c3c0c4c0015501e40d810342e00154004c40300701001040c01c3d00e446408205490384401b5550030000d03509111014911400b101f480058405030b40010b014113036910820071144440c0020303206000781d0400f8130380b00000b580116001d40b0920328001c0814098070303000c070743c408108a40180701428500c0045e940d100810703000c0715456018408101020242e216800380c0d8030034040710f030043c0444a0280b8006810100000d02048000c1d104112400420b070306001910281c9402d480c0ca5601da41d505070058034620010b4210709002c4c492a000c02400c1623054004181 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192364 1250 191114 191119
    0x80403020d0201090201051204020406030212010207060608060405030313030203040803040b04080c090402130c0201020c010504050c010f05040302060301060f030b0a080105070201060501050309030301030201030e1e06011401080f010603021308060901020702 112
    0xc0000007004120b080b1001060020b001903c208400035180c8207043c9034603002400144000340590b5654009281d0004500300e071041d076500440c00d003080c003416100303040c010170010020b000285415074032280c41c1e10008040007860b4410340c00c281c007410710804c20348015000a004407a511621103501041c16000361054105901c96004030100f01e0a2206006024035070113031818030912030540b900e03809040103100600c1150743c24418045d10840034041c0a02807809600603041c140e0241d000104620300304941481440408c100400c011f840d04405c81c0d0441d181440c0080f00e804a02c28100d0151005030304480d07100d4000c40001c10005410760100f40501000d4000700180ca95800c01558180022a00440d40750400d000410265000360800a108100750007991000c0c11030728444c1114503407501b0302810582c440c40040c0b200030340c4050311741007150090034608100c0c9400d030000781d145038050040004064001c21403040c107810000c210000f8081e0740055503050701c1c2102c1614000d4104003026071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 193614 1250 192364 192373
    0x8070f060201020a020705040e03070c0306020304050f0303010303050a050d090b0702150603010905030403140a080304060902030606010305060904030e0102030903030708030604050705040303140a050f0301060201050702010507020304050f0111010f0c08040302 113
    0x504038014030884113490f46035000b411185240408001c010310302030080088134041080b44c0d0001444c80c0700070344040d6103d0702005132603042c00c1c2840751034041d2804492070703154400c00051000c203070842c2c04e64170790800c24a8410341d05d5258403920405230140c0803000f002055440f050007405a00400c07010940e402c02e4a0001a540d06c00b4201803c0c0c0ea0300ca10702414070b8004100030f002040b81d81842a00b16008030307088620716003855035180219442260143e48c0b0940d100039900451171700780f2000390800400d203030900003810214006410000c01602c000c060202d02060002c1c04c0e402403040d01d003403e20040607a5190780c1181810501c035402154610b206031b00d031000003001329000e503090f00d00707490b010b0703490b900403946120b80c04806a01070b5005c0420721030240100c0711030308402d000440c00f8040503400440d071400c00700f0340030342034400c098407890641d00140001c0c0820744482000700070701d200c2445d006e0f0050028400150044c207802880460403401d00155010075078118000b50300961080d4201c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194864 1250 193614 193619
    0xf080306040b0102010b060403021302090a030302030a020105060303130905060d0803070c02040e06091203090f071401020c1203090609040b03060403020601060f050705070b030402011704030201050106030e01060302090403030507020a0c08070f 106
    0x4a08a401b06c1d5052507100c14144820310241c10003941104150307069217801854108090001101400c140d0b004400503400051074109103a07084c029150016016001581030030381989641524841c2c138021400d500f9910310014030207a442001c00000d00350414a1141c3d40c0c00e000400900c2e040c050482a40920300780800c402d141c07400024820300c80c100032000741111f0792142003045482d91000d0500d01c103a00c0f51040b00340f114001408be1a008000c000c5840e40c900d802c01d80060304113070055203150f101d8603000710042c500c0c070004001c941008100703c960b01d0341da0803040002001062501070075501441020100000c164001031880d068030116103c011404240300000c460500c03442c3c2c0d00505503081304904105111700326000e1070f0003520504080d0111500d2600c4010074010841b810740c0182e445c1c0e80100241a01441840c260810082c000e000060944c0c0200c2c0160703802400040415594000042d14a1320030300c41c01780401d41c04810088116583c03a200360303035040ca500078417520b0321103507000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196114 1250 194864 194867
    0x50a0b030c03040b0402030f0303070201021201050303070302070317040902030a0504020102010b060307091e03061401060807020705060708070303060f0305010605040f0203060306060d03020f01020a03020309070603090201020703110402070f080306040b01 111
    0x540707108507003086032549180d44a03590300c1a01400680100d030944103491103003414000910103076114030b060fa0b0005071140e08010007100070a030b040c2d100a009410412200340400d9000ca0301006890f08119450135520402030590014825980300070845403020060001c8a8819008140154002d80c02070200d43c241c002006800d200c20358200000c980400400c00603880001d0001000b10038011112004035600d8441a043d0745000001503035400c0300d01c0051010b1900b01040c141c0001840c8020302a5608000c040741e2944500d03540500014800320701181050b00c03070f40180c000341c800082039400b019a40d00d0441d0180000d40980342c0b1a13030030326100c007450b58005c1c420389200790300c001d00524090b00e612090003954a1004001c0e4214040c2e02d0381d0001d006000d00081c19040c0c1160b400694034a081004242001c203560458002c240c02c2050355400f41c0c0e0300050040641e90403c050039917041e0f020001500074410180700400002c0060700c0c100a000030540550302c10241500d0501100121000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 197364 1250 196114 196117
    0x20f03010501050603010e060102070302040207050607021501060507030806030307020d05070305010f110406030b030109080307090e010906060504050603090102070f08070209060301090209010b09030705150415030c02060601030c17040303020301050a0b 110
    0x83c180d0445020700040014211078685907802005c180144d40c0425102e4000c90140d0b0711070081518140e00120a000303180e9030400a0802008102460120f80d50600e41d00400700d103c1c020019080086403000308040c0da0b03080c002c603900d080e4010f103500d542d048149051500c4840c944030a4031994070740a4150200d08007801888840d090342e0b17960718503050602d8400d07401005804c2c600c980640d60348240c0d01c0020304100055014039070585541840514080522450004c16084807105c1800c042040150b00c3d0004c0c180c2e000d50b081200e03044e0f280d42d20b280d0310b00e0080c01004806054035403032241c00020b0141303840c02043d0560003950190b046540d404141403e0300d00c150b8000f0740010280004206040b0140090b010210005045e1150947da07940025415000740002c8030311203030005400c2001d10b000303402d40340180340c1d02e0409211418116501039180d40d0010529810704d5203485e060399065100700c2c0e1082641c62114011461801d00f420002c00a4009004150107040f4081c00451031000010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198614 1250 197364 197369
    0x302070507030209090a020d06060503010b010507020603070e01050705060a020901030509010c020703110609060304050d020607021501030201050703030608010219030c020c03030403060e01060503030d02030a0605010c0201080609070e0d0609020f03010501 111
    0x103004003041441c6a0a101d4001001450320b0f0780c501413428a0030041c0d4448501f00050703409600046040e07401c20301054211040307041014188602040110010380f26001900d5000140d41020403e504541c00182c1d0503200d01e00d001000c900682c000c100c0e007241d695005e030003044820f0b0317800c001c2651075105090803a0301030010140564080c1300c00300001210b88501d400c5c9654080e110a08060481e000b203200ea40007030320111119000300c40480310440c4c0c10081140d11030214402080912903200040b0040c1c201804040d040040c00035440c820305000340c122000811020300215075400c4103442490303081d444400c00c180006d00b401510001280b00146082080c10f0040186281c41d15668a0344000d058451a501407175499240000d11503800380090b02800021003030140e81c80c504580f40b58101c8034140c02a41c180300d03591060b00e0250742d1004103035034400d0090303400034a02d8035102801d6819070907820240b540182040b80070000c002098100150440c0309441406c03a07400e15504050a0f54000d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 199864 1250 198614 198623
    0x60a06020a0b060301020408030c01050105040c05040302060a080901090804120b010501020d020309060304020a0308070308040c0b0307120207060e0115030b10050102060c0a03020403050102040e011404050103020102030315040e070906080706030207 108
    0x905014002c40c82500c0e107682c00030001800141b070603542d20741650640d00720383c0361406107035500e03801004030b030506015041c103c44c4546401031401c0c0c01e59001030a2806090701c0340c000c100d0010300081c0041001d500401600707405c0b42d9880d80f181c0d40d4922241210740300b64403c6400c2c0a075513000090325400054003043c88503007a00a18200400501800015040200113070f80c0440001c5000000c10119030061010718066030710f840345c2e49040e003000e2080c11600d03440710007000010801c102005030b01c200b040390f68451724180561f4803900c0b401c01c60b001c0d2000c103413403142c0e6520b0720b13140742401150501028100c91090001d2403440c0d580305805209200315215407800f6801c0040094407000008009026841540c1401803c09031203455607800c90f04950000e07201d4070740e080b0041c0a0f00d911400d280542c554111030900c620340c15540002d40381d0001826188445071140f10085803580d89811036080241070740b0480315059076035400781d406131400388038508440c041c648004c9041d038841d008580049400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201114 1250 199864 199873
    0xd020606090106030e0c06030a02090102061501090302040506010309120504050414040507050907090f0603020403021c0f080309030f030901050403030506030d020a080a03020d0504030306030b070f0c0b0402030304030210030e0105060a0602 104
    0x1c1070025400b500001000d05103500465410380010f40d40e6402544c0a030006000041e182c1d084bc40019184c0310010300081e1060780512200641031780d102c2100703800d0b02c3e415100410706899034001600541a082c100030b254944000b0084c030600c1e44540a041100d1046038148122942c0400c0d4050600341a100036050b50003100050255040a01ca0180c02085504d08160f0580c0d580e0700e4200c4403c0c1e01d810420003ea00010100258602a8040010484440c1400d429000c40f9601c000c40740b214100000c01108000c4002580c1e0761007803040c1c03544141c000640507964500029000d0081c1021141140460f1929000c1440c50500103580281c2c001d040c0c00824400e80d0540b1851000c1d0000fa10140401d5000c0080840c100720030b0060600852003610042013090071860300b0060359900030001c40c104210800a00703242d507404000c80907006d4100141103199100c81c00443c2c218422500003a4020581461801c181507041e4011a134101c481c400800803500e0703030000c00c08100f01d544500741c010b13840f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202364 1250 201114 201119
    0x3030a02070206090901061106060907021b01030605060a02010609050a0209030604030507020402070204110702010201060603020306010507060b0409050303040c0306060504020a050f0306010201090b01060c0501060f0b040b0a030f02070b0103050d0206060901 112
    0x1460340241845400104070500f03001c1c504002500c014000d800c5640060402403a0075020a8200080c0740c0004044464180d2442c0c1040002e5039080c1b4540d103400001003805462034035034002e9001b140688409021a6940c0410000181c0a00910701c03501d041d96250030002102e4400a00c280d40050703038000d01402e06034407152011070300c030740100b201640e1280e802c00c90100160780781c2c86405603071074808400310f4403200340e070001a0858500d50702c030005140c010020070455030b0340b200440722019400380780010500303400c501140c020054460014a079210000900060100c031080a600716131007040d0510101d52100c1c20f00050b03008070414500490001c0c4441d01c1040804d4001e503500480602c000544606a901e0781d445a0b41c0aa000c480401d03000082601800340c00c1c080c1344007815100c0c02d204911845c10b90019820308c80c038894058500b00200b1280b030031034440d402800368040128003e549074111420f10081d882401c2c4012200c1e44116851200f010b400451400d21a80c002404858280e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203614 1250 202364 202381
    0x16030201020607050d0605030709230105090105010c0302010905010501080102030108070f0803030402010c05100c1e03060803030606030403090801050709050109090903090b0a0201020702060c0706030b010503040b0705090a050d06050f1003050303 107
    0x40040d001046110b4039201b012400b501c040013844010301d209000070608071082d60701c0032611b007811038080e0041e030a10130051140c0d84446459034111402032034202c100003980c0c1803c0b4010000748000605030750030f2000000325050150040d606803445107081d10031036651046201e1b03406140380703d01034564209000042c055030049445c50b0041c0c0c025410f8441d01c0c6600d1081f8400c0300c120500d0314012603042c000c0031100000d90795401c001402c4a003401c0102c64108020b00d6501c2c00005c2586100303100c0000010304140c490401c4400030701c1a10001d21180c02d00750b0006d070807441240141c4e0f0003e01c11000000d44041c1902a42000c15095120500102e0034681c02100f030740d120184050566400300701000068460400400c0b04a00460150020300c3c1024002010ba50300d0fa003083d81048828420700002c54450b0083c9a00702615040c02a612966100815920403190384490390014419400300b0138000313030303400071803041081c1e948000450380c68025008409a06020181c1664014130005000345c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 204864 1250 203614 203617
    0x20d0806011209030201050f010807060e060d0905060106020a03120203010b030a09020103020f0a03020301030b010504050118091e0501050403020d031104060c020303040506030108030d0501060c0206070b06010908010203181603020102060705 105
    0x8042c9841846844400404416511041e03021001030f0366600030800000c0e14406410301400d24900940b01d000c1c507090303004060030700c8403070354501c91500014071940d9182c0d298040c443c055031000569046682d00c240182d00c5180c2100f06030302086880c4501580b54003d8421241610f281a40e0b0b2400c45c0c40f01140742004141c2014104d05041e8200a00d1060302d40420244c1210b0040b44d80159480d81140791945070703044183d024501032414800180000030300380080c1d02c0141042074002407a10314a04007120b000054122130801c1c0f00020b5207513000e014040d009940b1807130180d000c03a000710407591030450854104880c00380c100b0f04144418492a441000d4a04000e80003d0859082540720070015046030b0013a0b00001039070344001a900c5600010303016460040c103040c1001035042503150040740f0b451249400c01401000f241000506584c021164400980348450085445c0d14000080440c0c1d499a41900c00c03c500c100e101030300d00ca00404819009a03541a4058034030303911441000da44a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 206114 1250 204864 204871
    0x6060303030402010c0f14010204090204030303060801050702030301060c0f0210050703110a021309140102030903040602070f0302060405060703020307050604030201020901031109060406050f070807050105070807030504020904030806030a0501061202030d080403020d08 117
    0xf0317410399408100c0800387c00d001030000303850441001a599461440d002d0111940782d0710005150b4148810001000d401009403070440d031311414141d85e04070036890151144040744a000f0350000701268401d006a17400400b81191b40e1103a12590b100100240406980d0f80a03038400950001031041808480882c9810040c060761003850200103101c030101d48542a1782045950340308652020608101e601d41c100503620040101d501c4a444480c1960040b4a10f0b00c20380c000d080c0260000030701241014401c00480314404d8101007555400d05051030020701070b5111100c802d00090a0030031040c200801c04045461b5000c00921583c9070600d030480560b55500403445020b6161018049140810001001032100313520600000a940c60048005007442d400500b6400030186010100300040c1c69403140b158001c2e4040c100034905035904c000092900c0409040280f941d400c141c80021181c50300951b0040c0d0510807015290040c0610030116910903003102c000c1d005920030300484081710700401560380c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207364 1250 206114 206123
    0x3020c0105010b03040309060801060e010302090f0603041103060a020406020a14010603050303010605041a03010303020a020f1918050106020a030215040804090603030503070e030102040807090203130204050103050601060206060303030402010c0f 107
    0x14080004611401c46100f40d00c03140d203564000040108155020b0004c030050009801c00031041e504200000344241e1300050f10034181540005c021700103070f0b10b000e00102804030061403580e4034985031900c0001c203001812481c2c001e10a90002c500203008034000e035403d51b07809600501c00495561101d403552031440d111008903550352580400400d20500055018041945032165100d00d008071580c803144600c41942040b520500061002a50103d1900c1d0602d404913821040c54032180d0004940704070f0b00948481c080d81d40500091804075204841c100c2c1c0440d1001002160f070b0b90301041ea00d4800380306005005801044250404e20300d1030200070381003070050502c0e0f401e080e00c48801c80110342960700254041440401041002d40d804503a402031030000b0383c025414240780c4070300c0d29544e02844c041c1e080801d80100008416a00c000051003049030018028411540d69003451911264203004400041c054040040c1043c01c0000803a406107606070340380d54440788103458018a51010000c11903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 208614 1250 207364 207367
    0x50d02090901060c0c050301050103020a03020108040c08010204060f0207050904020108040b0403020309150301050405060d030504060e0301020c0102070303050417040b07060506010e030a0b01050f030105040507050d020a0306020309010203010603050105030307050c040c0302 119
    0x51441d2100140e05010300740f02e4540b090580198107040c0310507506640018401d030f04140050005032265941c400860b6828200100c65858524218131001461b82000705150b00c0443e00080b0154803039a0000400000d0b000d96244645840c01d1080c2110300b110042d01050741d42c0041030010b1400c030354031075200d400b07441a2400c0c10035240c00200b400b508100c01c4001d4200200040c0801d00d401e10840750042c8045814185042c0c44d503031302401c03501891080d541440168254100e06807029011103441d4514007008560314170b4586009401440184c8040e1910110500901208080c02c022607040e504203444290070300e01076030386201c00340c10010100c42c100850040400c0c400d490030020fa211045c070940110307040d03605090501c401820320001c000c0c4640c2c1408180404104041502410b46409032400c5403d5045400407400606403031340024a020b10000400906000c1903010798183c1e100d40c1d50902c6941d0342d59041582d603026030b003000f400c1500070006080d51850241d0007182480c0c114100036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209864 1250 208614 208627
    0xf0d02030708010302040609020c0c010503070905060408010c0801050102070305070b0a03060504050f0406050601020307030503060f0102030408030304050106050307060c1109040c05040c02010e010e01020a08010611030f04060e0a05040b01050703050d02 110
    0x44166081a00d616021644880040c02107203818020b0001501411720700310b08185110b256141d0340c410035103a043c140031000000c0f0b0202841003015401405010340440d540d16543c000107802030101c92201000901504004103032503101289034012030350000002d2050a04100c402c6e174243d480034003d50141640c5450000d190703101d50040768031850000300074044501e0036042ca10141c0b4002821541150000c00c000720000303030800190f0350070a00c10b8442003200202da50045c0d10310310443d00f01441070310010040000b0420150021010b8a106a0690f161660340d0081a9240000300000504504070704112100301d00b0114481940503004829001e01190f40307002050840711045650320045c0d440302d2a030b09400d4400d024100c0d08294541c001c602d00140c0d5040286400700c103001d8801000340c591100d03d03003c0020070503079054561080140e56101c1c0d455201038038148140c90030500600450100140fa0724051180180002041e11041d03d0f05810356002c89042d40090f5045c02d01660a2055 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211114 1250 209864 209887
    0x3050c010b10020a030201050105101403090703050102031006020706020601030f060b0406030213060806060901150c03020c04020307030c08070201050f01060c02010908030703050304020a08010207020607020402070204020d09080306040c0203030603070501050f 113
    0x19141d42c550b0310f030060300d242c60309810004e0945a05802c52401a60803d074815969580202c0f003441d001c150140c01a141e45840c0c108034100146580064181d44c000310600c007000c000e2912003000c880094088442030b5560308026a00c0e81030910028003042d08d25100c003c003140f620340080914400c000c100061440e00c03580059030410000c40c620700704942d110f006100165040207000c2d080b080450707100b48a90300d01586140c038068030800035401c000e90284030400f014000c02901808583c0284107544074900094010010055100c00400045061012600c0e9500622455000b0880051580d038143e007003070001c0d101000d60700400ca041240396400010019400e0000d4000c944c8650340301a030306e09040c0104000c0200542250105034410006940140e4504080310b08055050703c0c00350b2107d1072800028001d00031365405604c01400c0c84130007410043c0303510040d032080c4800c035000c005082c40000304a035a030008030348445d096800f0faa0705102c0c0d5070040c0b01a000c03051070b640486140010000030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212364 1250 211114 211129
    0x702040e07081c02061302060901020a08030a05040309090c09051009050a03050102120105010203041503050604020f0307020609010509010207020a0b0705010608120301030c060804030c0f020a05030703080304060c030501050102070303050c010b 106
    0x10b100240c0001640c034124120802c120040c181e214030042c1070034202100d81355902d41d50074038000d210f85400a440c40c4142d0003440842d00040d00300c5040342c0c9a240c18001c44005e410121422030009400c081c0118000c0c080d841140c08400b40c035a603070503045003000203100c1c41c0c0c500120160148640813000150329035588150901442c800c000140c0c94107071007041280301d250103801460654205110501071154120503040010009190101e099190b40000c94024402c1440b03502c103080001040040300740d00000e01500840107580200643d40d95851030781e08034040c10b08003e50045004a041001d041c1c144050842240140000181956944049890010900d101070300910021004009014515540100600031824041030a1820341ea0040400c815500003c0010003040161010340d00e6206503035000c0c100140848280a44038100045260000c0305c1c00c49459040480c18142e00d13120340103803030481d04182c00030030310036042d030350141e54036040000c3d001c1d000c1d0b50300d081c00c640310b5881c441d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 213614 1250 212364 212369
    0x50402070501060510020703051005070306150503040b01050604050609010309050309030304030506040c050301060b0306060c0703020a060306170304030308040201080403050d0507260903030109090311030403060219030b06030403050702040e07 106
    0x10382c02d481c207400c5c00a0301070745201c41401c2d500140340c1040844d0020a02245560305e451001600e6600e02c0340a50051400d170308680f90302ea8400c1c200800ca035421400031801a03004400b821300983c0d840e000c03c68248658000d00d60488000d01103110154025042030195601c21415031742040350f12008a480c681003a402a50554881e0f01030106108454880001034501600240714403820070080d441c5c684006070549020f641d002521049610007404100040c5500403d24107440c1d03500c1c00014040c16041c003540072500304407115407640c00e0300002114122a4151641d008503500e0790019101018010015005e00100704603045100d40b192207640e01c05c0d1080d03214260001c429040700701c00040c2d00c00d4041710350316002081c810b81c080008140da0444254041c042000060361904503100c0e07401052101103031002141c044200107458000c1c20b641d2800ca030070300b1030b80c5070158411000e403941020980c0d0012010030209000c2072040f0000c1560500192001c6581d0100a400f107203020f580d42d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214864 1250 213614 213623
    0xc020d0b04080702090703020901020604020904020310090302030306040c02070e0109050601050408010603030306031104050405061506070c08030903010b0607080304021302090306040501050601020706020a02010207050907030b060703030b0414070503041b05040207 115
    0x1074628110300d4141c2d03085e80c102ea0145001c50030030200383d00103903a891026101a1244001e40c0c001011941c0421408180d034003e02d07018400da810f589000f84d0b50b41c02c00d44440e13100b58117005449001c14800100b10341112504103040856919282184000340030291001d41041010840890700031000d008501c01103100390780004170355145040c950445a0700c078418520560a080c24080400c42c0001c03090782001440900e0b1014000d03a500041107031050640c018040b00c0c1c1c0d00000940c00002101525081800340c00030300488004504106d04c0b442001c0c0c0c01460440103102082c0941400d81c001c502c070100d44072005103001100000a840d00b43d00310350403640c0b40c0d114002c0244c06d5905002e400c008040d140010b00c01050543d00203500d4038440c0c000c45003c2e00c1c030807000410b075900c2608074030f0f1001d0010b42415030310103182c1001000f4000d14071049008a041038512894401808021407003101e1940d6a0760860300ca0344d54486100d4080d00c018218090344a00c0801c2030386c0c0340d200a01295100e07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216114 1250 214864 214867
    0x80310030804080304030302060a050c0714010b030706030605030f03030405030d020d020708070f0201030b03120f070510050702030706050106020d090302040b03010b0604060903060605150304020904050109120507061d030a0c020d0b0408 103
    0x6601d0000d03e4270600414880600c2e050900b4032151240030303020355a019a1000e10030307001840e59040c450043c410992103e5051042b40c000150803500356001f2000d9503015809c0e039812061030030040d13a9034031064030000c0003544100504a8000425401340c1b080402003c0058070301200c0d62501142c2c1d8004400c152100c1c0540c81c1448210744e0103105d0f05511103001d8001e00251316024005031074501400f990381c10315142c00184882004014006114207540d8413408200c0c50030301c024020356036044140c0880b00ea0b8500340021400c0b90000a000040d401079558286c030b4a4215400e00000e0b0010142c450780564071038104031842d0381d4840c05040504540e50342c00646c00c1c51814200250340301c90740464050100c01d158001180900412264080d0b0180c0e4400400d8950380381c200d0050a020742d010704a40702c01c80041d000385c6e5000c002000450300503141400421184288002c28946000440940b41d0013089819685401030b481c15424a00040c91021480d8843e00c845282e4282143d00701c510300c90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 217364 1250 216114 216119
    0x901020105060102070302011209060603020603010f03031202030f06060c030c010509030a0e010305010b090405060d06020301090203040606080c09040201030c050f030108010e0708060f0a050a020903010c0905010e0d020d080310030804080304 105
    0x909204641d403080c4248010000d1528540010b40010800c0d0b11401c0100d460700300348401d10900d90440c0d401903901170541c2d0360302c1da9250055140341c209804101c1c009440292031030310722041c0c0d009590162405440041c0640ca5071810440c15510600e189006400309000c55070f0030313000c00c0c42901d12035a5030402842d599098410003c2044203402f030351074141450b000040c044150aa001d0ba240f505055400003900d07194800002d0a0450810009005a00000001c01c04c42c02d603070080c600031485000d080c007846407108801c60f11081c21491494000c080000083d002d584207130880d00501c00f0a0902500e0041c0340d14061131240c1c17090304040c0f1745039154014981046410440903005045803000303080700313081c550b0340034444007805001d440b661034450000c40d02400d51541200d10f0514028020888843c01640140480c2441c0c425a808140903030030f5190941044400d0302d004550003807080405001c10f50341c1c00031300e40015001a4882c10034050110005074100010000740034100c0c000c645440c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218614 1250 217364 217367
    0xf020a0305060102060604060e0109020304020f090103030507020108060405040323040f0803070b0a0b0303030703020a020102040b0d090b010510020c010315050a030f06050c040303050a0302030703090c1401020601140109050d03090504050106050901 108
    0x741006d0b0189241440c20060541e142d40f0b01d5064813840040036a80751550b0001950322008000e20303d40c00303c00312000104064101000b024114401e803100e03080350b900c0f1008c0004031001100c001d404211035801e00c8118255842c0325044001c4120359890402e42c488440c0c01b00c2c0c50180d003003000300358400030300c1106202d060310301c0c5a408103034510184003810984010039202e0001070054401d054012980001c928000e405a0300505003080542da100e80109040c5005010340990a0314140819000030074075092585c0140d0f4000030a40003852421003900045004084000d0031183c400a4401c0206007940c544c00050011401f80070043c00141da41d043ca102141c00c0030b0105034130b001c0d0400c81080040c1c1c00105960503188141801030300e80e40d036900250301405c6d040d1801029a10124808108003180d020440d44100080e400c842c1c42c2e0303072610340288000b40d845001c00d0205001c01800c000f0303854070002d0071519911130f02d40900b965903500301083c00c4e900c0a802480c00300304085505096075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 219864 1250 218614 218623
    0xb04050a02040503070501050a0201020409020307090302010e01090503030406050f0702030307060c020607020c0109060305041401050406020d0e030f090d050708030304060603060506010804020108010308030912070804030203070506070b0606070201030f020a0305060102 117
    0xc92030002180307054079103030001355203200030702c61030b41440808244072804038000e40c180d800602c50034030150f50b6441c090b41c006082903000c0c00224041a40494054410352051003a4000e9602c0a0019031a06007402001c0c0c419820401039031002d030900700300607801030b20300b4002313010187e120300e10205401000b5200a420700f48000c10a80466112400e860440c1e0792000c21441128401d060000c0c9980325400c0a99824101c00e08046980d802c06080c4010403140741e00a201c803005803001000211070040c0f0454480c480c8004000b0500021300490350036240a00c022240288540c049440d0b0036920b800d041d04503001201d059480360b550340c13420030600c400c0e8007410741d0203c02460a00143c2c6080c0d4000303450f41b8411300000c2c0072140c000c00014401c4004000b140501c0c2c0c0360000b83c545804640c03600690690181c007003240240101c02c0001254101101564116540201c480c0c10955600c824010281c204000982c1055101e41c040d03102804548010b012899042e500411a480d0660019140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221114 1250 219864 219871
    0x4050301020c01061d04030203030105060d181103010606020102040501020601090f020702030607050d06050603040302190c05030703050304080114010b0d05040204090204020309030a030506120d0e060403060203091e03120103020d02010306030501020307030b0405 114
    0x41c1c1703105810000000e80c044100d90540d2800c4401540700d2a05441540003490540745200c180c0042c500034200b8009294400802010110001d20074032791101c00482c240c0c0600d1180302d0250340540018001d040ac0360704444000d1010040050078104690006032a000703041d600d00300401c07000a1021003007211401107202414054400d585981002ea50080d9100c1d01480d0401180c10f0301c1000703400308421402c10000070100202142d404585074189244c50380e1181c894840a5840d1002042a5442d1540414101c0c4c4000126609003505c00314400007801c0d00030000c80e407040e0703250001d5006075214030107103028400c2c8070002d540302d45200401a08858014140b02d202d204248034420200d800002d240c08420054608007045060981c0131032018020358200500d4540080100003081c400001d080c01111180780e1106891070640080545030321400e1103980080401000600160800f40c0341540703c60300c189400101c0c103640340ca4090881e0000da800c000020740b40c0d441101d00f440c05010b000d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 222364 1250 221114 221159
    0x8070506030601050403030309020a0b1801020f01050106050702011103040801060306020405010f0201051009090c09020703050c0d050403020102030f030601020f01090803070905010e060406030504031101050103210503040b0a0506030304050301020c0106 110
    0x950b0408a00180131030086100040800d9200e540040854079085c2200e070003894003030940c40d02c0745080004e000004522552050052140c50b131203d510810500445040341c03034644409181c20040c0d00111030882200c03862495511040000141c0b8034001d10400780294021000107032503c2c07c0500040c5050b0781561008111381c100030510903000100c0c42d0840865100c4030001810b00c0c3c140c40d008600740119481540c0140c03012030340c001415004001070544070300320000e480086451110560709406240406401a80180080c510484a0400131038101d00305004550b80c59a0410406007540c0c1c247c00b040760038980210601100503000201f400182109082c90303491500c21801059403401079110349000c0549600200c0e050500078045869190b2440000303020541c1c480c1031040c5550344a0303c240c0300030201120304200e210300c12000e1780c3c0205d50004014000f42c641a4500f000303001c002d040b640d410700040200080c1a5000d1000308901c1c0d10b480300214089140c80003040d41454a80e00c0d1700c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223614 1250 222364 222367
    0x801060f020610060e0102070b070606030b0105030a0b07030b010306030506040302070303020106050103021c09020d02060c01050106090501080601050703030506030f0307030801080c03010204031509030e0a06020c0306070f020a03080603100c0908070506 110
    0x440e4040c050f05020030f0301e80d00c0ca07080b403828900c000100d2030b10443d640110341d450030010ba0301d001d111040e000030703007502e001e075030880e4643c1d90314024190740700d4140c100901031810300404038580307d109401007864050140b401042564130fa4a4a43c1072140a460071000760340b094608104042c1c0a028200082c1003d00381142400381d80d041c081e0740ca0100000c0c5c001034950315040d0390115030328280c0b42d02c48941c014041da030712940d06950060003004280181e0001c18144200042e4940c4075001c610312135801a0b440504164039590260003400e405881544c1c18049c514004810b000100081c0c0862030090b51880440d514200000d030602100b6035101703000e40d00402040c0b0100d12340f00d40821006850040004034107050f4241210100d03460900c09512104001e000240710340e0010342044010001c0702640e40036219000256401d10390100c0e00005a0000607440020900607101c2e143d204201a0550300c0340d00f06c0022140c12500e08240040c040380c0f900f20140002241080150090481034900d103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 224864 1250 223614 223621
    0x106030506031009080d0608030406030608030412020603040606050312070605090303060307030b1302040c05040302040c03050603060604020a030902090108060f01060503040308060f030c0901081b030102030103150b01020312070801060f0206 105
    0x6a207454500c0c4050f04000e882d02c140070304100c02c500498201c0060701c10b00b001540e8035641e110385c60703a1151148600003414a0f5001c5607058002c0204d50440300c043c88481181d00c1698240805600010400e03142c0a03500c0b080040c598906002c1d688202e050405100da40b03100910b008811204040c1000c0d44650003802000416140001c0700c0042c2ca4008111807841d90310b00d08234056515084c40020b4000f4244074684e81c090f80c000c8017402c10f59200300c0d0107110240840b1412001c6903000c0303c07001c1c0c8c1513003c072000c2103a0b804d043e8004c01d43c9680030b207404184d04075280c011440000013a4030501d1250302400c2000000760100001d41c2c003410741e0b450510f00d142801d4074005d060400191aa80c411a02c060070800c01d07503420451103083c0500989410304c02c5d030303494900f80d443d0f010080c607480814041f025000441d02e41803080b82c1c141c95104054294001310421410010628104513905501c0200074000318030901c0700c802481380c09559940442581010b40003888055107088c070000b9503001c0030070b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 226114 1250 224864 224869
    0x402030a02060c120703030603030806030105060f09060a0504060e010501080108060c040306110405030105090106140102070302030709020d021605010902010201110405010c0308070201021902010204030507050a050105030c070f080409020904050106030506 111
    0x5103005a404441d02074543c000121004d08250b120704010700d40d0480050000c1c20036401d900150304807400323900c03000c0031555038800389400e940045a1a1380c1c407403110610700d40e65107040d8071415000380c00900100312581d00d800214040b2002c5800464400c1e4441d070040106680c0300b109503000d8000c1101804003810004140700a5005a0200400958440c2c081f480a50780c0c1200b5100104002402407229080c1290694020800b90140c0390640002c1c107807850035940001001012264060021700d466490824220700035003014025402c01d507002c0144615210200110502c801d02600000622a0340741c0b0001e82160701241d000c2c0c400c0003092004000581e08607071070207069609420803c0300c0d039448600881c02807113410010500d00c40300600b000c050b507034158003a106480c8501c0803030f4075844c2c4540c1003104506a503c40d25000850810011703503a1248517001c0c1c0400b81c17040c903140c0e81074074403640d6001039030f0410f4000a81903030380411000f581d0b142500900c0e0041c031042c1400c00c900e003002c001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227364 1250 226114 226123
    0x4030b06060403030503041e020907050309010606080106050403030809010902040e0d080a18030c0302010f0e0a0201020705030304080616030b0303040303030506040f090201080a0c020a050109030906080106050a0c030c080d050708010503070e040203 108
    0x604020b5411231181c03030040100c00105d14540d4003e20f900402c0c6042c440160030354109544000081d1b103007500106880780998a00c9060715980c0e00d99900700b901c0c1d990110343c049802080034502d0b540361403ca13401030700c1c1e5000d1034091042c130300c016201107412480c0082041200400c065201402c010a81c80c41d400800345044c01c0c2c1c0d030185007035102c00e03115040aa02501c40000141c0300c0314036101c8000d409003008103504580710700c02d03420381c0c0c3e1050380d46007015940d000c0d900031074171240c20040101d0402c5003186c1d07114800a10034280030170340c00b00d1100028110b802c03035030013034002c07a840d5010003880303240c0352240394034801d40c40400704425211900021300402c8010310034002c1d0380d40c03a9103c1c8002d6000300204000194460004e001d0085107150040002c0e05030312030070010820ba500041415402181590060303211030380c1c0c2078031419098030200d50600d5900d50a03035483c50204100d182290b894000c00d4400c0001e600c4240f015403420060600d000c48541c451406401c2900510005a60105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 228614 1250 227364 227371
    0x30f0f050901030504030302090a08010203010f0504020304080301050d0c030602030a020301090c03090506040201081504020705030a08060d050a02060d021b0a020a0b0f041707050604030b0405010b010801030302060601030c02010609020408010204030b06060403030503 116
    0x1900260710340c1d0b00c6c9420b6000f40303e0002000d0703201008000c00980b510b0150019030581e41c4000d0b01c0c0e54040d41e81c00130320042c4d01050b90028904201440107008500340b0403240160503004106807100c280c0e41e03803a920101c1e803003680c4000616400100622242c0301c2401000c40c14205482c00b084110965110143c84e00d0001e080281000708d1080403c054000c4050300c482c15480040045549030a41d2034041c1d40e9070f01014104000c514020002002454040c0b80301e10030642060140012113a150708014940e401100d00101c210b07402c0c44444103024054213000403060f11040144040c40341e900400a4540c80f682c08604008070802200801003250001d5404542e0400c10b080c4e0826103521506040504d142c01c00340c0c002102003000801c1c0040942180e0156005800802650180c00e00449114400340400b40141c0c4c000d4021a07004d5120307600000c2c1809440c0300018074a9200c0c0c00c800140da0103580810020381d000714041c424000e07000d00d41a0000030482d001813500e0301e1660041d0070b502004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229864 1250 228614 228617
    0x501110318010302090307090203010302030106060503040203061501030207060501030b040201090506040609050d05070302030a0b040b060d080304020105070302070504050702070303020f0616050c07030b01030c030501050702010605030303060f01020a080307020109030f0f050901 121
    0x5001201250f4040d805a40102c10014242c4821686a0100400a400901c005c1c0d110b50b0030820f00003140c50150085a0082c0c0d0060080c0a080d5030f030030303030410302e00c40072000d158105642002050b01003407440c855540a103101d18900300b02414503000042c980706490f0421031282e0f004000400c80b0a03003009042081307620549046e40201c0e4581000e0703080ca001680b01079094024144102c4c1006807107020709201d140705203c1000c1d60b031201d00030301403514007072400201407500800c0403d000d98090400342c0301da02c0c482e20480c0c000e50f45960105c2c050328819140f100c056480b0510a208040d014480a0642c01035480208698034101d505c42d03100c2d0482c0310610082c0b220004203c444104244154405190000c889222071b52b500e1400c3e0170a1446440142d0f0554a03080120b14600c1c0706004407005c42e00300400460454440f94104040081c84840301c50652040c2d08440001840c60300103540300c0d407030a400001e080286414082c0c0342069039196902001141d8601d030000e140c06c6800d6a20f0210300707 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 231114 1250 229864 229897
    0xd0e130b010e06070605060108010b0405090103021309050106080304060e030102030907050d050a050312070f0201050610030b0402070209130201020706020601060801030605040809030303040507140303070305030604020702060f070b0108010605011103 109
    0x3030040e00d9a400d02c0c501e5030340084000400d00d05100755900f246004040aa03a030600581c0d071000d42000901942c010264018043d0380100090310341520714201424099200240c803000960700d403401c549199102a40d1604046410091560410750040b05950194029840c5260805600361107160a00406203e5816501d42030305000040050b030880961160440703a41d41c10034815021110303c1100d85e2000141c3d2424a401c0b05841806543d01491016000c0f00c00070340f42c5101580600010030005420a40c2409108056a10342850900032240150b08080301c002500009040141c00c2c0c2040041d54040401005200d80c02455181100d400400008558480307151900c0203208503c01c0e96450b2102205000500c000420007008442c0010350298001081c402810b442c2d010f0310202402043c02480003502e06d00b8103400034410a0b100910311441d2040d00c0c003582202c0e0700700c900143d440d03070b02040060202c54000d101e000e019140900f0000322403004084007075524480c400e4608405000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232364 1250 231114 231131
    0x60e0103060308030109050702030c0d02161505090108090c060403060501030b01120302120307020a020904080306090106020106050a1e05040c0809060901020405090402040207020d050601080109050106050f060405010804030903020603010e090d0e13 108
    0x70034400e46a083d2011410380343341c1c18003c03c000b9502c410301c04146240446042d80040c080c1c590401109800246403520f608106040c001518200740c010407802981c0034a07400b442e00750761003900034005188901000102e55045041550b05070505070420ba141d82e00031900c1e00c012940000b40221004059042e1079034a642e0320f01c0807420502c0e0179000a40103200c0c10140410003031100040d5118000030760320160907a80c2c078003040307007a21885d208039500040340d034400b4044440c0c4038444c00c109441c4081404105590f42c0049012a0101c0c0d4240c400500080c0a001c0c5c015401d104103600405194001e50400341002c000400a81015000a11580d400a12041152140d0f140c546c440ba8024080c0c0d001e45da50355441c1800b034400150211001d51a000300802c55140c402c21012210202405c8c0600f003e040074015540b0b114054425024000134180000040c1e9550000794041c08451241c111030341065107055281028418030074040c81b00c00d6409003110703195240d5105002e102c0c0c02e800300703e004c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 233614 1250 232364 232367
    0xa02040504110301140a06140702010512070203030601020d020706080604050a0905060108010c020f060118110c010c0906030507030504030c0204050c0c01050f01050906030a05060705030a02090d0507060e01030603080301090507 99
    0x21455100c203400600b8004194070040c0118082e5040f02d000c810b441102c1e00000c0c0c2000a1304805000310340108595034001040d80e00c140000e004401d2040c10858681043c420600444540031100200142d00020030080c13956818481d1024400160009250319420543c010389000c4004010703500440e0b945e40003c065090a4210004058207c416143d5558450301042d020703100e000908409071194620301c4012a500090b154100e0b00011840810f442c1d481071907402604c4030750145c00d2126030621190068000a01c40c03625801055100c0c801210f00d03000d0090207035800107102e0f80c1410f14100030840882c2e080000306010f194120780024007561030030107246260041d81e6890390301b980780500f00300c0700807960071003141a035408640c9214503a82d0001095920400d1110080c180d0304000040761850713010748082c42c1c0241c0083c8025042440c00c9001ca0b0300321388000310035209a4808a010407c082e0401d100d0005c044003840d040c05028155110b0034050301c0103108542a140c0e0350400500a0b9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234864 1250 233614 233617
    0x6080705070c030602070b0103020405060a03050303040f0507030c08070501080c0301050108060d030201020d180b0901050402010c030305060a0b03040302010203070306050405090703080c070b0705070e01080102030f010905071e0906020f0a02010207030b0a02 112
    0x1180c1c040350854a410b00c0d4240707007c000e602400304074002e900d050301054080c0352400c100c10440f90f0000c01107103540c0e00c5035540b83c0340d42040c14085401c4c1c800c44402100082e22100304401802d03c0d8002882c010307207410001080e02c0b80240007020262810001800182d80c0807425a60000094460740344c1c2c0d25840c5400c9009100f426019100c1c1c82c03801d03408240b1142d0b000460b59075140604030b81261030320344803e558220f0764140c1c0c0c0280810500315240d400240290080351f07010100034180b84c0030b06d50303130004a001a0f10403902200141d50020410103130f07640501ca42c2003d010b003501d0400c440d20b000e1500c0c0c1e564074818000a001d1450200d243c0c074205004006203005070081d0403003c0d458500c2c41c42e103603030f0b103442501801075481212000450b00c044140b09480c414100c0148894050340b900ea24000140350150822040150540d1050070380c4044052840c403800050340ea80709042e2400c88002e08010b40009103074242d401c03514007540542e80c0040c1080589402481405203131b1a006002c8009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236114 1250 234864 234869
    0x50709020a0504030510020a0906080c0409050106030b12010902010210020c0c0a0305011407030507090306020702030a0203120301150e0a060e0109080f01050a0609020306150306040b0603040f02010207050105030106080705070c 99
    0x945000003400030721168000050021248200100d88400314809050343c00da0003000404030028001140c2000351a100c0c10000d50030041c9e8403202807410781c4a003c0f02c000d85200f6004072002c20b440302260344240c1060f00161807070600c2030000700303d451700540c0001d44030300071403040078009a000301c3d84070031144c420300c111440b48000170190b0351619502e11b051406406601e0441327082078034030300008419600a01409216840b05ea0302c80b42c1003030030f65a810000b03411100c0181d17014420082000d0060310104a9440c505500145494a0350f1408015004c048072590080081100b000d407100314075151444e10f602541c60f03500300745a824411400480303194684d03a005a456100301d9100391140709041d80b00a0088030042014010681c941400e4826407000307407955504010100c0e102c411101c800c90145801c000d0003807020842802ca1000660b5503081981c00340c540c0b608102c002d800311b40e01081020010102820200d003558034043c80030300395410040c003000920600003011800c0006400d40b0001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 237364 1250 236114 236129
    0x1d040b0306090606030607020303070c08070c03050102030403170108010207050c04090501110f04060201050105011b030c0203010b06040305030301090b030607091205070b0406020c010305060a0b04060302130302030d02030d0f06050114070507 105
    0x42c0c9460884165148025214280203015071000700d5521440481100e1040c801c6840d4103880d00d40c00e954072070042e40030f400181d0742e03414040404030006400703000a500440c00f0b642c038218190319041c0c4441046030b040e40841c2c290f03841000543c0020b580070a800144130000c40b030015001070325041c25800b400710646450051800000e8040c50302d182a00a0400d4540641c02003000d6038984e001500e40c41c45414860301821961000e078000030b48980c0c20384a100e403002e800459051004004241a0f40158000300c42980000c030060004580900ca403512251048009200e64240030b071014210050328041c680d8035200030803660f03040c48002c201c031400030251721405503511940d07802c00a44a10103000840d00190600380410814540100303400c00761502c0007503d901d014074008086e4002e502c0b0703440c022001c284044d00000541d40070311030842c04e64081d4000d107540c1d4052000020444118400f1200418a42881071060b43d0b0b210135005040319405041540c2c0720910f081940c6480740560000a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238614 1250 237364 237373
    0x5040804050612090d0801050a09020304060608030a0c0203010b04050403080c03070504030503030a050402010305100302030601140103060504020a020102040f090509030901030f0f0507020706020d03050103051506060d050408130b0a1d040b03 105
    0x81c4091110440350b04c80c00f00541685c03414116510b08030390f000020721403942e205020a00c01d101880c10f41d402141c020b032044800103507090f6124035040c159004904404089100d001c0c050095040078065034510803401c480030406498160b0b006020210090000c2c400d240002c00011503844c001c01c1101c0207580c03c5012240c491428214100c0503042c02c8030120700007420400400ca80460109000302980da000380600003980c01c0002400c1c2070113500f030755141019101e03000001e036505d50b440200350204281d80090396890900204500c61040f540c00001301d6841e1200b0850040c00110560b09405070134030300810725181c46035820700604090500304800030314000500406a80006108048030081e400307682c0c01501d204015402c44500f4130000d03006400248160140240e4a29400c0d0301101c014819410880340b40c071100110340c41240c046030f0b416030003d10000b18940c2c2c403180070010901540b48500c0d000d01160300030007400d0809400101004c214410001580d00c640054200c00c80150844 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239864 1250 238614 238627
    0x5070212070308030103060c020a020d080309010605090f04050607050406050702040203060a0e0a050103030e01020d0507021005070506040302010f0b04020a0509100306080d02030d0c09030209010b07020109030602040e06040b06090102070306050408040506 111
    0x141e035035201b88400c036005480d15250740700a03800130458251072a00180160344000031a1280015640020700b50034041d580c0d0f001c04500c541c2c801460030300032044007060484500d401c0ca0618680000580703580d091220510082010680c03050485800c1541600e015850f07071145002304104180a030840c100c40301d0030400f001076024141d48054103c2e030013581d6000d0200b54101c0107980f41c0005410020000e1801c0211202504003591a0289551a841d24038500851901c8043c1407002c1602c0c101d0050351a02d201e044541e1782c50049000900089504614040b80c959014001d8894521300703900031401510b001071311a000c3d520036001030200505550b910541c000009407a50302103100304204030710f00407101d10014441e8042c0000c0c4c2e51f02078003026040c0d080510300700141d000400100c0c1000106500400011b903980040e10041c5614210b00c95103060240c1003005441001600c030340500420320100b42e2580c0c1c0055075800b2a03802000005007512141481070251040d0380203560051030000340c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241114 1250 239864 239873
    0xb0c03040e07050c070501030501060507080f0403050f07030501060503060609070e030a0203030406030c0909050408040501080a1104030606031202061504090201030b1002060402011803030c02090604090204060807050102010c0302040b0703050702120703 110
    0x13003420305a01c03416902a5030701c800054049031b8080c020900094002d10000d00002d40c0c03e4001d00d03284111800c61401c06641c1d41d0b48901e809a01c400720099900803120030810000240604000742c04200d010f802e0a281990104051003801881c503801c0007010282c19219403020b100c0ca94803581c01a01f902d540c0d41e11800c001e4082c1c013161030b03a03900041003428005001116442580d0280b60301524040c94140b8003401103400f00d101502510002d980c5402030588000042d009000951081d100460540c3c1f450514544a085c40280c0f4819074112408003c40e0015005020001c000210b41c0001ca003000c60004270000c0c62501903164202c16011010030023290000b51031407082d032003642c480d10a842c40948580c2d502d80684402008a190003070007200524000c00d900368000e2000c2d10010361506160001410785a1503440341200c1c0e0086881441076580c28000c940c130840981c01c003985818541080101c02e4403031604c01800704240440c44108554a15240c070706401000401c99000b40d449050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 242364 1250 241114 241117
    0x7030803070e0a0f03060207080d020c0105070905090405070501180806010305060604050106020a03020303070c030302070501051006080a02040602060402120102040b030108030a02010b0a03050606040e010e0109030203030405060a050103020a0b0c03040e0705 112
    0x1104404110752516103002d61a00c212000256059184110344e2075141d036503094082d40040b03400b22030a503130900c00c8525000c100d10281448940c20340002c00e007410704100c003414940d119000140111a844c04200c0031800004d0701d5011160280b800102507188041140c0c0084110b401203007842c0540340002041c00800580f841c006c031310481d42007100c0d90340e0300d0707050780d44400c040c100401580007803001810407030143d0703290601c41c1c0c000d0034007528100c80f55071007500f100c1044404002501111009016056000b550961f1003208040214641030900102a43e01d0b4030040c8020311452940403800d0050350290191070052440c4901580ca9585900c1c02e00d469800a8803503000561805190707900c1d626040d8440000c40c0c0c0c025000e0106034a0f83c1c024000074144a506080c995901c901420b6031203002485007001140c002c0e0701441e12810246045810407401621643c90542040700510242e40e500c1c2c218800c6441d640c0e4442c3e510b40b60703900700030704600a640c0104914100c030340800169540240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243614 1250 242364 242371
    0xc020604050c0102030c07030303020f040302040c0201050901050c0c100513020a03030903030f0302040608010504050702150a0605091602060c070302160303050405030d0801080c0402090604030204020706140906010509040206070201030b0307030803 108
    0x90035039100c2e40e181801213a50f80260054990182e00114003000868000d034018500f403d040c07600c540c40d082d02c1750041350648800d4100c81005030f543e0010092550300c02e101e413170b4122400c02c2c01e82d403030a508282003955421140c075441005554440226450880d41c0614840041d03010388814859a52820040c00e118110300c403e901059101c200714180034484d00c221411788510341c0713421080382d09250612008100080c0040198843d031001b0342107040e041c2e1012403041562550201741d590809081c8803241c07501412060300c84428070102d2482d00d4001c84d6055204030b640e141c868464002c0e0904074503010a0003480050005880004402d25a100009000340e800c15400c540240007034031011034803410244201d90329134203c41524105460560000c0400a034018600d501300368403600050200d900c40403007140d10b00d40c0c40345401071204140b01e80c1c1e980040001e025100d40e6141601241d0b540354020b00081c4030b2840014400c045a01a50001c02d0b90500501160041030b12481c01500030360044d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 244864 1250 243614 243623
    0x60206010801020c0d030b030307060504060209010e0102070803040308030403090b0706050403030b0306040203060106050306030a050102030f0403020c01090b090105030604060902160506060307080a0b07030b0904030306050a050603061e0102010e010c020604 112
    0x800000c64000014002c484019040030018a00700300a00d50031001030180300200f40d40340c00100421400309000b4041c450180d4081c080043c1d5074000200003401c84075500c20320034195040b00104104503400070003520300303c83e0000042030b980d9442e45021a0b01b10b10136000212082000304031013003072118503441184a580701c1e0300d0422241841904050352034004580081d4580e004000600c4001d1044010307540004002c1c0c00c0300d0814405a83c0c45080e80c10890710701d101c0c481c50b2002c203c14141e040042c40014032080c280950303410300740113038180f40d0321031121301c03c1c14014008040742581e00c41c1c0d07001354010442000115115108120100141042c115040e99a0b106d0b04001c0b03191880c010030303500c0455080360001c02c494035a42c0d65032004250000c0c0070505156940c4110740d0152039140000c0e208500c81e03a000075406040034100400701503680c0015009101c14010481c0c1c9898070942000007001081c0303038010382009140103c0c090500c1044041140d401d1000450707003140c0005146000381d100313 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 246114 1250 244864 244873
    0x70308090105010b0c0c10030b030102070b0f010501080906010e100306060303030902040e010509070501030e01020c010e03030103060c02011109010302090316090209040605040203150d0302010b09010b0a0206100302030d1407021302040602 104
    0x784c420700440d0b030185c8a0126516004462505411301c1d1a40c2c0c203c0b001c003510b050100310b80e032020f8006800ca0304504015a00c840c0d8607420010090500429280502401d00b402800f034184034a07242d503108014001c00d58800b118101181e44640100c1c3c400009561080b02408041d4483ca030040241c0b00f00c890890007031b03090a2803c107503500e041c001d00307110340c240d00c2c01406090700d0300740110f028000214000b030007558200440d14a800083c06500480074006004540e070b5450f503e000303130446880c014070320304591600b41000350700041c0c1d2080383c4896509103030150b112815a80041c1c1085d01603202103c2c003040380344000417281d8958015015032041200d04000b400da40f0b00034841644000c49070044945e11500804013240350090f83c520396a80a03100000e01070007400d01007140b06000383c001d02c0c0a580042900c131403050b4100a61507209081e120300ba0201172a40e80030951314580c0711440820f1125191803441e0488000c030507640b9607900140242c000c414881803002c001e5001c3e00891006005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247364 1250 246114 246119
    0x608010506030a02010e040b0a050406030b0405151506070201120c030b040c0302030103020303040519030803010305030304020f0409020109030b0901020c0102040b04060906020601060c020f12060a0506030705010e06030a020309030403050307030809010501 111
    0x30045804040d95030181c40380c1b099041d0318400c01004001d41203149a0100504402017082d48031480b4100245206917480303d041c2c1000d0410303501e801014007001c2c01000918003000b81d40840881400454001502d545807200e07160320040eaa81c41d003041580a141c2d240c01400003c1d694540c212480301c2c2002d4504001da01c0d4400b000f10140c3c4002d020107501075001308810845400c100c0000c0f14880810700540e4151512940c508040d94000c2e032050f170307413544040240015403804084001060408490400c00c000f015400603102c00103500c4080c100010140000f21141003c0d01110300010720b00340210750300d0752940502c103495041b41c0105070024003c4a40840c0c150300000d11641601c080c1d1704c0d0b600300c02e602c50b0b0070045010741c80102103801203403002d82034000c107a0400240d80030307d8101e4030200387d62800d28185481c0000b0343d4049810030030100000401619840102ca0b0020700300c00d00036a407507a0302c04401d450341c4035a41c4003d00d80d00c000a800401e250f80041c4045c02040864000c1c850360341d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248614 1250 247364 247369
    0x90d080106030606020304050d03020c0d0302060703050c03060907030e03040503010c0507060e0106050105030a020901090506030403030504060b0102011107020d060605030a0309080106090501050a0506030702011401080a0201020105060d030801050913060603060608010506 118
    0x40007030240c5401741e0700c200030034480752a140515078003845c464030403a804400c1c69408511007406034001203015a029005101071941c01d402680d41c4004403070307422411450488009142828007600d9a018141d442903900307200c00060049502403c2c0180080c00a08541d12000701103030312021054403824941009000e0800041c0150b1007120070503525039040d901c90040350700003544a6042141400140100080c082c1c8034900550310030350294030005154a000d0400b4816034281d20707195411a403500c0c400c22844482030003950308098060b584028052502e10b0660024041034008030390522880303079098101079000c2c1400c000d41300000000e100f819a07415090050312130a0140d40c1d4404004442401f0504000c0090f55000a484c0f0000c50b1910f981a07107500080400e030050265500300c180580f0a550f024014242c200360305440c42c110351003031030b100280341c2c02040c01068130441101002c1a4900d10213280c200ba1075800003410801ca903034900d40f10001705850f200b80c0541d0f50030b202c005911072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 249864 1250 248614 248621
    0xa020a060f05040201020a030807090807060503090d030606140702030a0b0103060207020111070501020303010b0703050d0606030c0f020a020603060603130501020a020304050a0b0a0f03051f03050102040501030506060304080403020d020607020603090d08010603 113
    0xf6541a002040c7c0e010a42d40c0c140d0303004000500650801c01398260010703c0c10020443c50340142400d8440340e0350b03800c06401c114140035a0300206010715050003410000743d0740c04034440b0100c0b0303000d10441c1d440700128400030381030030b46034000540f8143c40c0070000700c04c3c044154010000903200340c0303c40d4081c540141c0f4a03501c601803489914090703003052004200c00010300b170003030181c81c3c440c0c035181f490450059005012500c49410280c0000d5590006022540d00a1001c5000348480c3c0003d1124912903800502c5905c001003401780235080100c0405c01e84c2081c8848408907a500500070364032041d42a40007952a00a03215541c410014142d00140c078405200c11103000301d000d079440f00320015100005030050100941014030403040c50f50851410002610000003941c820400940c1c0d507440c0000043c140d803009840148221400c000b8000002c00c0d0000700d900726070707040d120004036201c117000094080c06503901c0a90091800030812207a070030301046006940006442e000642e0340c1ba03079401c8007203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 251114 1250 249864 249871
    0x30605030d0906030504020103090f050705010206010f0f0902070602040803040303050c01050106030603050303040f0c1214150105130504050703150912030b0604031b0f08030c070909080301030303020703090801020a020a060f05 99
    0x800c40c0034a050040d0f900c80c0d044694042d0060402041100e00d82d5a5000031149110055a240d00101414009580d05114850051468943d056125424000000c0e01c01d20319108004007194002400700420525405440050100303c09594455903241006010396000015000c1c43d075103820b0022800c5d501910641c81501e41201c0114215501c1d591000c0c101031040c0c4058510980d02e9000141c02c2c0d500c12a400d00c654410740e812280034480d139545500d444480500b01102d8130f80c200061202d51903600c05040619441d2101181d50780700d9050990605601d038002034894100040d900b02d400425801c005030311407080318003400781e01100c0310032000c44005444450384900200000c01c046200760217114071610118001784009560345900d150549070982c0300742d00c02c6d00701090051140f2000e101840041071401c03020704c0800c41603a05c070038540c48140001000d241d40030034150141486050b4140240c558040210354a5941d501e000e940e030b90085000321906401c00c914651105a9801060300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252364 1250 251114 251117
    0x606050405040c090902030a0203030c0a0507080604020303030402130b15040602060906010b03010b070302030409020705010b09010e0c0f030c0705070801050115030902030304030605040302030c030301060c030e03030c0d03020c01020c010501080102030601030605030d 116
    0x2480c3c2c04d00c12180090820001e05070f078948a0031072440d02503030b0248001c00d1003a1603240240341030302041c0341080c1400c80383d0780104a1034001d04208005070300c010084950050b81211541800048a2030060044c0345404d5400d400c910441103140309180b90100070701c2540c80300d8081300d0165a0303002d107040c3d40d55024000d580d41003209000401044c030313007180035101c02840780c010b403800c243d00e0f015000308a8204401c180c455039104c02004500c0c0c00c150744400e000d0400f14030645500e140c113080c000b8851081c000d084840300c0300000020301700030a100a0719505a4804240c40c10030350b84030b0a581c06000c0038081d40030318003010106072107510f00a124145810b940640990700307003861500d0b04001020010815015401304010100388500107100031406416035885241c410480c078103000702510000d08005009174020403003018498000548100010201d00e00544e0710002642d0843c0039004000011035150701b020000708041c00103401a510885003030340e0402155a40d141015a101c0e8013101400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 253614 1250 252364 252383
    0x20a0201030e03070503030c030406060b04030302030f0306010306030b07110d02072301020a0c030b090712050a02040b06090301060303030204140102031306030c03020702090c0d0c030209030c09040c0e09030403060605040504 98
    0x40154000d40054640c6501d02d07050380e0030018251100390550b8811140076007061000020407040020b244100b0010700b4480102501301800c65502030b6880c441d614007920182804000949541c0c881d42000e4050746e40804036841c282044540602010f510000500c018002c01044245a40c800a01e10381101d00c803216109115001010b8072220007031402c0b103541180140ca01e0314000c295001c46000096200d0394544031289003640e9045d007002c1d882d800140d0045409100940440c0d000034035903903d507404071000a04166a00e001820f10301c42c52103016095402d0502c0041499003540c0680119003540c40c00070103030704103040126280d1013401c5e03640324881c0b01c2002c10300c800c51083e4809012009541401460514290001003410200310380d4400300080c00905d003862130300d46000781c2e10b101d891801c0035403c1610610000fa203829806034414040c08800c1c0008007031103289045200244140f1814041780d0a1a2450940302d070702c1804255407c900b0444001030b5802d00340300d0f19118a4200c0030b0754 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254864 1250 253614 253633
    0x606040302060c01020c060403020a0303050108071202060a020f120a090e010e07050c0309030304140f0405010b0412020105090907030b12060903030106030902030309090106090501030b0402070f020405060105040306050408070b010905060102 105
    0x301c0740d500003400105113907600f8080040c07000c0f000c00c0168043d40c06500207212040700d602d001002e4520503040802550080e81041211528911701050036541c1140c02c145c40d001e108408901e00348804030008003c2c0700c0c1c15110800c070302c42400200203034030740f40c0c1d901d07802d00c1d1301e580a034440035500380708070808000c0036400189000d00c42c4002c0c1807140c48250580c0c0c541602c1500091a41d0841e4201d20081d10514003190300f98582105190114003080d0b40600813585020702c6d10102d4001c43c8100d580e0491301c90a01421603102d441100c072641c030000c080036818103190000030018144411428000e030481a00ca03802c10318002407162107017418a0081d0b00d0751b800c00c04120068071300c0709412078040c0f00502c8101d101d640e50b90107490103000c07035586520640385051b0005043d100c001140d58016481040010301103110102460081c58050302c01080c1a00c4040c0101c44034480c0d680b001c0d00003031a080500c4108a4840001e0161038010b110800050341c03a40400780c12a04255a1140964440f03c0d05 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256114 1250 254864 254869
    0x70204020c070b04080105010f06020105070c0201050a050405040203011212020307050a020f0604030204020a020c01080a0e030304020607020105070c030f0605060a081b030102040b040602010501030c0602030307050703030902030a0206070305030402090601080606040302 117
    0x1c1c070031080c8900541c1d504940c0c0d81940851038000f50080ba605075155001407040303044400c0c3d13400040c2400e00c02400507040598010b03003040c4070b943c1c010381000b400184516034030780900d0880c0c0007880080c0c021992503039948250f000c5045607034001c0795100035a1030700d46030300c03480042a1044070b6040b0010300301c030191b00c1c5e00300b0040041480009400060a100010140c0c0d00d0f03101405980c50680c004e452107541c90000100910070003042e40080c280783ca0271001c0340c27510000607039510035810780d280c0e0f0355258140010794040c0500d800040990b82504000f0080101e910001030304141300f584203010720b4585400300300060000e07001c3c03100268403c40140480d0030b681d00000410b0107001d00014941a00d51014540d00c0c0e100d9000040580c2d10b8000400400c41018014030003056203101a40c01c604014070010b25034482c0c403d02404241d103401c40f14003590b4092060140f0258000c1c812651b8652034540980242c00031a02a0710134244c05001075402d501500b1250321813180200384502c1d05003541d08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257364 1250 256114 256117
    0x109050901060905070203030405070509010f0603050a0908040308040812070b070509040e01060602150906010e0711010b060d0504020f0307050105030a0c0903020306010e090f010b0307060c03030b1e040605010306030807020402 99
    0x100c003000d5901c80c4400a160605071085602408090b03024590340d01c0c207820040d10b4602181d101a01405090004104500424801d070059034407602d07020035161248000341c80074105003070014020303002c00140002040030f501c0041c0100c80050007600d030419050300003208603000345d4502a2118003c4400950002e20070002001d00030303001000010710428018070070342102e00ca41c1080e005030388a01c2c01d200e8425410160280e000d40c1a5008100c1581001941a40b406001c1d00e56807d004d0002c001c414524030a4008003078800004d0015a1a00301c0c0701e600d0409404c0c2941c0a03402128070403022681405c0104840c0142d810603101e407851600c896000741c000f4034034200c5100420981303040c0400142c1d400e00030300b4000c00d0103444038402410449070712030402060f00300c40a40c07a80b412250300e29649000c2085c0741100d0850414005025042c142a4082c28114408550000081e4003120160b614181d02508107003080d0344c00c215468035080103400326a014000078042c4141885128014a010780 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 258614 1250 257364 257371
    0x70b0304030201020d0603060606030b0402090a03030804030207080a08030105010908030c06040b070c0602070602040302010311030f04020d0201030e030d09050705010201020a1403041a07020102090108070906080a0f0b0a0801020408070602030f03010905 110
    0x20005150401c0e60b1440d1080303c0c0e09820071210181c584104002c0705031b150203000e90ce82403c40b411403520030690300190000e0703428030004082c449103400240c2458009d0004000403c100c034151003144406140811b5154024054a03020030710800002ca40000008241c0726942d607580028005602d4903102c0140c1048000c041004111802c401140005c5050014212171441214056103540c15031001405860702800d903110f480209004010140b211322801c642c1140e0181c0300740240110b5170004a000d000c2080540d04c00d84800241d0540c1c1e564158041003205018406841c1ca998030b0304012800c0c1d00c10310440a00081c1d0b9000078440b058216802580c0052007140c58941c0712180b40300034004200c04035080000b503540451469103d503004550345510002c0e82ca0b241030001d05040d0080c2c100c1c00050101003a0315500d030481140e4405540c04015101c1c401000703200350582d03c07000e842c040d5120b4043d4803001c2c0604000050094000025200c15484003d081c2e4103582c24810088010140203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259864 1250 258614 258617
    0x90303020d140d02040305060901050a0905030a03050705070204020301080a030f05030705041403010b04050705030114090610031505030105090304030201030e010b21070504050403030204050f010f080c0a09030804080a030206070203030702070b030403 109
    0x10000f03c50015002d04c0140015482200030b420f41c0d10740754000da403c41e00024095800349040003e41d200042c0d02000326002d040079814005560303299102d08650030700842c1e0000390001c0c0300000208a00500050b00c0e00c0c0144a6519818a002c440340c0440303d80c00103680000c04a0030a00052250240c0100c4501500f440a400058886d41d14000141950f03000d41d10800481c50020041c0306500950342000004038040d20208482d061000104180390401d9844c1803c06580d6150512400c0460307458000900000300240300c4c81c24030a07683c42d10380d8407238801280030030728100c071280c0d4078581805072481c506401001418102400303544002290703205045662140a100c0d0003151603580c038408c9a0003140242d030010303110382c14070342804050f9480307500040c10320500c3d81c11a11100d5000351519400740a1402c0c0f5902d07481e244206071030840c25500010140980440c021078008800901c03086000c0c003a600b26941e80d00d500350217a84903c02590f2035070040e04800c1c014070000a1040c002e50b00316109 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261114 1250 259864 259867
    0x31b01140d06060305010806070201060602070504050a0e070305010204140108090604030c030212030a02090a0b03040209010302061303080304060b01020106060c0c05061803100902010305010504110d0b04110c0303010305010c090303020d14 104
    0x10070000808695140d00140c1c082a6100b0043c0840c02003008900d51120355400200003c600f0840f0195880881d07104840c030941d100c00c00200c0014a035003100f801d00d40e411040341c60864503440d00c3c1b0f001c1e4106000740800030950203400501588035400301030242258070003605482d00c494504031141d290b0920180c0a610a000c3c581e4035030620500250f1164844800c01600c0368040c078204694200707141d200d10020030051040c04056070b11059803604482d41100c03540c0c0c3d50058101c80e195907561603803000e08000004402c00c018010309800c844c0c0d15804c02d0f80200b002d1502c645068821231044140034200740000c0c0390078082810483c1c001c0500c141d45541c01d405455102000924152500100c265500c0e12060100110358150150902501088800344061039402d000c5500c0350090040b5090980d4a602610050b0748881c0e104003001909a0b0030103035540c850a14140c1e90f644203103c11506503181005490b0114410480001a80c1d8954050400140d104600301d44048459591a406200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 262364 1250 261114 261127
    0x40209090106030504051005040803070c03110102040303030501030c0509010b0a0c03020106150f03110c0c040207060209090403050c0f01020306090403030207030e0307150206060301020a09050d030504030b0a050a0506031b0114 99
    0x160440c240c0c0c000d0000d0781c1e0103d040d00c0e2510b8054107021803585c0003141d0b2400c120a020000d8081d10640703501013243d2400342a401c2e100e0608032031032500342c27080b00c01e070f5440001d0110600d603154202c0380c1030b00d0003881800c01d100d60302d00900038000740034850003000440920070011018400c018903c40c041c020310012850725116428240c1c041016100e2901103413010800d1884590180141200d44010034032440c20030b04141d2106843c2c2200391f008920440c2c2c00140c0b141041444c1c0c1c10303980500000340c0110154030f8a0316000e0a2680a900501070900c02c5000c0c0046000050080b2881214081c03e6801c407038540b036809a020b500008070440c10300140e0800e9000b80c1e10100720f880000d1181c8074101d0000e81d11254003904190000c2c0020740603900400920b03003260740140ea003104035442900c050451050360f080c02c130740078003803a003009020a14480a000c00e00189030040790040620340e00800c07241d180c560400d80e950a0b403901c1c00342c07482c1d02c811900c02d1a6005948540d030000c40b0440062070304c03d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263614 1250 262364 262369
    0x3020d050106030903030c0206010305060117030403060501060207170a050307020105090607020405040602130504050603030304080c070e0c04060e040207030c11060c011103010305070602060c03010308030c07080705010b030105060a050d0b06040209 108
    0x20400d82142000031394807004d050a16500d40210314140c0524005000d455055469032502c1f8041402079190034112090140c0c101442013080f100219000181005030b5611a84003d480300c0b218801d400b8510b0224440200a80021072020120b0703501c40f005500d0042d490340155855000210901d6200d2000c0c0030160158485008051055220f2100180c0e42c40c50b041180c03079044980d40015000d83c1ca02010402a51000030032203420503000008580c1b100d0710708210380e00e44070841c2c000c401c44000d80c2c02444200e20b042d4000e0402d94940e602e0301e42e010000754050000b240500e01c0090300142c00c1c1045030000c1880304c0202d15000c080501050303e410f034030345a02420b40310240d1101a290000200400c00e000c824070054019040d10f10180c0424200082c02e10400e0006000c05484403070008080340f0005080e00845811341d62110502d40c03110030a0424900030070741403248500a5003031800041e9035190040a0001346c480c01024402c0c04090344d00d40d040a198001c1c11582c200b54200211400e3b603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 264864 1250 263614 263621
    0xa030204051005010809010204050303040302041113080303060901090209030c01140c0a0311060a0603020306040b0603070315051005010e010203070605040606030b0108030c0d02010504030801050906010207030803010815010b0403170a03020d 105
    0x303a000b8018020ba8900c0c2c0400100044401400d1280ea80d205100074021036601004075000c40350102c82c045100d0040d89103000c01c61040c000003640b0f1345000100007400380343c0400514401c40084482d0302007aa80c03086182c0a0307102d107004483d41030308070781d446460542c000c1500c001c58580500740103013011140461180f901150003810340200d64003511000ca41c02040041c0b641c0080100c60500443e4a1a80800d82e1481d02500041c080c80030b500010360f0649040061600031604050180c01d0000020500c500902c4261004c00c191b80f06014040303002e5010340c0038031101503c180c2c000c514181490711800c00400003c1d02c03c0780c0b2a40c80d80400004183c040b0012400307420482c002c2c540e2041c0c800d903041c1c41c062a1951030000e590411040001090304040d00c04d0440c0ca058070303104c0c0c8070b555090040f401c0159a4000418440000c800444c080400050b52130f03c0094480d010280c3da604c55201c00c403240101c0c030004014011104882c850309561001501942040c1d05001d8100443c1e0011a81074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266114 1250 264864 264871
    0x9030804060306030203010b0301020901020703080d02120f040501050703050603030a030c05040506030103290103030e0402030702010e0109050606040c02030702091501020a12020105060103050c070c030303050603030c01061508070203030708010509060a03020405 114
    0x9448070411300c103526007071090301a10342c41100214500080000040d403208190f01c0080c1220801203202907410700c1e0ba03011100100c2000074a4200d0b07151600e9240b05000c000d8070262402d618090000b1000340c000c4c800d003802401c0c010700a40c10701d0888a0110080c02c40034880d841040302c1404001215203403000914041c42c40346201066554405825542004019456201d008068001040829003000800030749a00c2079401582e41d07030781c11005a0240a40c010042c1c030540ca00100c800c01c0c003002003040d50050304200c0b0240191303608507204a0ba60f01a0a001035880350803100840c2900f20650007a4000500600507079043c035106448480c0081054805400543d45800800449607414420383d9886440000c84904200c00d070346030150882c41501000b02816603400101d0b40341d5404105884440d25880000d010a170349440801c200000305c1c0d40300c40f011070b20400209003000d00100c1504e114001c541e98a41c2e41d43c0c42c000c1000324070b46014100717039040560260040b01603229409214130 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 267364 1250 266114 266117
    0x301060305010501080a060c0503010b03060d020105070203030a0c0203011118060a0903050303070203070303060501030c020c01080a020f04140405060102010203040803040f0206130e0f0105010e010f03050a06050301091202010506040b0913030903080406 110
    0x20301440608080092381c0300d1f5085c00302003200420051100520040969400000640e0040441203003840183c942d80b04051000c0e50520002c00e42c0d14100782e102d066440307481e209400900143d100d03090325404a00554074526a005c14a030603402d501e00b41a8007420740020305180c81d0004036502d44581c0d040d030780f098540c100160400117000c2c00341741d01402504010f1074286010400ea00790030000a4844000212103810807540d0004074604c402d540d016120452070220320107030f07982d0b506d04105040113400d0400601444c10140029000d40c010720135644910b4201000c1803940d520350b55030080480c0220002c82c1d1002d42402102c02c00262002140d01401342c200a00784103040c62000c145454405901603410040b049892650699000312601074003d143d05001c50103445a404031f001a2000c0e0300701541661070054410b040c84281910b4134005072081d0000c000301c0d00c605040c0020380300498080d94004038071001113083c0c04001208540d46a000b4601884804e460755074140e42903005901070300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268614 1250 267364 267373
    0xe1009030c03110d0503010501050304030e0a121e170304060207080d02040509090a05100b0307030f05150109060803030103030507030c020904030305090705010503010311010302030601020304080105040303060603050901020307020601050906030106030501050108 114
    0x100309508482c407128104440c0f0018400405104030051081c1700500460341003200100c04142054041d5000c00301d4808000c0c41c00020f141c4400790451080345200056400000c054100c0151600c404000c95941e900300b088113122018004611040d503101410842d8034542c204098008a24008050505004a4400541e54500d09000c10088402c0540302c6011038004038044070002d5400100d080030031411800100d003892500c0b0009080510640c405000880380d00400400c1080201d102c1c02440440b1038100ca40307980f19006401141c065019424056100300011310200c0c0c000c4000c0d0692510070f1410715404000c075404070b003011201352005c4001c80d80721014001902410710186019110a2a0540c19980756444001035004601003403414141d00001040c044d920900c2103c0c060101e14009100608152400400a09e00c41c420703000040d20306004118400018001c403406001e07581d00810442c1d013420104420703080d01030005a0701d0b643e61000040000d4083c0070342d6000785050b00280 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 269864 1250 268614 268637
    0x302040e1e040209060409020306090a060509030a090306090206040314060a050105030a020102030d05040305120c0307030501050406030201050d05070e0a0303080105030c0102070302100503040206070b090109020102010b030102030601050702040e100903 110
    0x60506009001c0740c11042024840e00808003610803007941c0035404a40d15419a120b03034011500034501100069054080c1404002c0c024a001481041407442420100120b59074294115124081c412152001441c0f0400400201d945d64006291650000b0000fa10b0142c0e00e6551881c458070114800403247c00000410a40383d1131032203a0b50041506502401341c0708a07580c0000e44038403540b4030040041d40d40c5c002140a052081c01510f0401448074240003450a00000850700e580045800b08002810180080b4060030240501000c50764180c42d03840c1441400000705001d000c00400b5a0708016490703403592515550000ba0100a50080e1181c0c02654140010f040c18031b003c04032614155400500204010f0b2540c442000c2c10807071a00c1c107551030307890b03134800540180314035030001d44547c5000d0305010703012506500a40f5141d100360000c01041070440c05060a0b4001213440c0c4d80072032010b104800150400e90001d006400758641610340010304400f510301100ca40f031313074181c00080d00d00c1050b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 271114 1250 269864 269879
    0x7030f0204031101090609060507080304050f0303040803040507140904060b01030e01060609050406050604030b06090403020307050102040609080f0105040308070e040e0304030602040608010e0105030304090c0203070501050c0c01060b03010e07030e0304080d030204 115
    0x104d00608082e01c0e100347c03141d00300b0030042d085100c0c0380402000c1860000001342440403e00000c02d80700b108605695490a007030420403029041520192840e01840c3c030b0004034507145082202000c00081c26488103a84c0f1912900d004014020b80e0605040d110360b00f00340100020b1040102612103902d8510b003482c1050240003c8a989800082c05510208412300200790003441c1c6036480a01169405e0195aa504e002c80c1103026007400105158004500401d03403035046001c0c0001d0711b828000f224446074900506a00340e840c05d40340900401c101c20003003503c03030b0f11a41111501a0002d0008102d9440d00070b07105107158880e41c010340b6580d50104007403210940c40700c071944c0100341d200da030704510f54140340002ea00ca100714401c0c01d034420382c0c46980011090003030069507003043c0c01c113008010b14680100300c41055070100008070603035440e0001c04210110303075a06807030503180303070702000061545c46400170703401005001000050f41c0710038000098002020803516070300c240140d034050780f141d144c000e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272364 1250 271114 271127
    0x8010605030102030402060906090102030409020c0105010302040f0513110307050901030b06010e060408030906030402040609020a0801080c030a05120306010908030c01090210080105030604060b0a080d02030309160501020604060507030f0204031101 108
    0x1005100b640100b042c003002d07035500030030b451040340111521941c43c00280d0050f4590701c45c680c000c034401e5001007000d46000e28194081c6040301d00a4805000300030102d04400e040719030403a00a01040c48101a00340415841458a004140090200e80100703407100d000036200c460983c421203c15410000f0001156846120800c070118160751043c1824204800c3c1d0b80c070781c007031906828084d1038080002002d65849400c40401006a003808566510f020100144400f0b400d0007510114407544018a245083c001600600b00360860003400000c000203141c0314007030748050907482c108500004003154000c400e200501918000c44000900d070005807040c0300201c03400c204403109010040380100310795100890a03644c45644400005018581c4800145d140c1d0042e800450303140c4603641c03c2d043c0c016000030046006203406c5084880361203022807809141403890181e540142c00001c04100060000d4000e250014814103000c00c003100901a07840880e0403da0007540c140400c11001300301940c1125 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 273614 1250 272364 272369
    0x5010606020610090c0302070f080c2104050d05010b03010501080a1403030c04090207030c050303010602070e0105030105060d030503040804081902010f0305010b09010c050c040f090b0702070501020d0f0c020d03030204080106 98
    0x5840c1038906051620784800c903034404c402d03c141c0c4400038990040c1c400d50468400c02d520032924038070341e41c0034100780c00e00742c101e4140c0007418440d100004903c071010080e0380d40300901c0040500d161030305100c2800341048444404a990303641316143d10b80203a400780030380c6000c1c2c03070044020b1110366401e041003407003410000c24030081504104240400707442d440045509585055a02507619035007443d084070a40800000030f00035020110000c101d9640c0800c104044915842e00c5119030f0340c0f03ca003054202e0340c069641303543c03000b4100209000240100080c5034858000c00b4403030b08103951140c40e82d05100301d1071012405400406c2d0018215a00801d41c0c03003002c0e0f02e6182c10003896041c0719904100b841142d000506001a10b404182000f1013081854991400a4028003004d10754003200700c045c1c151242c00300c43d010707030705000585018400030341841142c00580c0200920074210901341e80d203500340311455041140d05003c0750701603114030322000703c0302e03109903801a640c82c6006521421100c0d1034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274864 1250 273614 273617
    0xa09020304030203030106030c02030d060806010602070603110909040219060e0907020105090a15020408100903030608030705060106050304080408010207050606040e0706050904020c010605030601090c0f030903050711060405061605010606 104
    0x62080c071000c282c1c0041542c0c10b4410340c0c00c1c00035402c180510309034039601624140840c19810020702003040c405c0403130054100c96540d0211003406441390003e0742a504280d44c04095003000340554511845c0a0340034580041c0046c15150303503d501800d2580001e5916003000c1d0104200140224003400c100b068035620080c0f5100070081c6041500301251510070140000d803060407542604903522807a81c2c1110000c007420002c551141c0c412411100152100981c15000700389005030004480c00040121021594000e018280b01d070f00b01403040d0ba160b04090002e55032440f00b484081078501c024401420158000c0005200341c3c5050000c1200390382d19035514402035088420100a119004000c0d2900080d00311000350701d82da50140c000d40103203495070140e64580b10b640c0c000900701801d54041c01c0005455a01d039204114801015007d0310740614006000480402c00b880c0440d1380800e811f403011400512003440c1c1740e0f80310005580c54104841990203c1102002d0f442000024401c080040495 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 276114 1250 274864 274867
    0x90203040b070c0b04020f0102010209040204060306030b01050301020307081605070f05030d060504060b04060305090c03010501030c0306050906010e010302010c020a0302090709080106050f03060c0a03090803010303080115020c030304060c050a06020304060b0a0902 115
    0xe82d0790040240b00580003d004400d60b02d11f4410b5a8002e40640d0b240000280045403915038800005025040f1031100ba42c41d4003a010010a1904045c021248501d000fa02c5040c0d1a45503111149803802e800403103101003150600c40d8200144040446904a0f40a9030055440e07206107804034080b40e03115800140300e00d00c1c24000300300c8002000140c43c1202c4007810001065520311030090f0420702031019455055180000110030008032075000c40a49020300400c210660b5035620751641e4400a0280b00f1050400000400c01907210f21890360109102400c07400b42296640e021800301402136800c58080b82021205000c600b20034420400140801c0740c1910301c0e012200e0100707850b0034002e40070072442c4000043e990396660107904484240e5600c00003466403580d4900b80140050b60a0044544042c00481c4000440f403000480303202000f030040242d803516143c0030082e11004894170080322603024004807078001c29050701c059442035006a2010400d00d88a45c02c0002052140d00200c28580c030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277364 1250 276114 276137
    0x103051305100b04020903060106080403020f030403031d01050705060f07020d0804020a0501050309070b040303020102120106020c090711011104030c030201030c020d050702060a03060302130608010606020307020d080a030204050a090203040b07 106
    0x400241404814011031400a642a08240130602a03c103420754140c040c80703668000141198030003078880c400c50007503099544021611510350b80702c1c800c5100c06400a940200310b10103040054440024204d01418001e24003e40c682c1d07018244a4222080c5401064440801c9041c03501800705500204803450070b1081840c1660004060b0400d44c000c141c1042404000107c0000c0f080007410701600c41112800d842c1c5a4034030f00203001c2c1d03000d0125402c200c001702c3d0002401c507000040c01c6032803c60042000480760342d0004107c0781080b03a6120002151342b078146e03903011480050020005180145081541c071400e500015058038901c6100200315030180c00011100c9034000d00390303032803140c0c11281c56903070310030032002100070300724940021350300032200d94001510102c1a84071104a644a0001348992a5111010398480c01030290180d00704a0f0307199824006181c00008144412460600509054541e4041150707460650884204160700200740820710405c0f401a0703511480500c1c0c146156003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 278614 1250 277364 277373
    0x2030301090509010204031401020301050a0b0c0a030c050309041505040c020304050108070e01020a02040c0804060506060903101508030301030c0609080a02010f0302031306020c03070201110102090105090108090703051b01030513 100
    0x20052003a8035481d95107001082d1045004c2d012a130040d900300a4004040400d2440c06000b98006e01c0f500c2d01c10b4031110800140038007440e050342c12170350751034014146204047c4c8058443c1c1c811a07070201c8903800200400c0006540354418010103001140c080f4000ca420041844119041c40036801c1c159442030000b0025030b81e00c000c0340743c0d10007020705d08000e21500d0040140c2c584116080d0095010382000030f2030044681c0030b01c4040c803407405004180025140d1000340450b80c80346000007501600b006046189048454120420342c25040324400000c0e5542e02409045030003c4c0c0007103c40c2c0030115010082c182d400b80303c80d0058084440a018112074644c0040d00e40307412982098185034010000031003645220740c0c4001050341180080d0b544040109040d9200d501c8031078124041644586070540b41c00c014401d841c4440b4060b141c00f0b10b009569030065603942d40003402c0c9086485600c001100040c400c2c030441070240c1030b0a10200146000030005001d481004103041c58010b1070b25009000b09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279864 1250 278614 278617
    0x40b030f0a03050c03130603050a0b0109050a050402090303070503030702010509060f010e0406050403051608040603151805040804030f030302030105120d090308030a110f030103060501060903080403020103110705010c080601080a06060203 104
    0x341e050808513030f81c09008000e181140160304001c503445000b4400054569010b0b042184101c24504040004c4c0c2c65200040d91441c011780141904594041d005110b01e08155000b80070104009040b03034108115655403070b146a0085581400503510f810901010702420000341c3e800c0060768811202c0c540c1041e040b0687c6c01c4005101400701d949032404101030502550403900340304001d0712101001c94581c203201c40c0b194458801c54001a00d01480d03c0c0150410701c0328003040c2c540120420265114443c60031004d400e001e403041d1010300381000004005050b2940000720280300340c80c050385a601d0081045264004200d25400b41d07044404101022a4860300a030140c81e4040c40154980c4c035284040d04c014502c46207400481e4400042142d0805c0d0300c0c2018604880c440d41c400c1c410b580e00d8410444076813806210080c8009020301040c001580681c1104002e1110048103d0500d505030b00c8540c00e680e086003492020512000074403986592100c0d200341e00404403101441228642903000703641e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281114 1250 279864 279883
    0xa08010b04030b07120603050a050d0906020304050303030402060702040608030a03140105040b060304020108041106070302030301030b060103020c0304060c061401120b0601050309030a0c0203070302060406021605040902010e040c0309020405070509040b030f 112
    0x4221030101d403201c01340251b5000c04051604401101c80401441c0780c659a6078002825190204800c464000b03025172000003200c00ba100050083e41c156100c42c0d085c4980b5410512003203134400d40f01d220102d0001c0f000c101400d0399044596020032000120146a0308101068004501407410700440107096101c0398202c1c4c2d045507081c64a07880e203907120b0404640424a14881c2079110400160044c241503000010b18141c0340120b1408076141c6440700154100d21504149000540081c0800c100c5e00f401079422900e03c500403031000c42d864101003084002904241c00036016582010314000604c03900c0c800740c0d68401001e007095491030610504055482c080c4080c24001c02041c03141d020215141030001400444e4042c1c403040d110346c1c9130302c0d01a4451a24030066000301e1812900000d691815006000210390182c480302d41c601c40b50b409200240c000020084145925585110b006807150b200c0d00384141c03001e03030350152181ca050040000340d0301c2c00c4074036503c40d501104a03440c1100022404466 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 282364 1250 281114 281117
    0x70201080103030e1201020406030e060105041b0507080c010203010906031104050402090606070302010e030a05040501020d020303040305030705090111070305010203070201060e0108030301050402092701030213090302070603020a0306030b010305030a08010b04030b07 116
    0x4c400c0b02203400078114809601040c0e00755400400d00080050301904150912003020007070300c4140c1c0e00c031801d00049a442038550f072500180000c903a500070780204002c260940c05407070036603e4802510400c0d82607034006e911554060307556540800034402d40350b00c4211054403c0307505000c0e03802c29400003001d070500503020758170800c000101d040400d4000d40c002442c0540c100d007501d444d070b40451005011038001d131240b180075014001c03046140c0e03880030044910030f03a816100e0a04644030b4400c00c80d0141c108103107484c14001881c40781c22504c41c04100610080d4411400035036680f0b8030800080c25120564401500403e010700103000214011090701e0554206950040e11048035100052480c40010521240360f4000d10100b00c9003494042031605984c003c2d249150a106005409402c51f03006080107070044e00100402c1c00210302c00d400500403001680f80104180d9226111140181801e91040324281d00020707683c0a81e40c2c1100c240b600502504d01007508203071031611110b0080200800300360 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283614 1250 282364 282377
    0xf01030b01030902030109060b040506010c081204030e210706051c0207050109020a03060203060102070e0c09010305070207150201020904060902070309060c02011b030203030402010305160905060304022103030a0b0607020108010303 101
    0xa49648a6440740f003040750020001c1c46081c40e1820302c0c06c01000503180282c003a504100000b091540120744852040da03201d000140f402c242082c42d1070781c00802400880c2005108003c3c085103556441d03a0917029405a0703480301d440c0c400d2038051840c080d02907111b0b00500ca810303c51244011140d180ca144080d0401c0005070755041e1a190241c010036000b00029800740d40d152012003408103a40c051741c0b24030420303000c445909488094640c1c00100441301125402c008002c200788075442608016084134103801100c440f075840b080c0b4044001480307191280140c1d8042401b000760310b0107000759030050904590440c980010750f14020f2040005019803418482c140c1201d40459102c1c00c1e501c4007034510311402540102e52458000e489a000351402da0020b405c2002050100704022280c0d2400c02e00c607200c0c11403240c034003800d014164000800603648002ca6001e02c3c0404080c0b078001e20007151030140555605e1510001d024201e0758400840e9003d50f800303004108c0143d0300620014150380e01747c2002c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284864 1250 283614 283631
    0x901080c090301060303020a03090501020102030103080306040b010309050f01020706050606030601090303050a090305030a050406080f090c010309030201020d0509060103020901060309050c010305090a0c090204060e1206010b0307020304030b01030b0a0c05090f0103 115
    0x4003500d110741c00100c1c2e055032070030000106140d408203829002512039503403070800301e9032040124240d00003070202802d94101080880d5035481c1235407142941e14410304010580c51029140d103424814180b00c1004135940001340c0d41d0810800c2d00c15554046021030343d0905504080f00000c0241c001e602000301408000150070f00c000e17004900d801c00455120701107aa481c5001038000340b0a80003440764801160303120300451080b404140c18503100da0007400080545505000044025180243c001e4042d55030812030031607210303d02c0c090f0034030a004040041505525500c14442d00b40c0050340304004061500c480340c00098800320388000c0280003444c02169640f540c50407079003031a04180780208003400071607001a502c3e100350050300840703e081e100c1d00b020100084c18040c10500105031784500341c00501c01404881d40e84d07000355070819403d20440c7d0a00351655104a0918001c0c3c005442940d079900401c00860000c2c0502e407840200c61414605011f110720100b40c100004c20585418140c80c1d0094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286114 1250 284864 284881
    0x10061403160e04110d0f050106030c0504020702010c0206210f01060215040302030409050601050c0303090105010801060f050102070306020a0c02030303090616110d08060102010f0c030b0406090506090103060506040b090408090a060f05090108 105
    0x40e80d032442d4000c51881c41b035110311310b021402401644000c985200504070002140d02e0700d8800e84801903010385424101c41540c0c0d00b0450310b41d1041074080a1442c144410301080b00c0310300700d1248104003514600146506100d000b83c40c00350006040c10381040e82c1c904100002e071307000c400e603412200044400b05141e01c07240016203450103075035000c0d00c3c00d22011040000605054000703904a41001e8003c011043d100c01d080504204503024060140e44071010400005040d035004040d0241076181142c04001e40c0c0e40060300307640c0280c8445560307078170110500c103050581940504c0040c2060800c04106c511422045486240b48510a024859032800180281c5d00030b40210040d100c00940c1046440e020840180013010f105440034040c1f441d00741e01041c01b41c441c1c0724443c010b2100400300c10303540e03281d5610ba1001c0e03c03000702801d07003241e2a0307a0000300586460741800d010b2842915202c1d1a407019006002e00d54201e6071200d410482056940104070360420704944240c0001e11742024a40d480719076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 287364 1250 286114 286129
    0x150616030212030403030c030501050603060102070e060303040504020a050403030e01051602060304171b070e0906060603040501090605040305070b090703020901120302010b030703030203040501020d030507020606011110061403160e0411 103
    0x30942c8110300c00001c000405038103601400103404142c404104590f01d0700c00340030240c081122040e0240c0c1c808801400002c0f5540169a0302041c0101242d240507281e9010409a80000d6000d0002c00e001180601c00c26410401c1020421002e00c2e0042c1408511481c0c0000041103510280c001e03d8000046028441d01e00e034105010115a2203080e030b2040360a1041e030b001d071741c0d50f82c5a907200e000c0c0c0031000c140030740d400c2e10140c06a088000104125100c0ca400c00c1030652028004841a6680d040c2580003d04d850055910450182d103c05481e0255814201c3c910b410040407203465412a080600050360f429048606580340041106020b03403961400b64014100c6008080d85841029000420194004020410b440c0c0a030309a402d45480900190166481524800b0160304850001001035104103200000c1611407012a0540140303103204204480740da070028030000203521012026030904100c20321240058040c0c60703005d10b00c3c042e60b182c00039101410081c03100d03005080d03001a50b6650070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288614 1250 287364 287383
    0x904020120030306040605010e030607030e03070507030b010510020307050d050307090302040501150e0a060804020d080f130306110703020303010e0406060312080f06040501140907090b04061101051506160302 91
    0x89103040051114048540d0b203400c1111810701c283c2c2008000300e0954880c1d20100a0600d01800400d140d0725000401d42c06007405c100c140095203c28408407000c54030411905006501488061502c0c3d4104028032000c480e046030758505661007000608000380000640d00040c0070946411070703c0384c0324a9811956892141d10203580306041c18008910528820022400d041c52034035800b8160103414140000072105220300c0000c0b4003404009809410075440203203845104101d5140b400746003d0b24402c980d0040248000d01060210060040003c82c1c071913403c280a8401e4002c2c01c01a80381d070025582c3c401405141d00140c2c4542c0030030100f00151300081c5c080d6030b02c031032422000240640000c0c2590350403030b4907041c5500072034041070990400348a440e040c1c56116030900003c480e407409101001d000a0300a5003081458600060a8203107400034002a101a590b0b02d8900c144212115080d0303180900306d203500001c0182c54030000d603200e108075904d05000792501e81106409080070303070408a844 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 289864 1250 288614 288647
    0x50307140409060303020102180904020904030302180607030f020706020708100b060403050708030a08060406030c05060304050a0203010e0a0204050109050105010801030210020705030105010902030105030d080108030f0c0106030503070f030809011104030209040201 115
    0x3c0300881015010b401400c120421101d540701030000502c104801e04006131400fa400940340008100031903c2600103096072200300c0d10405004070024049503240c0d105040950015280710044042c46906129400c002c10451000308101810020001d07200d1607454146d00030300740e4841c81c00b01d15450b050705581c000c603004000e80700f056a0303c0801d503880f5404526000e0025640310005091480e29214a2041d603812403c10220541018140049a400034009560034490210107030f0042c0c0e4240550448594000080c000d04012441403100b521410380044040e641040c00610450741e014905c50704403138048a141074230344000b410907030601410360003c0d5015401d01c0000b0801815940045040324025400c544503002d82c1d0300112280b150038003400c1e855401c208040f18513808840040c00c40411000e00021742955255209495035000040c202d41c8400000092030034140c100c1c03801c96001f45103900a0010b114610040c42c01481a80402031042c0d0034000402d05591083d01d000b550618030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 291114 1250 289864 289871
    0x10c0f03020106061101020c03040303080402120d0905040b01050309060c030c0d02030c03010302010f020102030702120903010209060408010c020106050a0305070504020a0522030507050406030b0a020903030c0d050301030302010506060703050307140409 110
    0x11400c0003800b0f88a107020b0302c0003240d15094194900f050500c2200e65100b015400f079820700f0f0960340c007202c10300401343c03017643e01c210645003150201c242031150315000c0e8040d8552441d040d2420342804280c0f204074401c2c9050203418400c00099882c00304a40341d0003900c0c8817182c0da482d0303200540825917008501004c954140302004121a94501703000541c1628003d0700c4030614089038a404a0a0703200c00c071207080058000350005da54002541001d01200b002c010009030400c480382c4041242c0d5001640700003641da46601280c0d034119021700c20440640019218101c0e058110b85450faa1030070103105460295500160181584d441882901c4600f9510a10a04031150f41110789482c10920300050b0360b5400351a50002c0ca500c2c0c50b01c510340c01c070390340056004201c0c4c0c3c40a820500070342004201c207406000c208010091b03500c0034415a40c11400b1605c40549130b5040d41802821204d000b440207004100c10040000402d03080f0003600d500c00c400349003480c5118100c1a0b009240d0040c1c2c1e0107031001030306 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292364 1250 291114 291143
    0x71106070206040c050409080904050414010c0503041401050105060a05030c070204180b0106050406020a02060d060e0408030a0501060806010e190302060409060306050c070201091502010204050603100303080702120405040902010c 100
    0x140401d401e0f000f503004008580e4025100c0301000107c6203a104010040c003810000742c0403070f04054020903806409000481850021650602c0c01d442d124003202e40000d0000041004108900c5075001303d100821000300010b60504001c0340b05441340080da01d052010110015943c005103c04840d22241e01410901c00f0803151003d6803088a151041103a1780a02800045946071050003983c003118000c0d4000c0c14015110340a1010a40c0202002150b140d01c03400003107481091150824040c511412100360789141c4a0880c0040f0741041e0007850800005009028060303030f00c400c000d5811441140c0f5161403030341100340c90116010703951000f500101b02003000901012241d2000044900546050006540741d640224492140c91402804100c0d030103410b000c00e000d016120f81d40744903035000041c50513454000082c201d810494015460760b10f2144103000b01580140c0303031500301010b4001005494440d0301c10200a01407805400c1c0202e507598588015684103400d010a11a0002d00c134805451 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293614 1250 292364 292367
    0x603060207021c120c0503040306050907150306050915030102120403030b01020c010903080403030305190e0703021206060f06090402090603040809030d0503010305070303030f020d0c0206060405070c0203030301050907110607 98
    0x400c181d0099214000a800c841e980e001034983c0f02800c207078400c1c40313410040780140303040d40c024890791411340b4035200602001c00003444610810f8060031a605c020203c0310b00e8000200400005001072004050600c04204421385401c0e8011b9000140182d5038012a804240420300900607a84000410030341c00c814441415019404041e40ea40c0030303401d4034084503114005542c1c40d000ca00c401800e41200b0041040441d04c81d61007650071089010703601c2c6004107112089829184c90a109081607004910200300b1882c0c00c03482c0090150340d000240540d407510307030002484005d203407030300502034080041c1c040802d42d076540c100da20420004080c1030b180d00b8941042c622a400503182c00d4001c0c03095219104034107004506484c122540300b4020400c2a0a60390120081d0140444842072903400b800440000b00081c018444004110ba0090006242420401080d52006003c44041c4088420548050784001c0204d034190340b030540d0404516201c800003202c01080403c200c2645d4003890f020700000c603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 294864 1250 293614 293617
    0x204090309050f04060302030303040602030a0e0f070501030621060b0307050a06030b040e0303040f03030209010201090206040902030702060609010501050409020c12040305070305060105030d0815030f010f020c060903090a0303080a02090406030602 108
    0x8580640c1e14020303c00c425000d100c1181e846000280d4198018000200022541d4004541c0b028000901144031100145900c2c50800300c20107610f01504800340c14001940e161080400610f0514544802d031150340c441c1c0c0340c2804581c2c1024181941302c09034a00c0c1610104040e0000b0032014007403401981e0740e075030020028908000428480c03801c1105643e040100007040c0ca004039049041130000303e011307a07420740080d03120509150565488500c0d04000d640c41d0f5000e0401003001c641d02507600d03e040c039002800c140c0c000309110f209664000c014046a68407600769002e956070b88800590303030320013040403a217883d032101d580380800701b80020044108000801c000e02204e100f50110780559890344200358640040102605c00103d428000032950208001e00d245000b4020302501c40ea50f4264020b6401d4070404844400744680004050241a20400c03486a11a04c40c1010758184040f4400117240300c04244400b03006c100107403000c20b401006ca50704486031444010b204200c525503074038109000c1d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 296114 1250 294864 294869
    0x6090c0b04060908060c03070503090a06050103030e03010b0102010504030203030610050405040c0c02030f1f050a0207060c021b0901030206030c0c030c07030b04030306060509090106110c03060f01030c0501020d050301050d02010c0204090309 105
    0x41c0c42c0f004001503458000601d28012042c001d82c09003151b4906404980715007009080c000d080c4144540180402c40c203110b40b9028501a545100e5000034030720074542550703e65a000c504680c50102001701207603021080c0c1c0c0d0429801c86210703c1400a4080131240b0740983d4200325809890811842441c81d000201c1c2041d8620a07402d55414180c4030000d252189401e61905544c050460403074815403007036a02141d8400051900141800081e031990b42c21991900d01d03803005640500038142c4107240d01d2a001c410080700300c3c5c80200c00e44c15540402c40138000a8030b0411410804180da04a4110600c10b4901382c138543d80c1200c2c403040d52802d180c0d408440c240c0b01900480e140010216101d80f24508440c2c072240061b1558019900c0d05004507801c0d400d4250703403450b5005105041015550900c00c0fa4014890320703089001075411410482940d18680e4030a030b0540d4000b21100349681c0e044010b983c1125411143e41d5000301c00390005896803101403030000d500c145003418841c20103800583c440f00f07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297364 1250 296114 296117
    0x50909090303070306150e0d03030207150b0405090a0807020603060d0210020105010e06040501210501020409020c0102070204050105030a03020703060c1202030108010203100501020705010210021e04030503180604030209010303080406090c0b0406 107
    0x4090f5140d042100303001d51b601034a0001203080d41c40e039159040515080503818802e00c0c00600c0d000d159240d14803038040030000c0b50805a03c885c201609460705014298100902402030202e000301507440708528400e502000b40036100200c002683c680d03c1c2c484441c1541e070040c0040380e02c03d414800080c000c110900410b04403a17103aa001c15401c0c2024400c40381039a072109503000c0c10742d0031140761503a0f06d0984581219559000c01000c0740804050002d4501001d1010000d612040b0038410072090301c40582140307001b40c0c8001000700200354005460070444e900f0101c00651100541011110320030540c01d01c0e05454000000002c281c101540103600c1060b81889605100b62540012a2103610320b100d0140140d0080c06002c04a101685c01000b07801800340705001803c0050110320346540040e8000d82d03854002050fa10b01e1031200201580760200104e401921b41825030740002c40c5034106002c080c1c10083c104000400304041540000c0e45950001c1403040700550300c0c5556503260744039015110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 298614 1250 297364 297371
    0x106080a0507030603020a170f030d0c0801050d020a0302060a020a0b0705070501050708010501021b03030c07030605040b010902070b0a020702040e06040b010602070b0f040608040c09060303020303060418050703080306010509090903030703 104
    0x90440e440f0f8883c0c0801e4980c014846485140340044456001400b03540b0400705004101c0c64980d0b0030381c10070040c401c181500c00c0100d0706242e00d5030041d121401c164420341c01281f4540f1100c0040e0385462062040c3c03941210001d44584100004034503000c910f80c0300900c004c0703020003404040c81d00300000c0d22185200b407001b486586c2d07505800301c1c3e0b0b601d420300c20030b80940d100c0c60600d291101074655100006001400b12400c00c000d00c50711900d8950a41d0082d65019590400d00051190003035540d0301601b0761040030b500e0001642e40d000240707103001340703864040303076001c03810b0307811591032350088400445558200c41c46814a403c250082c01000c0c402e00c0090311a151000074081d403040103440181d4110000c0703a0525152035000e80303212000400403100300e407007000040b0321030500307100310000b45021703900454807890860f0511049840c4482e103032407603d000348920b100050001600c5802d80e036002f461a9240d88840700107a491f03024204080c1c0c0c2c8080d14808001504c80e000024610a661075030742032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299864 1250 298614 298621
    0x5040c0306050a0207120f030b030604060501080105090f030711010e060304060b0102010c0e01080402090402010c0206030c030a0b0d080306040c050c0304060c02030c0105030603190314120403030b0108010b09010c0507080102030106080a05 104
    0x50100d2282c28001820824403480081c0d06e00e004000800d1307610001d007000b1680340340c00b05c0003e0428408850840744182d60314014820700409124095001081034010040d241304c00100e00c1ea24060404010f000b10900f68025035584d20600308801c4d007030009000300f901c0341064640080035040700c42c0e0203070056280101036280c642c45003400e281c3c1c108041c2c55290301030721a44c0038020b40d0301d002401a81030000ba05142c10042e25110015407140c0c940345003041c0c51341400800d02041e0bda03c03c062034802d80c00300b1510400707c2c504c10b0480781c003c44100c0740080d000c05c414606444038003a0688c00780460001140028025070440b41d003441e0325208a0948100b070510300c0055070140420b40c0c926425501c2006403a00807056030801c071162501a042c1a4104a090f55400c101a4092817202d50307424998028001010380500034100c10110908244200350305024260416004440c3ca45040011110001050000502c031035405802020000c0d907980da11078030080c041080c1503074520340980c68078002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301114 1250 299864 299881
    0x306070216030803060607080a020303040b011202060406030e010605060409020403020306010e04050303060108040f0203010606170601020105090c040207080f0a020604020108010b0f040302040e01020c06010609050a080f0a0305070503040905040c030605 110
    0x58a85800070266040491820b5489a45850700010b02003600b042007004003401188804000e0200344010b580295034918061412111424069000c50048104480110016030320f6000f641c0c284c8070300e4500012150304042165000d49660b40c001c9030004d02c0054046141941c036001801524020707400c4402590340c40c54170501c602800c45000d00250418400b08942c0d621402405410034007885000d0860070003900000d0841d1201e0703203c40d01040c20705207030600a0000b2a0041c2c2d00c500c090000300813030300d0010b03101038940b810380c0340e418440c03940096001c04012100044d94020f4150091b02c0e5100c9040c401e0203540d612060350181c0c0403070030f1a800003036800072620840300b443d0340c81d4040c00e04091440d401e01c40070b00403e004105155409116228040704200007080c0282130a5903000b00151810090080e20207103900170701880e40110350040c1d00244001a851003c603807501e8020744d2020182800e07801e6000d15001014807904240501c030910a6180c064030549010310400c11240d20f96111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 302364 1250 301114 301123
    0x80706030623060901050403061103040b010801020c0a061d1605010201060f030503070303020a050c0105090a020f03010212040b040206040308040905040201170f04020108040206090307030b09010608010608120a02010209040e01020903060702 105
    0x4401c1c0412000302c0468041d8100040644001c00d818101075017000e0b26a0740300000c1d549074424172030b0600004000c1000380712100f01d4550051201e800214070b8410366549150715a07a141102400391500d40b1400741040341c46240701c9200c4c4c240c0c00183d60703030110500c40e03800d407051140c80307020300642c00c0c59404a40341c089202c060f8100c0b50b01000452030f201e03103507406901a41002c1d08407001d03c9410b009205521400b8092107101d100385901600410b650b604c1004104004480e01c64000c0e881071001e682d11b4030f0040c02c22a001900507184d0402955240700048042c890307500014000e400116002070640c110790003490255100341c0740d0810800d6032041c10650070908032041411102200049005540915200c40d0050b0011f4030803880e043d076050101e0700d802c5803a823084503100045000c106403a8028481c05002e004460024020945080806070303584045041d003080090002a007800098001d504075684008040e1040c8403500c2c11203d000c1c000d41014403650f009018030380000303090038030126 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303614 1250 302364 302399
    0x1020c01020a03030509010204051002010902031005060a05010302030a02070503040303020607140f0f0304020a0b0301080a020a0503010204050303030105090703060306090803040302010f05060604060c060f0908090a06020303010303020613030c0c0807060306 112
    0x1c0c0100074251068808a000e410042c3c01404255420040412170b0345868100d200d43c14043d80011440040e01c1c818145404082e0146a0000d031401041c400b060351840d02035001c441007481c02580343c0e160300c0302200080c4503900d0300510710f1100013800000c01d500800d0342071249410b900c82c20090840203081050500c111000c082d40320000304007495510400c04045d640141c000b40c803102d0350070303200c0074445c4441d4401e822149895000701c6000b411460720390524400780000f900294100740c031b00390220b03540b8007040c0a620300c2146001c0014410a1007948864020b40e000f6006014486a6003000c6201e68820343c0c01354010350918844480344c1d00d0078011640070f0b107000740416140501e045000c9861005000c030494100382c440d9251604e00c101801609600c50045900c1d0b552541e0380803c000b106081ea5000800f950024001040803036004a84103912040002644c607000d081ca00d400c0b10301405003540202a14203001007c91a402d00050810030b0300c049803020408641c90b0302404180c1039003072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304864 1250 303614 303617
    0xd0201020702060901080903090405040303060503070b0c0604060b0612010306020703030506040209010903020603090109050304090e010b0a030f0303090c0305010c0e040506010207050306040206070c0b0307050909060a0605070b070909020705060103020f01020c01 114
    0x2001544e81a51007050100c0e440310940040c1ca040200b8840094107894054a0540000351540c00500c41454103101c440f00411a4114040c9056041d007019526400c0003040503140c180ea49905583c50340b6090219004440c2c001c116021560712483c01c13100035006104140c0019142000180c5a820240300301d40c45000141c40b52000c99185030300300007440d40001c280d8011952074113160030000b10300b04040d0010b0003a1100124880c0c0c0c1c4252000d00311103a550f0240c0c86032826440c200082040303c0850a8416010710300801c0b070b175940d8104600108d010350310081c036a6180200b00aa166030203900c0342c12002d0121010700039500c0f41c0c001240e0f00d045034050340e03030f164214101050040c50100c00a160640c85042c2c8545041e580798290382440c0c1040381c0002c042200054080ca8038a01043d409074050011190040006e050550040550140100c010000070028012074201402000c0702c1d4024401e54600b5982c3c1e85a80c41c000ea1103241c00c2c40100d00488644448400541c0080745404031070006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306114 1250 304864 304867
    0x10b0105040503060f041104060306060e0c07030516030302040509090a0605010503010b011b0c03060504030206090609060c04030201030b040902030102030c0403050106051008070c030306051f020606030105040c0b0702030102120109060303020d020102070206 112
    0xc20404000500c0040d00c1101c105a1034401d105103238485000701c0000354050680040c40c2c5240c9004c4000502c0000d20140c0841e404100c0800041d401a0564181c040354010007080541c403490182c009100c1c1d9041a40d1004a0208000c10210001640c40303d4512484c1c00f03010590b0f90b113040c5402ea4011040e00360120310700032180120030102c22042409280140303260240c065803912060122842a103055006800003400c02c6990b000030015250400030010040c0851f00d0143c007000481c0c09203002c000c4c105034507aa01c014081d52241c200c0d001c0b050300107008558904015014600350f078003500c011a610750a000001451b854a4080010071141644607035250340d4030351508a500c110104001c809140d034512010805844240e140902c4e0030307000c4a03501d0f41c204140340203407403c080180154400c2c0c2c14001007000160300204a034084170b403a56083d5840c0d9078244002800b90158682807130350011441c00000d80f0385070b03d070401c034126030180e02651103004600000700d00b40e11070402c02a421940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 307364 1250 306114 306121
    0x5010807030b011206030302030301030515060108010308090409050106061101060509130201030b030703050303070203090103060e090705060a0201060e04051b0105070b040206030406060305030a0305010609060504050108010e13020303040f08010b010504050306 113
    0x70380c00c500815441450006440c10214038203c1c01c035009900160b0040c0d0001c001072003002003c020300c5505451300345c1e00001a20b00034000070b107030244c14040181029004280c480550f10b036908050551903100000f406100e40303440e001454441141e00c01c00040d820401e000403942000595140241800c9122164208140c1c0055020b061010941c2e03405101c1c20400002103502400514024400c55011b50b5072244064001001d07183c0ba0341015180060f030030280080003000081e14411a10141d459545580568001383e004103440e500203034000004004210820502044100141c002e400034036880303038540001186c81c3d00405e43c00422801252010801618000002d981e02a100d030102203412600c030f680e80e50a6402a145850110b611032005004c00c03604011a000034103021701d00340d0f04044c5003600081949a040c468500b01e4840000451141c00000140b42c1c41e2f1500903040301d5540303503120548070440d0124440c1c5c11a55180c01080121584590215001c40301c4c0140104150349 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308614 1250 307364 307367
    0x60a090b01090c050702090705030105010305010b0a0507060e0c0d03020303010305010e070f031e0204020406050304060f05070507110f0a0806090106080604031d0d0b090102090906030102090a030311030403060f050a0e0705010807 100
    0x2020801d0f900500c1424024540140d6030300070000d109024039582c440d00c03949404009429601c042e005441d96034028464089504c0d13004040c1d03549075030007210120b0001140345c401c07818480725040c0710303030000b40d4a10b0381010716030000011030482c1e1080d40208080d094903000541c42c0c00d200d020b000c0c41c540700002d081020442c0180c000408107038034203072000804500c0e400181242d0184d8410000f01d0408410001402050300c12103800140b284020320440c0b500710001070407031148150003018210014890340240e11003100590a030354016040240e00d50301c80e00d0b1070b940c41a0072518000c00d90700380720011400310008540c090155501d0b442e228003110180d00052a0040d1900489130008008880800410342c0508910302070032000e000140e44140c00002d00070b40c868010304a0340682c0c01001084030a49500d1901002c9075010700d440c050045040070070608511441d400a012542010300e102ca0148042e84121302640c00468108603502104600c1511801f40c2e00c10a40030a48034400111f009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 309864 1250 308614 308621
    0x3010f0b0a02010e0607080105100309030f03020f04030c0803030609010801090506010504020a020f060a02041502010902060301050405090f0a03050a030506010804020a0b030603010204051306030201020c060f03010b0702040e061305060a090b0109 107
    0x19501e4000030a01c00000312550b071138020200d4a00e0001403d04004000301c1c10444014181e1850500d014001d000d0503440141000080c40654410103a0000715007206c0c02c1500160350207140d1111005c00a10b698034040750341d80d042030700e10b41c1c8114401c10002641450511605600310340c441c2c09041607031b20f00802c000094111042050940c0100c500e41040d6600c18080b45118400c8680010f032150708201481c000080c600c7c501d80d0a5a250403107500140e82c4040075241110400c540104540d52031840039401c01002070398000c002d2158114007010150090054400c2e41000e40d020415a5214801106c941c001501c0203504203032750417006e21614050304003c55010380e025001501c1c0585d00c001040c2d1149606240004659071803005004541e410b120384c0200607807c4070160308091050700704a2082c801841049145440020b840d0115101d9030406444102d0707400a0b905540f40c03581c0240804600c00301c0c101c405002e2031001402c40300180c81001030564000003203001ca40e09003502c0c813008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 311114 1250 309864 309877
    0x40303020a080706061d040303060605090a09020d060308030f010302090604050c03040201030507020f0a081207030204030312020306040902060403050d090801020c0a0b04050f03030103120306140105030a020310030803010f061403010f0b 103
    0x65a8540c1070200b040c0881407440700e00c5002c5c01144840605d1b150500802b10741c0b0b10b400c042c080040030861a51550350b007111038401d842c0700c0c010050780c0310390100c2c0c03020050a26a01c0106942004420801c00042c1691118101c80c0207480c903801c941e4500c400c01c000c4030001c80311031790507800500205015500c240d102950200c003a0049400c041d61100c01d480c60800301640480c2e40c3c0000003442d050742034a40c0308480d00100301303050640c24030707044d542c014190385040543d012003190f0210005269a6481d08041442900980480e0350b2315180e05001d40c071a00385a16003008514a0f5900044260051084803207280180002d08840700301a03030f40807000c0d2f0b00540103803417034415030014056404051000f103008611618503030304200700c8564050709440702c0d9482050800d80785032411209076001811a5800100c0140040c0c0c1ca0b07a91401412080c0b5454101400c0100040004100140100a14001c1e91895281d02044404841c074920b8648024040e0000103003a4500030040605044040d02a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312364 1250 311114 311123
    0x414090c0703030207060902030609010b030106080105040206030103020112140703060305010c02060103080d0903031b0806011403070206150102030c010c0201020903160311010302030601021e0a030e06070b06060306030a02030106151103040303020a0807 110
    0x1c07841f4081e00000d03d007200c156190041c0d0b940d5030100c1041440d0074401c1d0300027041e06200a100354649900007810702c1c0030502c0b019040c015032030041440004070741d0094200204081e01d040c00c6040c541340c002d00030421400201d4880d0f18142b4101c03419800010f0050499a100341c40c1c0349052a03210300d01c0b000c3c12312100200c05050312116046e0740384032408100c4066000c603540e140880e00c0e000000500044030846e02580d0031408109005619a000c1510350780840d850791454054090000100e00c7c0d40f15000c200703215075213000500b081c07855041d00100a0428220101c41c540d055480d043c4010b2400ca100081109500413102100e40d400703600070355030140b414019101601c00c0703207011022000129405c00703015040b000313190080641200865644110641d401e9044c00c55036683c0d08540d403800b60005104035004400a03071641d500b0040800c0555000e802444020f9136607503c079000202003030031140483c030341c0c51900c0600035000080c2c1d0100d903010340c02000808a141c0f07038003030329a0040106a8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313614 1250 312364 312371
    0xb010903050304030602030402030d050f031f050603040b0405010507030204080309040b040216050102070201090b0316030b03070504020c010203010f060c030801140a03080703050903010b01020f0a0201080603010905010c050414090c070303020706 107
    0xc0380742800504000d500403540940c1e40c1c90507104150a0140d0990100c0c2481814080d6010700f82e1480160381e481011000f00e0ba03440031b200c915000c00018581e001a5005900100300000c1101801c007640c01030f84618002c1c00a1b849040040d000d90140d4002c0c0e08090b481030105c58074515154000810000000c0c10061400594844401381d01400d60407c0e12960340000d083c00465a12452340401041030700705030350460805120110800c0150f2025504143c1c80d54640e0340d0329a8140994130080c83c000700215a140c075070340c940714041d4101b4402d94039282d610182c006850b0340605041d02002da4036658051a03a801c00120504882c480345c4036603049415003002000051a800c010300242c2d0107520b449440d10038090070182510f40ca01401811500600644024680c1c00108000b00550900780004655a114040b031b0040c404500060700540c00c0c5000071202c950484000c0c800d488200c0340b1402c031000c81c00705020140382c049d14402c0703410b442000708002081c40703039010b000203510400010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 314864 1250 313614 313619
    0x5070c0e0c07030e010305070c02040207150507020a02010305060a03080708030c07060908030114010306050f100201020702030304030c0806010b040602030f0702130903020102030105040608010506060403020d020a1703070b0106030203060a05040b0109 109
    0x14640903908480303503500d96070300195000506410140303403441c07000246404d100034a82000d00400350002d03040c00a014075008504001005185641c000384201820b1080165103003080b4000d41d604140c0d82c0aa021a107454080f4034542030004a80054a0300000c00500c2d186683e42c44102c1075000401001401e0401d0040341700040303d038000d42e00c01500401025440303504140d1107829242448070064140b518040c002c00c056259640201c804032400c4500c148070101c07030341041c4c0c00381c400c00400030341c1400005000300400060b4802c40041d188090101d0710182e880748000b036400d1003240150350150388140161000030800c80006e00035544040d1902ca159441c1020380c1041d2a1001d2044000d1307500400144007a04203031013083c00030305400b0003e006509000303001c2030361441140406400348103041035031030540d100c0c481c00c00001c20215010074002040c04d00c4594880c0c002000032900310a01d0030001422900c80d00a50303005480c000d003c0902741c0e24080400c0018804410880e052104c0b09000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 316114 1250 314864 314879
    0x60c07030c06050703080702010e0d050306060f040305010c030b09040c0e04021201020307030e0607020703020a050402090103020c06070305010608060109060206061210060603020c0c0306011a09030307080406050c010b030d020a0305070c 103
    0x70100144020b80f0b58640710009440c0181091800518038003c684c5000203200360040005502d150503d40f070f0810f5503aa8940c60041100e070301c00c401e402c41881c1c00000300007040140c150310940d0030741c00300d503020000024594100130441c40250b0f40070b407032015510400c1c40554401c040203500309200408019410840f074600c3c50a81c0c00071104040030964800003143d18a100784a695444542440540081403e550000b0803146090090030300503903000c50340910a034040e81c1255401a0414100c2d005441c01d6070004014020034000c1e50001441e000102d2041c0d4000c0c4464410f0f00c1c22500504084d0f03882c2424820380e659500b501c2e15862003014200042d843c400e00c125800f8000a41d4050703030340d07918900014605402c00400500980c4444010062460403040f1583c0b64111030381c0071a900c407809000641b13540200c0c500500031110000d000101c1981210061483c0e008400091000f1702c1100d0406859404031400000941c010484090020707210304024031103244034508089403e40c40b00740 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317364 1250 316114 316133
    0x8030604060e0405010903020115050102030f0906040504061211010503040809040504060f0203070906020606090103030e010804050304050312070201030509010606020613030302120c0301030b01080705030a0609050a02090a02030a060801090203060402060c0703 113
    0x500782c44ca80d55038580c1c0c4061581c28061846041040c0c844820017038500b000003540c80c45a180c540102841c08600c652040d80d800701110001c00c0010020306c0155100d00b140c01501d0512001200e0a851840c4404170729400b400540e0311990300400d01508010745241400082c110040040765200d0791002c0340021320902e840658007520b01e84d51500030300c1d4141715000c1e142c03881c09002d2034454140a401000041d60120800e00f42220a2800a80340d413501d1405a145010b942c01450789400303604805422100410050300409000766030038000c03030300d130644400e00b00c407207a0141c0700058004800169460341500f040440d0503200b403400518205045c034410054080c26036400000c0c0300004010400c2c0300c0d0b411511405080804040c00f0540d240c5800266641072940c1d004280d9500c408000c41405000d115110025402030700d00110740c40c0081490000758801c032013803a4003900c0c01c00042550b400511034065441e07409001801580c030f860b002c20086410020306d9070014800c0b4a00030001448085 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 318614 1250 317364 317371
    0x1030906060e0604060501110a0f030507060606020d0e01050702030601050103050606070209010306050103060c050a020d1b080307020601030201110109080f0904020f04030302010e010501060305040b04060f0204050301020c0309120601030c0308030604060e 111
    0x210b40e201107052040402c815030304039921140c1000380f00b00d00c8480200f0f0100d0701100d49503005c0540c8401c20340c20710b02070f1414096440040c120610300f107000a0000c0c1c021462081502c0380f5642d03100701c56061001580c0314040c8580c060740540c0942c4c01400154081c0d0b0000d030b0050700080016080080302e42c00141145400d0f0801c49d81182c42d07500401c01c0140502030b0740480046400c040707081004151000396913582010228040001d4a2100b14402076840c021003e9180c10030030250341d038903203020040e60340c110a2004900191051410b502d802c50107209203403169a00c0b0302950b281420050040303a580d004401d09507803141c2c0c00c00c50041ca600400c00280021803091b0001303c1c1d503480d041080303400c54005912507014507041c44100300c00a407000458a5009900200c0062190b40c00d240c003a009001d150003958056100080c240c0000c0340c0040907013501602154040032406030f040c02d007511400203100040000d203d0080510004800303e000d540e1045010340001030b050398580300314240003001c0c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319864 1250 318614 318629
    0x2040902071109010501031803050702010e0402030103111003050106050a030b0406050303040806010303080604020f0304020603040c050a0b07060509070506070201050a020c0402040603020d0b0f0f010302090301090b040503030108060f0103030c060504020103090606 115
    0x10040e11901e0f0030318204180c01018242001c201034a8099806003450440403801010040001180000c40e0301600c000340030103030301074411500c0c0d43c0c49281100b01108041341c07444c401d8a94030500d0401034428015203043c2c65850343d5950510342c01101c264054086a014658026250403000c01c00c1d4904001400007004204020101545103060140c40410050042c07801117004101e41040840e0311800c4030f8100d941619059035a540340e040c54440c0cac0781d10380c000725440a00c0c4040051011200005010036500a100401c007030703103c44d142103542d04803d110f0690007850921190300998052405000c1e072103007500540f40c010500e07200060890740107400003400b090340401c501e842100c0d181303d44000c8400c1a036034100000c1c1804c001a4240501d509014101a00051203120a0310b080d04501c4032643c0c012040c0c0c04038142494459104d070024000c05406128060005180100306e88409040303070f416480c1e0f18000f60481e102c040c00341030020410381c14103440c0c3c5440b00028400303100c0d0000a107883d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321114 1250 319864 319883
    0x902030309030a110907020a03050307051b060106020606100305040203060f0c04090e070303090501050a0801090e010b0306040f03030b0907080601051305060705010902010e010903020f0d0203010b03030309010903020601060801080604030f030204090207 110
    0xb4042103201c840c0681b900c400c5600c080403400009420004485d041a5a810002d0f180c405521980007040300c0e102c0b0040ca1b42c010b240c00040c00e6900044c94601421003101e0541c14a00211012012500c0803200603515920120225162095203d070068001110031b80091500d92075500684c00d440201c5c1210b40c070b03a80681810014581d01c480020082c10003480c1241c80c10282c0034000b4100031041c01044216665000c0461001c0e80c01d50001d10060781c0507040c0c030200c0c5407a00f0480000442000d046d00401d040c4a00041c541c1f800c081d030b040c898581c6440d8100c83c3e03201c2400464203a004641c00641c0004000c401003444e03981c4402821025100d203001003003402e141d00c001812200c020800b42d06200b40300d0b00900c01a502c0e20100f4120b0242602c02c43d2808220307000084c058214980e685070980400028041c03895019040504101d002c0e80071100d031643d032000304a80602091140440503003104000c87c00003845060722406000581c40d01600f0251541c01c41c8049074805181202d441c0b58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322364 1250 321114 321143
    0x40303170105060418050601020304080a0b010f0e010602070303050306010c020405040b060112050613020702030102090a0b0304050606010e09070806010309080301080313140109030807050307060204090501030203010506150406030902030309030a 107
    0x410100d030a000d00800c2d01c001c0c0c101440e140d5803204c0c04028007a00083e040c0c0350700c006405a40708001b40c5009001030012581800401e08080459840c01c3c0105210b0808405000c107100354140c00044c1215003ea0003040c2491440e141110550005401f80f03042204444c81341025988a009a41c069406955061041e080140015260300d5040768146906030808040101c1d40c0e035024902501001f00d6100076036640400d100003802880b4000e001781d40085100e03008034100c2d400234051846944920119040d548454005441600f094074800b40c2c4040b80200084880380b049c4110742d0459018100840c08000c41c1c1d0320b41155820903000281280e0020400c040d40011008050005148550f0303908100c01031940028004403160101a00b40440011114100682003040302c1480d50064000c548580d111113400010f00000c4c80240d110750700709404a1003500d040801c0700072102c0b050600350325007450a0030603005803858071026a0306010500844115803001c0c46140b1100384100c602d02d00820 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 323614 1250 322364 322397
    0x415030204180203090c010305010609060e011101020c010b030f01020301050901031e0b0103050d031a0603040b040302030c0d090302010e0306060901090507030605150c01050106050a09140a080102070308010305010605060702030613020d0206040303 108
    0x1014480e0040c100345c12701004021803074016000406440c40d03803500d804101e13100c20042e85c02c14146554028075610008201c0703c402419444848100700880950701501102c100c0f8074241d00080c010154400701000041001601c1810b0945001c640075518030a4079603203454519003060300341d101795103030b0f0801c9010844050381440350600611500340104508450480401d5060200400040a0750800030120b42071600810641d10003420481c1115101d5040d110000e20f98030851004074041103000d04a5a0246004205136200380300103002200141c0c0ba1122120150030090040b20505d6038580000c20651911550b0320860500c000d0080e070745035503d404481c07c448050303014000f044410f002c0d245c061980030350381c40111228215541740202d00c040000340941c840d17a0090310b8a42c40003605008050f00104e40d58101c90054008100c2d803540c403020b00c02d540c480c44e04000e40c90340000001480b03190540e04910744950000d4180101c018090b40807910360b5000e80c0050f004a00c04250452492 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324864 1250 323614 323623
    0xf040209010b040e0105040504050307050d0504080607030209010c02010f0e03030703030902090105010302040803030f0a0605090103150608030301050a0905040606030602040803070b0a0c0f030903020a020a1509080102040b041503020418020309 106
    0x60070362070307030b01032030300740f6280d5000f26828041c050144aa40c8800224090000070010344a19a07004800c1e140c50489282020305158020711031500140039810002d0700c1540a4400c0d541041410b03110480803906507401101c0842c0041040300a0000490704480c56840c10006000141d03c6038500003408201d44c0108403040304140d11441c10140100003d0000c41004010340742c0250140c1c00c05006a03c45c1c1d009440584204c1e04010f030091b013410000024040e082000b480c031000203900401c03070703207464500282d1603120034020366810140700c08081042207081e03808107a02c14000c0000084032520303903a071041641d011394040030480e4408907041052004100e81690010440c0e1004c021503204030101500043c4445404000d26503101104002d00d4000e02c403107000aa4018816804a6290800d034031040210740017110028600560100d4001814821035064030743d4038108074185450001d6604403c00c031003401c40e0805409000c0001c55100034444401e0000a10701e0160300c03440e01041d85880c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326114 1250 324864 324869
    0x102010b03060106020a03110c03030f030402090a05010303080612030c0102040801020903070602010504030c06020a050d0e01020a020d0507020303040905100f0305070501030f0b090105010806010309050a140601080604080301050402030402010c0204050f04020901 114
    0x242c000b1001008201c1d000241c820006034181000d003898010024610304001a4000064243c04000341e00b80040701da20f001188102d20032221a040c60b00e0709034a100844101340402004642d000300820035628001d051035041800310002c6030310f81110700d02c0c510309a0300142e110745200d80d0085440c00c520b03d0148030500150026100030401032402e600c008000f1541098050590b960006140488510690031100c0c0203c2195050040c2518220315034000d5000d000d03100014000e44243d80300d05449101200d40742c640007030085007083c2c00c00301810003e11026155100390391250500040703440040940c2c90003540102d0240c01319618000002d0140c88a100c010824945000b0303d114099035126000e0741540d43c20300e4a51220ba0700c00f00142c004041840780139107140715400000040201c1402d4002c0c0140c0100d003a02c030305136a00c40c089590780c60b041d10010a41e85052005010a0a1590207154014014034004c4414005a00814101e5406880c400317107800b043c0341000300b0f5042c032000c600d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 327364 1250 326114 326119
    0x501031b0203030601030209060706021201030507080f03180406120303020301030510020301080a0b04020102101a0310020f030403030902010c080301060206070201060501110309060904022208010e071a03100807090603020102010b 100
    0x311203003a10002500c03480020409814554040342c5908507850b010299140254414800c42d038030170481e051800503000900c0300300e4562060000102e1205000b2889204071b00070301c8029410012014503140380904850f40385500195540700000f00003400e090320224290003a240141d6070f5045081150030402c8840e9044602401040100316400d40000c203000c81d5a000540e507034440d1503d20040b03040c034480e251304000d041d00701418089202c0c021b2140c035070b4000d030860490300e10701103140102080c1e00811481c0520b82ca02480010040303400f0380c00070100e0503c14035158802d030b501540d620301650000c0c4c1088006038040310410071220f80922415014140900304100c0300410720100513624803a5000c1d050249802062284064490fa01a9103028441080019007010207241140d0b5400780e600c5502e40300c1d800c2c01d0311b07441490b0f4042480380c20f452030010441e03036600025551b0012684040e2401e00050340c5041c1c0000c03040024400000503000b8030303002003141803450000900b541c608605051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328614 1250 327364 327401
    0x806010206010e0105120c03010f150504050708010308070501020c060403030b030f12031501030603050d02010504030f0c0206070609030e040501080106050102070501090b09010807090803030709050a0801050601020c0603060301060302030a050601050103 110
    0x43d600b110f20114119081180e40a0780c1c03210320f00c0d0746130030200040c050941640c00d080140d5142c90039601b000b0400b8000c801c0078150242c2c0d4000b04410380f8402d844500200e500d030380040c0003180d00d00700180b800760b00550000d890081c0482e5a28034141017110290002542e949090030949001d202d8000020803407001030402c007420880401d128031010340140424400031005a074140d0181c4c2011000355000f5056a04940600724080e0103004212011000030f0448903107030381c1e054020140d4000241d0054001d9040ca202c95603100004c00440d10203506100d100c00603a249580c0c0c900669010703103400c03000403070030034648030019191601e0307604040c5c1070094006060054040d9402640e0342c01d00d0901c0c0441042e02c0c0d02409a03004c480302e4004402c2030100208029a19801510510031a1300c1561104261542c5410391030803180d090b0707540c5005803c02d14a000c44c9182c140083c58000000800020341c681d5203034000b914200c01080c00710365540020300100440e42c1c040c80b5a5404445070290708 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 329864 1250 328614 328619
    0x315040903021e0106050306100303030c020303040309050105070303020f03090708070801140609040314070602040501020606010507050c01030507050c0a06050603010b030d090e0a0f05010902030411010504080c0103020c10060b0a080601020601 106
    0x40c3d103581c03a4410070314103124042c114100400302504490010000903050340c0c11801c0400004a080390603010640200f4149580e00c103c880c0b00004480c462500360f40c3c0d0451281c00c0c400110791941c0100c40a40405400340080804111000003d500445000d40142041031420720440d0802445e54231607103e9900d007440c1034105d00c084002e600e07403000c1e04840700c140390751700c5117000e03122075600300000000c002c8040f446004008d490707401001030356426001c0303603607560300c8000440f010711807100001c14607000400c4107501540681c01c0150802c085003803280c00c04e0a6030101c68982007403e8415035019481d402403084030f080c03e03c071b1140d0026059000d0311850103030b50302c0541480c9051003124420b542e42d000044a500304d81d440035004012082060045580d02d00c18600650070a503416920007481c1c07100340d403056004008603021112040c001c0c1c5000ca03074000c0107400941210075486028051700a88100100c01442030038080c1c140d0720031080d15a030b01010000d29004000342840d05560085005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331114 1250 329864 329867
    0x30303070e09090a0602070807140d050406050901020708010e01020a090905010803040302090405010906020a09030318140f03010207020a030c06080108010b01080c0304020105070210090503010e030f03040303020901090308040603020315040903 106
    0xd00c04100c1c1a60010110f8803030f07072001443e010706a54090001c91000c2649002c0058060080000c68094407403100b101d80940300c0760341c9a0320700b009480e0104600308030422280380a20050a0144414015141d525940e03190003030139036490580c0004203942c001002405c80c0d0f0840c0d20a80948060302d0100b00702d41c148100d0745d680b88294080030b031107041b941001808202007500b00741e2195502002c103540790514298054418085404100c0220b030054500c7c41400e10041c08540442e812801d0385503d504224003880000304010030110b8055400b0070201d4003503214080240c0045119803500c03a47d00d460400020b100c0c980603004250184d0419090340c080340c0e408604c454000e070101100555a4403603100603502882808002900b004134000c1040c3e0040d00000000221f13442900244500344580013001d8480c850031002d5250f085090021401003031103035000d04100001814510708107030f101c0d01d400e60643c010f03034008000039400004002202c60781c00c042041c141001d540510040d041e50344d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 332364 1250 331114 331127
    0x1020307030c030603260403080705060f010602010504020901060f0207090608070e0105010c03050703080601050403060e010b090a020408070e0702010e061302030705010c02010203070204050613020c0c040b01090501020706030903090504050702030c060603030307 114
    0x1051b0a80c004030003516804420000704543c021070f842100540d840100346882600c4560440d038462515224000000d0003500600405100f40d6008041058076070800b00c040c1c07000108449420118403a080300411414210300c1b03008003510400c4024003030b0914050b614540641c05030012410442170a604000081e00081912585c81d490309001e4041c3d612040105d8403805643c1c0090542c80c204500140414010b600c000f07114403050b1030382e0b2007503030310300100b00d069116034454090740d80c0c000c0c00300b00031041c15201069005034103480041600790024810b2403400c4801e132540b120b42406000107504602e82084124010f000030708000c0885403070fa07000030b5140d00614101070300540e22840003540c03542c0d40310701c01c2e40c071841203c0007192107000510859507100c001014880c045d503e091040030726580a110400110ba0741680185261401d00d04200d02a00c040c00c0128148114010b021a03d56294040c0c03600c203425036402142c84042c0d4200140c075010011f07212038041d400070028414002e40c00320 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333614 1250 332364 332393
    0x3030a08041104090c030807030201060b0301050303040b070809040203040c06020601080a030906050d0b040c0201020d0b04050103020d020112020706090803040b0711060606090307090606170903031302010318020a060201020307030c030603 104
    0xc00c20b041d600368000109000e000460402407814064480200410602c0c070050080d940c0207500810605465a46282c0345200a0040503850f500c140010001850b850000300b5005200e00e100c00c0c1000c1696000c50180e0704180c070200c0b0b82d206d17164000c0c440b80364100041c0c5e00509507000180b042c00d400380c401414540c09806081c00300800043c440f202108a60000705c0b2100c006001009041c14a01c4000e000b500400004040c1a003088441545480c04d4060382c0d041e01d40040040c0c0c40072100364015035550401c07141e840310b550380a100c1203001c108107110b180b402c02e010b451015030f01d00e0075207801c4451020040008080c405641045100f2200003c0c4440d40110269031082d80c408101000034030344171241d8001c5061505200001c100240e010b080800c00d40122081c807422900ca031040281c807800300301c0754003000507a0480754078090742c0b00e030b004081da000300c10620034207154003030f00858110041908801e016030340010a1103086681445034522642580c6410400d09040d90b55508032a100301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 334864 1250 333614 333623
    0x30106080919030203030603010c030209030607030504030908150601030e0102070314090102010905030408070801060b040e07081005030303070c030e030c06040306050c04080709060306140712090501020405060a08010306050603030a0804 103
    0x40c000038024072401c01245400c288401040c021404607842c1c001c2d03581c0c0c82150110b01039420403244954603400f900039280184030040280c00c8607900c1c464118000d00000f0320507010040400c10018031400c0900204001c2600381c1c04d507005601d460340003d000d0f034118428010081e8030402203a40440c7d07022051146100048070090b69843e0110300403405001d8004001c0c000b030000260000d03a2540c0090300504a89940c0c0082c4041c42e0fa418070100c990041e0b03c541c02c0d520030a0030000f4142d40c46418040d0384080b0548122000548503400b20703103960000c40b2040003050089424009040d008444651040300c00c90045c1407190480340807070001c6c002d61100901c60354440000c50b40100a140079540130703010a01c119101141e4528160010389500e1009480c0d4a140010040405005507161840340d041034442e213043c1004010344000418032210240d8844d542400301040d2503403040002e050070f035000c3c0d49100d465411414001c04460b800f8090354401c0c0d00c00c005041519821010260b80950807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 336114 1250 334864 334877
    0x90303040b040203010b0a0905010f1502060c0a02070b070506040201120c0207050d020406030506040c09060605090604060f020703020a06030e011103090c090406060e04031101050609040302030904020a03020702040608010207051011030106 104
    0x41c3d1021a0141103200320507a03104882c208080350145090307000074101e810203031008000540d19071030029820f108480000042c0c002c1c2001410722042c0030020203220f41203204450284d40d0381d1045a44a4000c514215410303001202480155a801080e045240c01102c10070410048100c00c06581c81405125003806002002d072614150354172a4030100045821070709075010362030329203406607001c0ba46000d15540f45181c2407010881d41e00c1001550194030020b031005240c81c0c1040015984100c801003520700b18450801c001c00107845131030041000380260b84001c0752500314410381ea401d454400c07048200e101d404ac4100900340d00c00040b071a09000c41a01e128615484d5800c0c090702030407440e0401802e00c2d4000c410701c01055130066a1050403000c810080207a41c40d00420000880c00c16640600160300034099070340300c0e16181d030041c1a22181e90030010318003000e941c0418150b404513400440242d6012490390248402400303000e0032004140300030050070134100514a881e000602503141003008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337364 1250 336114 336121
    0xd08070e0103060302060706050402010813020102060612100c0305060a05040504080403030810090501060804030e01020a02030a020103020f0c07030602070203060907030305030406090201030902040e0d0908030c060412051605010204060201050609090303040b 112
    0xc2d030701c43c50113150090040e980c1e0f5903c5080c07400240c0307003d40b0101e001407042800a500c42410b54016420254140d0241030107807125001c10802043c04107019103107018076000001e141b48503206095507540c40f41c0300861949040010840301c042c0c9940010b00035402d000404c4002017a034421035003900d41c9814003503907948440c044204032030090741145003480d00d400004030f800303500120700b03c0c4128801d65940d00890540001241c42d080c01b80402074140c1d20030710082e0015802500603122178a0038603070440c10030002c0f0b100185405030a500981e41e5a1303001135658150300b024404980e200604030300030000540f441d58000c2080c480188080c1202d5510b411510443e0f00c03a070860074105400400c1445000c00030500503803101002c40354031010074070304d480c00151000048191034860b0307011000b401d21607590303840702d12a51940702e00000810008005c21107516a070f680d0b0007146c45025000040e1124181200a0700f1510003506a0348950404420049910400402c0701c2d40079902c80303400e031450b85 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 338614 1250 337364 337367
    0x20705190e010303020a06110a02060609040501020903070b030108010606020304050102060703090302030706020301030602092b0305090d0206040f06020105090102030103080a0c060b04050a0c030506040506030309010c1401020406030b010f020d08070e01 110
    0xd0350010000034038218000810306074005140503500780074040801c5820031000700d000c6240308660b640d001507005180050003600d0801c40e0590f000d40104000352030101400e00083c1400c43c103801554600c0808001844020f07802d110310805030440d400110318050034a000030759171300001042c8408268585810f035080500c2803040e039103202c1c2d1011080d5102e50f142c1c544100a9044868104c3c001c1d0300c8120781c00922100e000305108000c3c1002c0e072080d01003545480889041e4056010ba40d040f6011000c181c0060b10f40d000100010501007c401c0b203014200180207003510802751407807c00380c0c014001800070528000c102d481e52030a40c1810f1500b502a864000041c105a2441c10b274003d140508018480210307800482c0c5400451350100a1551030b001000103d402c280d5021380c0590040c8194a0103500403805d14903420b002c4c0b01d41c05001901d0400175400c1e41c0c002e400160029440b0704001116503001281d440d80c82240b80041c060350050300310000d1441d41d0003005242005107a501d010074a9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339864 1250 338614 338659
    0x81008120a0c0b0106030203060f0405010b0a0e0301060302060307020606030d0906050d0c110a0c0810050408090d03050408060c070605060105030702060a02090d0c03111009080d050306120607020604030807050a020705 95
    0x564008083e158540e99400c001d0000e41040311194040c250408203040700f07152510485041e10f401c0c80040f030419184290496a40d00e6100c401501596645400310260303a4641c0a540300304219401007240e80f80180905080002500191040c01018002884000e40100685005084030000059500d4030f500003210b0310b10141c20100704a00a1000c960240000c00050105035030000d02200c0740d011950441504849081350050030100040c02251884e1a140c56200801c0c1e0091a00c80d003020b446050b52410290241c415021000c4c000400c40204201c85c0510b0307a01c50f0f0242001030462508440107519044c0080c0720020300341e80080d02c40001d990700e41c0d103401d9645e007001c0544c00175512443c0c0708007038580e00c0c2900d0344116204541c04034420320510700c003000d0380e03d45000340401d180082d41c00d072016000548826031002c85c0108641c00600c040202c82d11904456004080c41e0a142c01c0240c00e03410003a001c1c5003080b408102c04610942c000440348201d45054038610300b003402603c81e00101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 341114 1250 339864 339887
    0x606040f0912020a0201080705090a0b09010201020403020303040609050f0405040201050a110708030d020403050709050402010207090b13020c0102090a06020303060f01080c0708030c0d0509071401030203040c03050102040603020a081008120a 105
    0x1080400542140c41c0c03030340044c0c4103031150700c01c0c1c81d1810584c07140c0206407468024014107e62100005c0d100b071001c03910a2018044060041c00094146602c070350019046401070b42160b03001404080003080340303107000240d0740b00f0b00105440c03c01160420b900024000c1c0320b60901c04042c886002032007a891042009144000c0c2550301c01c4d80d40b03442c450804000a50301c03034842500e8500c10300802140c04007803485003d00499050700200f08292405508001601c0c0007151598025200704034041040b0a900013003000c96042c000059660030310340100060703003800360000411544184108a0316846824540030840000d003003600742540d40c1542c050661082c1c0100070301641000c03003803084403898100600204246a03000340400c2d80c460640e99561081481111035020710710500700381950203030740110340044c099407528a4840c3c0fa520740d503007640c1c42640710b44001390380000c81d54401680004001c0c0c20000e40c41e4007005d4580350030b1100740c1c0ca4071124035150f004c000008549800e01d0040780321404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342364 1250 341114 341123
    0x108010e040c0503010606020102090a08010c0801030b040303020412060c030c0201050105010516050a020301020a08100806060603041202010b03070e07030b06030603030703050906070b07030507080106020a21050403050105040503030402120304080606040f09 112
    0xc13890301d41c41f000b1b010b5000031240600645052030b0100d80c80c00e06002e0050b443c1d89550320004268656100c0c003651600203081581030550803c00440c50703680780d41164010318040d404c0491007040c110402012070720309480f004210f91401d40141700c280c2e480011110b101c0b4494049460040c2c0c02d0030414104500382c43c00941c150310003e00416681d400801e0b144c0b203162040f02c0302002076901d400310768031345504462040d4480010400540000e04400c4d400d000e8207030901c000074205d000c01011901e000e5640d00282003440020040006a036850301031002800030030354240d4154203082c000320b96a4003807120018107004007c40c7c00b4202e0f48505013510401600b1040a10b210b003003c002c00b4000f0401a1410400596498004148180005406030140b50f00c0541c8048008140703040314901c6100980c07010410000304000030110741c1c240581405140254044c1d9070340d0401d4810000780e1804040d50600b1f60300280400c0003400030115826034403400039200454136424900c0d042000300b002490060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 343614 1250 342364 342371
    0x60504020d05010302090106020601060e04180506090105010312020307020102070b03040503090a03080403050607140304060507090f090b0a0f05090103080304060902040f020c120306030703031404030c08030a030c08060108010e040c050301 104
    0x8400c241c140c000c0c9048030300a5440019607608c4a804980352142400b401e004102008054541820b00c0d500c8440d032180010340c00110070307103141c1d41c240c02c12501f514158641c4e911540103000344a00e01c0c150f00c1b40d51016000031480d00c0307001e500103511081076118410f1034140100024090140a1040301d90001004001154442d00c80c80d25120036005408160740c144a114002100700b4010445074221082204a060a603507a40d9a0300d0b004d400001e02000400030360401c0015541c11126000c0f02604c03062201040c810010400d00600344d01f50341c0300070040d00d9500401c00c000e80301c1e0f12550381544d40115030f81c0e580303036241d003800405881010f900035000392801a0952443ca000c0e8082d04200c1c84076016100d110928007480c51650000351160342e4180c1000104000190140c42c0d0401e051515403a01d0b41800d580e86c0381c0407101215030b40f0440c4140c00004042c45499854031552080c0912410404420b04100b00004c000d85e1050048840c03c18050002c85c042c041c0114651006000c000c00a2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344864 1250 343614 343627
    0xa02040803070503070b01060302031003020f0d050105090705040506060a0c1707020d0c0303170405030a030e01090203030301030303050402010906020102030412030e0f0709020a11060402030a0602031e01030302060106080115090b0a0306050402 106
    0x3d982c07503100000649a03040380d000081a02c0d1311900850340155016020251103500f95003c2011805089000d40d6204221102d22400550280502c034410180d0b1070141000034646070501080d140000c1450b4482d03001040b80840b40e68101002180468000424124020088003444168030904401960190101040c4020040810101c1007540d200390749240f258032103111046000e69040c2d80090082e04240068404180b080d80049101c960040c0003089545031900441d09551080c0c02c1680025100c03400c010655810501c8440103001c148021403446c501034941c1212003202d800322504050325603c9082491108110469100d41aa0117a41e01702c0d5664208200130340c1300c02d501601040c0c2c5020031008007139004c9131443c41386401801074041e1544d07660707074000250b20040800411150b114010201882d002e44003e0107540709800601c881e504107603001d8280d4030142e10410000013504030044d55964031102c0703001140d00800d50945c80e84000e28080c0c001c0c180e00e0b04140d400034801300e480c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346114 1250 344864 344873
    0x10308030703060e04020d08090d08070809010306080f0303040609020604050301020a03060503070602030f03010902030a020708030c04030501050a09111909021204020f01030e061302030c0a0b0a030b0103050709030201080a0204080307 102
    0x40d405522151420000207680303400c0e90555520481d00658010b0113040c0050100b4000b40051410340710003010803426000d26aa00c8074983c003c2d40c019500c000010a8941e07855800d88503a40241ca0550010070240d0389614000360b4030710001341b0040507540c2380c4040f02c04544413101903c001c1c240c000d000350348035031403003a000340144000c1c801c40388644541030001480d43d00100407280311003080c80106245a080c022480d01030750010700300740580ca43c05c01c2103401049100c0082c50003048804041f81c3d98915605009081d18400380041c0c5d01030307142500c05070000740d209440c0d13a00c8000940304902940e1050695080003942544507004480c0009900201042c00e00085403040323200302d612203070315160a40110b04442008402100360341c45100440c0341d60b10404964000e840c8014121807841c1d01d80c01c0880d10603c090742c000100040c2c045141080b03940c160181d60140e541c00c1c41d00300100e02d8681070040c244015480080c1c140b15404011070362016658045401418001040fa0340d603072010f180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 347364 1250 346114 346117
    0x30d05150906060901050f030603030904020703020303090105010f0e010302010305040f14010902030f060702030909130f06060905060f0105030105060a03060e01030302070e100803030103020402090102010902040606030506030d08011203050307090b03010308 112
    0x851072298404074005079a9142c8001a110244c0c0181e403078030b060100480601185604c094100e81d4148024000940d50b035a03540000d106481c880d501541d2a81000307541c090a40c0c074180c0080c010525042d40902000029070040c904417030702441c02181684440c2404d045900c4210301c0901031001785010792566000541108007814800d42c201c420503448084540d0321a07005881c100c00680082100c5c03c080d2400c030601036000f0095490392480c4103c16a070700c01911030701d6882200d80680f58807003000110102d201d041e0707208409a0f203100e42c015417640001c0032448140681481442c010800c0c04541c1d00c40c3c6c1c0450064001da03920070340956120309010b0741e10043c40c0304070f8040302d14160025201008559000003140d90a00c0154116400c640c00c11020350002901d81d411596500c1000026a460380a00070082540361000582405d0440505090103041d00c0c4410510a400740100130700d00120441420054140c90440e0b04c1340c603200310464880e0309a07400404200d40100000c002d0100690 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348614 1250 347364 347401
    0x40b1305090304060f0206040203030a140c0102030403020105010603060b070f080a090503030301090204090509071a07030c050607030504020102010605010309020f0402070c0e04060b0301060608010605120a0b040609020408010b030703020a17030d05 108
    0x4545d041c440d42111002c03666004129002900b54105000c00d0107124040e902c8164902410000075041c03004006013242203030000c881c1980140e4440d001040b00c143c1511510340030300007900c80c8928081d16038a800f1690140c1d160b004000c0380002803008201841890440302612004064a03901d503903e480c107030040c0d00b1278010303040e0b035518040214003100303c005521001c032081c0b1802c0e0103d130482540c200000703420450b015401d002c52032a075000080c00034002c240c03040002d620001200d091074000242111215000a41071615206543c0050b950b4a250030440080c12100980c1d982d41924100c13000c1d060940c054400c030200c00c000d000820401d5004051200300c25402040200d41d02e05044414002c00e100c1c101c04a002000b09610450803044000ea12203c2188c0106200d002c2d08042000c88010f6403001a42d5580407805001070b203020b00a0803400c1d04101d00415071582103030000b0303401200a10801c241cac413490074046c40681209109031156101111b6041143e49440a8689921845003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349864 1250 348614 348617
    0x4030302100b0402030105030604030e030c0604060f020d11070506070c05060403050303180601030201050301030206070303090506190f020406020303130606050306010e04021008011406070201030b0310060303081005030309040b130509030406 105
    0xd80c00c10700b00d05003482a00d0417245d0060042406491301d031402e03110b1200007424241c050151012030303021610f44000400040030f5594400e1108000000700904042c002c240b440100013a402c0300c203d00050010b083e00590b40c00300c1341c181da140001d1500034440e085070f40c0000d4200c07002081c000103021012001e0f510902741c405212005000c040d041310b882d81d4007400000d021410610040c0058208580601b0105100341000034070020251a140d2500c1d900321160a181d1440c401e5a2085560310701890554829034071003075081504182020f900c1e404028003956800a4071800d100600145410000041001405854031940c48002045458408031420390080c041591041c216900c1040e40314100d520310025108196524410443c0c181c1c09140268109521000680703010341c0c0c144403440248601c1280050000c0c5145009885d000740201808400040c0001c10041d6850200c2215030f105022180001c4121505e0002500740700d100f80c88403125490003040001c00e40e40000244242d0700f00d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351114 1250 349864 349871
    0x303130b0309060c09010801030303020304060b030105040803150402030609041103070306020a030203010504060b07030e04020c030c01060e091603030203030103060f020d021b060c040609030b060a0b0d020702011803020d0b070207050301020403030210 109
    0xb00c0c50030034824170030600c0f05800070340c000c401000400c0c4070f903002c0d64109201d034401107841c25401c03001030f00b034902c01d030383c01d66003c10000b0501540b00c0d4080d100100d604400e80301076042d8644000016200070b40140f0140121400c540160407540d01403054001450f4030910454031007141003030040080d0824050640102d1416001080c0c40051100343d40320b60f62b041c2c0c0c0300e1291403403010900003e9008140304c0b190342c2c4801c0c400f84051031030031b00400001c3c00c205240e07042140b4150b04aa40f6000d6202034005c03040369400d0007840402d0303011045a0640350400408600051a500144001d101b102c85000a00e88041032008418100d26803284203080c150301200c3c00382d15169041c0445101704e1281c8008101140c50400c0011803075030030658811801060416415901d00701d5a020380e10604040132a04d500154400c00c40da08035a440341c24030940d1071529800c500b180d002c03c0241450040180080d480c07100081d1140b442044480043d11000d402591129583d19010317644041c80b81041000604 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 352364 1250 351114 351121
    0x302090601030204080309040e01020906040608040618050601060804020604030b07080a060e0105030d0c0204020909040309030506010801020a080c03040516060c060b0607030905060a0507060203040b010602010f050402010905010e0303130b030906 107
    0x2090013030b0750940d04104060740c40c0040c56402c0200800d402881c0d01e0b2155000d1002d05080d0751190301400041515403540300742c2c1e1a00349030020854050f2001c2c0072146500400100200d800029001d0540e20306040400c0240c6803400010a54003a40d40003c2c40e403281401004030301e9070310001c4c030f034002c0345a03910901c003181e00c1c0d601030007071002c09000d41d641542c459003400e01c0301c0703102e103070f14408582c00075000520b424020404204614012501600070074034540042040102c10012203004111000c021400c2540c603107001071130054080c0402c02040e00100100d030500006100003030500b400855040d1900d641c8040141103030303080c0403040d141c86240c00001e1081e030424600b2074400c641e15517216584e07241410b080010a40004010804010b030901c60b42000030424802103000e5801024000d100390f02d86500242500d03805168110032a003414140030042c0d82011559040e40e10900340988400c080c02701092541c05241846140f21000d00000610300c0a0800250700501842d402e4405d2a80e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353614 1250 352364 352367
    0x6060103050412050d020d060801060305070905060f09040204020c0f0d11010b030606010507030909060602030d050a090b0105040b010c080706020306010215070206010e0a0f0c0207060306050f030a0609020301090209090105010302090601 103
    0x194120b4000d00000c030805040b40781c00748203030b0052094141d400d41c01030074204000404400ca8205400000d42695551401e1042c407004000d8a401850000410700203464a00c0210b0790250700804a81d0180d515a4040380466940c2d40580f0414540e603407c503034207608074410082d82d5040e003425039404180340000e0003100d504113000b1380f88414009002001c080d201c034001158280e00010080c0c0402c202c00c100400d00030b140d80959401400365600071626158009440d004880000c1d0201c034080380307004c0c41200050b820301c0e203190445100f02d40014085207440c0058038035010f03c0320014102400003d1050070040791340e000e94029074080c1e0840d045000350249400d14914140c440201590002d0700400c1301421b81090154081d516070350211350b0203e5541c1900c01d07a03000000280241c0c010340c030240035103036040c8242001858103c1c1c4481002940101081d03c4031000d0784041c18050300cbe400f07002c081d52001d400202e902039000e04034200c5440c000010300d000380403e0004038440d0150070042002503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 354864 1250 353614 353621
    0x150e0102040b0403020f040608060403050c010606050307020c10030e0106031b050301050402090a050403020109080403030203030f0601020102130e0603070302090c03090d0201020304030503130c05040203070306050111070303050703050a050d060603020a0206060103 115
    0xb1501200158038007401c5030200f0a02105440c081d0b58010740706e40020401d0a0103100c02d0b40558400d17100d554a4259400d03180d42944c200342c1000c400c0100a208014880358001a104144002a50031420a4014450480c0600301d600814819582003040000401c45048507a152a08900c1044081d0540b00c000300b6098034810360f0080d620001d15800f1507200070b02944840d4029100307000025000c5019038079492036800c00d6101380c0140c0c001004010107601700d20022075200800748000c610b844000307040a041800c4602a121001c06410005015600c081080c140503580003020300001d842e02c00d0184202e6482201c5281d094010207280c030f50880d005000381c1340150740c142c0343c0038255554103a001c2c460a0304c0120030342b040900c0c070800091589503840214000c0c00aa0b40126645003800000b4010701c103135005080a9900c0400104042a482400c0d140318941c035140099480c111942c044450b80110300c8240c2046260210001e59960154000c0190007000d400b500c80b16924040113400b00d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 356114 1250 354864 354869
    0xc010e010204030506040813081b01080601020a02090c0703030b0406080307050f01020a09050904050c09090106050406050102030301080a030807051308010902040507051219090b100608010503030705030405010302090105070203010504150e010204 107
    0x1903000c0d17008980003480310009030440c0b22518079000d1900e6a500c000c81c0c54415081c001105007910400c144d6801d580c4041c5481d80f04800f1f000070041600c141d8040740d0308903401410950750540201d0042d08252080d002030080100041060000c1ca4441c24441c2d100c0c1e01c22042181c1a01c00e0103040f40104006001340c6207000e880307032543e41038646031800340418150000c2007183c26000b031000c00b5100c0e47e02c140d4028000c801c100c1c00041c1060402d400d200880340c0d0394222605540c4180300420806000042c840c401ca0342c54580083c0f40e8840060950307460150400c0560f100341e9116000c9100d19056100e0180d00c1c3c000c5074140042e46688100b940c1600c10125050840c4511030005018600c05225415051002d42d01c00210030722651100c1c580f0b40c0042da40e071040f079441032508001090340141003e002d420100c0c00b941c9445074503070b9403d60741d00c00c0e4400e540c1850b40200d03840c07860383e002e00b0941d400550090024003180ca003030314051305100608168450521718104014403a44414801c0e81d09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357364 1250 356114 356123
    0x51006090302010e0d050105040b010509060109050f040b01020a02030d081005040204050607020111030913050108150606030f040f080d0f0606020106080c040b060702030115061209030806060c01090c0b0c010e01020403 95
    0x36100d003150011aa6680c0b0002200d8200d00300c54850400940d09105403403140d4015100c036030039941403a081000c101d202400d05810040d00c1c2d4014040c030360b10340c072805a40a204440008410100000513420800125006541406158286031036a5000b0803a2031107601120380290754030380c458080100301d01803402807507041041884018015402401c52480d02c8d130700b10046174241001980041d0486540700d00000300315841d1070040081003010080120356002e003a84000b9140b9008011500c540001001c1e1010b00b034800000c101031054002d4204019504014400d0380c40c1004c8134607101130280f5200601030320340740410010340c051061044c035042e20a0800070b860081101000c10016100012485921840401c0032000581c0c00744180040c141e080c4903029001c900d891030250a00c0d90482c030f207400c0141072030055400240d22401030b80c0c0c004012503c06440d810f50041c407500401d0036000040c0b00000000d008520f111040002e40104048032000380f2806844200a50903030096120042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358614 1250 357364 357377
    0x10f0c0303020309010f0510060206060603060105160c090207060203010501020f07030203060a0b010216030c0302090a11040303051b0f0c0a0503030408030301060e0102030c0703030302030103020f030109030206010302041104030f1203051006 105
    0x100003a100b6001182c01400d21400841c0054041d01c20000701c60b07050342d0001095040700c0080040540601074180c2c4803001721109411441e00d0b10001e000e512401e5180717101881d100d90810304010016603c24041c0401200841d210b80c400d19040000358421301440e805071055003000340c480d05001030328009695002d03024020b151183c03e0310300080c01280d071442d41980200c0e444421814200c0000c07000460017000014103042c03035401440003418014101c0386002c1c0c01e001e041e2a008100204540840e6031624003181d603500780955001039600721070460798140c050030442d100760710350001e01100e01840c01c94904070741030b50310030070503941c1d1180340700b81702c040c0c0c0051004100b154011480c10407400b0741801901e19146e8a407040070b09010311a0011004240d011005100b941004010b503901d000040d4000c2104181d2070700c0203940d4400521000f4800c0b601c03103c0c02a03044145405031002954401315440d2000703d00d2400002e602285050741001916100000d0a14010816030038102c032090b86403103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 359720 1106 358614 358637
    0x80304030806030613030804060b0603090106050f040902010e040b010509060a020d02060601030606020a060b0112020703020304090510030b07050702030304030b0a0b0102010b010503010609090905070803070302060403030506010f 100
    0x2107002c2d43c825405c0051840343c2d5002c980d85070350076060034000307541c491900202600d0a003c01c5a0482c00220030301c0610601508264181d500445450b840000800c051004a5140d0503000c0c2c0010910801c03645642800c0d4081200300d40c0c103240c0640f4040044010500350b46c000b000c1a40141c0c030140768000c980e9414000c040e0408401d103814807045182030340c002e40c2e4940110b03014048550b1201391b10b071305a009003036000103000f00043c03c2d5200c1c4111308003c0e440c0d4215100d6990f40a00303020018044d01c0c03c410482003031f03a43c04003201c0400d882c1c402c01101c4030380190070101c2e0544400c02c804800f045502658a119440c0c05201095400001000a0079900101000350501100340018081d003600030984d00141d40d1a0f00d0b0004280202e410494541030159001d41d102e8040064002d052550100724580b2481c001c0c0c0f8140300d03d840f02e00045030300407204191000094a02840c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 179864 359720 := by
  have h0 := BRFrame.cov_init 179864
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179864 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 179864 ≤ n) (h2 : n < 359720) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
