-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2197
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:53.830089+00:00
-- url     : https://prove2.me/submissions/1ef84ef0-c5a9-465d-aef0-06ba61770220

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 394964028 ≤ n < 395143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 394965278 1250 394964028 394964033
    0xf050c030f010b0a17120d06030501050109021c09050c0604060809011b020304090f060f091b020c01020a0321020403032003040302131e060f03020f0a080d08040c030c0b07 75
    0x101c0c00245800400801000c54101e0015180b0702403070040300e10a458164000540300010401c0340b180000c0701d00820345031408010000082c0055000403101e030350919000003540000360003502c4040c80c1c41481c42c00c146840010f018020007000f8025a1a4407039070b99120f405446000080019041907a01c0040340e1500c000c281d0b0075131380c50714060001e06940c4d0004015041c6d000c420b840946403400404155504021180c501401d00ea03040801d40c1d40c18420001006000b95101c0b12214100c2e00090078108850030042e40c481c2c0502c0c51090142c0c000006000c0000d00c1202e581c20140c44a00001100383c400308100c108980040d0011000708040c4041e01d004904004c00302014a41c0200c000c500c0e240c215408514418954103003d0300c000d8a4000703913002c08020306c3c4002109200c01404100e01c56490301810408038141c0320903401280110500d0340d0354140700d06894207881c01200202010903800e40110741001d0020420f070340306550b8410210000b55810607903001842c1c030780503064980c201030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 394966528 1250 394965278 394965283
    0x120e0a050d050307260d1d06010f09180b0f07080c0a0c03050a020c15090f0103060e0c070201200627070501080606070503030c03010f170c0f0604030f050c03 69
    0x150840c0e84141d04592040d0300144001088424096200101c0d030750303d184420303609005110112040010150100e90860f0508483d03100309901b488424401c055034246030850781d100c0e0020b000300c11004100c824107102030005604140e14000d070344001d2001040c641c0c0c868007294002078503e03004a00740a41480313006075104040a070840e0106103654070b00708517104003a01c500c0000100070103004002c6450762080b4000d200100008102401025000540c807400c62007641c00016214414007480006018551007071040100740c4660080d803a5140d20341100b801c9540d0448041241004007103c078800c8644840d0f15030030700f0f5206040040055042452305001d140b0320304000c4601e42500941c51031455000083e180007122001c0c240324466803140404503600344160540981188800002d1041c0120000002e504031400e0704040c1031541e454400e21074054907800b0400e4075a5000c4006003580d4580000d40d6101d9107401451549060f540c0d07070301d40007000d21400003a41c09404c00490b010281c10103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 394967778 1250 394966528 394966549
    0x412021504030c0f020d120f090f12060915020301030210050c032a0d051909031203111e120703060501021509070b0f0301060f02012016120e 62
    0x1580050251249110100c500203040204050100201d0707210f25014402100c0f02241070a130080c16182a80d811800d042d40e02e1904441c81d0400503408070084a10390748075103100c0d0180c414094055001a1510360018a02c040310700c0d00340d030b1840e5900031450000d0424440501c042c4544440982c032585140100104014038040071001d002082041100d4013101100b140e594400000303000d00307022408001c284c01c030f60701d5820b811403a100b2a101041010741000181c04096400e48801d10030001c0c04204507425091403000400000c00032603001140c034020f820400301d480000041c1c50800710b106415000031440d50105009490001600410950306490f505502c03004508042c4070300c91806000030741c0c1385410b4a41b0202d102200c0f000c070315044024082c58008040c150102074442d480c2c3d03035480440b54002c2c0309030310129212013100700c0b903035006005004c807800030400f41004404441c400d014250303120403807840400241041e03c000084c000c034052500c040850740c031030100c600752a00380003040b100e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 394969028 1250 394967778 394967813
    0x11030d09080f030f0706020a0e03030a11010506060a2001022203050c091b07060b0405070e03060f10090203071205010305010c1412131a0103080901080c0310090c09120b04 75
    0x204000042c0130079040e070121546154000b0f8010395844010004484119090f5046545400006505440f042c0d01c00c6070b030010780500300020000342e2108010000103208600301c403008035040100c007084103524003100607041620040007502d45001c01c021101d2003060356400d1446401c0444080c000d00c10300300301400401034181c2c0d1080719030600d5a43e500744000c0410010350040c1e0300241100400405070028140d0300b40260080c4114244030300040c20300c0c070034400321314020701c19000040c842640c40202c072402281c28034103401c103039810301c9002000795200400032020700c0444117000c6c00100091048078000c5006a00004009410000080c219040c0d100780071079851050100c1c4884200c038a2600341c0145124104030040e06944c1781a04a18104101042103491410300001c00d2080030700040041040990381c200c003d541d1407107054030501080d201110b00030f1001d9070910002c4515880500c252502d810300d40e180d51340c1d40d1072500380e04542c1203017100c1081c103507000d11042098109010442d4075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 394970278 1250 394969028 394969033
    0x918060a030813180e150601090e0a020a170c190e030a11010210020c03090d03031805060601120216020d051e0313050a0b070f21051b06090a0f11030d09080f 69
    0x64240d803c841e0365680481c2580c079400703110303030201f07031944c0c0502100c0b0000e003456000c0e040c1c14030380411154000c0d0418200300000c50007a00c020b82504450010b018070524248102030705004001c00841c958040300d030045003e00420780140705142d6800c01022407980d2046a455000680a00009040c010303580b203242d071494014002d8068100000c0b00f40d6a9804054032040c80820981c14210080c06201004240d02844a401803007804404500144188004c0c0c8a070106114404c00c1c0c20228821912600c1b0860702002140c401454580541d030390b0180200116826180002d50032056409481441da4840e0310001e408154511b111a00400914040390200d00480c9092440e002c203200304c1d4002046004006680802c000d03050456220006a90498402c990b0450001808980c805076803101c02d10b01020302420403c40000701c0c123100761420009024413040b5a0341e8614100c011020481c1d524a8281c881c60094038200440c0c10082101d0341c030310b0365061411554a0034142442d54501d2541c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 394971528 1250 394970278 394970291
    0x6090c082d01090821010518060103021b07090903080609010f050603250509040f1a04020a03021b070e0702121e090d030e150918060a03081318 63
    0x740011408882007681440c030501d038800c010300032a0043c000c00100420300c0c1004952886800f428050701d031011440d000d40038102e640c13900308118849220046502248100c80005012544260064601c1c8425141c009002e8400d404110303040030b0154100202c803039510444441416480074049070011410350f0040c0b444c0d4180601c003404d5403490b02400e401040c1c00800319084000400e40e01c688020f400c2c400c885906041d48001b03095038403005086121b13906100d0070070b0000380c0c07a01c11050840c851180240e40c0032000e80c20701001c5c0d0814000b50b001d240d8280f10300941040069180c810451206010380103941c20441203c1000002a11000c2150301c40540c1c4940c818460f01215001c0c1c1c2c0c00c80340020080036014612000c4d120b030340303c156040340800c17203100f0030540c102c001040221000c4450303020180c10303403507010158014400781701c1d07000346007880103501101c5540e529a00514040d0086440545036202c1e10500e5115208045084010000800200f0400044516202da011a060020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 394972778 1250 394971528 394971553
    0x20309010f0b09011e08100204060f020102090306060424030c030b0708070f051b10050403020c040e15040203011404030509040b010e010f0f09080a0c0f0503070e0a0f020702090406090c08 82
    0x4405010741c1d6006101030340d2000111081704002d60092614600300c0c1c503101515803c00019420601c5000c02141d00c11405104082c018001c1d14032211015000701019507541c401c000150041d0b8070050303c48800c01101503080300d1400d8406020707500652104c800075140d46808041024000c012201b007049520070700104640c000020b4000022518103a03480f0a106141c5c0eaa01da005040404040c0c0318128080c984803440c1c1e00072600c01c2340203401f602d07440e084400130b01c4291075134071a000c2e03182d40111140240140d1001303405600f1a002400000701d4020014150b08205010b44040d0040b030000300c0c030704d0b255140c00c7c01910541c11080c0307084420103922100207011001001d14020601a4030a4040011f03882894000014807010089891601c185d05090640310302900800302070f078000f44070204903400c00181c3d6408403540c0680c407180542d02d02005100510001c4040c03030b0429020441c1342c01581d110800c05000cdc9006000000381100300c0d10300164551803c0c2d0010115800c0210361070407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 394974028 1250 394972778 394972789
    0xe03130b07120c0302012901020706020d051615022704020708030c0d0f060f050315060306010513060305011a0f010e01080a180f2103200903100e01020309010f0b 71
    0x581003120300f8280c4240c00b00b407500b0f0340549100d07100c01c0c2e9901001540130707151060f91320302d1001c420f40a800f40c624140c1c480e001240c030b508406011b90089030040240c00d0041201100f544120b038040c20307001d40017112101c200c105981c0050441e8a400740c9003070aa00101d0507820120340b0092086030114a00400d0b82c0c5d5035522070200900e80400c0c00008100c00045a560346c00611030340d841140204001c50311400302c1144251075010ba81c0c0a8442c0d04044003624614503110b90080500030004d004580c82c01e400c02502403806113040d10120384804000000420901403181c5c00104801003a035041050740604c00b169481c03000190401200002070301c2c42c1d1760002e01350f41d003050359250042509415454072172840b2850710030040036036801c100250144807030012013000c0e0341803030080c1044040e070140d011410742d4058034544e11286000c007405030020302c0050041500c030380060b0594603081c5541a404040750962a03106490765000810804804c000b0700c900b10407000c188004000d410040d030041a07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 394975278 1250 394974028 394974053
    0x50703080f0702030a080c010b270612030d050a0f051605090d0f05100e280606210203010b1012021303080a0e0f0a05062b0e03130b07 59
    0x20050540040ca48035440c500d0340446910700c0c2c003c2c4c01c442c2c031481a46003082c903d0384a2002c211a95107440c1a0f0480c80c03401c0c0d0b41150351009488145000c10030407120a42506802800040c0c2c050842c0408006e000c0e8240040c0490000303180d000945440c020081005a43d501115442a0780c0352000b013103a8038007801d5000020703101c549085d588039500d2034042092044442c60203815010645081400c01500040c80c1000c0c803101e02041c441125004072032650f814800d9807003a8042050b89001103880395640ba0894181c0c01140e0100d440b40ea02c055682e07a40603161900580107680b06000340035800d00740130304865400180c0ea038949032103a4000c000c00f014140c0031079011103900007941040b032607036501c5c03141c020396082103400d0303a103a088040144c8550304500b1014040d00501c2c3e02c00826180901201c4d003105c00250000d8580546185404000d0180700701000590500004442c4940c1c81403042d1034174500010000c595408103420f55900f01080740c3c0c06070100708000c110b0440000d101d0094035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 394976528 1250 394975278 394975283
    0x30c17031602061c020318010b0306010608040f060905150928020f04181505061005070201110f010e1b030304180204180b040e0a030207051011010504052107050703 72
    0x100860341c040d100062040c4902c0b4070200e5016010494026071400507030055000365582030086160b107203d200660700361880301c02c80316030680002c0c004010740b501804556510074460440d41108002c43c0e40d85038121509010190745582c010009022082c0c0120410b64028107501d00900440b0380100d03007280300c5041d0403007141500032031411030011501c8000c09862610001402480b03092004078601042ca1503440c015507616035001c56100a01c01544a001e00401003d408501851141001554140e022084c102d0421804444404181034103003c00c0805148600020130b4060121200c7c91604a661400c403201e020400c240240a81d00003007200c0498014170850742d801042440690001d0145500c024010000c0900c650307150215039000e40a001c500f182d080003074172400c81070281c0c0d030075103040d0090145e4408501400281360408c000e900680280ca810404810034010040c25140199404c50741d660080c01c0e0850740c2d03440071241e001e989008204503400c0c00c00c541c58451303540c002448003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 394977778 1250 394976528 394976557
    0x302073e0f0d0204090b0c03100e0c04050d081905090a0603141810060603020d0e03070b0a051801141b03070906031505030d111915020a0201140907030c1703 69
    0x8074115220794101e11780850b0844c005005d00e144c41d005101e86903004888800b611120303010041a46020f006080d402174071019000e50406003031101307000c040160400300340c40f010002e010204c125900d00041303a0310f441d0559540c54481c0d801e11f050020a1500390041000c1c0742c01c0c201900107a18201846e00c7d4813407410040c8a00702608003075030a0410002c81d811502d02070400c0404201250550001c140c0505165010800c030317181d9025440d280d01811400902c400b401e1030118003400c5407034202a400503070170060003600300f4003003032124216031050844048090380403081000d080520302c4903c0f00d02009480c0c1c0c40c074602d4501e0300201440114011007050560381e10a0b058980501111100900400340480d98035401680003e006202c604400404038851280800c0300d00821114a50095610020000f01c0403407454810010b0740040c01e4280441d9a6400d0005000444690b080d0284143d00c01900c51513042d401c28000160751500030342242a1040b800f008181c0340003044402c00d082080d031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 394979028 1250 394977778 394977799
    0x308031918080f0315031e07150806010e150a0c02090105090103030c142103040b07210e030d090b0109050c090a0e041704060201060e060307030b0402010f0302073e0f 73
    0x80c40144009034000786031b054850043e030b0019401114420841d241c0f007440469858130303900d00c07545405c1415221000c00055201c000700e82d0365401000034000b2160014961440c3c122044412440c80d00a410360400241c81000c140c4254108804c2160140c642510003020541c11500c5c0940340d031a02d048010203c0300b41081c01e1031960001c0c0804541d240d054140c4245240c031004043c0910b410030b442c15540030114902080c80d4502030464900c4a854500294169400001c00304004103541102c0030001c2c04100243c0d071a07080035204d14214503210322400c0302154102009541101c0c1c4c02030100869900411038614150b07206078003142215074a075224110f660301d83c50880c032407007180c0d0703d01c0e0340d070140c081030208041c4d4064100340c1c1a01c54442107100700e0b43d036540402d652048148030140070304001c0404180907500c5086050840b001a04000d440d05c9200d5850740b04400300701503007480800c50124500c0c0200e28000c80f080f010951220440c0301e6501c0400020104050120924800e505400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 394980278 1250 394979028 394979041
    0x10603022409030106030b0610020d090501120b040f021e040609050904050f062403030304020907050306210106091a09160c050a05070e070203030403021002030705040308031918080f03 81
    0x28110341030350b01e02500030310009903249400c440841b42074560718482d160145000c41c3c1240b0000e04d400841781584d84003002249450015a4102c1140d01401d50716615004607080f03e0b100c0c1d000310001c0700d072400401a40c51406146402440e10030700d1b4014480d0200300030800c003080d4040013250560310111505a0703da02d5510341a490141000384680d6240200e1080000007201c03100d80f0f81150802480d24840e44104c0820140c40340b2044500070f5001c0760f01030120701e03564130079805154806009006100c40c001c240c015107900c40460583d900c2d841e91600c40510111415005e0513040d120320441056911010800142400c00001d14007400c524410803d418002d00c40e03419540e80603000703800e6560745c0b202030400544804803401290158844c000100b2640c610000450348119013541c09805507140900c420000303944040c103064100141030002102203500100150b020303495100290800729807010001c001c0c0c414140441d164000e140000fa8080303581c6070f08940e080442041519500d540701d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 394981528 1250 394980278 394980349
    0x140f071b0312080108060105030703051203060f210114160305070212040902190c0c030308060d08180301050a0c1d0613270207021c060e1b011101060302 67
    0x164400341c14040c88910718510242c000f403040d4140e8400c60151440740c0e807118285566000c0510000b8040d07801a00c60784440c0c0d01100c05140c122500508a8103c110044001203c050700300d503200c0c96144242c83c85050092003480340e0b4425034080c0070124120300d40b840300b00c0f0307030074400854076014103881d100003641d69031080c84191800040b0703c0242e80c0702c2d500c543c5c82100075041000b0f0b40d0314400c0885445105207000d200094030b1903520240d070303035515030555070b04544907c0040e00c0303940c2085039074108000040e9108081c0071a0350907030417400110300340e8008142c2501c4d405400300d8405450800e5058440da48210940d90082500c441d1036246442900850303072a03c40d00040c0c01d260080c201010480103e9a1403900d945100107400041d21540101c10008074401c15000a5224000c01456500724021603058196540914000070318105030370400d0b070410b09400f01692042161080c14000c941e040b003182c0d40607074003c1000308040c0c2c0c11940420f03403400100015030411004070070380c0c1503100c404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 394982778 1250 394981528 394981583
    0x10c080723030c09130501032303040b0f091c020a14010e0a080d08100b0a030f090f060c170103110103090c080a080307030b090f0a0e0c040e0706140f07 67
    0x41e00c1c1c06950b603141c0b009010420f500242440d42c8690009052510400c90602803941602d41100080011035250f800d140110060440400d415000074000000d85d14003940260240024107082e55503500900010070500b142602e59050202e115541c451700541c50340781101e41aa05601c42c0340d45551a02c030016100041c110a08a034000820351012540c0d41c408a9440f04400f50364846180b0794a0b20500345010b03d0310342c000c0300b404d00401c0c411110414806d03084140034284d51000000c0c081155110b00b041154102015501c03103446440701220359912040304138900704114407245055045607035001c40d001041000c02e0401d601c4007081014043c075203070f0440082c8078180445901c10300394030740381410350000c44e441170110345400041e01e124241081c82c20321441000d00700b00e4144e034a01e01034070002c00c994030300c0c030f0203a10407482c00d03120036191031065800740d01d15400200001d0f4a8528001d10311404207000c4240d440c41171188101c054028403d03038031501e40c000d80a2180c0c0301c501d10001a036212 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 394984028 1250 394982778 394982837
    0x31710050a030f0c0812090613170601150f1d032d070501030207020906041d0d030203190b09040312090804060c0302070905190209030309030f060f01050102010c0807 73
    0xa40c60000002c100c01c980d00d810f00d00740300300c507000c0c0c0841d40c0b140c00f0ba44a440030030a40720360369400c0000390480c0ca400c0006094408601040340000c9842e8200000502035024900700513030711840061088401c02441000c0c41503203031602070a041c180b194000d0400d80d807850408800c4101c102d00e490103a600b8460700903407110606d0401101c0c10341c3c060100c002c080740408455140903d04000c502d0b54070074021200c486030003405901140c1c41e0a000d10000702014543d09040e10240a0201300079501400034a40320f860980d00940c40b13042010421042d800c1203160010795510b8494403441c6034480140302079100f605414103000d406280640300c006040b00350030040a003400000c010509581118181461074002c2e400ca42049450701304a000711768061326190441800051080c156200c0c81e00288144078019050701e04000720714001c6403520404803003000040c2c00c840304011440c0705440e0480d0061000344024040c260140c040603082200c06404603007006205c8114058246940410814490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 394985278 1250 394984028 394984039
    0x60504030b040816121d090c16080d141008070b0307021212090c09010b030a090602190801181803050304030c0c060503061005040b041e0801051f080a03171005 70
    0x1800b46802e00c117404d84c0c8400d141c04039003d8540c0c0d881d6103001150164038801e000e08840e006e038603003110100311604584005001900c60030341500000d80c030140600382c8100c1944020030350001e5090b0907010102d00504d03135158000d19030800c00c1f0688001805008840028920965030384a00408078241290a440410b40c00d0001410840500000c40c0c03440c401e11003d4141c035807441c002b40c01c0004500081c071580410090a00118516400e10b41c8a00502d074811000103180486032413401100e07882031071821001c02c0095004021003500c1041041608130200b00411003403490203120700040d8000200507081080100000c0c04040c01083e00d5214250842c520020706c2d5600c3c03400500b554421195240168101945c81148034080d10995065030070300319503203081506014200700e40a0211801c1260215070303103800580740c082032080707a0240c0c0e40e50040301c4c038403200b021282c40100c200340d01c80201603002001c01000b00382d1104030040b10440003d00c3c0d0300315031280300585035000500d80100c0e0340702 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 394986528 1250 394985278 394985317
    0x1503083001030c080a0317070e0301060e0f060105211005030f0109030e0102161401020313120515011202120106090c030e0105100803031f170a02030f07060504030b0408 74
    0x80c20310590030304803071042a545403840e0711012015201d068540000700412006c0c8030108102d4800c1c9182d0380c1c80b020b1464005004a219030010b0700f95540307648503081c4c1080c88401d100c0504031a0590690004080c00c0007403900f00c0322500840d0195810800c081c140b411071010170014140c888049004142c02011508070650007403101b4001c00070300d9801c0700855280c50441581e54004504081c50091081c1085456403400e00600c4001705849a42e078110f000030013030b80428203035008603807001e0402c0b502e103054003114602d40b8a14024498450140003644000100842c5005100d9020443e60640b030010301d020b40848036502410058111104a0f400c151444503d141d059105010b4201d92600a0050f51100c920040c08007590b030149406a41003040001d03502c070213044800c0d5524400e800c0700e498080da55001c0c02c800c07010007841c0c01400e801001c2d0340019482d080005280c0364558a02500c1e0701450090068010f1240d44401059440c010700010f080c0a480303010b43c0e00e181202d02c00710041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 394987778 1250 394986528 394986607
    0x4060302041d0705120304060503090a0501090c03030810030b070c05010e100906140c04050d0f1a040312060f05040b04020d0203180609011107030305270304090e01150308 75
    0x50141030310b15000c0c4210500015a072808081d050701040031500511f10782401c0c0f1004481d5030b40b0007854407005224640d5410000342e02449440c0c0741d00d00414001560702e043d464014491a400b415503045111000f0060001c280010080c1c3d400001905000e81294800c3c40d11501615180c0f0006000303000d804180c03000306865820490110303101e4101001f072400098500b4022460580d101d401e05803042c0020b003c18100700d00c0384048140a0707503514248000d16581c8840414003000d481c41d815007028240f01c03c040e040a0220f240d400a0002840303041d0501d05100a800181c1c400c040c400d5441d4241c01030551a00c0c1c0c11900d0a6814000956a1b4501074202c00c1c9440707091b407101d44c0301d1f1050400058010380d041c42030400078001072020302c0c50002181c404070064040a00b400c0f84c0711034200000a40a20242c40103011401c0f1000030f11b450760310f4441d05804813021544520780703a034182040e450380000e00c42641410350b80e2124200e40c99030005001d0345018404081c0c0c803461800041c81d10580d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 394989028 1250 394987778 394987811
    0x6010510020c04050a0626061518041a0603010209010f1428020f0a0f020405061302210a060308040b030901020f030406020405100906080610030b040911040b0102070506070803060406030204 83
    0x240d80c01d0051a001d651f5011000e4001c941c040c90520b0303243c3d04030700301040280c015a0f03030031013450720001c1c4200c0d10804130500300603050005030341c00c58400640c80d82e4103001a0300b0103405a809041100210308102c48c1030006011840500701c088200034201c0f04044c0000000b41c2035400105c5071400d812150600c80c188101d07039004c2c1100c0500540f0441c2140f2582e01400182d41000c29801b602001c1070241640c24400a00000b07400c076603102841c070002d018140d04e548040c151401c07045120041c03c1038015600c6e001c090020307006038543e508110040c0301040b00300041300d04460941070070641e40e81c4c41d0540300b4028051401a000c1c040310000502080c030030f030323a00600160f80c0300300c443c3c505414400360180d60f1841948240c0002c12444c0001601a01e401d2050242c0702e00740e410089610018000014202d4a2036201141c7d080702d44115041c2c01e0410740f041c2c0c49809000e00080180e24209000a0030500034440000d04a0390000001032107134a8903000a0000c5a001e481800500d20340b06103001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 394990278 1250 394989028 394989041
    0x20d0f0b03060a05012301090510030f1109010c02120a02091f330e060f0408120c0616031401030b070e030c1f02070b0705070503100504030206010510020c04050a 71
    0xd01c41e1040b040820000c80c070720302c03a140c103d03064103075901e07841c481199461003040702807503506041c0000300b85c00103610b880d0f1940405461943d41d8001440b6402d031300950080710301c0f286113207241c59020b00c61055141d8200c84403143d055012076074200020707200c403840d81c94650b21050007904a041807080c841c0b00704d0300d0802c03496042d56190005a0890300e8160a9803510390700c20500900c4400001031003052110000c0f0741d03100c900285820b1805000c03940125000341d000c56100c804510340060200700e028800d00c240e100340030b20347c0701042c584841040d6103907031810060411542d005000400d01c00320b9001c0d5108011480c0d082e0048449580e69080c4482c0e2503400310341610111701403420000041c80d004c240d104c07035040e00900484000008201c1d0741d4101d14482c145009500c1651804606007200c01e003c0c1040c0b81c070482c01440060304000a26040100d5031014880281c05c01c800e1100090b0080b450b50b0541e02d040c0c48030b040a0a010310b0491414444489050700b29150009018508070700b070300004d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 394991528 1250 394990278 394990301
    0x606090609022a0a0f060e010c0f1805031216051c030e0606031e030405090a0b011e0804110a030614071e0503041103031b0a110103290301020d0f 64
    0x1850202d00f050f03142c000503059064801d1507400034260840000c943e906501203440c0034a02c0060004207010405007180d400003d60320115100040c203000182e4800303065104c0e84030b00410389003864a0072004c00e81c1c4000200a40318820000b1410a040c50050025540819048011a5198442c02d40c0c1e5a00c1c2d605410a001c000070b051207440c0c0650000000d5144c01060080c006210051441c41c44040c0400c10b44480042800104000249903403103001080c012240404d0004440b120b210000d85a4802147d050050015942c0c0501a8503041000664410380241c00c54113000b00a5000803085280c1c0d070401040315182030000540810001c600f10b1291341c1c51785516280e52520845204120015555400011410000074000a10400c500903243c03002070122428910105511102d103144005100c095a0100e02120b05005c20080382c0c1000003004e0030201300c00245808441040300491305d0010020035441c14107107030764500f541101c28007218003004000000394100010064424414072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 394992778 1250 394991528 394991557
    0x60d150b090a020a0503041b150e030f1c0302070213060b12090723040e03073f0c0c23030105010504020f190207030206070c180e0d0c060609060902 65
    0x1824990b0309108641034640c2c130f0b403104c500319a0780f40d50b028222142c40007e491a4000020001509041020b02034400340c8070351100c0d00b0f0704078920103161038040d041c3e031480260383c807000b45030001e001c0154ac10500d10005140143e0741d084540040340c0c1190310900c4e40c000003850100001016178040f8090820710750840064011626498100d40c0d8a603034030f015081410400c1d40c190f0310300c038520b9482d0000d581e0000c0d01c0440c4412221040f9800c0d900310308015940440d0440500f2420280100541198441d800010b002e40d0145070b8020302e41010f405445060001c000c0c2c4030414020085602002480c0c8035184600c40c944c859680c611401070301185900a60070600049150b00c0d01c5c0c001d9817400400d9103e07803070610408079114040003600141d1407003580140c0d4408005615140010b00c2014010203141c1e095924111000490394030084203603d2451400500c1c6801040206d0045425506443c29034981c0746507051a1006240c20b612511401c1d02e8a50000703844401034014041d01000300a5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 394994028 1250 394992778 394992781
    0x20030108010b0a051302130801021b0f0d050a0503041406041415060916051e0421241113080105070c11040f0e060403030b091b040e060d150b09 63
    0x40c028200f40c0740c0181c0742e00c900000c1d0003440d1149150302800001c2c091001c0404910f1b41c0303800345800c9a03c0f031a00003411000e142004180c000040045090281100c8010030340100813040c020568055031125404104001000c207060051412a07800d0b4015010256161750800c1d2606400c144042c0080788014052000325170110441f09443c54410308010300324140b690b0341c41c40380e044101c9408007040c0c01c0c4101407014130041d6031418007606419059181203550b0324100701c400c3c80800e14510715001648850000b510000d0310396003206292160382081c40c40c0807807400f440003020740407464600c00c440c28041107403c00380c446903000d00100c0b402100204481c2e00c0b50f59084070582c0130b201002d403e40f654080401c4407800d02750b220480504c0184400203480140001d410304054080d41d081d00002c2c1c0714550314281c0c0ca4820f0b489a040200c0d01a04840406c80f201494103d010314428442101074440c0080c00c192100000c46000d2644122110600084c118640c4020301d03074a240da0780282422030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 394995278 1250 394994028 394994051
    0x1030507110613030207030510090c3201031d010f0c020a1208041a04140705040e0c120c180f0601020313150e03030c0f100b01090e09012003010801 65
    0x3001d0a10101030102078111683c80b9980b60711003001d4801d084085200700d110020105409224480e400050240085051080e40c00c203000441110341000921b090b400000b17000c5038a50106d0303420940d40d4010510200210b10006800070b000300c00e00c606010290382c003640e40d118010340c403180c1c0c0443c00700820042e5817280c620803640c9140700c03c1d0040419080222030310070540511805da501a10500f04400500340320043c0e401e4184e0151000c44a2402180031101081818400c100c003506080d60100300407469000c10a40d1007080e0800070703014035071078003844160807020b01a60741e840601038258541e00204d0011100404030464002c3c01d0101500b0100b8415803011003221640c5034046004070f0b2581c1000708600001000d02000740030300881044440c40c5450501c00380141030094005800c040c0b0003820054104246c03100c19111140c0f81c42601501c507a0060041025541007080c00c0c8030550703030b0602c10341c0102560002030750206844e100d40e00c0268801001181030b40c00700802444520442c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 394996528 1250 394995278 394995287
    0xb0306070e01170601090b030411060a0302070201021c080c160f0f2010030f09060c050307121104090203090f1005100806100603020f070b0109090b010b120412030e010509060601030507 81
    0x43d5013880c0001c400980c2003044103600c0c009150007600a2190100c80e0020b4400505654410f40c0400003203500400c5440a541c0c0505c6480300b10700103400004020901c401c0010076038180281a4100c01c9004600580015040520841e105621242029294005003440800c1030800c1e00100c0318502d60000c482440c05008208541c2c483c005011540c00261112040d0003400003030401400d501d50b41d510281c04a2958000c0c1d9016075180d4984555a04200034020203030b449415400d480c507428143d000c1d09160310002250100e40400c0d00058032038a43d0081c1504010b00310304050b0080c0314504242c0e180c00d981e80c2c4601e000e588010485404160390300304254a17004100cbd0b9070554104200d41c01c100c032078000d800400d212030020300c400345890a0b59032100682803081c0c1040440c00c0d91950082c00308101c1d031504502400d001d418482c208800101088980034004000410700070490010809140c002c0d0021301c0d845102000900040c94047d0305555111821070785180000d041c0808070b66114003d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 394997778 1250 394996528 394996531
    0x92d06090b03130f050d0f0201050601050906070204090501140c0c211603092303010509010b0904062412021504061d150a0f0201062114010b0306070e0117 68
    0x1038035000b415607503001ca40611000c0c0461040d01c200c420910b80b5000920300f88917403800c0342c445413208034201070070b030b400242121030040919060100c20002428070f5510902a5246140d0484d03001c202183c151510f80d000d00801c401901035640140e050003000300e0303070101918055100c4421580280303031030405161402900048042e200300108580390040400c7d10080040c18064142000035a07a01c24170080481d110760981c080c05c2028086026840c9020b00460350030012010007880f1289001c800100d40c204003030310091a00780c1d180f00802a80212548010004c1039001000030740e203075151894003101e03a20395012413240c500d86650036000c107410019201500e13460340e41c020345d0380e460703411140c03c9580007610194460000d00c204c2c0048948140100714000c41c640c4c85c209003518a84002c0d081d20085e40203428544144103074482c0c3c07007031f0b00b40912000e03c6c0c11039181d840003107600300028014024210311a400d4013031103082003070f00c603080121542c80107801c0c1e03500103041c208850303042d034030500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394999028 1250 394997778 394997789
    0x1503060506090f0406051009080f0a030215100f0b030a18050601150e030102040f1505071104111b07140603010305060a05180708060412021b10092d0609 67
    0x10b0160524500303000e09510700380c0340c0191001031480d0b210070021708200300d89418100042c02d01c000c01d1210b40c0052007842190400d44000b4040b214031740e9406511001c5d60092504d15401507000100b58102100841006000c1c182420b414282c0742c5000d10380d1580304943c084c2c805410040d0700100705000c4401c1070110358110f4090151f99090401200888052410820812200c2c41803400d00781d500b0b100400081100113482c0c118180740c46100302280c1241c0c0c40b40c109120044c07142e080400c800c040c280c0003115007110001044602d021079212240104101d5000c05050500c0c034038940354000070080305030740030241c40840b029103a00822020744000d000003070854002d01c0100e03a502080e5042940c103c60307244c183d00b01c4c0070100c52400e407a11003d980807101a5004c8001e220034030100b0125040003141d01c3c40a03000e040018031134102564070054170280180b51b4030702c04241c07851081c46044081d1241c00c001340c1c00070095007418002980c3d03100000095a842c0f2400044950107245c1100031070b00c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395000278 1250 394999028 394999039
    0xe1602030a0e04050a02090a150305060d030f14040305150603120a0c11010c1a061503090a0311010f0608030d0f021201140303070803010e041407080a0b1b0304030915030605 76
    0x2c2038202844060400940866002a000c1c46005042e13610740054201900b104154001e011980d5980141628800b400c060701410080d00038201099201a00c0c02c8c080c54181000c0b4602c1c0ca606101180724404e951020302240100c1390416603c00268290f540180340c04ca04480344008140d402003d41c0c865207000c500840c00b10142040001c40141662540341014100b01044005545900781da0182ca0381e010040c0b200b08030104803803031818405000022203010a40c5040d4a01040d815580300c0c0180009000c1c020103211200e043c0d0000d40100b09450034507581800102e5440e4040c65172500510a1642c40340e040005205e04021103100b5250169410840c81006910b0071210320b01f00f4041c0911550540000c10810001c00d2040300158001e08a4120300c03d031a01c2c203820003a600229070038880400c0c2d041540c0401401c40000f8050b120a504091007981d66291a03412090102821895400182000c010802459000007103d002c0314000c00d1f61078040030030303a981101202c0581c0900c40e40310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 395001528 1250 395000278 395000297
    0x9050c011709071e080706050c060109020336011d1504050c060a030b0603040305070201030509010c020d0f170103031107080c03060112081623010b0f09041b0e1602030a 74
    0x544e0307400902400c2c168130340c01c40c1103064450540608000c903e0708100042140041c1da01350703150301080f1650042c1451841142141043c201881e8200742c1c281c1c050b440020b100b001129000411107007034400c0080b00340204810016007000d10708440e082110400039010724019110310700c4106d045548241d520502500c24100e00e80308108140d00090050401c0640c0e4015002c0c150b21070900850080340291101038075206c0c94800181500e80091109103d80d0400345071030703142a00080c0700051f0820500307008900e440c8e0440110340d4180c41c04100c24944030000000806e00d6040b0689040000072602a1011580c03035250035070303940d01034070603098140e0310541c01005000030189044208030320510103a86003d030f45d00e0050310100c12045082d90600000c0101001e280c51b81c41c890708103041d18800034003580801c0c4000a82403058501c0d03140c002c0518100140400105122011802c00c3c00c40b2480c01143e19904141c1000604803003880fa40d01100b0b070056581c1c4d00000503102110a15030b00e035250b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 395002778 1250 395001528 395001539
    0xf060f09190b0105041d0c01050d0209030a080405041b020c090a0e2e090521131203180e070c1103070305100f0203060114090102070909050c01170907 66
    0x248020248801400703410360045010001070031a554050107000d005100794142001c00003101c1114185d01d0f81e103610410882c0c0a4640441d046240480900700a915040c11141400c0a4458203c680343d15006541080c010845410b010340223907042540c00b0828691440d0611060b0480000c81a02507071001a80c0000d614261315070030b50020300b882011a028103010750452a00340b42218000100e18020781c0810003c0501c1780524000300806c0341805034280a8403426140c017071712a204254034024100e0b0403a0f00d020201114680c85c02010f0003c030710703941c80c03004038485280080300b100056080c0b40c0f080c250000392114a42524881c1242d00b0854660520680b0310000214044a00d130310901041c001694040c081100254004c0e000790061410405420088407600c4a003e0220340c03051007440616640410b40a281c4c9190041c0709a4541c142da0050303142003061750160b032401e410f160f0940c0c00c0201c00304003009074602c02e0301c4624041100b4040e181020004407903800007a0702000c0c00300503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 395004028 1250 395002778 395002801
    0x904060e2a04120503090a090b030609031309050a0219051806040f0902090d050706020a02030601081912050d0c0e1003050f07051e040b040f1a0706020c1e0106170f06 73
    0x40c49110704d04481c546204a40407a5407081c030380e407041d003440740d898034809294142071080680c400d441c540514074040d030b8a500d4a445442c540545002c082d990800641d111031994121880075400c2c03202d079503240a9080000704264040315906542050b8800e004805007003520076503003503800010f80b00d07081a0500c4094030081d002000d0103507011010148400100301c0070300c039004c040c0c010350307010309100020350045c5403a020040e80902d085a102181c011910410000300c1c00d4880e80c00351805900315090070046419010b030800055030586886003420326290000001100e10000b1784841503d120078035415012100103da40d080d46505010001f4182441003008041c0300048102c0b54500404d07a08405107180c200b47c0040811882c0090140400404a982440104004200c4200c138031102c2c0c20841650242c1000104600e401084042d42d5600510401d0b40400000703140c0050a030003107080038080c00701d070b00c034843d10022910324400c02000f011804a841954100c0101503980302d0044800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 395005278 1250 395004028 395004059
    0x5011e0309150b10020f0d050a0c050106090603140d0801031e080c0606030106080f07060c0309180605040507021203010b070309051003050402031504150c050904060e2a04 75
    0x2010140e4440d8600000b4406906100050010500010b150702603101840000c0941000700001d650191103556607008000841701c00250047c03034941c2e01d401c0c0702d41c4203607550b21007440014495401d1040104000c20745da8482c00c11640102a030994001e070780d0740c560780c554410540356000115468010b1010a81820b50740751042c0e18031030482c2c801c2200742c44000150b04900c0d081240c90300503c0a00c8201d15003409010051301214015202100c40c10506958a1041d8421442800882c202c1c0505040c0034107580001040c1d800c812200c0f605050640c04001d16140c001c1520891808001c41c0265100003080c2c1c0c0494802c40c21325107141d0030458140140e0300700340422010008414800300d4140c690b4904009984083d4a0205040c10507104060070050303600018020f80904d0010400403030046908220380f00250710000600000c1a2011540d40c0716002d101c90b003060134040d0001360f410030120802e204000e2038148051320702c20041c0c07203c000455107880180740c02c01071105001c1140e0890202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 395006528 1250 395005278 395005337
    0xf1006080601081009060e040c140d060c020118030c0501051b07020415030c0f0f060c030c14070e0c0d1104050a030213180c14040c021009030224090d03060501 70
    0x81c464a0b80e174004202903038081e0b04040c0000c3c0f20702c000d200c1044820000c4d0005410706845c0b500c080394000011a8640740000d0b0080c003060345801000540ea4001c1d40910241b040d02442481d0b406503906019048d50025901182d07190b03e044001401854001c000c41d0824044c1120149010f149400f08009000c107540b0901441030424000000180d20410940080c000d00115032040c81c54080c171340500c00c282d54400303018001c0541d9284002684440b9840401c0d81c0030214000c3c20f40341d00022458154280c00080702040310000b44001c51780306c00d000c1e0641c420744c940b051004d0401c0c6603c803d00c45c0590301c90705800c503841000600051804000305040700552903000a5035a0b81085c54642e100309a1109032501882e900041c410130351202a0620340070303010b07281413001d064a128001d6135001c84c480d01000c0d42d43d98a00b05010180f007800048035041c40b84030803005003070b2103924000404905462020503031003611031515050b4081c2c0508c404498058551040075260002c00000080ba1100762 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 395007778 1250 395006528 395006551
    0x15040b01060e1206151806010207050d06151e050d0b04230703061d0303040f02150405060d1505010c080f0306210105010e06010e062d030405060f100608060108 70
    0x3c0035544102000030780d204e0066000d04401c80c0394140d0510201880c0d03c0c1e03109100500e02410440666000071741d00c000c464041e600800074420605049004001c0802d0103807660340314200c00190781450220004007501464a080a4150381e03100700b00000800c0c80740100341c800e024001401040e5034480214100303403080b281c90b540c0e04211403c01e0801d62181c00403a241d9550349006858101e0402422903180c0ba003900039855414151220444254200802031041e000e450204007200e814005403402000041d008940351000740d080304001e8401c07407162086034000108000740c20341c814008070241d25048007489180c070f0744007100e40d016540000d08440d003210350513902c42030001c091b0903241403104014000040780e5042c14010340592f000541100c2c10030000c48125030155a50030112100c403101c00800c80300240040030b420841903029020900c40d074102000704414880c0c0802d03054410300803031000c1e00d15580c441e0078011958030140a000e0000d0418400295194026135456400588084c079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 395009028 1250 395007778 395007799
    0x90305120309010507030501051e120312041b21060b09011502060106031506082a0d0e0102030c041205151005040609060b030f0717040b0915040b01060e 67
    0x21a1854800c00e516008040034001081101c000740a12400d508280d2504d004d0005515150001d0307030b9a400720135410820b4140d031884a51507a40c0e4006075950401480c1502e840c0c0c102c0180392803400c1000ca9080d100d91010300d1942e01c100c441840d404095541003011001e028003501428a410f8825200031100316a90300003100c00c580c1e581003c68001c10300004140f0b601c1180c81002070030700406a00200038182002203020440159021407030a44000b0728101010b640c408880484200c1403568000300080001001c240324800b0000500d000c00c990a02880400c6a01c8201402c03071008589222035a001440140034501e90f586003030300740c00d0050b011a03041c00750413481c9403a4920143e07009090280b820f030b01002907081500441005201070841082520f1900340c4000f85440002c00d0304403081ca0700000a19903601940078003071102c04401a0502c40e00d0985854a070905060729880e0b0740c0e101b13010702c18520403040508607104039480406090b6a9203040029580702c0741c1c2c1d610195100c9030703110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 395010278 1250 395009028 395009033
    0x715060509010e0a0b0a03030818100603080c0f06040b0105041a030d0203190504050d0b090a0602071104050c13051c0618020109050108040b13020109150e0f03010c0e0d030903 77
    0x1004a40078011002520b50242042d140e41000c51703d8220800b0b0058085202c204086900300c3c110302c2c0d101140074045003501d41100d14150820305a944c600e09085e1a040380402801500405002c180b00b00c0021642880d03240c188803662000c00303c1d0010455000100140004d0038603800c0300c905031211880b41c5e01c1e2000340000003414004115181c0006070300104258651004841c1e03045001007590038100d00e401d00300400300c2c1220300c001001400603101e000c00b11300c1d920300400480544a8014008648030940ea00d40240d4041d050680b5a01c92410100410074100300102240c015024080c4030380360301460304051100804100c080c841c840c401006039400800c203180281a000c2501c89035210030002c103440050110346003070304118100010030040000040e80c0c0442e0715000b00000120f4444c5288a20040340c11070440c1d008040340c0c1c40344542040c0180d82001d110103402d90110398540200d00030303006050886580e20800d0000800c144641c106a003805681000182d000e8170341101d071039403680c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 395011528 1250 395010278 395010289
    0x3140d0e07260d0311040b0d14180a020405180d09090c0305090c01030c051b010615020f0613020d0204020a030b360a0b0d03020607030b091b0a0c060f0905160b07150605 74
    0x72014040341c0751540c000d0043c1441c400e107020381c00302b143d04d2220020340c2c180400983c1d40e100100b009000740d0f51072010400c405008020118100c00c0c040031220442a403290040403000c29204084a841c105501c5c150001d0082c0141481107842d50010089040044011400340c840400c2d503205107c010001c40c2c0703081007a610881c3c0c55181c80400801c405140c1082607012803543c1c50203000f107410420250340380c0c100100c0e0f45600501034000a090468460000404450743c40400a52043c8000740312625030341c164015000902c8100c0b04d584003a202164500e10107018040003140108030702c00140009024262910740000345280300042c0c8425260118103804140e800a4026a10800801103103e5240c010070400701015581d40c4402e0418486d062003900c0d2415880d0324210010581062052140c0303524080b06412040a104812640384e140b0018107182105403094002c0c440d010306080c0c006120702e41102c4210b00c406280040c41d4654001d00d05801e0011381580b0b40702c86002989543da07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 395012778 1250 395011528 395011537
    0x121403010b071403030408030c181c030219170d0609020c010b09010f030b06040c02030c07090c02070503070e0f070c0f030807080609040f03140d0e07260d0311040b 72
    0x10030300203581e100c0490400301950020150f40122541c41003040000283c201c2c1d050b04c2d00b100720401c02580350701a0f078101c080501d0580400c0b54121468409120305900c0c0c40d00b82c4400c41c1c0c000d800b03030707061070740d00e04a02c0000a034600c1e00640191905858001020044c0e0010b100000d103442001940301d0f201c401450981e8002000802180e4403003811014510344890464010300b120101500218a140d0301c040d600003000b020315200e182c0d5812840e44035070091040390400c50f510001d540d81c04d42c44000000080c1050043e41006100e80c1c0d2000c50142000030b01c0b04240c039050300031a120390359a0808480414001401c0c801004007900c40c4d04006a404140f15080134400d0300c1e410154900b001c1c00400c01c08004050324491042c500070b1202090703411404900740ba030503240c904000350405805143d54030510060400c213a1611b41b10302d56506003c15504251001000030104441c02c0b00c041c3c45140e82c0c0d00400041513040012501da495000358840d0b5900d4444415190400c0d58504403008190403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 395014028 1250 395012778 395012789
    0x70819050127030507110d060e0c0102030a2703051605030c0f0108150a1511010507050309070b030604111b120c0c121c0c05010b0f0d12140301 63
    0x820141400811a0a010b0003030544101d0912032031841d40344201c1c1001c641d520070701400340800002d88509010a152440500545c0548226850f41c200e26081004007079034545180140100c1180c0c046942c404401c580da0030f5100d0b5989456404100c1040c202d81c204041e0054414603075180010011310280244502d406241e0030300d202480c50681810700f4105896a03d6220b48065032110080e40e8000c4d07059508500314488003e1004811804156160156000212095a00d007080300c2074550080c110f1000e0800032000340f100b13841301c1c1d03c156400d00080c0da5620380b0350003407801401003080c0000a5940b00754002c01c04140c5a000e508543c496030310201c614603070f2014940b0420f030408001c2100f8800c0108140042d46880c1580c000d00e5100d202816106202e10081c1030807500c0e101c001c2218000c000034a003110b0542c0d0010a4010701400c541242c00c803495404c10501104900e0702e62090150410054800788208010b0741d202841201b03803081d90010b0003841c050608000e030849028601030103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 395015278 1250 395014028 395014063
    0xa12030e03090a09051024020c040e0a031b020a090606020d0903050c010c080405150702012006070c1a040b311103070306090606211709030708 63
    0x10005400101a5a129120212168801c1240d90440d4441c081d4910440b2a11000002c958682100c940308615042d80b001d280750031100c18040c2c0d10300c2008171210704d0703e0181c0c0803142040e241105100903034400c0e0010040c6904841c00c0840441c7c003503c42d006000000444070b9810340c010b0350000b000706861b0f030012042c5c5a0340341418002d480d01000042c060345d100b13041a0088625541d02c10369150180781007241040780e9118154100040001545d0180130300811700000400000002101e07a0404c25059000030052040071030407820b4a0f001e4122000500094101076886c568242c2d1300040c0381000700c5108058040a190134460f007605140282d00c511414492400c1c088917a6070815002d4580d0342070018103608049580c4660113120b0b1b103403540100012100210030740000d003001c006900c090105400d00070440100900e6500500c00d56000711140c400035541140381c1240580c120314000d10403250b060f1907480580600015009036000181110340c1e10340c84512450500e201601010100c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 395016528 1250 395015278 395015303
    0x80405101b200415090b0105070212160b0a022a1c11043303050f0604032303070c020f04060b1305030d021005190c0509010206060105090d060b030307050a 68
    0x80008814048400700222401e0154044420340700184c6400c61242c02c010540e9070500d0051030340120107032510590003e02000c40729142c0c81080b070f110000540000400801d204001c51030203011016a009100d43d90f00030615420f80020132080c0c0f444010800b41c01480043d407500715a40c80c0c040c500100980c0e00c4080d0f0542c00581741041588180c03042c6a840b4a061402d001c1c820010001001d0303081c8040c00701112560445c3d180201d000c62150405001400b801c490151800000140c00e40140d1080c2e49c1c5121070401da6240b5019003412201c0800030000c1040410003040c0701c0c0700084410390005066403031078212840060100c403d81e512404900402284440b0701000721007c0307200500d0217038083c041d00040844000c0d00d032290610444050355071000403403044500b08840070300b820302c00b80302006540c000300030241035078210940b6140148140b40004086501c01c00581740c0c0010702a00c0c2d1031284860740d41e0361000c0c00711202c0c2d00390107100600110012400800903101440d015030703e50b04c0c81c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 395017778 1250 395016528 395016563
    0xe060d020c0106050105030933070f14040308040509091018030318170309010f1131060e010309020a3002100c050a0b2d04080405101b 59
    0xf501da03103900103810301c401481002030502001c600f1540c41b04405110300c60100107081d00d2402501700c3ca440940d0141c25100b0040110b8000440320b040f642281c8480c41403520701c4103100c0c0988100e0100500c2418140010400350411844403900440f85806980c2c4d26100c055021040b038840e501481504202d14502d4018180c0601c01c07241d40c00403985907240b00d1280c42c3c07110354207140d0500d0780c0003481100200007071030130030b0030340c003010384158126000e0010128200c24400f581d0002c82203040305800a070fa5603840c2d101450310f001440c0f400c0311000c4c0c41e01c9191803003e581d5650000b100358145a210243c010045e583c000aa070050b0580401d51b0300c1d40072284ca5103482446040561800c070202d00020300d40175079180126003842a03900d142c81914050b030f9240a5041040110700203004da4107540901c4503030007925a0310300f0600c0d580c100b03000041644080180c812442a2000340c0030805c00c100c2405030703050802d080f8614208904003403458503000c04a600f2003c5200070199035400502128510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 395019028 1250 395017778 395017781
    0x2010606090b040b0313080705010c02030703080601020c1f020111030a0906140f0c07060b0301020a03050405010b100507060f0b0d050c1009030317090f011104031a070c0803070e060d020c01 83
    0x14001440b020360805050843c5030724140300190010320750510000342d4134100480001202d82c1990b00100920801007107113806560794000740c00031804600600c0000713065500c0060b07001802c203801802025040102c1c90244440d00c4094484c4085540300d08280c40d100400800640c098082d02c88005130100d5241810000c5030f20b08420f10690304641c44c28864060301d02c0e0585500b0080900005654041500d400c0006204200049030994000728030301c4001600b546c0b20500c80c034001c100a10203100800100411058840c0d802c80126906000c2071000c00c80c2c3ea4018080286a00800620090900002005a50a00701c102d440e9841010a9010350070429a0218500e40d142081d50300c11b8190342e805000c03840200b6441e10121030100008a140508016138111440d0a500800c13130413046c0302005415a00c00e0100f551409a103d1039000301c4c0c1140d2071124070521003680c03100807010150b500d00d405c5500107001e03074042001d5103125001d0390b40c80c1001041e00b00440c00f401a61070088140050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 395020278 1250 395019028 395019047
    0x1b130303021e030307090b091c0506060405150a0b0913060b0304050f0106150c03090b030112051b0102060402010c061104090606170106050417010906060902070c081207030f05120702010606 83
    0xb00c0d641042c028044500d0304041048103a485203050307643c03a01d0300345021550100c24203800540d07002c40e0908140601c2004105c690152a040d02c0c00d100954481e003050a24000a00e0f00c290006070542080200103400009050400b074000c1c035480c0c2c051410444501039601c20307080b0780c0c0c240000100780020403408006c4090703845803c00c003e2040c2450400c24540700461940860305200700700482008041c403406020300600514a40715880b9612410f6154440032102411640d61007000f0103038182d0071581030401e00300307003059004140346d54855004454000c4e8021045501c0f5031100da8041c405602d40f0b01601c040c10001a00150103407800381300034582c41503809000391091a050050041030390001c200c800b0b981084406101e520740328061640100341028010344128030f030a80100e401341c180c0d0014246035004015500410b82c650104503110300c0c51030b01c1c03407030001020494003000a001d00448500c034016402e010b03007000c0038024840107805d011140c103001070355582c000b440b00981018814 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 395021528 1250 395020278 395020333
    0x18070501121a040903111c0933090617041502092103030610030e0c0114042111060a050409051023190501021e0f160315050405061b13030302 62
    0x307103e50410354401030302305080d90180d280388c0d0f4440f132a00348100486000207040b20301940980d40401228450080c000c1d101d6008940000700922805522111110022401117410000b0341d000c0038a079a003030100a40c0900305140c0c005100000c40d400399034604c0449003000d00d620014550304d180007400c2000b401d440c515018241444c019001d140d0740400904a20b50600031b081496604603200384040c014011a1b202c1c00e650f03405c418011410441420a010f440b030b00c50042c1c082c0340156030741001801e0084403100c0d4001002808204940482a04140d401080e048000350f941900ca03540308030a4003025039010070040703511520300d4240c10141407003603000317112001c1581d80c0b40c14000001d46401241c603011414880041c00300c0140c0d042132000100040f0200c0484041180c40e0001c24020b118034441500c80b4089001068404d44550103458401c0390700101030036503a030758214a4140b509119020101c010400e01a942da09204440c0000c007560203a0010000a250381100c1c982841c030002e0341 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 395022778 1250 395021528 395021563
    0x60515130e0112240e0a0c0602120708070312021b15240a0f27020f071203061802040f0b0c03070b09030c010603060518070501121a04090311 62
    0x100316031007a141d03e242e003182e40b2900040c0b580c1801120365800d203060a10340a0030b18940031089040d800000381e40041e4521980145051550354030041c3e0300c0320226140d440241000300030510004800307a00030b1090f02c2c402d0400c0610000c0c10b011800490704181141000c40c0d0400d200c5000c3c240003040400140758048101a042e494104d0034020390101112186429000d0401c280d00c01c4e0b134a042201001c1c2c108021102540c55a814040700d520a5051140c1e0740d07070140c02400d4518210324001c454400618800c4030317191001903510300c411a910711501c0301c05c25650701c80c0402c8070348851020a15000c0500790250f1904e0900800103049507413a80085900a410000d0420075040882078510b12034104803d098039079030b2428098210b200d15110340c0459403078500d004c01046195485140142038200e010031000450703205581c4e841c0414044c0c1d03404120740c0114051820f030789400201505002002c90080f280c550340100b000d07602e01a0f0b0803004210740540300784c8101e2017089403420894024a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 395024028 1250 395022778 395022781
    0x1003150b0c1608030a180e0a1b080f010e0a150602030a020c060403020d170d0912030b011106010905090c0a03050606010e0108010b03040b040602090303030a050415020c03030c0904060515130e 84
    0x81c9542d13034801c9402501c20b018030b41c0c0b103041c40c40c000b4658180040240c200e24400300d10303140f0f4021004002070b0032000d5124440200e2404014072a41c051849104407210800c202d9003061520074070508024100c0e05800d4458250490304004034054200814031a0011070325030080410103418080400a50b9004180c00e000420169442c41a0494002d40000c0b16210403104443c42040c0d9200c0e08150310050350a01d54410708200c4d16040c442d44d420003903a01040280006070044858081001c2491110751000005009000d15684510340040090049400641d0700780702040306540030340d00c25201c581000007000b05c40d50b040402c40034400340c00d10342050158145190b184480c000a04054200c0f9000c8001500b085081e504892050342c00400300c1c1e449180c40c14446002d8802102c003114240d03200402c0c45216201c6000fa11407a10a487c041c50442d51541e284442e9600f00c294a10340c0640c50f58800a50b42e111403220700d0345000703825401e65580c0c0d884a0480c0c64494160f0100780078413880700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 395025278 1250 395024028 395024039
    0x6060c0114040309063e03040e06040b04050112061d07030b0103050c03010510030b0c1b061e060112090804090501080d020616140a350f090a021003150b0c16 69
    0x854107510a00707003113000708280004010388080c11b00c0c018210040380b000142c0419507020388d4089510400b411501404003107500010300060b50b400f84500c4217401c450050000c000f0f2a580c025240d041000a0300060004407000c0d624030b862074942c81900c80c451220014001d0000900611001c0031064001f44620f0508034110401402c462002900840c0698041074001141c0303c1240d81a0f410321003c110001052201e298507a0800e071075804000f03e02e02c0080d514a01c584805c1c41c882d180503112a15090140b07202c18010b0000000300300c41c01882000003041d03100c4544504c1e400b80500074006c0801c0c94a195010f0b180c01030103481b000e800710401420900040e40407852429924040451580b01c240c803003801c2c0d4403400001445000d0710820054400c000050032a008060005403400c03e031585c681c02050300c16241c054800c01555000540400094103103099600b4610103d0f03d03001680440f9613a03441001d10594200c00c140b1000021800c104400c03c202130308011660362440c0755110302c0c02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 395026528 1250 395025278 395025317
    0x11030c12130c05120102300702010525030603020301020a020c01020d02151504151e240c02031c020d090e270a1a0f0f010b0f0306060c011404030906 65
    0xc0c45464070030700c882c10f00000840000c0d01581ea0b180b4182440b0b16210240c00c2c2d0124841100903c5580182a81f40c00100e03145d1050042e0780c010f54443d0b44100600e5041d02d5210003030071019a07050285a1114000401a1001d200400300b1324459809401d15a1440c2c000a04001070341d038520007154060410b5083c82c01c003603010290003909127003c1c18500d114890116024148100030b0f4940300c101e4510000d041100c01158040c6040c85000d60b0304855200d40d06244000118015090b0010041c10a0a80d407402001100d400c94001404c0304c0f08101d2543c2c1103606840350078100130050300400441e09039144c12080c0c0601500510a81140c1460300e0020401181c1009610180030f02c0f4200c03845c02842002d01081a20700e03004400401c44100c101d20107070340b00505480c1c03140004190000201c4c0300c1c0e21510b0950684800f10310803854030800000c0706180d50405411140e2100c010000c1d0500300009204070f07892800455200100f6141c14207000d095001a580403509121042460016a1124 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 395027778 1250 395026528 395026553
    0x30606010c080f161208100f0803090405150904080904050a02030708270307030203120115090308130e0108010b01030b030601050a0605030901020f0a0207090c022404020411030c1213 80
    0x315080e803225a085181c4a44146101001c5c002d0204642c1072040c03968000071080c800c040100c60010304a82d1004900c4c01140d06100b21116604280501d504070301e0244c21040e0000941c2e0f00c001000200000058620303001a00c0848003501c000991340704604107402020790100380348004504528040901402148d8018005601000c4204460303411000540404880c011980e040b243c5498441c500607640c0d901250800803613409600c00080d0112000c20810115405603851840007441c60340d907201c042d040034070101541288200041040b9003407100b0107009000c08000031642450190000d800c075000d5a4816000350000d0300184510b40f11112044100c170712a14006988c0d503607035000c4a0080c003428101040203480018140103d1703900165450650701c59210800604001c00402d0343d540c1e81134010241d06c401c0c41800e00411869180c40300e81e125001600c0810701120504051145a00803a218801d00e2000b141a0050184003681c3c90340c8141106030b03801c0300301080d45641084011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 395029028 1250 395027778 395027797
    0x11070504090309030b100b03100509091903050f07050a0308041104110f0f09030d0e0a081c050a1b06020d1404080306190e040f0201080a020a080a0c020723030606010c08 74
    0x4d031102040c5c40f4680d00031501c2c024000940c180340c8900703149c12030110468240c031440c0c0c0700340b03200c2c0d0104400e134101180180c116915940da545d43c0342c40e55501500c01c0d401040190410782024407022000c244140003010a551003541da030207072840c00c2c2c42e0100110520340e059030700991800711340e4a00b007210b010440e468121000b551079210580b04210034501d00c100011240c241c0540440a001690418070411600b1021941020900d450305030781039407000b0840c501014003640840d0000494014030040003c001320f072606c1e000101c120710440c50790500c2c0500881f07205030700240c4c850804525110311070b00e060000761080254203243e19180400c4c00007500c0716206040002840c3c0d400060016a100109441854500145458201800125005001640820324910000301034020038400c4230782c00107858031006c4450300ea0240080007002d4600000055200319000491194080703540b0580e495000441e80d00500d116005040c2002d90260a440c1070290902c00b01e00020700080039a00d590380b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 395030278 1250 395029028 395029043
    0x1051e090106050d06090605091c0c0213021201170703030c0209070e1305040210090815040201140f0903070b13030303050a0204030c12060c140f03040606080304061107050409030903 80
    0x440c0d00580301d004101652203107030f00104400d5590108100c1d40c0150a0550088104219a94034400b400d0780f41e1100055034441080801e02880000340a41804000c00740091304d00c03842440500c5001c4200d91090045500d0460000010804c2c2c55583c00814021403040014244552566a001e17088409400c0001c0c86110315600040362140304009038140c0c20390003000c2181c50714007040900001c080555051303004034440c1030b405c29007038000c0558904030b9207134000030300304c02c580380c80502602e01000d40202d04000d02c005984200345000301c0030340a42040d500f05203941c0c80c4144101490402150300c80c250803072b0240b01000c0d40d010029084802c070f942608002c600b03941d4840c1d800c0002e1040f0b801c020310340762007554040349500c1800e04410903144200750030400f10586030303000d031a071a08602c0d040300400020010a65007801400155030018400c00000c91820f440c0c2e44203509581164010500041a815940c80f524804100c040001d000c15182040188081d40f030052491906000151086 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 395031528 1250 395030278 395030281
    0x15051605041d220c03030e040b0f010c030c020324010504090809090702070e0a050708130c050d060905070b0c07090506013515040b01030608151305030f07060e01051e 73
    0x4141c000d005240710f01c81c0c641c604494600e5407410792102102d07400164000354948282c0925070a05200d12452032400074090b03041d00026400448214880c60300890030450310508650040c2c8040106049050b101203a400304207035070606c00e00f203000c0140c0c00544603600b400e030300c880814500800c0301e540710401c3d5907020459949030416403604000f46e00000c0c1d0403c0d100b08001c8039001a500031401482e850759444040d840711581c2d00100300000c40c0c080c2c8101503a45080120745007030074040300310a12506000c0f81c4030180c1d031182424000030b9807040b02d40013000501044100000d004030800740c080d01d0010841410a240000d102d0351421402500c00c813031148840c0c1c6031040c80880c0c42403c498405044001c0e02d01030800c2a251400031050074003840c1840c495040c298001e024240a80708400d0041c415203c1e0381c0c6d5000c8803060061b024020080c0f4000200d0301281c020b00c000c0141134a40b825a40c2d40341e201d8030300b00c5e0442c1d048103030300b8020340d140c401805030083d10100e8101d0f4841d1030110300da146 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 395032778 1250 395031528 395031541
    0xf070b101409190908070c030c051309240e010203130302010c021606080a0906020a021614010e0609151602100908100504030509040603030c11060304030503040f060915051605041d 79
    0x41e2142c01da002e001c01080301f00020402400e07050050540d030096030b60041841500c000c1c0740c01c0d40c80c50840148440701103014981c081d600c4401d0700440c00441c60004c00c04c032413215145422a481524080c100004240c15003041c140c090040111480c9288010041c0f50941c00c4c200c090b662450190b0410403e2500202e124140950408004a600000215528064a207002c5d50b40e40b6021008103815800d800000f90100c0c04200d10300a482040c1c450030032112a220401410382d10003100280d0064191040960003071a01d400340c0488110984141c001c1c0c5000d004001382e01c00c00001400401c0488201032002c01d9011840480d4521100c00201e0941c071185010b43d01344c05410030391600589402000030074154003520075840707607000e9084200388040d1241404407038841158003a001c901c0030808207001840300200c40d000d51380190b030700040212066690100e46540f0480c1d03c070301c06840c2d01c01d00101c045c10800110f2122801d04100e8541443c1c007962003160014540c00340c6008400320001140b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 395034028 1250 395032778 395032793
    0x3061503052e0219021c1b05030705060112031d011d030c040516120b06031f080a0309030b070806030c060901020a0c0f0611010c0c06020f070b1014091909 68
    0x503500740148043d500c60811903c0c1c03021540b01c1110301001845140b59140d081140c02c14407901000c0da0361345e00e258100040030004000c4000ca10125583c0c4030070444000461001e2141d035020740b0300302d41078400d90f50f170b1800c0003844224201c980760020ba04010100d01c80d81c0c2c000d01c07400010810550700e02034182141300000d0900b500518066040b509200c10001541c025001c034185464142d1603000200701c040c0303041804c079034118010507000007040021810f0710100d107840706016a41080c01210320784e05d8800c0d02c0d0919100101c21000b0030150031051042112103114507038001e103246003040c2d040c5003160000c0d5030352114112542c002c40e00000d920300d069109001d03c41da4160491007910103a43d651454141c004054403410000039660900c0451060f030600a00c036003403009039649668540a92a040c000358000a040c007904141003081d600054104000c041c850700644560340000d40c64030b1400100d90680d00035051081102104100c41000750010902d20032009800001d901070140c1f910300d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 395035278 1250 395034028 395034103
    0xd030506040f0608030405040e0a02031e030c0d08010f090b030a0212210d0b09010608340f02070906060507080304020a05130902030c060906400306150305 68
    0x788024141000804d010078000000c10840b034003584e040051a0458407038513111203404100a5264000d0075090400009240c071080c00f02001d40c05480c602071604030b4940ca003510030500d550126000c040104880404070501d40010a031504042c8101c04451001170740b80e003040c0354024801d50845001542c500340c02c10031010704640c401c1d516075001c14114940061608102d881c020f8181c101065000c050900c80e410074125a01600c1d107080070344403003044010032007421844003610018048013010010307030749541419100c91a25080410440041c000381010015081116004d091030710800106a005045540c840d0f00414940d4482e00e45200040e1981a203078071240c1d0010005c580c02840e1809640720420061003207045801a0b030340d090034030a1300e010fa50b1079564099070500000e00001c05500308a8400340650500c3c4070054a51041070036a150f150072541c4941151020900410032207106680c00d40d0500c00082d5015031865586980c1c0b031605e4007840c10050810401e0503000400c401c01007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 395036528 1250 395035278 395035301
    0xc05010b0604030b0402090105060f0a0509010c06050c03160915031509110d0c09061205090f0d0c0302070b09100c03020a0231090b1f080106030c0e0709080d03050604 73
    0x1540c2e1580c0da41410f04880c0d80035601603101d104088000521407800300c08440c40341c601c02090900702400d90f00f055400d0b401480310302c2e0600400d503000768005560740c845e007842007159010581c1c8074100160800751007600d0702c1954041c441a51401e008005460071040303000d4075a8600400c003a40002c51411529915610000c080360a0401003051840d850020f4821074100c801e0402189150302e02c21128240300b481840045100e07091140d10740207041d0030003584442040200c2c1c03440320500030003618202103800100c00043c85500248100f43d4140a800c0080003a04941801c02d2003100001d48460b155400900501400410040c1018020303c4064081c42d0000c0038101c814040c0000070758448003c1e0403007028009144507080e6801014480c0030072440d0003484404896441c42c4100221410480c0f90f01c1d480c50500000085e961800d0048001540c4a103c445031428070b0001d20230009130028001d1002d0042000013400101000542000740c0c40380ca14021442d0f032102400308000700241c034000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 395037778 1250 395036528 395036539
    0x10b1b0d0305070f0201020a0509091e0903031e010806060d032a06050115080402040b0f12011d0a1218050d0b0402360702030f0703021605040501150c05010b 69
    0x4103003a40c265000b5441001c07103403204204005540400c0f8200d106075590000071520070f02c0118000d003040d2020a51000c00c016885104050446c0c0001c141c0d44204c4068030340740d0002003002140300e61240b0458500a00c007001030100e504001d1078580340c8500901181c01841d07075503e01070915106d040714603a09095500130110540c5a407850180d0411b84100c103503000380c184000029091903a000d100400c1c412655055455290b941c20003001d0300d8440f07100740c2e0003a640c801c05001075840141210240300c6c00400041d01d041e441c00c0c03080706034921240c0314010b9000a0140c0c00031031804095100078000342e01d4102c84807884821913401c0b885580d000740740c0001e81c42c2080c00403c145d47e0b50060080d40200c500c01c3e401110081e01c03804080900440b64121811410410400c109080b4000c3c1c00181d10f00640c1c0c140754100900d61250340040310144c0c01a4441010900103600c070050b46000741805850900c001c0d810003120300303140d0b0b01c58000d120030400604030090501c0401c0d40007160081c00140f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 395039028 1250 395037778 395037793
    0xc1a12010803040305060f01050f010c050c13060e060a05060d02090301180b0f0f0705090f0406090e0a1502070c05010f2f01050c070519030905030106120605070c030206010b1b 77
    0x1c04907529040341c0800c460a01c10761011500011a00d0265412520020b283c6260728800d0001150300e10750a0208651600c6668000b180e40c0e980c0d42842c5403082c582803030018009160461605103e00301408080c0103070308203030040c04942c0310141113503520120140056a2003940c00d003c24014500c049c03210b240194561402020060800d401030700a2032510381d500381545420211124906060722804042001000303c01040e04100600300451140180000340f0315968080c1c040949400c810703e0880390704005444010040707894842e004184034104110308251195461954040f114003c0d241803240c82c5a01c0c1281c80d100d0740c100c6c040c0c00584081c003685414403d04000c88034803c1c03001d400855007800000741e6840b450006844840c2e821200801c020700020202c540f1086189400707078100042c2c0880810151000d00910000300414104403031542c109090140c02c448000d000e507410070040680300d0b4080703540010a070b03054540d00c141213a5140b40c1048400d070f20140914980340725004512 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 395040278 1250 395039028 395039039
    0x3041a0403030b010f11060106120204052e0e0f0402090d050a03110712020619110d080709062105061801030c0509091203070f050f1201030201030f090c1a1201 70
    0x803c00003036007400303032118400621181015180740d500729444403010fa00c03200040003181e00c180000c1e103541c0783c0f00c2c40c010303c0d194440c0d0100f1480095441e8034400d901001003040028000e4914480c001c03005450012981c2c0b00c40c030001560604444034070b82c482d40d00455100c545a860000c41b40e58251300c01c1c2165403914a9180150046d0100340c480b40079801038010010703c1094030300303c000105a005185a14000404805007814580202d8103402c120300c22000d01607041082003280382149480d100c0c40d62518103848001c1840b4920340100d41080303924103003410020544002c268900001c41d1010503e941c0d0a0b0124007c4400507000c1c035000343d00c00c00000107010f60018a0401d0307600c2554541511b64500301c0071503036158510340400c0608410000030300d585205160702994507981d4034255240c0488007506400c50303000101800100354480004108541c0c041c4110009a24591414450303042c240d2500c1100160900c626034031090b542c00e003001080d00c0f0a080341d0388029005056a00d9503190f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 395041528 1250 395040278 395040281
    0xa120905100809070609050d082104141009050319030f02040b0c280f03020a08271507082107020708120424140a030c030b0d0f0803041a040303 63
    0x303461001c10b84c01840808150f8601c100001c0b82036482c0035200502000d2559030b20a200da108041508010600f034020b021507107554014180601d01420035403040300c880c042034030300f0070000125503c0810300e00a0a00001400881a1410725401c0008030b1301e80c0381044c2096010b0440400c0c1071400c1031000a002c2600e50b004000f51241519030001c42d01720029071880d4101580c0400041c1c0c401541c5005c1c044001100140110b042d90310910545000d82081d5852528580240041a002600801d0701164620108806103e030207000c5414a4072032004680c00c0032a1702c9540806441e10030000f5038400c0b07030406404000d413521140811180980740003203009440380458015502540a1010780040401141e42aa000e40303a182000e000342c000b400c02100444207071007040000780b0082804500c020b661041c040e000000c1d40ba1404107481c1e0712143c0007000c40308101c07030b424452140807006078041641e405510072140d50103a081a40c03500e032810000100f00680c01c2825a00c006282000704243c0e15 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 395042778 1250 395041528 395041531
    0x303020f010501030834030c0b0601020d090b090411391b1207081e2404020118090f060e060312030a090203070f0f060207080a1209051008 61
    0x2642035640550101003918280c65003880040c02c0f0020a024031070300e040c1c00003500100300c25200c1c030150765801e00c1c0d148000b42200c030744425004204844101c17014441d002902540c010750034030280120034045080980407014078040c03034902c5031021450300c0c00382d1556030240103005149600075454000d100e00c2520071001a840280b206185a40400945885490314201e03510850014245584101d40112034041c46084840c0c0c0c05200c0a407105500801404007102034226900504a1b111111840e00660240076030348001e21751041030070146076003030403041c035500b0b1004c007803020440e0701c0c0d070b0004031080e03258022040100f80142e80c001071300110a078002000d280551100340075645ea290480b290481c0200c84161301740e088003080969896440006642c49003928000090300d88941d00440d2601d81c03550058842d0b40c16401051003940c041412820003083c0910051140c41d0504035143c2c2c40b01d09000c40184410b02c0682c1e00440c060080d0917240c00381c60043d100c00b5040200b0070008002840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 395044028 1250 395042778 395042783
    0xf0601091107050c06070305041206091101020c09010e100b0a0305070e011434030314090a020a06080405011b0804030f05040f0b0706020702180403030e060f040803180d020703 77
    0xa840c40448400e84607100751819076030060090107400000800740000365100640440400c04200008500c04400941c0641c18602400c0300140c108068644441c66002661003079043d50b000b0260b60b800c599070800b03418107447c00b80c18007080c031351500300e100c01644009411030800c10501040003001240d0581c00140b090100d540d031040125440700042d03032052060305500b1000d1104200e00080720484415580380407036100a400b003c4000c64890001c2503202110450009880e0340074012250410380000380c100f130943c0d000c0d0280300300d207074001000807441c0e2183da014460044001820300c00e00f135010420007003440342e481542020240c8001c1c0650f03011a812008110440400c0305842e1150042c0c400795401003004000c1542440c0e848815a0800ca6089032000d800304076840050b107030303142001980c0400180402c42c43c00c01e443c01030241c9164403074030107245c2d10250402540264140c0d4403900b103504002c050303a50341c075110710144810001e06003440e41072040c030582c810241d50000368441201d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 395045278 1250 395044028 395044031
    0xb0f07081240081e0d0f1a031911091302100807080c071e1b0e0f070f1b0c05040c020102090607020f01050717190c0201022d0f060109 59
    0xb469219001c15030120b0903042920210318030701e00c80000c1200c8002d000c85111940c01000c820399000310382c6459801450000481a11020486040300890041d50518070241c0c0e03040203007450500100741c0d110000e10380c0f002481007503501c4070280251003e01d6140300714040c2003a1814680740b10048400b41c00e84008074041c140703525904000501c9400f041d40078041642d103405054a41c5682c0080a4011240a80c0d455411028a0103241401e5001203400351060b19400c1c082d05071804090b104032060760144206c1e003280020401a0440410785950000450402481c4146035090440d000103441c5802d040910030921080140070b0800c0e8103204444080784c0600220a48810480c00d0340200b0340d595030006001e1103940010300e81007402421483c4180351040c141130a60301c48a110341102801812020000210864070406914229400907081e0400210609890740000e5030b07041d0b8411250185d140242c20b591a80248551003645044241c0441c0c2110040703030120343c0c40d03c00c00c1c030550f004036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 395046528 1250 395045278 395045341
    0x40f0308090a2303090604230d030f140d050403030e10200708070803011806170a060b2403180d0503010e0901060909060e160b0f070812 60
    0x504000074260092603100c154400020b240d0143c60000c000891603c10250100740000ba10b50744507907002d4001010050039610b4070410018000c1060003071908101e0081d041101000080307038001c529039610070070600d803a030078001c410740b0300c00c0450003017152420707140742800184410315038903800910881e9002c2064441c0014621044c004450342c01c2d5500400e0701e016448611541c0c0c1d21805401001d000300002403410185e5982c5085a074426000703064841c2000310480c0c481e540c244110409002c02c045004040f40319101340d580d0f03c4001000050000d520b51154005c3c035120300b10118000043c0e040d0f01c500c8018403503480340315600700705d5070300b00c10300c441203c4c0c0f0b048101e001a298807141d4003500c070185540d00f80543c80000c050001c0c04141c16649401d000502c400c0c09204925010f4011100066501a000085800e1107914070418907400421101030003104405021190010102000950740b20a140f0740307100350f40128028801c00f00010420000a580f060110362403680c8591b038807000e40f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 395047778 1250 395046528 395046541
    0x9050601050402130303030e0a1e0309060305040809190305030a121a1f030902030a11041a0906010528050306030d0207080307030507020301140108011505091b160605040f0308 77
    0x890280e6041c68800112109040000c03d01917803018a003412a4020744080310a641c030354032b8000180000c0702283c0d28030020b2038000d041e03000020307201820b514501402141065150400c60340103100343d85100e00700108000340d114401240650086500c03a080c1c9031980c001270707005040c2d4981e00c104020614204070381c01c3c0f030701c0c0c181822025200000078202543c03022140d0b044078280103103064003028984d80740107500140c0c0d001c00090b600b09204000c00c02444403060240301c00d59440d0b180c4d86041085006803580f441d43d810740555403144080c82d00c20f88650501d03c00b5018810300c24107460390110b18030710b180305150f0322000a40c1304070003c0c1c048403094900900100daa40c2e00c1032207211000d410501040300001e106074000c10f0300a000900200380700040010010f100e01c801e0b03209403101da64481310791200b84402c0121000508c0201c500c00090311342140a41d468203204180180300d40c500141e6a400804000300003204103402050821040c0b4191070b201c0c40c10154000160049800480018403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 395049028 1250 395047778 395047781
    0x2b050309041a09070f05040e190e160e070903080d0b0f0d201201020a08060a140a0e0c040f270203071209110301020c0717034603090506010504 63
    0xe8008082c3ca03548080d0380d0940200d44003019003070f0700310800c4030800c0000382c1424001819801000b01c80640000007036440540130468840721114032164000090a40d51480490450710440322000311880c0b0542d112001161001401e0708000c21040010032040401c0d1166800041201e1007626507082d1000e541d41004201c3c1081c44000306149000108294500880400c031408000060715803450307454103032442401da80080e66480006198101048090700c1c1c80c0c08400010302046120f1240003400f0004a40482440d01402058920030000300fa002003407101180d00400c0c00c0a0001c40c0030361107903080d810035440b403000001082c0d4200841d011001b500d2007101d0040c04603440340c02c0100d01712030b000e4010385020310050701c0c00803a450494401e80c0342030005042c411151005812050306001c1ca020440c4840304541003640c0c000d205100101f900307203003010074454009082400007000030f20440e501d05c100030403560007490740c04c8100e030805405411400d511481107050726079a80e00e8805010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 395050278 1250 395049028 395049071
    0x9020f0105190e0d020a031208101202090405030403050a0302030406020d0512010501030b0a090c050d270807061113091d101e050108030a0f0e0d022b05030904 70
    0x1c0c02c007000e03004148000d005071111030071000050600d101000c00360300013540b0399516901c00e41c3c0040f1f192500011542e80701c4038207a441a001e81680f00381c281005141000507800850080c012000040440d0901a0030400d8500540e1b0110864080606a1600948a40061140d507015218071241d89000030301410544524008682601c82c07280c6ca400f004501400361050b0090304030001010118840c040c5028000200084d44c03038060b80d91400e1900302c030445250307409001c8681e58002614000b4846014805040354000c04410340740ea0050520303c0090460980e084c2c05103000240f0f00110108409540782124074400d0100714484841304042c996040a120042140c0c200281c00502d592466005035242000c036030204900100461424045030b00a800c18502540042055180b1036072010212900080d03502d0301034002a42680420f01080340304400a10508413102c04052484084920250140704100180112807807820525103a1340f0000e0700c18016420810003091810309101000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 395051528 1250 395050278 395050297
    0x1207090501020604153b01050108031204021201020c0c0906010305060f0118120f0209071803170f0a0906030b0114031602210307030501120503190e1309020f0105 71
    0xc207410b56842d900c07040042060510705c0718490fa80c544510000c000c421440b02120300c0d00001c07220300f0780c960901954503244241c40c14050313818000140007580e0003000b92148040760349003801d580e03161440014030001c1c0040345046290f00c081903105142c1000070307041e10191000c0d100c84800e525408011401e0741d10869240e9040581c030076500130203510070044514401c0d070782ca0150a07044e40711241040c4e03200320301c00140d9002d0b001451074015403a1185565410890f1418125604541e074030a460401455100c003400d40d00c0010080c1c044402c5d01000c07a142081d06103a86a078949c4840000f801a180038021400028130b0110a050194060034258558441d03c154460030b65860041400c1a03c0010720740e0303400c500420381c1d609582c240054044c01420300c803180954603440e00302002030456505900c902ca803001d02c0003a98002c1000030003124165500071404002c6083c4026086c1d1300c1416418249800481d00b162049242134268441c034a43c0340b08440a2005010210044403580240d0040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 395052778 1250 395051528 395051533
    0x6080d09030c0512370c08070b0c12070501020f0f0d060b0c0a0f02041401031a07050711040504020409150b150c0304050108220809010305130803190905010204030503120709050102 79
    0x440882107020110345117004600900c80044850000010f0402003501c0342150440031214080c44249818811500540040e01041d41408061200c056413100310806003482d20303200054840901800b07404444441c0c03071a01e440e83c0c1d100c0c420702c5000110f50221542c0d50314640340c42004181250560121513446161400500707030f20500da150645184401030080343e02c180e03112995640e40d51040070302402180141c0c5041d051450071802d40c40c0101c801070090041160030040d24000a400302c030a0f0380b000c801a240000c040e43d403407000c03078028505254050080003031010100e41d07420254102d036802140a54055072002a400861000ba0140b8003910135940c00030700c405c2c0300030351280c003400c1d501c0103900c0c0c10420003180102d091480390000303280c00c0c0d465201c0014001c94a58040c02103d8000401a5580c0c00241140d00c0e003c400380000340c0440d0700307418450814509010180c102142a542040085580303d50b030345000c1e81e40e507000101050620018000054002d40204150821258107030003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 395054028 1250 395052778 395052793
    0x13021008091209030f0f0d0216030221010b090a021c02090604050d02011e03060f0509090607080612011a010201050c070503030c030c0d0c020c0109090903090e060406080d09030c0512 80
    0x2000c290b260040d0a100341c05204801d12800c90007010000162161069400f078980e40e68400c1009040c1080325043c02600c501c0768404000685402503403000b42400d80e000e1131069464404070394050410940c0c0c0c15403103c2220180422050140d0040850400b18201856481c10404a0740168041c407071815034400d109200400050801d11000090b03640705240281c0050802d200c00e00800c0f00c020320315030009684d0f42d801d01c0b07800040204d02018041c00c0740e80e540b951401302c01144d81c1e40d0f8010f00e20003c101000c0701080719500d50b014903080140f9014000cac40a00300c5160b400301e81a1500c40c5041c010b609180124180584070300440f901140c1010155146075141c911007078182d8001382840c0d107a130004100003402016284603041d020801030b03000e000c0069400e07000410841064000402e8203150245080c0001e030003c20600454003243c5183d5078668400000a00503c00d50780141003030f0060303d10a0b8280d0780e0100c010b0f016248166559090540c43d0f90a01816003404400c1e040700e07900811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 395055278 1250 395054028 395054053
    0x907150f12090614040602090a0e1501030c0905060c0313050109120f02060706020c0f010b090c18030a060903020f060705250c0b04180b030d0c03051608031302100809 73
    0x81005405a0056402285680640710f4852001001703c1d01a6409035002c80c007003180307182000e11400100810b00f8489201c1c1000208461140304940c80141455504c8005a82040c015118040105401400d59458070b210110085e144c0c3c3c08603420900010700b0440c08140d40d8040c460340740c140c514281c0442000c0480da6112800c041519030241e0f4055400d10800000500d02e00040c000b091181020340780f1801156070b05d5095503200e01040d44200003120030807540d112040140d0302003840c0036420000b41e0f0805400309041013190078024100b10b091015240c00d240e000509040001100b200300c812660710044219418020301d414905414901100000941840114400e0b2103002e11500740690342e503814400d100740e006900403994003d908965440e0482d0500c60041d080d1402c0d00030b428841004075008006035440340c030041c00e00101084110008444080b03607042c199004085560703038100303240c140151528500c0200d1061480101511031240b14500c01c0c0d00078840711004106000c20030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 395056528 1250 395055278 395055281
    0x1e011b0c03141002071202060a0c0e040b04020c030a02030310240305060105310b07020303040b030702100606021f020a1d0f0a09051b0a020d0c0f0b0907150f12 70
    0x54001600b54810060b81c1d0309007180e24402000c100d4421005c00c0150351541c030000c0d0a00c2d100a120445c800e181201c07107017581f6040030030001c42e032034111400155105410000350003402200e080200710301c030100c2c0046401c3e070000000c50040940005141d41c8560321040440384400000395014004070308044448041e009400a5411880505002d0300309604030341c0d2800d80c1007408013031030001d60402034071000d49400c4007004000b608d80302038203e00d000070f00e40109540f44124428650410000000110075610a00002202e810309030414444256501d00080d69180d1503021044600b444803143c050300e00c40c0d031088403103491081d1100081507480c0d120b03003000641010a081c0c3c01c000c11481040c0e09640b6000e0f01005071108450000d11414280b040914828411103055880c4104018044200350002541000581a40f038962403c000354a4500b03007070f200e1650002c0c14603180c102804840034020a07400c00340e6442c5000404d003902c20f511b00b1580c058002c0c0e13941c070109211184481c440700c9203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 395057778 1250 395056528 395056553
    0x40e0103060509210d060b0a030f060801060515181306030303050f041e050f0307080417070b030a0f200d0e1c0507050703052a0102010917090f1e011b0c03 68
    0x943c0000b030707447c4d521140d10210398000b07841d58002070b50355003030340022400b948100b00c0a481501d000b004403034281000315510325855200c40c0d14021001c21180e6180400c4010314504507800b400c12003c0071000c000c04000fa01c414082200841c0c10140042e80c880b5101e92034501c1641c0012400d82c11981203044a8207582030403405031014024140702034580041000202215407140409550740c500e03051500717044a02b2280d1403caa070700071303540c20000034540f0810f480d00004005070000749c5000c1c0c00c403104014041a81070149284111083e44100c924a20181a04902401e011f1151543c0f41c40000c1d11140f08221180054014582d0000319034443c001030001076101c1c4c4101c0305407503265100d0b40e1515115007003044140c000303208662012240304080052981081c00280402c0400d0303071340c12400c814410507814294901103030240959072114498208241c019081c0b100d15842c2e91490704900101285190100d1044004111110b4000100c1c0d40c000b1f4002e0800d0085a06540c0c541085085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 395059028 1250 395057778 395057797
    0x30b1008010e10170c211c090911030f06040902100c0809180412030c0f08061c1b120c030605060d0b07020703031409090c1608040e010306050921 64
    0x41c403000402c46245402ca1004c14070420781c0140002d1a100040000f00c000040c61901400c00100041c00d042c500010a9041024080c4080b01100803241044640800d1039200c20029410020607404191403000107502908124103498501e960300028002610800403009410003044080d41c50340700d10030a103102010b442410124a0200703a40009503030f1106c0382c02d071000814200818041040701003010940140141d00342840303000b005480c060100c0c100880440240b005078400103d00755191a03a14840c2105200403003461174060801030180000106031886036095041c0114803104410302411440342d20048034031400f070a5640d0800a01406801103400204803240440000c80104400d8800c400960061000303500d0741c02c1c004d10300f03840310318041d01c00041008080c2242c0c03220100158048001504540c1d60490220460041c84402d0800b0f000d001022801140c80d04424084a040f01c1c011a0240190703152208000c1e2529511000da1071807400c1c1e881030728502d0324200c0140c02d4009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 395060278 1250 395059028 395059051
    0xc020f0d030f0b04020f12160909230405010e071d06040207060b0a0b0d050606040303080609040201120e01061701050705070f0f0605010902130905070207091a031c030b1008010e 78
    0x45502d0301180581c0c00c81c50040c1002d8401040d051940420741c00e0760348c1d100b075040700c082141d16202c8034050040c0009014640c44141c9650721220030b80d0700e150700800013542142114120b0328140c20017600030407040e074040590303020f031140c0003035415a40d403a5101400f070130203020521910707220108402548611803c54041c0e4864801e1605540c03141500402018188a400d50f42d2040c84000e804459009013400e1140509000c203001090348280660360003403080c0c42c400000e4507580016540d03c04121004809a410000704040310368041d0451022903042020404500c400002103501b605c2d41107413810300003002807001c3c4d408075940001003d201d40c01122030f0b000d8002c49032952801d03140709802640546400003450401c504407502100010600b0150800c0503060000c002074803001a8400c50b101036840d206409114840c3c0c0b03800100500c4006d00701c0e1180800052031a46030012102d10602080c42c0c032040008a00b044d488808082740556a4808a40e091641c00c00c900200900001000d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 395061528 1250 395060278 395060291
    0x313061b02060a08012c0106030902032b1407110d080c0106060806010806100e01050c0c0301060608010501140a050403350306030c0a140609190e04060c020f0d030f 72
    0x58494400400741003140b9135035032816605101c0074070014002800440e42844c4105c0d094484900c80700c03060b60544002d403030302003031181d141d000080c5041070290401e07040001d20080954032540102c4000b80850060321440096112003d0540751402110030140c107c003000c0948840f24130303226a803029210712a003043c2d030408104600c0c050858081c5c0e0013800c041604102840704030340c2c22114060780282d0443d08401d00c010f107024020b1242e003c101406040c45004200603180480034000b480300707801d002d4000c00c109587c90a00504a88080c455240070600c142c0c4c8044030600203204076610b003007070b589456107802c2c5180d07203404030501c94024252040b80850020495a0b1802e1051040f02014000140d100c2c1400c90405017803d18200040e840384254601c10012a0440d1a111004140841d070311a140c0102e1404209043c1911003c07a524842901011072450783c0c800200c2d000d01d0250720104441001072205917582c40f00711031200d01c140d10107480b90350040c3c440d80150040f46440c10000c10039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 395062778 1250 395061528 395061533
    0xd0305070b0a020d0b040b101211070c0501080f0103050d080a09050118060f1a1302120106020d02060609010302030a02040c0201020c12070605060609090a05100b0307021c020313061b 80
    0x1004070544aa030a1950005400c07440585940100c0d14406001c031020040144100d00180410701c5143c010000d1045050f080081071100340c0c054401139a01004041d80e034156440c0c540f086980c036000d414041550f0201144030350340c4034042c2c1c2d0305a95120b4020f1010300001d550585281030020716200e1034a03120355802000640a00840c0860222001311004100c030364500741d01682c8800c451640c2851814410080010084401074020715055501018229228000a020303104119440700c0d1506800c4c0006011540005c0c12441500194287c0c0c03841c1e102d805c00c001080f58203100c041d5159011301a94005481c09a200700094942800018941054012440c1c01e254040b0000d071007001001c9091014032860303004075070380308000315980c62a051211000503071100003d0304110440340d50f00002030804031440038800c064000324910740d4403480d003514002e548038501e0407504000194121401c0c0c0d59030001003950300c1d41b041400d40d000101d0816030200c1d550034a0344d0000c0c0480c1d84c0072202001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 395064028 1250 395062778 395062793
    0x10f0b1b0a0606140907020d090506030402180108031e090a3f031107050303220b040b0421020906100c0b0906070801120c0b210f0a0606020a0c050d030507 68
    0xc003040815504051105005c01030940e000400c0c500654005140840f81e19900c2501034040d960211020b03a1242c840d03001050f640d01d202c42c088034041403002e0000c541c013200040584a408922005144840d4000c4000801409000d04140d002080d140b001d00201a0503075110842308090384285030150680000c1580c14074804c0e100c0d15000500c0b003400003e16620131aa031500200c580002e211582c0b5201c0843d65921030241460b040b4600449210150303da0759801500402d203881c04951142d49034000800990f200c0d00c91003811842c024000841d40d07401940d00c02c03080d030b00205820350940c0d030841071260b901180c8403800c2c1004850f003504000180a4a0440d0050000b03000030301e80c40c42e241d10042c01c40281a00400188159513221a0005484940003400d0f0b0b0b803141c00b8036840d04840c0d826020a00c0b01c040c20b02038100510b10810640d03e01c440000d512800c01c18006002007070780d41e0070076a01e031102100050202d181104090109041c80f5000c7c081c000d1191502d02e16020f20354407480f1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 395065278 1250 395064028 395064041
    0x40c030f0c0905040e010203010815060a080d0e18101701020d020f0c21040b0a050405060a03090b15010804080c0f0303040803060a1a0304030e0a0503010612020405010f0b1b0a06 78
    0x1c04a00860300034040d5003890b101d0034104020310f03070003189154101081c85a5894031001a0601046841d0000e440d60b21000c440c2801001080c007180d07050380c0c614130054400c4e680e80601c81d01402004241c00c03811482d40e403c1c4d500600300d004e5050484c83c104000c403402c84000c5e0440040f10740d000c0203045000c2d0454802044038000305249961140c500f50300315402c00b45c80c00c031303901c0318146a8000c541c004101e803002c82c2c08860401d003d8961750f0341452020740e110300035503000369800340300420782c080442e803da007003481003c0c462039402c0b8081d610384203e02e2036071808a00040c000f50548000400140300e5800410700c0102c98001c403000303503901e2030042c0d2540d40101c4040364005c1c004028000c1a0501d10100c2c006081203000d8001e2868078100e440c03000e070200800240400145452a03100c81d10391284200140c500074000303000890304c1d0507044504840b60030049005038600400054040780c01503032481682c110007055450a4400340044802c04404402101f06014640d01100018005d12644 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 395066528 1250 395065278 395065301
    0xf030605061c0b010b031005040612150e0c12030d0204170c0603010605071515080a0314070c0b0d020918090f3706090501050105090705130302040c030f 67
    0x3144900d0540240b242050000078030b030b140401c24000000001e0000190581542c40d4224076903102e540710406032610703111580c8290780003440c4c41c02c040b5900b4084207503044902e0117180a05002c0c104070b4071901c200c4500d800b80c900d840e041a42003901500d485400c2e8031b003428207501141d0070300400c1010981280c0c019440b04058a44902c14a00580e4062040003034414048901c0d60456150030f2014203a1311449400070302c1c10002840c1c240844c142540094503e81a03030510701d2000e5150282966201c034006007d9012a1055042c03c07400014001158043c0703603c60f4500311510300d000e44203800d581090b20710000c415002e2295940a8440c144155800c3c1011445000c080c109104801e0030442d41000b840d000350000c8a0040c0105980000320601d84c105403084105030349407059806040c19151401000a414014000103100c0150001c506840c2c0444003004d00e611140c2090311140714154620f002000e50600410161800d1b901c0102d50400750708002c0765003d415000b600466080c0002e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 395067778 1250 395066528 395066531
    0xd1e020a1101090b04021507050a060e21040306050c04170d03110a0e130f0e0102220303020d0f0306050d1b0609080c040209011e0206060907090e0712060f0306 70
    0x900c003241e900080c00d07015807850400030461062583c0360341c1c5030280300078806030003189040030748550824810700b00c52515801005440e0759181c83e10b81140600b0814100003050301c1000d085003900351400c40032101400c00041e0007850a0b1959882030083c100040002484501c20b0000083e6101d8170b200f9041d12039042e2010704040301251001030101c03003040f04a2048000d00340840400fa541040e4240000a0100c94000c16910802d00402c0a883c50b985040066420141d00390341c1240150040c0040d091070125181150070b5050251011300c000d07100150040c4d00114508014070701525958034890024900854515201c0740451454a800c0350304854415a01c0a8841d00320251500384000c0c00349840c1411140d454035041f00e503640400b01400f48955800500210540e00441300e1054a10950070312003583c0781490006511207000315220ba000e411054001101c0e13a1185108030185c0306d612011064940358a142280c41d06051000100455070303880c008113401614529081c000c5214040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 395069028 1250 395067778 395067787
    0x22206020105150f0f0301061e05030105010605030606031602120c0a03090b090109060e031623061c15050603090d03231605091c050c0f0f060d1e02 65
    0x1002400c50354010580c883c140c0d450300d02c6070042d03550740e9110000500101c41c0c850502800100003801010640d10075012001c0b85403900e01d4001182c01c815003140d00460013000340380c0ea1048103aa16200071103405901000400000f25500006041130400008520448800c0311a49840540030351007072410401e1030b800600040100742d0300551140c003034103c0100c45410081e0f0324002a001c1200c90040005100c02c03020304408039101001058511500031141d0901243d650034481c102140709d031007800e81d614964804200781d08144045810b01c04407050010413040080240c4401070103501c128240301e540c08c8070001490754604000d14010a00103018111104103014090201c41600c0c0e541900312429007803410b50300460580503540304800145480c07588a280c00d00311114030598000070790049000050b41400c0d4448018540b06d9031246044580703103681e4078104200030303d40c094079940c04540000c00740c40b41c1c14010050328080104100110f20142c8071780c043c1c0104030100714802e60075130b400b24 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 395070278 1250 395069028 395069039
    0x1c0803040812090c1f020f10140703050606120406020c060408030106020114010f090c11010207030503061011100c031811011704051023070f0908120912010222 70
    0x240b4290003149000082000c1612140880c0312a01141402118181405d2141039600d00070300c107000252041209490000b07550800150007400640c070401c925030305d200009480c81d8001d11506005180c020503050403c46070341380b5810003000051048803032540034400707854415000c12210707010341e108007910381d01ca41c1886002421244c61800180349180074800420a200d862500f04080d0b8698040208644165150a07038050360350740381107245503100144810516501501442c0a00e900712403901c241c4120036000c07034900740741c1403904032983c20815800740c000342c2680c0304810b1903645090101d9104002100e40034150680c0c40c00340c8101e4200c1003c415a9a4401c185a081c0540b00320300c0300f1142002c0d141c05955640705d2008110307050351340940d010b04241c00c03c1100c40c04901c103290705d00c0c01c1c42d05034001004103a503402c600011444031034010a00c603d000c0345803811901d0b500394050401844070300700204d5958108012a03030b55420480008002d07041814a1100e0383c80070031041003140780c034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 395071528 1250 395070278 395070307
    0x1090309080f0102091c0f050a060615030501140111100e010902090702010504030c1407030b0115090906080a0615030503042309130b0603010f18110a06020c1c08030408 74
    0x500c0940b145034030411802c0701070b44d1242004078030341003122040100b001d110310780b49100f80030f80c100c0074203140725480080f401c2044941200d4241c42c0203007203501c0500840f00d4150190740d401c3c002e03461a190104829411548070300050f00d4442a000c1c12202002c0b00240c03003500311481c050720801c01c0e9440388141010341c249840303050380016540c80200054500307901c0c02083d5401105005024400450000541520030041c0303401841e00040b6403241c0d540d54000450282114a2840002c1410200c00056840340c1e48112001c030340014001d842c403070348150b40b140c2c028061012003007a2249072a1000c001b003a400c0000d00040c100501504034010700c082e003c200080c41d000d00303091051b4020401c101c80702c4000704400111580c01000300c0038a4841c100024050801a144215074521f0107450703100e00c115070071a030459540544448000081c08005002c041d07096809a0b1026a0103240c2c445040d08001d00c820603800c090b0091041e080e140e9030381e102c4440c3c0c400e9031305072a56035001c280c01014024a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 395072778 1250 395071528 395071543
    0xf09020d180209010e1504050a060503010e070b0a3006030b011a040306020f09030a1110050f0307050f04030b13110d020a05040218030712050115120609060209030109030908 76
    0x1c119030690100c006500190a1040500030382d0305444480d001705407001e9407614001c80d5004018010301080c9400e502080040c0514462240b0a42c240120402c0c2c00c0d5010a0140545d011514401c1c980f20452400b0b03111810b211039203907202c1541c003007545003122000c000d017500c2e288103003c0801c1e128076604180d120920182c00079600080b001a1044a010302181240c003201d5000d40090307255404445001054001c00c40ca1503014000c0225841c1040303092002518030f402d0445500d000c0001c40c8034112410b0007001443c1da8400010004545014051809031050512460038140790507281d640302c06181d179041c0e41c100b00c0c51002004040400011480c045031104050350008607146207500013038403003e1103124180c095503002840c00040e030002300707900a1100c2c024044441c02e035654802c0402c079100a210070f039410b518014a00814140f03000c0710008a4138103410280320104540c885030000c0030304010440304154204000303880da8a0038050300c06964007984a8100542c500000d90f400c100c507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 395074028 1250 395072778 395072801
    0x50f070f1b290a06120503180f0a0801020a09050411160201031d060610090806190f1416020708030d0b03010b06190e0a060c1401060f09020d 62
    0x2026039101015800315800c4080865250070750420311107400e140d0b80031440d6041d402c4001c4031400380250031203101041d1034020b1280e242e007042016075130016440c0d854404a07004140e034004210300e503455540120050000742c1d00600d0381090317250581c00500d0001c0035500007800c0341d40100f002c00030b05030400c0c0e600e802000182c4041c0000040507040340c11520522003050b0140501d0301c0c0391010759110b07620400700b100c80c3d201240030303001031503440580d100320407580305100710349201c04007000780e1284041d1002c60300208000e0000f034580080c03041080d011310f1404480c9a1b9903071139240c00b12440d8081c413030340902c1010303007104507041001c121030800009500c001c081d50b01110040cc81b48000000310742d60083d1000001503058a2000002c1c09401d40048131035000034007003a0000c3c80804115910613503d441d854000e8484507401c148a480070440c850340c00030464200c0319602154815034030315030034104000001006503ca1a4046043c0501d0308651031059000c60100c1d0b468600e441a40340001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 395075278 1250 395074028 395074037
    0xe090703030e03060f0103061a1309020f0604030c1205030705070f03030f030905030307110a0b0a050601110c0f061c11040f0603110703050c0a0614040c050d030e010513030b0109050f07 81
    0x14041200c07405905c41803100500b4555182d0388528528034103058031042d14001071051003541190b0407000c02401078407405078410081c8032800d0b85c280c50003008039400c880d03000a1415840345424102e4500f40d2050405907007900042000d8000548148621000f03002200b6000a100341075040c0185602c00d03904010090601d000444004690b000050725400110391414801e41045030101504100e030305200284005140740034440710640c141c10042c81540c0030307030304d8002d02a00201d075a035543d944004e04a802503400d0040c800e46040c1007008000001a0a900c001c0c0010380815500c00c942c8551066400e0301c00104003407000c9010185c28900034007441c0b6050009100c141100560341c070130030f43c001701030200009007810100018800040e030603400050801c040ac0c60600000710744c0c5000c07901141d120011520108140c0380031176509481c941c156035103414181c2c00000650342c0740d014240741c0d04c4030b014041c4000f0001d1290368005010b00b120344008180c6050111051103c22809403020b130500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 395076528 1250 395075278 395075281
    0xc030f1208060f030c1203090a080d030b06070b040605040c050d03030609112712030301080f011d060a050604020c0a030201090b150d03050a0e040504080c06070e0f0405060301060e090703030e0306 86
    0x50b500003170000c01c1c00101700c0b0790200c3c402c82020702038998452003c80d075411903e0742e0400071310b840f00841c095070035910b2070301c0030b204e441c01c1181004a60301c15000c0050040006078007141c04520298082d640c003c0c401d03441843d0ba01d81b80c000003840030003880c0045001945502080c000c42100307004000784482c140c0401d0b070900b0000d924200e03030301c102520758102080c04009003c80660f42c1034403036003202e1356036811740e5500d50b10b4854003521a400098005040c0d0b0a15519800b0790760502101c0c03900070b208001a1113613440d003214541c0600380c0504201d610540a010361031101c10705004210000b8442e4000007052400ca1601c25070709800203140440c1c0340b0b200a01c111075034942c038031031034034590741450403680e200c41410007550b100d00d0190f8280d4100c0c2c0740c0001c21007007040c4d68000300008079401007181e2250755289011202c01011003032482e001a0102d480806600b4185c00c820380000004001040c3e01c1e4a03141c00c602c4000d4105da141a05911000d003c1050540201c41d0044142c0c00341c0182c00e05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 395077778 1250 395076528 395076559
    0x603141506060a030f0906090b09150f0c1815041d040b01030803040f1e0515090c1509060706021e03011a0a02010b180702120405100c0c030f120806 65
    0x25000e00d5001000b45600d4071701c4000b1080f10344e0b00c0000c0031030344000104003060319414051a140c1084480c0c0c000c03842030031300c4042c124170251806485103001c50390902a9940e51314003003c154101940310b00c0680c54900003a0210b5660300f10aa404820b035086480c1c07110314046140c45044000864401c0d081c032407a05003c0840c285900050540707410000f401d56036281d5160a02c1d40006a0303802910074901c480c41c500700041107000708090f180c040c10072260740070a456480c264140b0181ca400605074851780710f0b51100d0500319146c051213150780a649042c10100d002080c030503882304030122000c90740000c0341c03001f128804c3c09201007060302e42c112606560400070a02120106008240341c1c0c0300303010403024101d44c402d401c80744c01c100b40030309001e400ba00c0c0c8455404c59087c040d03540780b0160041181440c60079000c1390549084803801031500b03404480080b0150b80b001481c800a80b0803520f0a00d011000c40c085403503a040c01841403044d58002041460001c11111014045034844c60403103100c01e01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 395079028 1250 395077778 395077789
    0x60a060c0c151103211e040b07050717090a150804020402030c04090c020f060901110403021e03240a020304030c0b1009090f170702060f03190603141506 67
    0x54544000030814982422501a02c0156503402404014030000425003001c0b007403400290142c403c3c14031241e4176500c0c3c141d8500302c1c01c1c005681c5155070011420000700490304065040c0d03008507450030500d26104041d107618100d900da0580c0320503d00000107003280d16090162603040140540032540d201096200f40040c0b03200c42c050006886960080301003903448140f00c04480c003c00c96520304110150151802949a0030b00ca541c0c40542d004500c0011075448041c001d01d070700c6507200308465107402e003140d0820580808503105c119401c062501c950901d514100281000e5440d10040034a400018840000080b4001405102c2d0f050040c002e0000103900000308420700e079407299580041c0d40e1098500071a2180c81e03408000c8680c2404032000c02d000035180840412802040b242c03400720011030303000c41d06115808000350050b4080004c0c02d403006500307000c0e5400c01035170b1801602035490305a4500c00e81c0c03402c0c0c20a5582c94403540741100f00e000200141840b40d180e241d1030808600d880000140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 395080278 1250 395079028 395079053
    0x601030b011706190b06120403110105150103020c0a1b08070f180e0a12030e060109090b070c0302010e070f080d0801060203040b070219320d1205071505060a060c 71
    0x300c44000c44184130703100070707264101c8003040c0c401404c0b25484402146800660b614284d400b0b90100e000c00c002e4041300310040c0510b07846035005d2281c02d03040e4a95040110002d51040d4418202400b590040000048040560440ca10655168000c80904002641f400c00030b499200390a001c908030f4081060140142c5030003540e00441c8000624842800481402d0035024000100360300545a840c80d15142c150340283d0380c44500b54100c80031aa21054410222291142c010f082d42c10b040d800100c0642c481c0041007020342c40791001180b162402d070500c9140c1005500b03c2c01c80030030140300500080108004a280880003440c0102140d458030f0000303501c81c42a8041c40e4410540005c440c000c3d91940e855115443c4040071480300d816a44140300c0d4051009030341c001740003118860f00114100500d81d01d1124269008004460702031055a4007044134402e010800b003484414480c200204000030b10b48452190050b00c0820039203032120401c00308030815040342050040c0701c003179140441e1b5901c0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 395081528 1250 395080278 395080291
    0x8011d1902130e0f030319060302030303220503030103050a0209060108071e05040503030409060608090a11060a09180c0306050102070303141303080f1314031f020910020601030b011706 81
    0xd90b20340800c0c0340550190100148000c2548240d90340d500c84460004015807140d064845801900500044002c0c140c684500c40030b903050b03005001096985038030400d040900c481c3d40f07001c000050707500d9481600b103800036442960150000d284000a5051610b01180c0c030101c00d1800c408a4503040a02405d0f05115080f590070021840d400059a07902400803140030b0400101282d403642c1c0d840400350040d08441c01010005000b03840499515440040c0660302d603a4020300c80c44821040c0c40c180403894110502510030061250800640c0c19425090640c6205c05208042040c1030741e040d020301a20074980c05281150701c13015040021a51084503515401c882d1000300b42da405d031107994442040c030160009417948100044407508541d202004141811503c100030b1096941c0b003114642950503810060b4154204c5400140c030881d00303039408144852075000043c14071905002050034507107081200005030b400b840060040c8400d2869240c014000c580101801e6000da0b00150303280d24014000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 395082778 1250 395081528 395081539
    0x1050a06120f03110129040f061a070602040504090602130506041421060c0d0b0603040f02060d0626060c131a0706052403070501020c0114070c08011d1902 68
    0x204c407018542900140c0c2c12408456414411280d1101d002e0040ea203050701642c4600d1416100a203607282d60b0280004031001c8108a500040080d100107100e0762020b107084820390303420440440e080c0d48a10403216031078083c4000680702c40e42c80d0800c100100141d04428801c101c241300401924602202607081b1510a48012181c1d02e6924211000d10141c0c1c80141654010b207c00c0050b40004035024000007035040c81c1c103005c1000c40a00b40003592100340c070060710510301c0c1d44445016041440091509207035040000070425a0fa801081c00c07004c1d105c009800442d00c6805401a10707130300b0000c05821000d043c002925003002e0480480b1455120f2042c00c5600b81c80000264448070b038030054410568100074188000d2a2442d130000c000e04071200d02d01c1900c04200100b603018100051001c05898042e0001c24605142d14019120030703800d1504c0b5181e09400f00710f101d0004008400b00c8000304040c1001003040802000103e17a01c07200000d000509038458090264404071540c100c0c0c2348541c05a80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 395084028 1250 395082778 395082797
    0x50d030b090a1d0303010e061e01050a031112190e0312040212120c010c1b2a0b0c100501061b0308130b150f220c0203040509040501050a06120f03 64
    0x408110402030b0f180e8070082c2d000c017000000c0c0340ea00c124200d912518003141c907074003d2500012032071710861010000f103000072414044150102d00aa00c00744403e82e00c01c0f038103400c02442050303110301c4900c01c8842c0196403648600104c4801a140038060003400302502643c103003c0c0141c864101c21360000e0000e07100d0300c503d4440c003200c007405100300d04829880622003540e443c3c5002c2018040c21068080c2c0300040c5841134405460080022851105540084c189011300c00f11028201400d130401110000310b5061000040d11041400092443d1804040503101c80200740c1d107a1000c840c0147d0250003408170007070350258132903d45403400b00c0a0ba2305080c41000c43e1505195194442100703480102916054030a011001c0440303901013405140032500c0d0380000c070a0205000c08900d0102c1b5000d10800281010507551307840d80c000c40f095121078812241080d595200090031100e066605a41c80d0750744200f40316116807503001e100082c0803001c64015140f0307501da4a07041c82080b91140902000031600e0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 395085278 1250 395084028 395084051
    0x2a170a1b06021e0705070510021b01090807031a06031609020f161a060411120402030a06050c220303050405010e041103090d0e1027030c0909050d030b090a 68
    0x141034072240000300c0555107802c0c90342d40c1e01039103a134130080e4180d072103110710200084c0c285090b444403946899513038090304558080a0030341c01c0551164000714140b0032141808180000b081100400550052000085407c40356491745104180903010600070381201d201c6050709443c404489044a4000c1d41c01a070b160402841247d05003d140505038190011449032814000f20178041d4001e84848510303c50a82c54000401c000c0b00c0510303002d807000c05070901c810041110000385050380240090242c8111801c03994035603041b540210345c1060000408520100c0b100410482c500c1010940c1c0000100a0b00b1610060894002c62046904000c03150040d800dd5480d150450598440080105620390512000e0189c0351040c034250742c00040c00f14030010391580383c4902c840c42d4110300c0b51a1b039103001400703403105091815901c090b40300129101070f0010000e0119010350005007104803001600031414505282041466a4103d0400d410b254015055541d0908099000008000000b81d08011070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 395086528 1250 395085278 395085281
    0xb0403020c0604032405040b060f0a03151d0304230301020d06060e03280f08120709030b0f04030e0913060f021b060c040501030902012a170a1b06 64
    0x81d90542c0c0009001c81d0010400c02c844106940c00f007030480d43c0c24190310140003600c0844204403006421081c030080850a41d052020000c50f00b024098040c10f47e65031642c594280503d443d08140c400c1c1da540c5e01d036088400c0d207c00c411107203d421040145180c00d140461109100b6640d10070704c120b4034501c508a40e01c03642e0075411103035a08071501c03082c0151560707808007518a0b52200c070050302174020024010b801007400c90300000b1044580120403042d0b01c4644950080321a2a9002c803980344007001b1841b5030216403601c2030303c0340c100c56449030401d500314900b04074903500151000e44480c1074103040c000060f4202c0c6113110500700507600120280d880945802a0302c404000260000341707401900d81984005400a00c02d06060100040c4204214401255525811140b0540840e4107100031700556210350844032103280145094600031545014415540607001d04a1100e0380d604400401007144010b0040c9409010700c9800703040455814000c1c1001e12a0b0501e00d8000555060100810886 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 395087778 1250 395086528 395086543
    0x180409020306090a14010606050409180803100510030b0f1e040e0304090c020f0d031812050d0f0510060c08040e09031327051302090c12060414040b040302 68
    0x804407501d40c10300407500b40d01c07a5121365094401c62011403210340c0d0480140140c00441e80c8036540d80d032805181444480081541c1018111039a525500d1400802c01c8a0003443c0107140d1a0001983d8900c1d0008101a1400c1282820305150808403c81c05980d2a80c009480898064840103895160030b504419415001c482443d40030b880d00c4500501c800d8004050004c1e01c0c1000003c201030481d201d001c0e81d843c070300410080031540c03007469030043d620311903086084900c2c101d00c01d050201025944103c0e58204120b00c035000a0307000705541030090130358020301040142c00c041c02c100c88d0404805401c0400315902524062041c2800e000003041a01411140104072500c090a5a81031400ca6503880364840044041d07682400c0740041107292031103410070348103442c201c603080ca50004c0c00ca81c00050600100019030f200050300320f541c01358035012129407044c0b40c0c000c869650744270800d9822561a1024110500403864035055618429410000d244c02981040003416680d82c0c0f0302e0220324041c403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 395089028 1250 395087778 395087783
    0x5011d09090a150609050c120117010f020a050309100b0a0603020a0c050a0605010e0108070803161a0703062303070b16050a03020606010906021501060509040902090c07050d0f05180409 81
    0x614295224041c03d2650146060b0746003014144955281c1b000c0e000c0c024041c03002c003420b08840c030300010851103021042d80344d40644100c0001c50071384404222402260030982034440070800c00030030003201440c01e10121031002d0704050204071a4a010380032070019519030045000341680051a4100755008501c0349124541c801c0886105800300d11302000a06006e00c40d00b007034500c0c6107001040c140c2021404074241d40030b80008600b400d850064000c40c86003250301c141c1c0c07021440c4555415010200109510841054602080003440c01013409001ca5240610b510041c0344025540216a004251002114490544c96480728607600d0703c00e00c2808001070003000352143d01604010141c010070030b548900703001d80b540300440e85c1d0352070140d8442d80d55440340040f1200b000c006000315070041001c0c0201e004040e01c000351540d10703540420102078059650b0070f03c40d40c021691000300082000000750390a0a4900034070102d0600d0009845405440c004c480e00103d003010341d441c0380d1540c1c0d01c1500f9858 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 395090278 1250 395089028 395089043
    0xc0405010909050106151d1f030507120b010912031701030b0f06060702010f0c06110d020c0c010207080703030c060b180403020114060f060708191101050105011d09090a 74
    0x507900c200000042c852070034101c8165081100000d504035100c0407802400742c10307440d81801c405003590710000403620000c10541c042a030300e880307540044900f0014101c0c1c58003624001002e045c805c0c0c0107007001c107088464622403410204920740b5640d00c40510021602d51000700005120280782c02e42e5181812007110101d9482480000203000103180b10038011000d0128004003610b41c401840f146120f500f80203404030f101800143c900c244102c0c41c50000307600a100014084e0401c0d08070301c10662202c121401c00a801150702011220207110001c00504240028003481c0d191034002501d840c070520001d824050030000c2d00c400d02c4003640001c032000c01c004081c0441c004030004131103c4002e0a80d01a0010f6181c1158124400d40440d42640280c0c00200582d0032a20420304000007540b00c070310111074001d014020780859000004021501004584490044900b0780048908481c4c0580c4903604101000062141d0021405c615002007801070b03c1800d00743e0b40b9a807290f8945042c0e6036006042c0b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 395091528 1250 395090278 395090281
    0xa051813020708121e0103241b1b05071203020f0601030b010e090c01050d0c021501030b0f0919080c01023106030b09060d020d08070c030c050d110603090c0405 70
    0x32000000800310744c1c0780c00312a08074944500c2c04c0704880c4555400c2c1d2010316110480140085101013400d0150708910800c0c94a5200310070300520706a0b034407030407601c402078031024680b41c0c500e4002d0301c15054010020000c0303030b0743d107920740701c00740e90305158408d0b469003008551082c0241031003800080c820720000000c45500f0b5035030f4a080c8000e00030900c1000c0c04601b02e6004900d254801255050601a05a480700e06192038040342200600507881a00194814240d540b0144080d030401a8001c40c090301d0704502c10f2400654080c1340705802010310700300f9000270380c02212040c400000c0039952f9820513a810b032181c04040a8070700a21035114502c240c0e0501d00c0040015403c444d00c55031406200305040c0701e03540d03035490301601036402090301560b202c035007940050154100181c10f044024001015510003d045845100c85544064416035040101480c2030080c000055603400c024502a641d0090300358641d04c0d80465031802c400d29034030400c000408554070031000c0140341c907520130003001040a0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 395092778 1250 395091528 395091533
    0xf0908010c0f09061715011701030803040b10060f0e130513020102070b0c0c06030604021b060f010f050f09070201060b04080703021c02060f0904020409090803060a0b0a0518130207 79
    0x500c00c02e9481500040e0f400c8000300c3c0072803250103206448910740004110a440c3c00218174845c12062071000d0400c102d07a4450307810041e0100702c0c140254010608a592810036041c4252040c100510103040c0489c0d020040000c2584594146840903161524201d510074210001e281d10f646181120741080c00c02040c42200ba4010784405003480c400d8080341c1240da907481318000d440c041c01024110a801c40403240c80c0701d003032a00c01583d0098008100521b026010340c038140c00300180341029400c6a20480c10840d007481484a50b0b03024111680218034100e00c2d1400003200c10a8500c0d440380074810300004070389418000d41203031011700582118151590303112641c0643d40c0383d145c40282d20440c3c0380050700340500041c00140164640141001d45000e141d0101107a03160b12401901e50043c1c0d0170000001c80d01c0161003840f6001d03204803504c035902d080050810400020310380000d03500b10700421444e50f80c107802c07000711074038110030b030303000c011940b81d504009a4150141e03100f078041c860000842508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 395094028 1250 395092778 395092787
    0x405130507051207030e0606010201050c120405030405060a120605180a0b040e070621020c0303011707030b0c0c010f0b130e1213080d05070c0504020c0a02040906060f0b090a05010f0908010c 83
    0x190700c0720400c88401e55239060049007680c4080d600700102d106c04000c4d240d012120342004981c010f000b030040320303d010381c0e0358042502c5901110985000461140044112143c1402100c4c02482e00f200c0c080c000b00719000710501c2010015082482da144d03a242c0c80c1003d0b4446412280003100b0341c0c1c0c11348070403c0c2d49200203045030314040300036844114006410040031282d40300703482c3c0d80d0340500019400e5a0904a901008404a180307602e80c5118111000001030f488034200341c07141e4003c01c40c558550b0402540142035801104030700c00c5160504941d55812b4035100c1c01c464080380e500c080400e002280c1003409040207450b4113042c1042c00c0008408041809070b90f072071011101840100d4546600c8043d00300d40d1070086090041010011510801ca946403d40181100001c01e6061303030a0711080f9400034085074088a01204d00c0750701c455041007152051800500104444040340e454030400c5070002c2c113200700d44d015090502c81019100181c1e507200300004805049202c0003007180e80f5500358060b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 395095278 1250 395094028 395094041
    0xb010312030c1b14150703020d0e06091203131509020a0609030803071805030f0c01030606020703080d050405120f0919080319050c01060f0f0b040513050705120703 72
    0x10200e4206210b900342e5912503034016082d1141010b82c0e05000c02c0f90360b1030100740310700701002130340310b2060b50411a000c88000394401d0207600346840051743d802052185606407032594054940742c0d080034040045900012510f11420352030410705958996980030040b1911001150140001c003070400b101000c28111780c02001500d0080f24048040c039910740c41165030900600005040000034004610594061440d20030f02038061312000e0304503501c03000404d10300b8a0300420b400b100d50044000c0f101958040c49071101814880c0b000c1c00481e4110b40703d282440c03040140c00e503245543d810004080c803c0030721004074030080301140c080c2d039041c1c281c0c0c8a42090300040074032071182c03c02d0200d480e0004400d00807203040f940b00130013035400c10386a08501e00002600c4000d42080c02400c0240707100101003849a84050702445405070f06036030400095101040c034940100804040c100014000c0780d9038212500d990070585000410035a6400301c0860301ca004800543c0301e00e02016040c40140d98060b0040e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 395096528 1250 395095278 395095313
    0x1410020405180c07120e150d0e030a0507030521010b0408160302010804060f0617010c08010807052b21111204140a030b01080601080d0905010503010b03060d0b0103 72
    0x4010601d40820703501910380c000d503480405480c1c100100800540150b440e0420310855082c0802040d4008000c070f040d087c038030425010241c00c00108032121120b80c0c428801000c001d8001076044ca140840d004d8094424001c0240900c5000705400c001c1d581c05e13840d501003494100f111100c09517540c50214020750014040c0f4292401480b29401070102110801c0c0c3c21240c05960701e180036212912468014411070340c01034400c2c0e8236110f000c40d04030140e0558040d05504030300006802d11100000511403001038000d90307040d42000e001001190b0700c1c3c0c1d00840a5901d400c907001842184402d000d0766086010074010400458488d4003c80d680406105407118901c41e1030700e0300360200d903851050f207805420002012180b01800f042c42400e0704140d07001341ca014054120b98800b503c0f51191007801c070b003d81c0000300e55481180140140a400e00051201c3c40b940e04224018500701800640640414012050061000710000d03000d940e810300b03110a0f0503040307081e480165843c1e0410441854811a42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 395097778 1250 395096528 395096539
    0x306141006020303060102070909050c0d03020f0c040506100819290405060901030803060307031410180309180908130e10180507020309100816050307080a091410020405 74
    0x1480742c0c0040116403048805034003502c401c500b010400c1d40102284202501e0501c200d181030006510344030f90ba118a04d010f44c0003041d12031142d1881518050311139540a0040b410a0140541d07901c0d1415104c81d604072a0800301e445685000501942d0b0004910051000d81400c0c141c8000d07c12819000001c8203800745443c040139148030600c0240d40d030545103550000d0082c2d00410118980e6000395400400003010f5810701070b45d03070b1922410054158111111900042c4400e418103000d807081c2480d90001c1e94101c49410b480c0e490242400c90306114010f00b982c1c0f549041c1080d0782c217070343c0b100f0b0b001a4032070910b03503d59000100c0c0716071125940c0100c0416191060100321100b0b84021449e048440d903042e00d01c0c080c5580302485020740005800401940f00901915105544000c1030300b880070182c0d0349040c0c0510704013801c00228103000d1b410754140641082800300c040c0d441145185c0c4a081400c4c0490038822900d41072500150583c0c42144d107001d413621018079074404d500200100c0f03500b29071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 395099028 1250 395097778 395097811
    0x1106071205070f08060d1103070605210c0304080c0705060f0703030f0b0310020915270607030503070c0c03060501140f100f08070302070503131806030308070c0c030614 74
    0xc0c01d40e900a03018003c84003061024000605034980b0b280985d00380c0384103201011056601c940403a240000305d821070404100b010858031185c404195000040b05400340203070300340e800c0c06255416244400740000e44108000560341850400801580c1c0040c003014000d640c1e01d0901d0000c1e810242c0007498224000ba0800607019408038080c040c41c0d001d8000240545001100c0b108607000940c00219441d81140b150041c144c002c1034030741c0152068140240307208441641e904c04201c00e0010f024101445918207101110120b0780c000d0599902c5000e600303050181034000c1c00d004c42209081d40c00202000e040000125040c0004401e8600c0c11809466078100e088107401003007450607106040b0000621450149405a44a81d054641040840c20f005161442c25181c140c250750201d002800c804c54201c404104441100e00b140b5413880300c0d4041001101c3c19a40c0050901c0c0c0060050020068002c4800044c0680034980000443e0f00010811400380d488044041840041300c120071150313000e80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 395100278 1250 395099028 395099041
    0x50d0c0822170a0302071401060b1605031611010306053307140102030402150712030e0c0901030c0602163b070309020906180a0b011106071205 63
    0x40c09680641c10710902418032840308820120724490094041d10345005601528140740251401000d140b0b550341d80242e60381c9102d09225845100148000a10768500002041450885001d55941d19081e0f62400b0740c0705241d040c05461401180b4285a404000411500402c4180d1414840146007a00c01384031841c0c2e11000c0118070b002c204441c15540400503070304c0074903014142d40081d40c402c1d00605103041018580f01c0c04041891a81c2a600396075000051009501d03001c10391014400031041c186d490010595901d1b600c1007610f48001d0180350f140d03030b55480c5101c010f02c84034001e010017418160303a6694138140079490080034450344000d8060070b0403480f048007407200c1742801d454001e02d211007030a9000c1040610980401d62030f1b50165150541000820400c2031550b00518a40d0380104420000b4010040c454002500c1c0300c0c030a07a011440d2502c25220020001d900100f003060000d4040c07040c00068403044204411484240602010010b58507040505000040080d24040000c0ea850f070303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 395101528 1250 395100278 395100287
    0xa0609060605090607020d031e0302180d020d020103050403051b0a0b010605070b040f11040608010c0921110d0c03140d02030a08150d0501060603060602101503170c030a050d0c 77
    0x3c159900400204980409400c10204881c1c4552080c0f41c00310200030700c404202c02030100403403c400029000100490018480030340030188110407241e15200040590001c0d02c10244040001d061545a000050600d40038a080c0d17040748081c8070391050b000c1543d280003031720340d00c003620b048030300343e01c010b00109026120b1415561455070041d0420641d840d1170311416500c030603d08084a031249248043c00d01e540f40d90103410003c1003020000300b00b80c84244009080003d035038204040f04040751141b081b5004e42010b1b884071080e0010001c00b40d82510b0b0011441c0e0720611000605480710304000003081000c2c0b421110016035044007602c40390001140d003261079102c1d9aa0304c900080c24040420264510701800081510000388030803991130f559500d03142580c407140d22410210703070f0395038041100680500c662198084650020400c413447e040f07010801c0e039014000a4426407041d0401c10208541000300d4158401c5d1204884d10307200040703070040c080d60045409412a82c10060340b0701c2018001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 395102778 1250 395101528 395101537
    0xa0504080f011802090c0702061b0c0906010f030b0303071a090706080f010e070e030601060e130603080d020f0d050108072c0c0a0905220c020712110d0602030a0609060605 75
    0x43e0301200c4141c684540030410b151364040c08440000504001400041c0c2e5507030002c0003410389440c00c840a0350003984100e410843c0e000743c03a5014170004c904100f0146c4c0e00a202c810919628240041c0c0078441201084c83d501824070002c212004921040e02c03100f0158003140d1058a600702181c07142d9031503107800c071103602044d12006080781c4550014456800c0003030345154844040e1400e583c210006900080c039026080e032040021803100c0e0305140c5c007410507082005c2c5031980190203000691465861802d00c1c442c40005084a03540403500a4a5650120859881045c0b40da400c7c0314a5031107a5081e0f81300c83e0a4441d910051214401e0b00d4000070071043c84c0e01098840004a1040740e441242c0c0710401d0f0701c000401070400244210210700c55850201500350301c44d00ea00800041d1000c03904101c1280c0c2c20416460075580a040c0c100541c1e5500c10140502c540c0c03244014942090036804035189212040d0020001c2c0e00200410010404070790106084400c02c0c041442819034078801070701c19209 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 395104028 1250 395102778 395102801
    0x1214030a0f030b01170f0108010c0f080114030c0a03060b043602040b0307030501021206010305090604030e0a0e13020415080304050f03120f0304120f1e020f030a0504080f01 76
    0x4658460012060190380420300752101030421174040b1481000d002890700040700d003004001361600050000344024800d152001041d170421080788400c214010308000340505c6007031040000c2070010309468400380719602c3d0304c680261401c0d103c681c881ca8243e002d07011890a913409145400002c0d6882201151400c0c4546142040880100c03e292248001912280b5043e0707000343c0c5889008480d80ca00b04a000003c5000e8400161980c01c492800710120401801840c10982000107002c10200c01040b90781d000f0380d040c10309050f0040a04041000821250f0242c80055005001c2007007540c2c804c10020380c054401c46e4108100292440c03480102c044501a41c0000d5100348002c0c402400c100c3c0703821a00440c01001c0380c2d001511146800c0d0316502074000020480c1010040c481040895076502202c50914200f418030480044401040180c0c4000c030300e2401e0307031048075500441d4000d1180b0300074031107048103580c0d4a44ca00b0b1000f0303045510511646600e4451f03030460341240c00301072141e40356081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 395105278 1250 395104028 395104037
    0x305060610050a0e15040803041802070b0c0705010902030d091805190b030f160614160605060d120e1201020301050603040f0c080d0804020a0b03070f030c0c0b011214030a 75
    0xc00201c0484100110f040c2d410742000e10181700391813203030a8901800060400c44011a074440c10080f68414110403c2026241c0e00c0c010f1200800195517201181c2c2d0006008900c180c68070b00320f040c40c81c050103074200041d4142c020680ea0043c03007644480c5900644850180d6850f101c071000c00740000b140c200300c2e4914440003004807078164885c51034000101c620030080c106c5981c409503000306070600c1d01c0ca240c02090418001001c024050700f000c0c445e4040c840403600503003404944c00740344441e80c8ca641d10060038203076074100007540c0766541d06080c1981d50b0400301a4040c1801101c01030100000645500c3c4500340495070041401c50500032681600c0001d0080c07811526544c0c0d40d417090a0348140c045a009048601c046400e01080140401284a03039a800915082c2801407143c0350415400c1804080d00400411551a402420414084e200381c40c0004054021f03c0b0215030104803407000600c0d14213604000100720b201040e494204e60f004080a5840360b0514154540d280300e980d95000115 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 395106528 1250 395105278 395105287
    0x3032004090212181c090e100e0108070803030c03040201050403060504060618020a0903120314090106091b0c0201111e03070c050907142503020d090503030a121806050709030506061005 81
    0x1c804150314006103a01e0500345401620703101d0244c7e010000300d03158075029511960800c943d441d035900b918010100b0b0780160080e01c1c24081095141d2100800d055104800040842c0440e4403d904460007141c00c0b0800700040d06140c5090000351a191290070302c50540544100c1c841c42c4a0b20841b07400c040151a901051351842e924000400513400c0750405260303441c071491000e1030b11824104e2041390a0070000505601300700b043c1e4200d0f0071041c07049102e041300804010040303800220151030543c0900b04002e401d07c00d420507524007000d10300b44500c0c610400c00300d400311003000000b0340000c074402c840b801c660745d84400030310031800003c540750800155030035848a0798581c85002040c95075070001608200d01c9003100800100f800f0140b0440c01079110f441c40518140e401107030381c1c02030401140514a003424030710005068088100d50302c4107807070b9a143c008440760060380420701e2040d0310440501081c0703031810010380344040038032068070f00d4001e0328006402c914215060501c076a0b403e07207405040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 395107778 1250 395106528 395106553
    0xe0a0501030b060903010c11060c040b0a05030615041401081e07080406090b010f050306090c0a050114130605070b010614070807140708031803030304050a0303200409021218 76
    0x80c2c031500c20415000f107420007030385413552000c1c01104400030654030f034402c488a480c040d940c07405e03400030301c0d144145600b032000707214007055070b000c4a85005003881c001b80c49407205800030340d0003208104440003610b00000e00281d044003401c14290703d20000d880302101d55842000d5844908800740f121160403034a440001c0f01507008801481c0c1080c0102000141907000c1c0e643c050511000f80c103c0d06003c01181c904000c0c602d001c220641e44148000040d20444104d01e0105566480b54004c540c14001400c81070081400d5120a85684d0100d218101c0002941c680d80a07000d03500121042d510008102d001240c80b034000e0380309000c24106807103198504400d0340c0b40d018180d0408501103409440d41d00b01141c903484108164005089000b028550361444517499a11071102d02210034000d41040c01000b02084010070759503240758041c140420480144610040303004081d200384100c00d4800305002c600d0300c1d01c030760141c04059000740f09044a51952003141c221a10b001d00c103062203601c000c1e551501c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 395109028 1250 395107778 395107781
    0x3011103010b0f07140c09090a050a0803092a010e011106040303021c050a0e0601090e071a19050a0207141f030209040c2c0105030f060307031a04050d0e0a050103 71
    0x820b5524400e910b0070400740f40d0310410213840140b85403a082d4480411403e152a00202048e0443e44c0c40000b00001d03c1c2c070b550362070b4031500d8550010f0000640400004c1e01d070380c414000c86000c404240090548100f4500d81268148440403089000a8104140c907410f035000311034210101340c822009221651760707542c1c00c8000c5d600c0202015000a00c24400700761100c9103005481c003444400d00082115005a40c103e882d001050b440105280c3c01c1c44003c80d80070501080c40c000740d03645042421006140308000144611414051200e074000c1c0d400500842270b40a00900f1111026a0903510615a074010340f004002c5041203090344952059104800c500280d450450070309103038240035060001c04d0740014212800c140a40c004102d00445140d805107051aa503007038000324000007251070f10303402c2c00208240001841c052428a8140110b200c658040207048021070707201940f4411580007040507024a182520201c42510035102000340d11805007a000c0c80040700034108441c900d150400460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 395110278 1250 395109028 395109037
    0x100203010602150a1404050105040b0a060f051c1a070f02010b01080115030f290a030506061306030f06021c06150509012c030d0c0201081b130e01090b03011103010b 72
    0x42005e40d64405140c80c10151080c1c0c6104e20302030400011141b0345800c0a054030100184003121651601800b40188604c02c0011019980c058410400c1d40425111090442034100d101078800d440130603803050218914000300340300720402c3e51844d1000d43d8586e426400c5c0c3c1c7c1c54030b84140c04180848014441074444000c2642c000100380b0303000c038001c041000107000315400c9503045800b41ca184600580c00241100c11248120b03015910f8040043c51501d4961f102c1401524181c4a58205c41200210412a402c0308001c0d5130061002007003602c02c2d190000003503100300c200801d9000000c01a02e14800ba610442c01141c1c180024000074842404080781c6a038001d10310241401b26191510429000f00d0001248002c502440c0c00312034000101098a4241c1d5600c401c0108110000700c440181d074800c00603904003104d54050541c4541c1091180040d020380400c016042416400020b600410b900d0074504032100881d00704581e021007401d1500740c070118024220041d000f040104203a220090040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 395111528 1250 395110278 395110291
    0x13141b071407080735070b16021008040507062003031030060504030e0d0b0103170906041712040602011b1b03080429040510020301060215 61
    0x2a00c0c06095586031880080c80803441c1c0e806501411003800140400c0115030058450785041c6161400030003005840b41d901014803240c1e0745100c00c3d80c411401406c00070310002c0c01c17010114a40325001d012024461403848a403e9114507400415412000d0080240c14003036078000024200d05400e00505035140207296901700500c0801d810305502c03d20061000e0350155185000710140640f920607585442001e101c10214083c2c9004603014a02c07000e46008030303040f83d20090100e0256540d04007515612811075105800c02442c0b40620204159000458181c81c4550360328419400b8456141c40207000b07411510781c100c0d40800040c080d9044400d000046a080e0710121625010080c6280001d50000d03030000c00540e451384041407641d00b9041e4003010903101850241e80c500140803030204c081101c01005811b0114101c0031405010000001480039050400808c0400c609c4280034503180d081110f00b1b940a00a1880010a030f07d414000c0b01d041b2002d60b802002c0403800c20107208024000900700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 395112778 1250 395111528 395111581
    0x30c02042a0c05120307081819110a091806020d23010e0f0c04061206091b02150903270d0b070e0406082104170102091314 54
    0x34460300034190554001000075030382e40090301009403070030a160400c02074075420418014010040c6c2183e01c40c000c158010142d02200034006001030f007031f50410b1807400b410100d40070100c4000042c414403d4440305105400d5800c00c00140e680c1c8403650441d0090030784a6010745282070007001003030940e006440301c2d0f00b0107c40042c5410030078440c841003808440582420588440041114250100d401d40c1c0c400a5038020302d44628040e240b00d80140f040d030098800348145a082c109190500350320000c05042050020000440100c1140780c0060904070140c00520680014000d4101040b0800d80074101f160000c508000d03030102c0281c96103003404005c022580f100b180b110440d50b9080004d502d0903004041c103a03464108100c000f0030000c0c42c1036402e40101d0801c0003c00507040000364034082000000c02049400402c0e000700313080c500c903907480300709034010040b0101410001907000305036280341180d20903800125008800180e170039060550032400c00d84000100c0e1003100c16243c40c0240c188400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 395114028 1250 395112778 395112821
    0xc031d06090306161205100612020d051906050f210a0609030309020a050315010612090f050c030717060a050a0e0303091f0e03030c07020109030f0803070e0607030c0204 74
    0x882e00e440703002c035a5034501850b400013104e0f5407a00030081504520701c1c01c4041c40540f42c1840d1055840b1158401d035420465020b1b0b0700311102d070255040d034131644444001445941031070310f401c83c0b4403042036940b84040c40c40c1a03400661890003008010091002426002402c580b240301144e0740304403d41d10101e03c0c0144550140001c4013440b403290103e101c0e40340000c50070790038014050050000d0700f0041c003035070100707104503194000c20861a044983e14074040300c00c1c1b01801c5020003c1c08480f0002000c08200e0600da100300710010074120710040e402d40c2141c20385550340f1030b20050440060001e00340f0340c000c603000c510802d0480d00b01c194810b850070b0010550400550007103146a1040b1202c101d10f40081d42418408000e20f29074680000301c0c1d603002d000c038070b40035601c0350340b80d00c0f0142c5100c40d44100025030303004590040104800640d00200500c4600106050074501c0b07034000c03980d80340003c0307945a03640180d183c1041070743c1605030556503440b142085030f400d00c0000e0040a0810f56440f40c1c509 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 395115278 1250 395114028 395114047
    0xa05061b031c06050a0608040b0a1113090b060a090e0406020f030103120207050603090304050409020310051006020d0f300e0307020906040204030f0305030a020408100515010c031d06 80
    0x80120101c00b1904a103900614901c0b032044551903007240d44112000101085070940c041c90300341e040750f00498010030755183c1489403002481402501401c0d0302e00442d50700e0072610b0341840c9500f143d071740c16002d00034680700c2c004004280c802c00d035054021442280c8244440c01c032034144680d21a2240c00c005140034640c1d000d01b00190026482100c0180c08042c00424403941403051000030f04065400900703604004074040c0d2240514010ba41c059a0b0f1102a00159138007004440d004a070914807c0ac440c6c04c04100042011100d80a000007520030703e107041c4500c501c254130040c03409101d03644128441010824458103505900340d05a4000041110307a50f008145110f004183e0704040700441d40d45a0b05d1041c400007040003042c0d0342c4524414407080004c40c5544007032060140e0b05280640c0d59913503003801074009000719005680e01c0d20038500e00c2d1103114225804607001d103400000ea40c00c56047c0c800111042400e03050010001642a80111904030f141c2c11030007507501c2e0060109081681c0e12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 395116528 1250 395115278 395115283
    0xe010b1909122d080d0f0b060a0c0302251a090a0b04081203010305030304030f02030f0c06010e01270e0a021305041a150d02040b1009030b070e0a05061b 67
    0x70380741518180c0d507205900b14101050700000f03120701540000b440311403006403201c0e80135000d549032840040c1c4c0c840750340c002016015444a8555180107001c15150351070b03050300504d1440001011805845050290f03107610305803500c40000c900020101026290a00d000c80610b581c0c00d01080301614001d21984201e80c0d6030a00501c00f500203600d44503145c602d450803a0780303002d814035401c00c0c1c2c2120410050000c140d0120403240e01503018202a0400d0031400300c02c92444c4038000003c43c0315540171441384c00408000c00e546040320b458400301445642c8614000b203401c56a00d4038508002c0c0804d204061409140c1c1140b03419509030000e03a81103240c81e801044c2604007040c4400c2d40703183e40707400b000104005c8181c44198182d01c446452280d1401904400d00384c1800762034039108401030603a40702156580d40001c2001c0340c000e0712891182c3c9842c0805070500606000444204038a06c00080380300d485802ea01e24a944020001000c981c500003c0c8079190780108512a8080000d010f03c40610004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 395117778 1250 395116528 395116559
    0xd0204110a020607020c15092b05060604202b0c0e030601120b01061803060e0303090c10170a0e0f0318100806090612071d010e010b1909 60
    0x19034002d40030f0351804c03100090900da448038440b40301e00700b00000340041c11041e606136425020207540c5c2c40d003071200404006120240c0845032405920898098604125020070003500603501940d00303002000d03c6040da03406010804100e640640401d200c0c580741a0080c02074001d420103020680461201e000901e20203840b1050704442c04680d10068800050034100071140c01442112102c0708a81001e65800007458010b100f40410803e0100d220581403030f100104200459124604120b180b2994004585a41044690344494000c0f44040314860401c0078410128606c20f13034a0009241140001000c5514060074030003c4c250382c0c0b03090070340b8040704015601e56640444000c507280c00c0724004903e50032048459003800340de400c40400290a4002e012150040403c41b05c5820564030700c0c3c04540200c1220a10406511488200180000210103104100507141c04000301070703a210303060415600b0080c814150140c10404c000a104103414800b0700c0307a64203a260107002e10345e46000140040a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 395119028 1250 395117778 395117797
    0x70308090d150f060e060904050319020f1902040b09010b041502030c100504020306091b060706200306011b080403171210150e0a0303050c01020702061606110f0304020d020411 77
    0x1134400052000f00c074110411079000408560b010001c7c54a9078905d6100d003e8055408000d034000b10344000e13000e0090042c501361a40d000211080a11402411800c4800e2001c059000d14906982400213003000741c00c150582e041008000d29140c541482411000500785c040c00c1107020510001d14900c0060055544c440c110180100f418107103401050b0902c0000b410104240d03002640681c0c0d04449226210440b4a017160110784441c4241001006040381d408051400001504400684490040603502030343d42030303841c0c450200520401e560a2003240401902c049000d010420001c2c0300102c00c810002404441d8908111329455036009140060f01e404070a164003400c1888041184030382c91540700402e140254503500000041022003084d40009410414009116600300314250104d0301c4007039010b40f1959030341d00c020b0140206903100b52800c440031400d041e0461850348240d0240d40010480c1d01046255881d41c0e07080114910702104200e0304162100c0303004032040c1c1000083e202042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 395120278 1250 395119028 395119031
    0x1503110102010e06100608040c0305010203070f021b1305040602072001030c030c080619150c140c060a11010b040204030503090111010507230910051209070308090d150f 74
    0x2282400003a09442e00c0c0301c80b01c00d440e440380d82041481000c1d8441a000c0303501354140002c0b952614204407118030140e400c064500e6000105101450364855400781480b034260382030311950204c207180701c2243c0c0706001090f58000541c0b0100c1500d844544c0c009074101d80305000c018031700301241c1d441444c58090b06200740c010105480401d400d40d60075002c1e06d001c0c20f0403490b00b08600c0382d44000180429101621890003010b1301440743c0800803924001300b01030040c0b928146403c14214000401300e0f80b01c007030112034905200700070b0b20362040005065044440000d01c40c504145100c4812101380f040307a420a0400d40d26202002410740311840100302a5020300c0241d80d5482c001780c0090300841c0345500d10b06043c0c0c98401044075240c2e20890702c2c3c0102080d096280a220b2400341102e5680c001c00100720741c8445060032003108035800000401c2402602c81103c10565114a8410341f5100c0307502c0041d00640c020002120726141c881c4902030014441c000c105c0007508108025800c0f81c4050a8002030700307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 395121528 1250 395120278 395120303
    0x3090114180a0b031e1902161e1712060907020a06060e24010909092303090a08010204060905010e030319030e1b030d030b0a080f06010e0a0504050a030f031503 70
    0x258100d80401d0800c42ca400480c099600707040201b4000911480b05c094031003a40490102500076554825401140e081101c45110074401000c02c60300d038590060498001d440c204140c5495500081a511640107803146048696070380002c0c412158802071041085000e17a40f80c07200080d0240c8243c03009030510143d1580c3c40d00c1c200252140405000545119850032004070240c1da0380c4c0211488180d0315000c20203e8040d00518001c104000c42d254034580f562203a0030b28841d140c400101a003407000c2c00310303243e50120741d4440c040c600302e1107103002d0100082c04003a018000740d4020705c1d42041001c0003408480c0703080000e06114100b680404488000a5110000700c42e0002d42006145000c00304007a01ca60450020740010395212100a07841c02815107680b007041c2d040c1c0d03880c4071203001011010162030040c2d1070314802c40d449803008d00881c000b400742070b0b0114048641d103105071407096500c0070003050b02015030b443c1074503995001070010b010162200c100a410354580031300c0800861150400d01c044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 395122778 1250 395121528 395121541
    0xc020307080a02070f09022b0603081611012a21030605032418030912010902100c0305070605150d030c1104020304200f040905061803090114180a0b03 66
    0xd41056101d000c4850042c094502c1c231003000748410a1700310051304800d2221041c0051030b809444d550340060708490002c540304410354450700c030b00d03500c0310b1140b20815001407076000103503480480b44480081303040400c00311440c00014100500e4800d4010f001c044810b040700c0c3c0043c000c0180446002000a464040401560404110b111204140040d00412029610000401515004020200740202c00007840c075440e200748120703040814043c2403078154800590800380603110a44040380500d104503039091102e48110300c2100c89542c50343d5254170300301103a160000504000b0f0a2402040c41c0400c98001560f0340800403e015440307502c90b030140224506108007620810703c9005d014600420410001418070054a4402140807090217140303500c0e02c000c908512586866181c001c0e2030000f00f5000d20400081c65441800c064040b00880f80541c2d00c015101d0050151907400305404250203c200382074403015040304041c01414412102c02d92000418001c2e1030f038011215584008203105a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 395124028 1250 395122778 395122799
    0xc0306090b0c0c1f02220e090723011205090a0605090c0a0b0a11030301091b0903020102060601051803120705070b07110d05011404080a03060e040f03030c020307080a0207 75
    0x240242007901050910441c2030700e0070388a0402c0c43c184144072410313203040310030441994143c49038800e641102c0885001d4014043d800c1004600600ea5214071a800041e50000001518410346403203807007072000300c210b0042051a45110100007414800701e18019150b0003118481d01c1d00c5445180e000b411840194200b16088503009081c0c00015003009620300d04c140c031010b0144044071002c49030f0a55800c3c044408541d1031415100b201c0b003900000000050341c0b04560401034100c1d540219a40803d94400c4080d100d15486101c003d01680008002480030360140b40036040b01c44c2c480b103511078080c3c0c043c03000030300309906a214110004d502207450701c10303c0f40c1048614041d044e4140c3d00d40c503044054492440c0d008043c941c240c8500c4440c54044208a02904489001b018801a00318503003403d00d41000c0b184c0140e080d40002038503007400014441c0f22648130178001d80d004036100d0140080c90b2000c5001c1c0021150784003e620041082d07400103031300341d070040c04c0f040d07240d03405488228148103900d207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 395125278 1250 395124028 395124031
    0x604200105090f060f1e070303060e07080402120f1f0b12060103020603040311010c030f0e010b01080a09230a020f0f03100e1c03090b13050a0303050a090c0306090b 72
    0x34104807040c00a80b190f40c4840032060103014003142d00720f0700d40042680c02611440f84100000e2a04008041d6800301104032024004403031181d1410f2040507243c3d405107025034402c0320003c00040c19400441c025003000020000211300b1441070f07030031829103031f0055823500707009500b4071001c8012892005000e850500c41c40310200e804451a4014510042d62545c0d01c403418000a4801c110000201c1c08042c020301081c4803141d10030000384044054490045c0007055000300c2511040e00b001080c402d014818843e4003151001611005450388510411000901d4880412030302a901c20242d9419003070342c10f03000d20368502001c0c01022146a5031050051000881d85000c0c081d5003004402081c2d980d01041f101c018003500d0314001082c000c0388442034542148118a0881000d03048604d11034a5410f40007940c8403130050780300c2c28a54403050240b8601c05c0148c403000d021034100741d01000001e0310a4111580115281402280110194940040d500c0040d40700312111035654030340b141089022031815 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 395126528 1250 395125278 395125343
    0xf1608010608060403051815030a0e030f070f020d021504030c080304050d0303020a030912020a0501050603070602190f0b010e01060e030c10200106090b030f030405010203040b07060b030604 83
    0x74007819203400d003071540c1c4200140c0010107014020a07080003460703010502d03542400c0018008490400040c0c0d024406034016200c804c90340e8100590942c14010020840361458120030704035241240340d0700d61428080d4191412030b032000ea00c1665901581d04e0350300c80d10455205800960351145140741079521000c484c0c0c051401034000340020460f542d01c029003400b0054140c00c01580d10014030384210f009054007034004000c038078404c00100308243d0000c2c04a11991040c2c00070021070700c90b0400c0564400151084c980182c0c8158180b2490503c41800c040009200710703007076890380303019503146660050f0903000500c0c10980b505c01005034582c040004540410142d000d001c0c0c442207180030420303501c61409081e0501581036415145c2c41c2c0c1e0710075422030041026000f00704060721400ea0001030309140140b0780c42882041d8000d2040c0380701008440c101e800c160002c6103400c2c9041c9030004142c000c030304207036881d564800c082c820588040c0f0120348150300c42c040031020910309100f80c40032205d418206 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 395127778 1250 395126528 395126531
    0xc0f06090f011505010828051f0b0301030204020c030d0c020c09010905070822050609010207030201060b12150105071e29010909110d140c0414150609030f160801 71
    0x4281c94045050441002c0c0d0b0003e29200100d951460744215019400903e600c00301c58001c81403082440c0300341d2015010748a80c404000c0c52700161614420b9164007070203440281d440420040005241c15030081900b4005a81600e0415a40780503070703c00c07240b011f440312003da0898805c242c2e040c907010182d9405045402400c2090f4142000003c142c4038008142a141c2d000791385000b00390709088103440e55826401000c40b0700c1e605e40f030421180070b900101d004802541c2402000f04100c1041c41c1030743c0e2114005040b0129070b98450140b406454103044032141808410800300021031440c900c00600130741402c18042c0110414601802c0317002d0b0b0109071014207102c00501c80d084e1002205658112580d1850204051a8905210307000381070211207294084d9001210008007c1c05031601c543c403075244015190304803002c80600060712090310030303110248010000103420381c000e1384500070034034005052542000b503030101091411200b1300200d150340d8840b004c10b4403403000c4a04401c0c00340115500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 395129028 1250 395127778 395127791
    0x6031a1e011824060504090509030301030201140d0b0a170714280b040f060e04050f0a1a0a0b0409110a0504030206180904030c02010219020a18020c0f06090f01 70
    0x1500b5041462a0440914032600c84848000c403155240d8021403843e020009551420350301e410190417580035105003a080e40c11702e0b000540b60b590110543c2d049a0301a1107096211800701640c00c40d60380705001d00c0a01e03da40300400841d03501d45c032064002400b1000341085240800c42d401925000b6954460f41001300d41000c07001c11610b4108030036070000021607031030302085100240ba40381c48002c0c0c0c00a041045000c100080c040300308004900840d1469107464081b4480700040c4410340745c0494030400e0203904480400d6040842e5486410814040b000440c241c0014000040d81c1c08250ba201070021200840e051000303044510842d100307140d81c2101645000e00b07880d0013800c64015448064480c900101d030f0441d50840003500c0070740c900c800400040d400e140034030300601081808030090380144110400b9040c40c1214405040c402c6400400c044211032034204d00c2510b000c42020070303503407481d028000d510318020200104514980c02c0c00140c03c85191583c5103a2424001550f2170025a04149 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 395130278 1250 395129028 395129039
    0x604050309100504050904050a12020d140d1b0f1d0918071a0d1103060d06020d0905012a081605090a0b1204020108150102060a020d06031a1e01 63
    0x300c41c6607180984509400da4203100d0705907160301030342e40038941040c0d40c1010003080001c04a1070039842c921494030705c140920070010417030340d0b4240085d80101060f9050005991020020068031102d60000d50204090004a001c4440c03000c44507103150100750181081242e094001200d01c85c01140117070410883c046400025080358000b40080c0d1004820800500d614641400001d0142003240907000548901d0b20302201d0701d0340410f180090700c615103e070a1500056440c1100d0140e1002000d42d1342d101c031241c41d03a02c020741c440c851000c1c0c010765039000d440002c1c0707003030040030002c400b1402c1c100c88041a055441c034540025044600801110390b00708085031164401d000c801c1e400030307d082030700d5210b0700021500100c039580165211040104e01e10403401007094000d48034520030faa90014030744030072a581090040314440c4a002d42c202000003000c007043c03a070107069905155103000c074080350b594881d41d01c01400801c001d034628a000e0200000808490803108035080d910004c034600d50b2401c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 395131528 1250 395130278 395130283
    0x10b070632060105310807080f0705150717090a1205010b01030902030d0f05090406030602091003180b040c0f1d0f130813030c09020c19022202120412020f060405 71
    0x100c2440170116000301c40c01c41142c0d800c1c90900b000d00010340494450503200e0b18143d0343c0300d88440000040d032183c50380124582c00d003500d000c00c8007061484200d080400654440801481c0a070a0030340020090180c06c0c8295244034284006080308183d141d01c241c414140710f425180800d62807418075050040f94401a1000112a0514241c51400482a4042c000211140d20450215036031203810303c40d011080c0201a801808403400c1151084030b100382e0500140e0507601d0301907444290200801d41c10340072aaa8160700345d0701074821349c5104145921148000100e0b080b94120001c6211442c541741080d8a0340300105811002d419440da10301d00e03064001000c440c441c1e074001000e024000c505c170891800030349003640203154400b55002c17140303071101d0808009400c40c1104824a201c0c05c01252450000f001448040c25009000c00034400104003180c0101c0c2c80340c0c00300c1c0301c2040c1d007045506081c11103a086580514480c58a81e038070110300c00f500a15041c0c00c80c9060200384c201c0b9043c400010b400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 395132778 1250 395131528 395131567
    0xb09090402060a090b070b150f150c030d0c020708120403020906010c02031c080603100504151d030409060504051f2304050c09040e030c06010b070632060105 69
    0x1120410f5a80034180c60440f0840002d034044061003d000c18041c080041d100c852a120302106140841d015071010204070f1502184113501c0c1e00403c0c130b84040041124110024400010700f24222464091402e40c144101c80b2038000c4000181c1100300107000c4007806101c1c41e6000b00a50000f0340c02c240c203540000d0400000504102e041c000e12654410071910140303e00410401e82d00c0710840500d50504004d402450200ca5986c400d00a05109880e031002c14821700780140e0708291062a0b0482444001c00208418a40280e240082d441c0c0c1e25030200f030410091020340044000440c0542c41c0c034003803101362400035001c1e0900c0d909103000702502d90000e115103000c4071000d008503184810824420380d801008619820341090601c010401d01ca000500200604142501d0401c07140c3c0030421000d03141c4c001c403100846180c0101e4010003003408150050032100303004000c00100104500e0a016020700643d0801d00c9490314469010a00d44020a4081d4007203000c2c03e01d075180c501c4648110900d51071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 395134028 1250 395132778 395132783
    0xc0f1a0909070c0204150801050703020f18030f03220b16030c2103060314150103110117090606040b0103060b0909090f03031311030c013c180b090904 66
    0x880001c2d5024890081c54480303d40241080014084408003250030b2074041c05410f40940c242004515014130a00c03c075040000d5070711140d07040024400810b0400b0082010b402e5141c8a0010404003a100600080140103100d900c488078000c90b21540314058007103684903211034034091085421160851000503191945450110881c4400c2e140005080b48010319800c2070708c0b010101c2201d1550107921040580c3d0094100b550641c01000f4000e40e2581002100410344581c0e40c010000502d01382c10303440d00044141844030303e141002a4a0003070b968201c0d00380c08554000401d010380c1d82000d110381c2c448094207103018480142071445040c01c07803041845a9003c1c01c00180080c2c3c1c0c200092101300c0c044145001640d1350380c103110342a0b100f40540c01d00c0c15a2094101c0c411180189400540924039000603101c4c00031150703105071149102540c0880740e10302c80c0360024600300a0f01040600b07075001152510380e4039007440c128504580510305a001416a000d0410014400e0707a141c113900c0341e1066 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 395135278 1250 395134028 395134039
    0xf030c061003080a0819060906060935010921110f1f06030b07051e040302030c12030c16060906020c1e13050a051603051b1803030301030c0f1a09 64
    0x442d900702d8050f01403001e030350502e06c80d4a40711022803468030680250302107402c0d50396085550340d1180e1101070844802064080c1058005d1400b2401000e500051000483c0040002030b584909455868113070325080160342c0210003000134414190740142e0412290041c000040c07040302442e001595407030a4407111030720b081c20105005544d000072070308804003840d44041d00d010fa50810001c0903100350003142d9400c08083e400181d58003010500e10941d0110703a00140106905907922061190780140402e50141e640010009a04040010882c2c000b85003006410800c94900d040001084034005400240864105112207002c0d13540c0c041d08024621020752a41e8000c0304600c001610094034201e44442d0300303080034200501c00c03242e64400c0d80715088861481d0144c501c039903c00c0702120320440f1150030125590003040064144103020f4003a420612003a046401c0744440042c0ca960803d910440300c1d106183c800303000f503412038a80c94000b01204001c00c140880011155075850195007049030151 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 395136528 1250 395135278 395135281
    0xc020d0b1006031103133305100510020a080a050906070b01030605150102070335030a11030108060f060f13050411030a03200115090c080603072102030304080f030c061003080a08 78
    0x414034010342400801000040c403c7d51035800321008060321040b9002040c1141c40000002c145c104240f00a20011141e40901140c803901e50b64050030307400500210003000424061801161240801041040d005074046204c641c0b561a203401a00d10084c26801c00268030004c80250741d070000381e440103880d8050304042034503000850354500710400c500104030045010b2012a0b144401c04000c50041514060a000c04903103188240c03800e10003031060aa031075014000280030710701545007454200d4002404c0114205c0c070540040c7d00c40010a4000c1c031801da54a00f440100048071000b0307801c440056025001d180b40c903403005044a905000c80c041c88598401d0900310004080d80881540500003a090242c151244403100040c290f0b038513110089540c40002c1000c61900040d4001101e59a81c2d48201100b210f4000d1603510140d51012a01403106100101d0100401d014035880282217a005580700c0b440d4600440c0381c42d03805000ca00f17050307251800038000326813074008a44410310b81c0d081c01c5505 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 395137778 1250 395136528 395136563
    0x123060316050a0b18040501030f0507051912060e0304140109150f0c030306030501140402091e2206050c0c060a0b06030a052205100606030203060d030c020d0b100603110313 76
    0x6001c0403501c917551007480d00c4000b000700100e2050b00c5141d41d02800840d482c1ca03071100c0a10030140c1e071048011100f031140540030040703030105e656210f41040c462400825080501c2514524603000398111403100f5800803c0300e0115648044494010b10b044151290000300b025070103030800d03da9612403002c000b405442242898002c1e040440215031040c020014948082c2540740c0b804801e4030202c0c403422020340803841030f80c100611604403003e039040034100381d01d40508280c2264020004d40c4001c40000c019100410701c140314581c4655480c80c009543c489502e1801400d01100410305110589003202c0c421003a1249801d8940c131803102400000e0548420214424903030306104082c40d02038460702c0180c02c000d000302c0c1c0401040c80421061242d01d484900071b40c241e01044440c217030001d55044081c80400c0c400d900e11156603001038040c3e8680c1042e61038840311802c081319540001601c813602042034560500c035680178010308402031815810284107141d600e01507110081c00110001c0d865030304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 395139028 1250 395137778 395137807
    0xd0e01140405010e180702100506030c010207180617030301050f030a0503030c031008031909120f0206071a0c0c0c040911090603120a030e0d051908090123060316050a0b 74
    0x5444084100040179182000b03000b5503415180005550b51801d020204030242400078401c1d00c188016001b50690504203050780c1e0444c0300c05200e9907401500c1d64800510854502681308100000c140074603a20742c10321043c00f448910244249020f64000019200420700101c1500e03042841141c41c280d80f501c07034010700a0580f50325004140580800586021600880104541141420f440781051a84d4500001d0850002c03c0000b03405075503814102c0c80149006070040c548a44143d550090040d486c500c946641e000c00c95400c00d032074100041220316031b40100400f50003000126000c0c0f00d600c039160358083e82604001d116034090301c101e0000c00c410740d400348101d01e01074a008480b25200d0194030130040140c008400724400c039018509040d008503200b54103e45c041040000c203100e841589400c121030070040140450700365541c8130300511051081d030094003087d12124008490b2810300c64201414010b48914140b103c4503032a404000c5600c5140301041228a0510b03099125000380b00d8040c6d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 395140278 1250 395139028 395139049
    0x160b1b0102040f09020d0f02092202040f06090e010e0709030f02040905061905060d020f010c0c1802180904030e0d02010c0606080703030912020906040b03030c0a03020d0e01140405010e 81
    0x280300000318400130a0403049603000d045800a151014085a03020010b941c08a1244d140721300d40085a00c000840607109054a01d1480800d00070018a00f550780c175100142e007030b02a0013140c00540d410f4410000011180813581c0900280b640300d00d10343c20090b1019040d154240b00003441450910072403030a5503140da01c04001b07140c0201c141c84662411415040303c2104021525080c1458032011136058107002c40c1d1144510750191404015450400c0103503030b0010360180440300710a0f192b0000c681c95100311560511031040550240e02c641840c1e030b05050707003500900310718010307402d01041002180e440025440340c6101510006080940b0b030004a03091912180c000d00410b00700400001d25940c0001c2003402c4a009541e505650358440c1c2d5104200b82045401070750107402c800208601d442c26a00565010000400b101e00d000000021142000c4200d1004d0300503030043d06052880c40d40218031001403107070901e000e03220f1000d2405514400e0161340580c03410810080010b01d40c607100c800c0f244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 395141528 1250 395140278 395140289
    0xe01020a170c010f0b0d080322080d06050d051f020d020f13050d150203060d023304030f120908190302070e060d1101021f0b03160b1b010204 62
    0x4401048075000703241c540e9488003000c2420356191031181d10200e4668400e0102581e001840c030385000303480f40c030740c1c803000e8001400c04c00080c1c2000c0d000d8400c001c4040c040051480c4900000d90701ea842c41000b803422107003541d0140d03020b030608894441c000780c8007140c401407404404d8001c0c207202000042c180d0003809000c0351640500e05c000303002c0714480c0807903001e8110b10042c1c401d0141e15544840a0140e0400305950003080c10f038000d0000004500160007640e40071780098034605819450b070300003e1160b503005214000c04a60501c4000d141c4800110451040243c00c4109143c589580d03641002070f401e00002a028008155288078010720606e5600d008000003070407908880c4146040c07500c0900b110030110094400c4a00001e11203011500c207a1056500030030380b07005c1522549400e02c2c1810450310791411400f40801400b2940b081070140c0c2c04011880e1800681c0d00c40180074185441045d00d0920088590144104a288241012035244032421004204a00b482151710ba000e4000c54001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 395142778 1250 395141528 395141543
    0xc02040c03020412080403050f031303060207080910120509070b0f070219060207060f020a0f0201232b050408191715030d0c0809101206090c020d110d0e01020a 70
    0x750085c80f0781c000280095034020703020340310413000420400d6541d01c509401d85004041071f5a04001203046036000d840000c0c01250600e00e4840c1034400620340c00d049000d601e020941941d400000d1030790500c0342950000105008080c1503080818009150040c061300440800000500d0300854449a10505071500c00c50450115291200c402035141d000c89d02074174000030540c5051a02c014400036807686003607002840d894800c2044d400441c4e480941e0707000e0070074415419401e10003200b030010043c104c0c1c1c10800b019a0118110144062000006007650b40ba0681040d0074407000c11090f000f1207103400200940742241c8800340c102a1281c0905000c100c8cc450300b075404212220000c12082c0381e4a1804805546052030300490944201d120008003074032134a401d01020590b42070401070050303401007030b042c005407120a54050006903070039a040710f01940d403140540d070b000307980400241d05120014100b00c07000d041c20102c42580da80407443c0b83d2040190b6044841e9581c0d00030f00c044020960003010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 395143884 1106 395142778 395142809
    0x80708040b2e0906050a0f0b0f03090f0d020109020a0b16060f060b1602010810080c010305041e0c0608011502150a0221060f0f010c02040c030204 64
    0x2982107010642c0000446003440214010008001d60751000c1916400c010074442c0f03003025030f171003c7d030140c2803084c0500c0006806c1041d5001081c0240f0341302e45941d145501c1e10b25010007d58034510794015444500c0300d03150306401400519009445c58025a40e581d1a05195449581440d81c4107600f011003220000f25650000000c0a40201020400c05d480380054401a07114021000c0031311040907465003103503000308030523038000e8600f032001000901d0002c1007600c41407032840c1141010b540c1d0001030204280034004c0365a1040e2140b40e8295142035142a603054cc0490180d4000701c0c400000029050803000003803542003605501903c98000784c040300014115010300f64100c1c1c0380d0203101280c07a03203101d80805505000200c81809483c10514140308044049803165030081818404840903640c001030380c02d6178a80e059400081e00e020211003100240101d42100a51100c01071 = true := by decide +kernel

theorem cover : BRFrame.Cov 394964028 395143884 := by
  have h0 := BRFrame.cov_init 394964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 394964028 ≤ n) (h2 : n < 395143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
