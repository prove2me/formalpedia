-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0858
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:12:45.018828+00:00
-- url     : https://prove2.me/submissions/b3f5c75d-bf91-427d-9192-2b668a3af320

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 154136690 ≤ n < 154316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 154137940 1250 154136690 154136707
    0x8030603010b130c11030f090f04021210060201060e15014508010e2806180201030507030b0319020406080601060c150207020f0f040207060906051005010201060f051005040803 77
    0x1306880950200410307040307429130741e20303074800001d9801c03081005109501d07001c00401804071103201307202c840b0f8111f50280303d2440c0d14132a441510340710304a0f07160328a0040d40741c10b074000d081d12002c0c0e00001c414000e10f4103008900c01501d5007100c12200a00700b46003400c06122039186007a880c00342d001801041e0206445480d645540c562500905032a00000401e071180029803c8076039a502c800c840e64040341000081144249954030030184c2c50391104802c2c0f0054131940e00f912852503460540d003015000d98021036070075104403a0011802d250030416889542c0c02f20f81d40c1c441000c2003044103950f2080400840d0313120b8100b48090411441510307140e5a4070b1201821144d43c0d800110ba007805110f00c0804d185a8510070350349440d800820010f1000355200c1804100c0040110580d04260200030003130102c0c006000d6240030a1013400001054a00286001c007a242290081e40c11a41852420400d80c0c0340c110643c02618421240340034078040d0010155034511460b03000514a0101140100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 154139190 1250 154137940 154137979
    0x30d03021e0c032a0d02070509071e12111201030224040e0705121501180302030c060904060e10030209010e1612020408032206020106060c08030603010b 67
    0x10752558004074103201c50350038441400490184400e40401030748240541e241c0140302002440005403680f07210001c80c0c200c20311241c02e091403040080096880001c0410490a110900340d07401090f6240c03054501c485000100940b80c1500a00e000b0840000513102c42041c8a0303001c600340d02c1d0007001480d81c0303451445010030040c0d424401644680c0721030911214219850100c006490070b140741851601d03042c200900303894030b001f030407000401c0024170103043c103d40400d280600400c40c0c0d20079481c6031507604000400029900308881d00119000d401040180c40000304080907a40440d0343d40e8413041080c001c10300401c01c030340c44030000718107840500070300c1e11f45140c0b04410340e402661540b400d6a203914111112660507906c1319800b403513500307414038a1342c4540144000480584d201618103640d07084c61501d560030030a04020b21149403c0070709882040c80e555074008201900007406001d260080c06046d401032a074025000b9100040000d0b1256402c0d400b5002002000303041d90101c00c071420024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 154140440 1250 154139190 154139197
    0x1e0201050f1803070803070c0927050f06011401020706051e12090607020d080708040201090f15020c041b0503181e010b0d230c030601060f091e091802030d0302 70
    0xa03030007070141c0d0401041d1000e0200c216051f0030b412410700320880d482c0400d250000c10214100544100d00030708203240900b1455400c90900d40030b00000d114400c5074890750381c00c11506070310044180c081c00f92520080d0343c003c5500d400301e0f50705050080c0c0b01c7c240281d00e80445e603911684110a160b001850006508200d14100d01070850035003100e0b82a0759010040c1c3e900d160503010039010412940000d00c48920a040450f80303d48103250160140707965441c000741a00094028540d0074816400c400380890b0704112204120008035810722206140b404c443e0601c034205461407041100000000d040f0060724940c15000c0c00b114011100300100d5560003c00070100c0c480c24400d194203180711410a4900034281290380c60308540d03031000b00d40550300250442c0246541c0070380d040c0104a0f6510306641c00340402030090049071070b14101c0f0240010000d141d0986a04031084640703c40604061062100b0014410748116440014015601400750622002e40c0d0300700961604c140e94201030110b9041e00034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 154141690 1250 154140440 154140487
    0xc06010614030f04020637022103131a04110f0f0901051c061a01021c0507060207140a0c05040507030606081303090806070c030f03091e0201050f 64
    0x20312008107080325030740c0a02c1c40152025018205100085000351a0501c001e0004440c11008482e00001c11001d808010680d01c040a024030420310411010b0341e01400351903c03c0141c4200032003a01081d00c3c05100c0f034000645502900b10f4600c81c2d030300c208003821340c00c41c1601c00d50002040c1c05207054641088003c0045210a016109600c41c5e40c180c1c7c00c00c012280d9140d81d008050000341d030b0810341803043d6200c04d14400500381003000f0806011038628030400e20703080f00c0c0c6030070b40e00e140201c0c1002901d03060301003030020070030308190041d800c0040c1d004c42511000f03940300c0000741e95000c00d8104118225025000311419002d40b500c00350411048014900440c3c609903014030003569002019400c56010307120310000303e0002000255101c908491505c0c03401e109050080c101a12800741c1c03807926804694160129004031b002c1d1043c542c02c0b524480054036280b805006020445d990080c50b100c6400f01802094250100d03541103a0154058400109044820303940340da0240304021a0800381d0140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 154142940 1250 154141690 154141697
    0x408120f011e0b072d060204090b030304080a080f2505010f0c1709120a021006050409080901051b0d03150e01030f0b2d15100207060f090503030c060106 67
    0xa22085400c2e0001550003120410503409062401070344401a0b00404000307546424044051741d8141c1c0c1c11040d1030394042d01c3c01020b0058845080c5403085048030241a01540310358010b0004202041e0000307221828030303912402c0540c407a24062182402d070f00451903400c09600e00d4000004020600d8122401d8850190000340000315080782c4640494066954900002c4c50445c500c00000a8460205803c0100c0e034080b200c1e400c0f448001100c0c29001207408900503000b250140451150601541d07020b0001120200034115865445440354440c280141d4103100d80810010010050740e0840307450b03000c542c026510000110b080040090864410f400c0410f208001c010030401010340049042c9c99214075040344d50100c945401c80d074000020235440c04081031141d80000803030901400300b960078180f5507003210b034104281d200b541010702103242070145003098007400d03400307500080e5101164014148140c1c0054150301c11140c0c1c4c200c607044607405102c0081c3c0700403016030008074581290010b64 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 154144190 1250 154142940 154142969
    0x10b04020316020607080c03070f0e04020f03060a0f0803070f050c030f0c0114190302070203030715090c0801020306150307090b03010b0301030506160f0302181e0108061c0b0408120f01 81
    0x41c04c0d0385842e42500c1511f03c000041c4002141c1c103000746054440c00d800d0f410b10301454811140003809982c400701804c00c00340e101005002e15810581d03054006820718064a00d45d042c03e001340741c0d5490086440c068420092a14000248901406580400f103005026901035419010709250303a21025052180001c0b80901190854120703141560100640b1601c5100c80081d41c090440203034020301c8080c2e074180810043c1a002070401181204688800704000c66181400e0401080c510081d901c101c0142e40100b0800c461942c43c6481440b41d104000b00303d42d140d8a403008110b44031096500318503540d00d00000041070f07101c016809507040300c0c0704000b100d240ba90707400c0f0305601d540010300343d075000300d09003100b00e54005000e600a0712400b0501d124040691083c1d800041d0018540301541e41564490440c01296507070204106501043c2a10414803c80d4440e94000c1ca581481d0f01c003401c05080140402d04114005084892003060034550280340d0505800c0c00580410a10a140c034104044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 154145440 1250 154144190 154144201
    0x3020f06040e0621030319110901051c1503030509030c040b0a0909110402191107060e210105070801080c01020a02090f150406080115210212010b040203160206 70
    0x808031816034401e100e500302c590b1188024088500f06900f80c441c540d041011905038000d41c01c01c09503100b448110320040081e10300502010859007459503494946000300250310080e41c0210031111261711030800811124403090000d0007d0000e03812450010100c020008241030780174020700780860048040e2031a0020740307000c0008030b034080301d006030300510f8034081005480081d0784290f03805170041010454400e90fa400003802c0f80e200308010445040018180c0c20b050f80c0c004e0354480c0e052800c01c01042824104140900001202107016200780c01000c07181554421000400c4040c1c103180b0002e105070305182c2c8018141000034014268903200d21407910700c196100150843c545170700034140013420b8450225802181c58028465007040030560311004413602d07603104020082c000540000342103007808950510040f00d030352010444007070100540400b09640322010044560482e484442056100d05450250886004d025809803002c03007041405020031b065504122142e40c2541c0c1c159450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 154146690 1250 154145440 154145449
    0x609050405150d02010c05010e120c0f01050105150a0909020d0506150403080a0f18060207080c060403172b0501090c021504060c051209010e0c01020a0b16090503010e0703020f 77
    0x12002c085911201c40024800075500400c5903c07012402030f000407441c0982e05251500c2c250642c1031b4520003070310000e4500e01d540b0061081c410a28a1000240095458000050f0500030787e00610326508000040c240390013401092400c00810000c41e0a64585c840161100c00600c8202c980380e000d44c46039940b200b00c84110000b02c40592354041030f0700741003503c03004044480003640301100e028054405c01c00c0320550441c19001e030080006500a0050a0030907410f03a0130b01c541803204501400003070000703100040300c07103820440301458081d0ac103484070342c2c2088a03610b8550520403460350500b01044010300840c26005030b4180c540f9000e060180b40b01462049a46075090301c26001140c4080011500041194000240209a0346441d0341003010314001192804000d40707903446241c6d0f440010b60307070310300c0280005050b40c02c00b40081c100e180707995140c03850203810050460010080c0d05000c808000d00800f20380b80641806002003007a2180c0041042d0b81d030380240800d0344141c828298034030043c41c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 154147940 1250 154146690 154146721
    0x1404021014041a040314010c020705010306050a150504150507020415050904020f060903010213150806060a080a02071e030822031b020402190801081204050108090114010609050405 79
    0x144072406460103203480c00301021031010901100001900300400030100f07090079483c04070110101c00001c1c04c21600040030b49007004d01c1c2c1c80141454109001008503a83d03a042c200102e45409200301e441c030054090444403440780e03420804c00c05504c01c9640640942c00409040454800c0c3c80c208001c1d8a07105140348445840e22600303601031503010029005041c2070644500320342000c2e01150400d4071000000c1e081e60040510340e500825204010002c0b02c3c2e0000307255400356401d04290025051010218a1a105035482c0105010701c03840411aa0070706681100d408940000b00409100c0c10310300d90212007109000260001030368100860540e1005000300040d0850210b8550300207a6a41d030700f6245090140100d4415131010340400026840300d00040203441c02401a40300e00e21113020003e000c1e6001a00030002c9648000200402c2400e01d60442d01614800d082859280e43c0354405035000d840c000403590040c4110200010702150007000d91401c2d5001203406001599801d6030f00806e000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 154149190 1250 154147940 154147967
    0x91f050c040302100201090501020319060e091504051c27050a06110106051f1704020922050a081803030c070506070c080a03050409050c09010804120c0614040210 71
    0x381080208018a0210b810342c4200121340004074103c2400d8442908982003103846600324a820030401c20310060510414000c0c01d0001759002c55824110601a0b07550b03031086400b480d664170000882e0074050b08001c00341da000030b400103032144103c404000a2110760802016050140b00400c143c2003040440c0d942c0d0190344000e17204444051400f0740803610200350040e180c02a560300c880118440d29691624241c2c99407a9a2010101044480003800e207000e0020100d00c0300742001c03e220059603000141c2e900306086c0721030b8004042280158600c1400d000c94010001d100b603440d8501005079000c0070788070302903004041000520640b02456140e2040c1d1070480e00ca60448081070100340780c054050303c0b825002d0600781403041d40b503261903868040030710b5003074020800101c5c04200c40c2c0c02d6401940e500003c0b02c0002e42c20841200d00103000710320701402c01044440c04051101d0307010710a0780030011140c1c020800340aa080d18107032481340407a058600f0f03070040c08504491540240124002070004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 154150440 1250 154149190 154149211
    0x50904050c06030705042d0608040c0521010905010b09010b070c090f06030507080616091211010e040617060609010605030a0915140613110403030e1206091f05 70
    0x74005102000b640340e00041005041c00b00511010900b0002c440311460614201126070158041c0740710b801c601c5580550040c0c081200820400c0300052140c60900101d42c0e040d00c50f05000300e00030112088454031140c00311129868101c0315018000305420010303020fa416510701d4602e0340c1f102d08030b014910500fa0083c09621001408020a07072203580810180310003040c00040c1e00b5101d907612410800b069202040b01e0703001000b40540c88280c50001e0982a01505059600b41e2601004030901038024201900c050a254100c1300540d024140003c00000000c20400c842c54458040132414815032a24880911562001500a050442a1750f060f90266104d10307056650b00156071020f404245401c41d0a5450a0346100421005000700c60001155003400401d6281c030f04280716407400e00c5200550a1410000c800700034580d800112401d580c0c052030109522144480440c200e00c0c02642c1c0c0d405540b082030f041007801c840204506115400101c107194050900480a40070b886c02a40c201065 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 154151690 1250 154150440 154150453
    0x10204060f0804060603140a030e0307140609010905040e010e0601050405070c0f17030414250510110604051f151205010905061005030d0305040c050105220b1305090405 74
    0x1c5000d10012a0b11601c10200803c8180d01c9039a4406072000480200f00d895001521040c201070700f06070000040e207819001049a146408103200000000174011401144005000111a403107602248060180640144409200581e0541c020401441c45c01080c1c0541070000ca402d00d8540281c6000312115519610021116200c0b07900c1c000c0500803c482501d12542c14640313206502c0b014601c920f00031030282844001100082d4100564845d15045a5030300c6410f05508000b800303010380648134255823119450b11030034007e850500c034206610866125450400c4100000022004200e5a214a010b90807810300d880440a1350594003251b0042d0f520518140071000400f400c04414500800005c1140d108c5a190f0a05000c416520000c00703420010090000e0f0900700a00103941843c3d00d8100a9450310b511615000c1e800c0d40191810444001b8502030700d004144103900509424003095104255100800c1850303601c804880c0401c0720102c400060b052a0035502284a83d4021014085 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 154152940 1250 154151690 154151717
    0x90801090b0a0506031f0606111507030b01030603061103090106210b04020f0607110901150e100212040905060a0b0c03070b0c0c0d021f0b150708070b040f02040b0301020406 76
    0x16240040a19815201342c21001c220038106d058291201c4003003070000a4101e0520500408403c14500c07000001d50082d03100500c070340402c04590343d2003022880d001038008000d00040300034182da07074006400c550918008030b500c450800e0081d406400003000803ca195518210441d20f51040c0c20301408040b800c4a40e2004034000f0308825030b00c20720051810b0300d559000f0700010056000220103540d02c10514044018078104080d0207800f500020090103580048584000d100a1030201f003076014040c3c1400b145e0040e030003081410211920500c1c49074460340c80c1c0034210000d080c1110754a209107184036002903c0008801281c1d05482444059807408c4001e842d000c4ea0fa00700501064090b200800c0a10700141003440880c00d03806c0715901901e22095050800d0b05200002e00c292a242442d10220a0b15590b078402c8100e9109a081e1585460311003509010949000c0c814002d41449030000c1080200a5000c4e520500c2d184212030800c00340c580e54043c1800c0780200d00482003c21014000f440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 154154190 1250 154152940 154152961
    0x90507110d080a0b1c050d0e0a03111203030414060606130501050901140309010207050c09270f0114010501030c1403070315080d03020307020613030503040807052b090801090b 77
    0x41c0c0c4a180f514000c501e0f01a10310216402d1020764480000340d40111104c0300402c401400b104540104524001103860002c000081c200c403c0342c400242541d202c45052015a05c802c0c464030f0b0702d82180003d498480c5454242003960000381c200d0418130380149000a000c0346800000c2c2e440210006545e000004d003800019501030340007075062030604c0b133041001803000e60400001c51041520500150310381105140c00c502e880491800070780b00f526198104151913900c8100c03003d0b58000d000000700c1c030100c5003494900780192904615a00e5081019040c440d00440e00c0c254102d41082e41c04100030a00d000c0304035942014043c8400b2210000c1000c40c07452486500704540c00e10a66a450340925a94903d4515000007508548003194002c000c000c14150140b01c11680040144808804600c2c0740e500105039100040004110410200384141404420428000300341c031211601a140a00386104070840034414071150002150608080707150141809803600b45903001102c1d10a03910b82420b20f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 154155440 1250 154154190 154154207
    0x60a1218031701180507020f0a24090f080306130509010b010e01080702100f1104090504140304080304180209120c1212160302160906030b180d0c0201180f090507110d 73
    0x6c00318442c024400b03003224414001d1084443c8120080035031103071215603c0c1d800c40418440407008506c0c0042101c080745e000164841e103560701c0940540c0c0da41d95480017903c40c0d030f07481d203450b042c0525040800800c03a80560241002040c240c0b41c262045961000445640030100d408100580046440c2c04892905810601c03c0c0c914840000c54000100301c00e0b540c1c42e42040c0d2110700b03000d49440610051010400c0a0040100104043d40c41c06040050082e501d200d54800c603880c69100050034505c542031075044d0355245400a1217800c0078503075010029501e004910300c0c141708100442d03074040c054000242c0300148200d5000c1315820510310100551030329600140070307010341c003d44407481559a5441951b2010b0059500d0018285045051516884d1802816400408130740c441130b0102403000130340545400340a1420240e6103541e0300c012200c00b0104504010301e52010700000c00c20380b40b503100b003030309440f5039140401c001d96840704111981c01185001400c29000110382d06030003803050700034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 154156690 1250 154155440 154155451
    0x6061a03130b04050c060706060906050a03050a080a12020a020c130605011d040212010b0d0c0509010503040b0406060503010204060e0102060f011202010f2307020906030703030e060a12180317011805 87
    0x15140c41d17940b4100070175500d0340880000c41d0035540d00d00061217400414443e0030090b1400340c4421011500b165a00341d616143c881001d00241800303d101d01d00c41d8800c500121448040b0881903441741d4030220065a605461107056105120550404c918402c041c40359104941c4160349481c1800e030741001341c02150100310107054000c3d03003c0040340640c1504440c03050083c0301c0c443c0802d0b6510840c059500032143c05996080402804108040140c0e0388030341520340080e000980720840c1e803500c2c9030130002000d140e400580c1550002c900041d40981003551000c3e940c800381c00342c490564a40300c15820650007401084045403c00d611800594460700c0c0d007100140e000e0800c80c032503103205002d070840c0304800d2448003181d10300080c060045050902115400c8034080e4002e00001d0b08541e0081c114002c020280c42c0a1100407d95030704662241400c80131428800d503040180c144120007110340518149815404602800b10143c99050041410780c1220b043d02d076021400d007140032610001e050702419 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 154157940 1250 154156690 154156693
    0x71a090d1101110a0e09090f0c0103020901121506181208031e0103050303010504110a08010303031e090602030f0c04031e0c080d02060412020d0207050f03160306061a03130b0405 78
    0x901d4a00a041507000309601c030503a1711044243c0d0048000c014400f00b0083c0001c1ca513810507841554040c83c0001c02403000300e02400d002d41c4860a602c0100c81c42080394441e140320a0920300a8501600c2100141d400c0c3c4019a030788521a540e0401079a201c80c6551059080050204520340301094120028642048010300940d6203d03603c0c030302c1c00403010310a0b0420707070301c40e040000100f01c075180902c108c0c111700c0303040103a942c105034007140c0c090303c140303030500c4054207054484203e11140081c820322848005640681001400c000d420210001d400407100d0702c0e41703d1100310114503156501c505440c2102c0d40185461020f6941030b9581c220420840801c450b400c24006011039040c1c0240480e5001030b10340d500400843c43c0c541401500a8211040002550001c640d42d103403090740401c5c0c2900307680e0155201c000d8241054046440d00c00070340c107545a0481d1000003c800c005194024004480030320741d50703510100d01102068a984815156203003104907040f0803500044a110304554414040c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 154159190 1250 154157940 154157951
    0x609080403083f07080c210a0b01020105040503030c0c0111160201031d0c240c030a0207081b0f0a0b03130b010b120408030a02041a071a090d1101 64
    0xb41c03004440d4100145200503260451421002c212500350004000c0f915500050603110b400c0c802e41c2c030603000140130202040001030009810481500032140f038298480078803a18851480c5003000a604191030003040c680c18524481c0440d8814060f540c0941d400201551664542d803c03494020303403040c00c0307038400e554940300c2042040c2c181a02030444114003010b034000c548031620005040700c080905020075201c1c06003116003600400038540c26182000c1c1d40c034002c0382c0e082c0020f41d115424400450080000c0015008410340000720141c050f042d020340072511603544a448140e290016600101000c51a8200426103850040034407a040e24001d00f030904c2090701e4030401d80070313548200d072130001a4144034512010040164050750040840143c82e505020540090701086071010f400503000c4240440070a4048901d41e04481c003c080e5100c42c03800000d82c8903483c006907000190240d84040c0c00441482c00ca5110890361441815218040d2000d4050b086080e18000c803900c0400d80d030f96580300d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 154160440 1250 154159190 154159193
    0x81c180302030d0c03030e07150309050709050103120206070e030c060d090c0e101202030303060f010908070e0a0c0507050d1b0b0a0e0f0d0512042f01080601050a09030609080403 78
    0xd00c80c1c5100d00100b669550034a0901d801c5c042c00b0358205114020956200c0e5408200303441082c04909400d140d540b40200e8038007100d050075803900ca2a9000503200354501000001007200d800000000d00c1165001e0341d40380c0d541e002045c1c0740d00304d070030310702e1501a004426031818a207800e8008040201c3c1c032040c00a00744074076031202c000b0000d0540004800d003603440103011070484450f41040042607100c200229a9803941e0200b9220b010240c060b501842000d03030300c0340b082e80c01190b0540c041c01004040b240c1231551207417001c4d12004155004c1043c240390030720b03100365507225038202e4a03100e07081801407d0000000e60120740d01d801a0a981401c0c40031705800c900010510011140941a11000491051705440d180760900d40840b040306016480300111031041c0783c20401b924451007800f00f11300103d588604214140000441d407030b0490b050010440400060a85d5131100b08403020380c1d0702201f40d5120030040d01d8920588a0300070210b0042d00042000840580100e9180c902c55010982084c0d0f49 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 154161690 1250 154160440 154160443
    0x30807080f0c1e0309031207051c020a03121a010c030207050409081305040902011b0512071208150102070b030c0f041503050f040b0f0a110a030b0307081c18030203 72
    0x8103007042280e040340da0084803100141d03c100c3c45140610307001d1480e2420b100300281d9980d001d0ba001d1070024101007102d1013400000c1c490f244802100d2014400302c0304188000940b42c3e0741d480011400302e2070200548070208890720500062242641000d0340c54468880151241c02000030101c0462103424030103d4181c81d00c1c003401c0d0003244079070b4400d07403914078410010501c02c0080d00020b01031440c050208004d0b0380c0c82070703070300080502c0010300d0480381c481d5041840c100742240e40710032504000007400c0300801144403110080904150340b4040b15480d02041600c0d5540e105206138016800341609000252881005580006a0416051400303a02010420064101d60300c06010511044880e0a107181c0500950307034082c01e0240b6100f83c41c5000e030756822422002506180741506650000344440d2620b900c0350019040703100a03c0c0d103810303580e08010050178480d08024040d000342c8400246440000465074562802c000d40901c0d807807900320381110211002072809514104c1140d002015860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 154162940 1250 154161690 154161697
    0x5130e07211b0e040e01050702030708070807022d0a0b1b07031209060206090c18040203101b0f05070807030e0d08030f0a0e0a030c06050705040503100b1018030807080f 74
    0x25440c3c01940110040403c4129000040c183c04964100000c2000d0300c0e0f03000c01100c0d0708075400f00c402502c540c03a90030003450350700070604029004000c00c7d0901421040e04a0030740d40440d0130740c0088036000162000d1115400c400d2007000d010180601100072006900320a1070035441001c1d00302c0c1d0006a494441076004480c03e500b03040070442882042c80140da0500409034000302c0840101012140d40008c10301406807104107500c2102004042011550244265000004005024040f10764580c2e580c041498030420726001041800c21942800c50050054844041d00880c0650400c00240c6080c0d030210080858507030300010809e08400018200320180d4068945000c170845240741000e0110f048498441464515611806c981000254400118840603030302240121b02d9441c0d02c50162110b00694101c0c5602d40a15801442580c802e41c0c4914240300080b24003030310f02c50040d001500e21880707031141400d55200b0501c041c008500140001c00480c3e11a0344a1860071030040b01502c00e541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 154164190 1250 154162940 154162991
    0xf03011e1a041b0806030a030206040602030403110a060c021014061306170304080115030b070e0105042303060a0902060301090e0c0402040303030b21150603030706050705130e0721 79
    0x1003c410110380c2991040d01d0a512020030340092004402d141c801a60313407200240000c15843d0000b000404162003403a0307e5516002e0701301140c0244606160100c007520032a0482c40041c0300c1c850302003500c040e041c020080307100441c5200080c80c0e00c402c0c0510810440564483c020661a44000501d40c0030118007041d840740c0e101c1c041c580300c5040000081c2591148510103028250740481880801c0b00c80b48220f8004510b410302244010902005031120301030b41c5d03c1102031034510300c040c00540c83c2e0400e11442401d002c4040c2c42c0d1942d205400202168036582010b5040031042c401800418080d81c0400c0a23410080200d5040401c2e07034000070103030303845608100c3c0040c1c3c90700e110380c000e800c0c20f02000b62891400d514880305c800f05a080385684003492117041052030aa17201203101501c09204480b14983c104009001ca0325040e90003500c03551107140b01c031010b188025400607051a640b10080c2c01200d850741ea0385c00c1c00701e85d01c50f2160300c00c0611008401c0503981d804008001c042180c052030802c2d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 154165440 1250 154164190 154164221
    0xf0203120f0304110405010b0d020703020a142506020a030f0306210b150319020a052119020f0609010e0409210809060106050a1103040906050f03011e1a04 68
    0x901d040d107801c034034500112001398001c5003440f006115181d0714009482c501002207000503100c04040c101203207007900d404005001c400c1e001000c005c03c6800411f00d110415400205020762011034401600111801d200c0d040040c0c0100390248002407003264100e2301042189404600a83c40d4020500000641450380c0c25144c03000e99002c08100b52a603840754487c800e400303590009603082d0302003615888410307041c5401c0c8840110000843d070392110110094500a4441da0b00b8181440314036544c844900c110b000d080c8900440502210240905000680d070f01409003a802c03810b20702072040c00d03008580a14140b2010599001c80e580b01e0307100d0b00f0340d41c0b401201601c400c503c1c21403ca00d044400918400b041001000c04c10800c15000100541141c0c42d92400c250303102c0c0990750403141d400a0841c074180a0000190000e45081150030600030b13034000301d9103440121480d0080508035040d084242540c55202640d104800c0d465501040e90051031401154030514460001021a8407103020610342 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 154166690 1250 154165440 154165447
    0x603110f03100603050a02070c05130908030f09010b0909100203060f0d03080703060b04080c10020109050304080609100516030510090f060e0a0209090c070501091703090d08130f0203120f 82
    0x710380c4c50f004154201010000444c0b0348010ba07111901103840313600902d400794503203100c800300250729a804104016040130380c1540301c0c00c0000003540310005c01d4038426102c0d0b00300f06500340c452409240c141c0c05401e055000301145554846040d02a400040405900c0100f03404080f059407540d0b050a02124440d958407407491801c02c201078112100d41c6c02130340b10200140070501c8502c40000700030b40340400846d1039480d007419200c0128003416050a00500500010030005428000040c5460054864500799040c054001181034200c41080b54443c85200c1c000040040242c01380c0d00083c1c000c0300d01c00e9807202d081d41b2180840140c0d40300c80c00300304000b90f40300c1c0100480030302c407035005800903d0b5800a41c90a000140040d21064029102c2802314000180000410509510403820141d01032403500e1514a100d00c51822604200c032210320781e0089588041c1503a100b45496071141c469100c10720036244d443d45404141d03584581c0205d8041c07240d002076140c60a0494060030030103100c00c4800381d070b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 154167940 1250 154166690 154166699
    0x30303050f0a0204051c0c0b07080c070803190c050a2f060a0e1c0f08090f010201060f0b13030507080102070210020f03030103020d060902132c06010603110f0310 71
    0x8032070041c1903a049500c188402d204c1d65892821050410b01001ca03144042201c42c01d10044140719075100f61051100040e202040002c008040c14860751b044041e01c02d00c82c0c0d42c1030f10039124032400380507442a010768400f501815009002c0918002d02803802c5a80a00580d178803c19200d4014134200c2045c0004040c3c0070091903e030030b0124410b1000c0d036916050648401c5c004d40301c00b06c046292031144500e1071100001d0503c69007092500b5400c405c8450300b000d01400d004800754071048161780104031402c41d101055005010342001c0752448403159408914064030004160004540e016920307002c841e000020883c1001079001802c0040d00040e9a4800f40c4100b091030b88015802c0021354011802101c90f079400803099138112601540c3e115032603980e92402034020480240c3c025441800111840804012584480201d082004051502c0d014076000d85001c00034090512850341d10031001800300c0b904c00d42006030300000404c51070342852001c0140d246c40c0c2d00211140c11600511200412 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 154169190 1250 154167940 154167961
    0x406020d0f11180a0312030c020a240507030e0a1e0212010c08010602160911070506040b070305090c0918071203050a120e030a030902030f0706030603120e030a110d080403030305 78
    0x1030041c3c0d800c440c051200c4d895561010601c04242c441c45040c1540c440c04c04200c10300a2002424903548049031400540007030039000c4140788022400080c40d4680300000391454005c0c402c2c15200b008000003010309104a5403004030a102031480d95000039002d500072001030b29070180c0b03001d040c3c002d5000030801c000e50000003090f040050b48041c045600502d1030500740d0500600c0740c4180c0d9000c40c0d0210b980c4000d2510500644602007004100d44121020041030100c0680350a003d0340c5603030b50034400c6442e04020143e482c011280c0700360b8880907000110300302845070381c10600b90007084070645190a640c0c00341a08030001702074094011503000140c1005d01540507141c0721243d1818130b802c014142013120141d5590090081400c00d1641d5128000e081d5601088107002800c14141207078010b580341d200040103040e01348411038844079940b001c826110b0254190088140703001d801008030005544a44414010101c036880c0c010200710300300d20210706550007e2020f0340c0a5180413529007413203265007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 154170440 1250 154169190 154169227
    0x204030b0a090b04030c020a050a0b0a0906053912190234030c06090602010e0a170304080403020402211e19020f040305160803030606030406020d0f11 66
    0x554905240d080018200f001425007290701450003145c6543d05102041581941d60440e40d07000d8aa1071000480610040c01000048050b0703898625490360303450300b03035401e0080c0d80d40744c20070107a10f060280b40e16040303001c001e0310030480036258850b00c44411846804e18007a013085403c0410001036440030440c0017651b140d104100c0380700a101c8241d8065490340c3e5814400020240712603101c90320507495103104509000780d40c010882c856055500d603406000c505007807003600d0141d42059044043c1c8000030800d80300c280e401038040b462801030000303c51320750781c40144101c0e2590828031010026031260700c0034150560401d504880441c494807840c2c41c40550003800f10440017560840240c0c0b0303e0a00c1a04d0b5081041318540e82111102d100311003000c7e0103040b01d20356240300301141c004103000e40040e948070304000c80403003980d00075100c02d5400c1e100d10048036031542103141040441c1c0001c6140d401000b210404103400201c04850380b42142c161350498902030001000801e10070302c40705104810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 154171690 1250 154170440 154170451
    0x51c0512040518040809030715090801021806090303040915030209010e040302150915040f0b07020d0504060c150f050105040b0a0e16260103030f0c050a021020010204030b 75
    0x1154241450000000c02c074003803d440d4034400700780d810041010400c441041d6000d6200007000c3e030301d03819150350241084c004100c101e900003613002e01000442e04010f02c2180c0240342e5401044000c42a4401440611b501006000b9010308c070402c4006010710300e82c411b2811150011013050822031035401007110b50001a08088240e18000040c44002900010b0864000e004500503a0a42d6210300c8590300300f038600c508400050b03650000300402c020140143c000c40d54403d60502d006071725900700403a515043d04400e40b020480400040c0000d5010b40c40011748103100344015822111060609000c1c3c0300000f5285850035140d20040c8201d1809029000c020401070b2113a0301e9881c40c181e24003c00c440c01902e0384485034140e0700740ca0040341c8659413004030181c1190703000c41d0702d0343c414141050101c000d100a50004100054035106684202030075510150410300074980d801c00354003003049450014070301c1c50500500680d106401c444288491900c8801d01000507180c030300c0c2d41000d11008000620 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 154172940 1250 154171690 154171723
    0x14010f050a02030306151903060810140103110a090f0504200307170c040204060c0501150506030a0f0e1c0908060408120c0c0a0602030403110a0201020d03020d0204051c05 75
    0x911000240d000040da85d0014007100c1200944004400050f0580710300c0ca13444510303144050721640b41680581117641210983d10840e00103042c040c020f03a040740e60824280c0710038035044004001161284410324403101c0018240321440b60b6840400044808914040880c50b8560342000180024404c0c0705016445803542031170b50316000d10000341c644903680600c0103c1100d54020083e012010421000f4125000e0421555980c4402c0d019000c07071800c0d202110a0341c01e01e42c000c000c141c2001d13001c00407610040c0160707085444a29207003015124800c0002201c1e0350780c1038843ca002204021018180c16806414182081e148100802c165002e401c01401948960b0a00c4001140b0808940b00000d008102005544070514140114441c0d6505102c1a205103100d6006101c0c044e8000c50103a4400c0c2c0702d82000030059008551101107980010f400f5070002044480124002c0d00103215001a40100501d07144e216800039404500080060560000303038508441040410440c0c00e4400308000c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 154174190 1250 154172940 154172947
    0x606060e0901032609090406023a020901020a1a0a1103090c1002070306060905160e130c0903020303030903030109060807180207030318260903060609040c0b0414010f05 74
    0x211845005410400c40482204c0c62200c1021040103403c1a03845081004000c00b000381002e09210740a5001103415120f6500c806500c0c0200d00f03444001064050340d4070661016103140700414030000c0d007054000e00c3c154010a06400d0000d4143e280002d20840041d2541c2024202019254102c401490701074002070713410018420510000600c1400c4d0040480700c2c0c0a001001318022403c0500541c40104282d0921030003098000541d000140b003180c408604a0701c0030124201118820100e052440d0010410f21211059140c40c0c3c001e43c0c4802c40508024146513680e40c0820329503401195076600030740010005001c5041300d4002d9400829130704000f041303043c1c00c1c004400c1c1c18407888040f2802842d40050b030b0004040c040d402491480ca460b036044010544907003440c60100461070f4945803605101c100d0b40d145405074800391150b004002d0020a803d139660303020b111038498050015581084071b1400040c4061640c402007015103040c2c4228011004800c001400c0c0000c5540d41e13400303208051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 154175440 1250 154174190 154174193
    0x8070306030c050607061b09060f09060c02010806030f030a020c0a14180a0b15090406081603060207050703120906030b0a051008150a06020c03101802060a020312040606060e090103 79
    0x359292000d0383c0c0c048030340550b00d860616160001b80610710503485003080d030031001880c1030b400003075000c1100c01940ba00c1e000850058801c0301c20759000c0c000c100201e81580f14841c00740d48030302a155404080070301210110784044ea0700f2407468001241e42001680600100045810540310510061014401d041c102252000000d007204001410a050700c0c412000001c810020540040c0c1c1c01440c090810841c0b407291485010300d682c07003410300300d00a50400c94000b540e43c40000d9203060108007581c1801a890441d0380d2200a540400025a490b01c2110004004130f200c2e42c040740d0b0141c03e01e40394105410b20b8044094103640355050030303500c032b513140a4040101e5101c81c0c8002040c9070062130180340e69602d070311144081d007001c003a5094100c0721240c2c0100b59290005580140b070300d4200c084400f00030081c004001038882c805000d466240003442c0c4400181407180107042d481040303005036810038020100b034951803203049600b41c0325581c80c0d4104200c82e6820014447d000b074803e0b95070361500d6056 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 154176690 1250 154175440 154175453
    0xa140306090601050d09020a1202091806130203030f160b010e192307030204080c0306040c03020105090120011d15040b0606040308031006020106120308070813120f0807030603 77
    0x802c510f042c440009494012035115500003000c6550040c41500d255454103100c25000b00745c3c450413400303503c0901c0440d414180c0070400d402e4400d080c5004000940d514100ca014000a4000482e0036110900100141362000c0c400381c00e01d01101410915001403c0c2003c10700d1800680c00112506e40290034400b1721a004907003003003a400801c001080c15961110b180f410b55800300002030308175040006008250342e050b001071080341c441100722000303020450101600d44406a4004026001c507000800c01940200050548800141084929110101040e03000034004095807030b8540d540f02840f0391a4207009400c004107214840041a0028100d03610200309030340604007500754202030380050010b6440d6005c40300a12340c841403080c1c882c10000065400c40c4614005c01c1d01550030800701080d031030b4010b240100120b0301550355400319121200d081e501100080c1003500c6000700f880d200340200f000e407040b00024440d0765440c3e50034007550341c2c03004029143c0a05180c0401d81408020008103e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 154177940 1250 154176690 154176709
    0x605040b0d180b090606010e030c090a0504050c090112051204030305120a110d020d0c020f0601060e010212070f02031005090714060d0608061e0106080c070c08120a140306 75
    0x280c90400140040030404582200e1038500c03000301a40207440c20003103130313000c041100d900a031b400703032100003040002004054440040e0407500e500410311000081c3d100c0040d0700010b0300113008400b510414090318000c2500048245c0100030300061040d0024208581000721919600390b0300d00081c103103411960002c00910401c084054100c01c000b0225407150065800414014090203d196030f032041e00d160003000e500145c0b07040d00720a142240c2c49031114000f240740303005c180700702002e02900d80c01d115068034100b0303428440340d0461207240b480807084098403005044071802034144803540411881007610304414010000841410003040c00221140041ca0380282d9070044c224405501e01c007000703d41d490240c119050000d6040c00b20006100b50042140ba001d02c1a400340401007500e18605040c0c0d20340300384921000121280b001400303c50301381000d0f20405206000343e46100d95510480c1c4d10f00034980710071113407038500000c5941c4065001035101c00c210f5285c111560440ca85400010200c03031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 154179190 1250 154177940 154177957
    0x80a1401021603031508010606030b0319050d0807020f030f120711100216020a0e100b03150f0d050106080303013206030c070c03080d0e01050f0c0d0204030b0f060301060605040b 78
    0x1502e4117203903072004c10400c844a0117808004002c010301e9644400040162840442e428041c1c0a10744000c0110380d60040324113282c1360080000c00142c0000903040b41e0b0600010100c00450103182c00b004020401030005042c822858410780351035175010000e2110907800644010709005540e45001e280110100340b034110300613240001625802c41c000505000080040002d40c01821003101060300094900081e0003494905040152507403a903584081a110946101244008101030075030b161818040313024220740301a201040c0c2103a40e5079a030307003980c0340e642003464a0f800200040c040304040201c004030f0381c0c0d214805036405074440c1400300b0061070710984040c05888000006030f90007188008076080075030320907410001d03295a030405c0d0141c0e130000300307581080d5420400e9071408a9414003555009140b4000404220307110502e42030013581c0103200d12105a40c0921001000c43d6908511030b00c00c0140940b449214034210041500f110740580001c3c00b481b8040c0800c0c003400010406843c2d10f031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 154180440 1250 154179190 154179197
    0xa050d0b0f0c090a080703140303130210050c0102030a0504140327120d02070602150f24030f07030b0601050f250605070f1e0c0f080403020307080a1401021603 70
    0x2d0322050b680340114400e581c800c50300410400c0002a541d5000591201101e000d1140320340b200603102d10301516840301b90765149070440e1003004440549042449070b05841c1b29401c0007850b002100b0f1007a1b00b682c10031035000d4205a981e070100003c0c85110415503514100718000b861030241c60003020181c22080913203000c00403412418014240e00e402010030320b0051140c084074402d2200c175134000d42d01c010780d000f411b005001e02c0c40402c5010038802c002c18090003624180602950700c9040140754845904144820148610700007400c5440038401c41d080d03040780c0405006442c4c150706144084c500c001c0e005904100302044048042030300d04051740d40c040c0a500c04801451071407610204070350004040074242c00d103881d050019040e00200703e079a074a00c060300c5800442c2c111400c00d40402041c804180b0106a92a0072203000a42d0495448000740c40307190040c4c01c1540b40e4020a191603000c4e00a100b09a011804140601c80c0083c002c082c6485140001d5240c0089003000c8212429503180c01002d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 154181690 1250 154180440 154180471
    0xb04051e0a08160221010e031c0e0a140309120f060106081306020d0b03061003020f0105091f0503010501020f07050a0e13060e0123100e040f0c03080304020a050d0b 72
    0x401c440f14007850304054008094149a0307620014808801e4292002412150702e8104419606c02c804000d60f02c2c4c00d0306140c4035000c01c844448086014240b501480a1240900a405000103d403412004e4031700703410500868460526005018580b50821283e1066510a1081a507054070014409054071407a14000525403202038071700e10344450b0390900900c2e0360300100e00c4407003490701740d44541d038802811000ca42040e00c0383d60b004e01c841c0141c0e0002075007120382000e6120040d401000100129000600385c0d03001c40d105103228560304081d4203680000280000b00400c80b0f5039040000341d140e50300410250008925000c0014400f10b82440796800400c08400022440c00d04020302804040c0c1010b410701c41d18020851150003803071000c868900c10129242d10203020000d4803c01845840740c1c86044001c00d091040d200c010007402081100c5220304540c020700040d0720881100001c62050a01580b0790406204004510401ea0486809150f00500c00408103072003684103504a0901002a140b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 154182940 1250 154181690 154181707
    0x905060d0e1504060f0b060a020a03050f0f071a010e1608040201030f0e07080d09030b06040203040602090a1202040b0d081603030204080a08031602011104090b0112090b04051e0a08 79
    0x51100c02c0e180e0407007205400303082100780301d15074100704807034008100100150084541000a04c2c0150100031005a01620b16000006d0048008080f0ba258403100181400d580e60807640c640d5201880494010804c0c414985800ca8042a4180034040c081c508030828a0b00e83c80400c0d0403141001c950b0208a2640c011800750b9019601001304100303001000d2021070321074124655680c0041c4101324440c440d0005c4421058811003030841a80d502600b0b1b160301da01e0f1502048081e40001d8410348400c3d900300f00c035001c641d541702c02c001c3c020815240110001c0d28140104800c995031014818018407091020310300150782c1e0001c0b525803003409800c00e40a800d460804030000d0240b90403048841c4150510742e17003800041400b5520442007411006a4103040b40022401d0714458104c00c03005080078003050181e42216040f001000303a042c034102d400380d03001c030103920b0541364503045c06e4400d0001c510a1005102e414400b0070b40c414441d180080004862101c450358541388084090121840401c4094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 154184190 1250 154182940 154182943
    0x1140d060504020304060903110c031015080d0f1d09130309030605090106140a141201022109100603032001020d020304050610140d0321110a0e010905060d0e 69
    0x30103031601074021503c926091510100074102d009065000c5007002c1d008850310030b80003c100c1c0c0d28560180192401c0210f003041c030000b0b0040c801d80d1070360024450301c01003400582002002c000c01c241c1c0c0c0c1d5100c002004094003400c1c02052418621819100240803511500c40000060700b00a041110082d01074550900719085491900008c1146080000348504213005420140695003502500b0562946807803c102940b009071041c0086032403401c103102118a04141c0c180b21503904000090b242c001030201c079026070040400d042c0900402d26040c8488210100002c000c0d41d4040d0b1002c00110f4215100903001100c0303030801020108960790f4200ca440000c0d016038004034443c49095403681440d141444d1a100203c1e071703d00030707000d80000c001104007100e49031880c80324000e0241c0741c400d0141e840c110f0751600e40080e03a002d000500c0f00e00c42c81000040c46542241c041040f603a41d04d81d440075034002c240201d41c0808504110124000f031215a403080d00f12035020344d0004e000030350024000303c5203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 154185440 1250 154184190 154184201
    0x110a02030d050a030c0305060a0902070213050403020a0c061d040b0118030807110910030602070804120b0603120405090a0e0705030a03080f0a0203010b070b04030e030307030c140c01140d 82
    0x250140500303818003180603006030150000d0b0480e80c50031300400d022110128107d480845d5015804052003104004044043d4010702c04d1a0000d48a07030b074000381114010007500c1080d43c08a006a010724011414803000b4000140034124074a041c06080f0182e42000c29116000410315104641d141c03a0000e190780108151800080d010171109225641c03801d0402d2690800c41050f191002c1c068224826403034504070300780c0314850100c1100c00c20307411500e41c10000d4100860071500ba08007007001084844200c0f58091400c0d03c18581160706103840c50134542888000403610201240c1400306011a5860b510b00340d500c203203004030000d02c000d0b0801e0300500e04800d560090f0b403d80500070a003400e050344000b6040c0718042c03030000007090f034585507003110491200b40306415010009014000000d01c081000c02d40050103464081c0150051500003401e540c801002240407528082020080118200c200c502c0d00b40e0600181c02118400400600610200c440c0c4402d8680e0004814a5051255110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 154186690 1250 154185440 154185443
    0x60909061609170102090306090f0d080c070206030a050a0b01021b010819060b0a02010b06070c030f051f09350c01022209050604060f090c05091005070309080d020a03110a 75
    0x2c1140a80c0f1020449000358012003400b0701900500300040d0703030003400103089a21140c142c401040100c02000381140c8256001d000424088400c000080140e910031006c0c41c0511104000021f8505021003140304482d2035401050540d0403202109840704e5000100ca86070003001e00b0032000c20340d50004908001000264102203241c9030603001318504020401909544109400030060350035464100f100314001d240005010882d401d1082c8000780190204080c0c80b40b2401c220707804802950550ba070380c24003020a02c00155984c20403d0140040e062600034542c0d60307810090315082c000e44468006896032088105c6032140000e09500c181000d5040b41c4c0c00d030940d0030200c07400c00c0d000b880044800102e8441e03501e4007810980801c090f0310f028032480c1c003118160794020410a05d486a10006410034088000900509000707004464950103003681c0380800070f903641562140c2900c2e01515041217600b01c005590300454040c884540c000581031809a0141010b030042683c44003c41e01d450042d910 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 154187940 1250 154186690 154186709
    0x711030105010e0403080a020c061b13081609060302030c0d030207090905030307031103240409050303010e1f0b093d0f0c05030d0504050307140303040209060909061609 74
    0x1469041070800900031417080d0b4a9a51a46400d940070f0f0603030007082a8440190400c0d00494402160352000800c0c3d0344001c45224241b0460820b80480e150305070341304009075001000d04c0000c50b0140d140030f03406000300d2001003101e42c1c02d680100c0d0392021513450450040030189404403d0500800506006280a801c244400c06540c509661203400a844403000f0a0809100c080084048416070b4840c0000740443c0c0000d0440c4910022030140b900840c2da0016a640132820100d00103000031406050245003035101d9081529003044503441c00241d80c5d1403030704800300500c942610001107035180c201c129080c9030804105254031003110000d6030724070041102061581388400c01c48948000c0b0301001d803501d02c0403111a880c280c80c0340075507080040054108000d607901608060340003d4000f13008204403420b1922942d6903008032102001a46501d51000c02003000310320740903020307984c8018280c44200729400c040054036a1540b000c1d01505806405009191109205440030002401d00d400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 154189190 1250 154187940 154187951
    0x1e18020928060501020c0117041101091e080c03070605180a050a03030206060307060306140112150f23011403071e0c0501050c030601080c1b070303050a03050a05060604050607110301 80
    0x5540001c1c180d030312400b13025001d8610b8440d50b07913000c2e0203200890303070340c0301060a034540c0d5941d2401c4a250746860381c5414001842404682c00309490440320101100241c43c4a0650030440c6e080d2074840321401543c440d0348007400602c03009900c03030255407040702c441114401105481000035505602a0030058125420041c00801e01d0b5002644502951041d01036070a0152600002c40036190240641428081d0f00001c60015511402c008080304030f1070800000d503410403208000710030326582d00c200f00e0f0040c210818000240e0001c0510202980d2550800c00081b40400117065041444c51400070b0383e40210000c2c5009000d01050406d0046a0301090050351544c5000b4000150401c1d09a92941c80d04001139900700d90701c401c81e8041c003016100c0c807440e683c40145000341d076401043c0311800c0122641604da18090200904809540702e921690b4580006400080440d03400a144208540c105070074411951203120498042d20340542c1c100e43c1d04d522b541003042031035240c0c1c403200d6019031030107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 154190440 1250 154189190 154189261
    0xf160f080f12100b0910020102070b0403020a03080f010602120a0519030f0f020f07060513080a170619060e150705010504032006150112020309011e180209 68
    0x7203004021034186400300001c50307200c80d00140264a141e01030200d44900800c10300703003280340c42c12041c0d581400900c00589441c0342aa00c40300810000c4d40c0480169100030000820542c00100a80d44490381001942c00c0398502080256250300d01d0648030486040011a140d84a204004030340448200a5a41d494004184001002090101c08504200d8604005407104948500850703100c88a40d00880703081c0041622445d0062030041e04d503030f00740d403142000d040028142c1c0c4064011101561507088a00c806045200d83c43c0d00020314503482618008048a102b10f5068500410744070285009000400140701040646002c2c0000c3c1b920004003042450402405401281c8034503c2035484070755407040012400701c02802040c111115400c210002500c0501c00600f0103a178200500d880030201c4244500c00c42203a00a80310030999944030201c0705800241104803002403502c10208000403404d048061801c0e00c10004020b1041c02c01c034001c2001108003420692031101040e110080c442c550 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 154191690 1250 154190440 154190467
    0x706150609090b0a0e090a050604050d08070e0105030a11040801020403060e070905010302090c180405150103110c0307140a02120d1202040f051c0c06090f09020f160f08 74
    0x124400c03040040e42405022420b440603000e4059a060081c0034a0a07260a11040020848004281c1d80c0c06100b240c5540e80460000c105c064084c602640260031480000c5d10020000b2200900800922000200c9983c041c0d034044201d070350088130490000380c7d8031252120654144941c0e0300018071b560000c14040240241944550140041642107540307880e6038003d2181526824800a503005d4540e400003405913481400810740c00740000180c02420840000141c225039081e00c60f400210141c40100301c403035030948141c841441307190385050f04000791240c446039280b04400c8020004a031440e40c0c0300702e902080050030b1003d58010a13000c4520002011240d440e910b41203e00c0002d5206460f04900000c0381c402c9800b40c1e50341860020506017003200f40714954528840380d4140f10015091800807408007040324001c0d10f01507694030300c41c40c60132020381d5441090380c01070920648100148014015007500f00c80083c200082c02103120459420a0076607a0803065000d4100840000c06000c6c3c5d424 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 154192940 1250 154191690 154191731
    0x3090b070e0406080606090c07150603080c0c01020109120302092707170402060d110d0906050106020f1b120708010203090312091b0f040e1005010504051305070315020706 75
    0x9041c0d070300300f00082d03541d800995140010384030203800034010380101c1c03a01b0900f00010080d10f40901ca12024410017080300c0c00840761a89d201f80c41c03120307011400004480c01400b800310030071002d100078415654507455130170900c2d45440702d0005050b4002207914003516921201090306000003515011a001c543d44108034103005c0702d0f9600000c1c000848104000366035464180211740151129041c031445040705802024891172030360008400303014010408455004805032540b0030310707000c142545403c0c4081c1c944000074580c61001e801950002c583c4445903010004d0703854040702c500e24000d05828809003003a00e95004109654000010070050722000801400c154685030300904841e50b820b0049030300c911031810428440040580d0282e90361a00d051900310380000107100240e8064203541c10b0385800d068101108070350f0345480c0100642c1c9468460283d202c420804440b40d100f1081d5111a190301841c000140358405c8083c09001040c0a903060324503883d071015040101e210003a4808082c900d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 154194190 1250 154192940 154192967
    0x10801090b0708040b04030804031116030b090a080d1107080c070501080606040803120901020c0a060e070608270312280e0c120c0d0f0b011217070303090b07 69
    0xa400d0390110382c0c003520454600340702da40c104800d20031903207650360200c0d602c040c042c205808220004610051b400014000e40c0011410210180409481c600d402e03120188020040d402c03a030071581d12035011428510442d8441c2415000008484e1070407041d803082c50140c0030001d0403901003c00c59006141c00010500c050310000d880e582056512802041241c0c0300324011a02035030814032545603051010425103400400e030394009401c1018480800b03281082e001c02c2074980070385802c461003a01c0d00130701c603850180659280030000d03440c02880082c54000c8102c00300c5424034a0a2000341d0007a002d02c260381e4510050094031041d03060070000150381842603c0381c101c01d500003034601d14001da45441113031840e01285c409004626040410421618491711141c1c0b045c1c040c082000e0019654103c8016401d4800d80c890050041c00d03040854420740140c01003221002ea03120780b0f8001c50a00000400407484403050165100c6a902e41100070305000080103111500c41c2040c80710082d0403103014000306 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 154195440 1250 154194190 154194203
    0x30312050a05010303170402010905030d020d080a0c0c030c0609060609290a120311060903041a070b0105040515030708072c060f060f16020f030c010e2701080109 71
    0x3034407003040d018100c42c828803008012540c109802810040740305401c0f54054014105506d1003942d41011a0514408001180c0103030402c142102501e90441407032074010550040030451a00c0d00c0300041e00c00e26455001901b40700154003500c2c1040b0f80d51300042000c0d80d116106200c03030b0341e8036540c0b2000f401060040e21031201d58044421941100980e20040020340113040d55001032038650750880031155400180c04000003800c0b05110010104880c03030007107110701d000310703a15442c00e540d0082c03000ba884a401c0021400300107420118882d414450b055610480b4001183d448a200e5584203140f80c5118903014001c3c91000902a030011901e0821100b20783c019040399000640c01d440d020740c6080c03150054943e03202c0401d010b401c006800700420003015000c0c924112240c0c0c4030303c003d131300b1403000240d44000e10100390045041001d114030b10f01071306800602d0720354480300010300084680c20410b8001d54020001c1c034803019082c200f859843c00c52480ca10031a5848a011038043c0400b40800d40c0d03076 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 154196690 1250 154195440 154195451
    0x80f0d080105090f0105060a0302120c0309060c03070903061509180209060d170901022404020319050d18090608071a09100f023415120e010e010501030312 68
    0xa50074070701c1c0308074030808600301d480391305a08240401580b600450b060300d0806909100c074095013012000d04a0207900307082480d070b1b168648114080e01d408002460280901c10a0007404800b50b000030340300301030700d900a401080354845130682d500c0200c4a070744000b150303a0074500b208140d6800e00c88010780190099520721820b503662018800d101040800007800c041c0c0381da5000410126072000340c066654140b040e07031814950000c4982c00010241d40e0880d103056050103205c1145010410560b54420005404c640d4000725101e5a8075802c0114410080c480c142e0040342452410107c1d0b84042c000b0700070100315080d12a020130b5518401c6016404052200c00c4020910035040030a841d10a0390041603c0c54034074440320100c0354903100f540c800c01944110140308c2c0a50201c01d000105040e00411401b610301c5600e9240701581c07810784d01030024003059440c0000020391180140054100020700441c41c0b039088205030b801045203580707a98403075107000004401c050b84005809008413a46500b07001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 154197940 1250 154196690 154196699
    0x409020d0b040b0a140307090219021005060d0605100b21010506040e0105010518040c0c030e0f100509012a020102070e0c030103030318050a1b06020106050a0915080f0d0801 76
    0x45648a102040e4030413500c500c1044184058401c0420061001d002c0d98101665183e07400140c0e0881d1103a00c0c1e61988009050302201d504011106082c3c80d04501480542007010110303008110300300700070381000d23240d0b00010845440301003440020000c502e850340e6555a219a007a611203c80011700100055040000425152100c240c406582042c2140c421a9107058019a032940c40080c09152011a2007449012991140309030404000c094407414030300a120320b0000c0510b00c0680115210b80051342038010592070380e5851046070651810a00d903594880700041c2c03615000101c503106001c000345442c540d04031001840c02c1c000c2d07100707808039a44c01c0d44906e05202a2071007201c0d0040c05500071300042011070310903000410f10050f0400300b0040030100b80c480b41d050000c01d40303007501c1c0c1c1d1075160b4000d816091907600010041c009440200010750038a400100340b407200b88109200701d602c0300c4601d0342600c030b4007010000a0000c142140e500c0030080c1a02d586996811a907040824580000001e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 154199190 1250 154197940 154197949
    0x708120703090b0903130e10170708010609020d0b06030f06011b0501091b0f1a0307140d090308060f06040e0c0c0d0c0606090e031b011104030309050a05010201061d1b0409020d0b 78
    0x18020410b510302d1030001ca0070301080035001000d8423140202841044ad001a000401b0302c206800741150310400740e07030350380501c4440056601c2102e20300d0203401d0410820000742929030a5580004091800c0e20240c0d180d0300380c940007094962400b0f0040c0d407a1145400401000d84031300342ca00707207821032002c4000790740c1c02c4040031030301261003000300034405c8201d04101c52707000340010365115149080c441d0210f400601c51103401e410170b09004007216500c0000b0400c0c1500040440d502034411241d200b4100042c40c0030501601403072180c50301010803000490740401100056441c070107042c0040b5a0341400d0110014040001c0702000e5071140c3c90700300040382204c0c85001d00116800403070004c40c5801d2403070200700340c041e14584100a103550b0f01d408141842a00c207001b00b00460182d900c950b440d600300800c0240c0c3e040342c0e9018038150b80c0751a41c00c20010001541c80805040b04500080041e95603104c11828010030040c0190440d50000700800d054480e54040c1c81940281d40003004002c82480030f20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 154200440 1250 154199190 154199219
    0xb03030702100806060d0603030203030601020705120703030c1a04050304090b06131203111b0114160308130203010f09060e0a020105030c0c1501060e0102060c0708120703090b090313 80
    0x7a4001c40018025240640610700858028402a180a180c01900c10364041180d0464008800607000001484580d6030f04014040151070101c542c5010f4503194800544d4034821440018280486451564144860819840c811040080f50f5441e286005d00e850740d00c9a0241c00382d04111481c203600c000c00c500f80002503401085094078079203503c6042c4141c10b140d00c5c1c0029011000c11450010031141058280440e1295254032109095001c08140000d000e40301021450103d1711002d1025902582d400903079500d405e6007606043c4107035182c0c046081107803c24804044e406609066001031081302541c4090000d40c003e890802801d590101c42c5610391480c0440a4001201400802c85030080b07070005181c240050007c541c546c1800e080c8014008909030f00c1100800c65490480741039580522625174441114610240380220396900d00c02603009920001004003d03003000524028000d901904505030440d03012040d61900044841d50383e030119402850065141900113a01c020410b1035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 154201690 1250 154200440 154200443
    0x712021501050319140f06014112010e0304170d0804150e060c030f010e0f0c0706090501180c050a12062a031a0603160c03030f0f0605040b030307 64
    0x44c0c402c1c41c180480601e0407181c03205058404014191941d001a0020031500d00a40045030180c50030b90700d8403444c0540b444541c10f4000e8820030707800c03050b880c00503840300039810f0380d01e409038003810b5191000101d6000ca494081680e20380d03107404001c04807000000702600840d6540c0380c80e103002007840403841c1e4981c84540c1012012401c104e020500181d210790a03a040120900400a018204160034a103000c40c20f4602d1030b1003800010510140e80340001c2441e000d051041184e14042c00e04925140b52000c4c028000c001c10400815014200080b030307041105000e400c80000e112000c1000d80105404800e141c1c1141d0b114110b6400191b1414401046411203c00524481201c4034580720107025114031072600c0d80d01c10180200b42010380c144441c0da40d030500340340d5001819444600100086450b451903080c8510024030400c0a4000142109070810703169151810b50001d19242c1540034007485804141c2242c1020341000704511603030701c24001c41d2004c03501030004c15406804d05442c3d1040302d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 154202940 1250 154201690 154201693
    0x5060f1206011706040f231504050727030b0a0f06060e031209030307080c1005070309080f0c0114090d0e040204060903121e031a090105131d0307120215010503 70
    0x340790349410f500180103030104146c0455403d10520b0003480860640e10180302a080345400c0c000c3e1100c031801040710400050380d08000500300720300301802a589852070786410428440b01c11200c00d001001d03160065500610000040c24642c00303510282400c00210b1809520313040c800200c06100d0131040304444c10150280c61000945a0028400d03400320314002d41503c000c0200d10000f82d4210020110844a0303009000d400016080503029114007514050825041410321f1000c00d00e5a0100d486424100c10002d0b0354007410b8000c0d5025141c0180480c0044a442c0104400c0c0d960105502c20240c1c05a9684007400c90340c0d10400080340284e008040026500800500004040c84240c011010b483d0501102c0402d00c501c0c620622100c2c1c80900000a80340c16010380c107401c50366600500583c003100c408100350706150100302f422000c01c115488194468018081c0f000d07a4640440712200100d0580b55182c000d0f04003440c035556051070200c018442c40710098021350800b0712082c1038540050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 154204190 1250 154202940 154202987
    0xa12080405101b050f0f0708041a03091903030b10020708070e01210305120a1a030a020907081f031202120421080418050103050d03021218030405060f120601 69
    0x51089400c1c5d007000c051802444410854004508803250103090700500c140034140c0c1d10380c2081c46d08130403505031150140c0060001d00038846004404104c41011040416801e641c504490070f00320041c282d9041116004103540200c07039200c55001c50f450003601c808004407502c40b5640d05129a50200910924681c0702d00a45d400300c04019008403004545c0c0240303003250800310480780d4840310940a41744498007503a0350181c5604009407400050840c0012405400c281030140c01140305944c00805020400c100d8000090224942d160100310011410100f00f4055460f860300410480b00c0e6003280d805441104e10990400003200122025150380b03448620300258103285194000d07000481c120b0f035103181440040755103001521700944240078500081030552450074050b003424a0403007598109801008110f29050b8544545d80d040790307190b00409081000b16200314110300650b00400d03808000001e1104003111034401500030f13800384180c510100d031141001510700d80c22541115645410b42c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 154205440 1250 154204190 154204241
    0x10c0c020315070302130b0405010215060906010305220b0f130807030c06020f0f0a08060f21011b0503010e0601020a120305070903020a06030e070504060b040b0307020a1208040510 79
    0x1514035070050068100076052120f5411801038817001b82d084074020700c00c08141080250b90401000414004000b40c2a0b42c03420040040340c1070400050401e41410385800106103141c0d00b070b00d00508900c1d18048a040c1188042c1b4240301c585d1401d4503c0082c1d0342c501c5000c508504881902d801055a00202861801101d41e4040d034584400400617a1415070901c009a00c0104010003451000b032a461041da40320350050000c0c00e1101d024210a01508042e40005d44540303401400ca031400400c800e0640300b2141c00c5091380c2c050040316070342c2068420318841c804029904000954141d1b40d030341c000082d80b44d58502c0120380da41510000508110b1100d010311038014001d42c020340d042502c52601c40c1c510358076500800c007621072a40c000301c0000da0310504d18040290034006a0090801114280166440d080b0003100c0c6010b103005600050800202207414a03000704005d04866034072030415064400024400b80c160641100d080d281070060300228425030700170784951100121503408240890412 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 154206690 1250 154205440 154205473
    0x6120c17040f0c1205061b030c13030c170712020904030503060d0b0c030109150f1a12090102030f090109051b030c0909011a010203040e0408031b07060e010c0c0203 72
    0x3070001e58502d022000c0340d00c0401d000000781800f8100c1c01c1d50140c000b91440c6005845d200c801004c014003903010103080048240c03194100e982101620081d00d8a0308184403070045058030baa8802040000c040e100000c0c1b2a059442080d0000c0074002070b6000c281c2d94407d587c0f07405c083c0311402940014040f0000e00020b01480156421002c040e2403141c00c2900340d13503206840711060319240ca4120000c401041503c1d018091580110040c5004007070540c9001c45244035040240134134800c0308540d02100300d2303048800040c2e074280b80c0708035401d2103e418901841c0d4000e41c000e40d8054a400306040028a030038405000782119954031200800503203000c194070107030601c400715205034540106050103503d65550f11407075001d013402c1c80000038042c0001904095020a0815050540d042031004000750700c40a4110b90344243c11801c6e080e03680d503132285c1030a00000340c80c103540b801e1800400c0600074440b040c0d01001ea0541504000c012840c00c3da03005450121521000035415800b11900304001c10b030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 154207940 1250 154206690 154206737
    0x15030706231b0a11030618030306090c1201090204030303053105010605031b090106020607090311010c02040603120206061e060c0325050c010503070801060f120e0706120c 75
    0x1107401040305040b440842071414151850390544191034003603d4404145428080c05400c01c14221401d0042c10b424030000b0b80700c2c00001d00c5940706041d45d00015128801d20804c03100c019003400c00090307896840c1c80c1c40030300035081404280d0009260600241d40d0750368080c1d040081c1a0340e411145990302015810380200d09002008482c0b654a60000203695202005200d40d2201c0c0d04a01e0302030010064180000c0040590004003194080d20034040c245d0f03084a04182565008413071660444040c40c0142e42d01182c03880001d40051400400006016050a111142400381d80c00e64100e034440c101000b02d900b0005604407000c00b03007400481520f02d4070800801e21080641e00b96402e20300d17598203060208114031009040001d00303001c0e072401c01c00d040c080d51800920909040b411414014001003180740140228002e0000300c1c080c0405c0745015070181d1240d42e030300f01740a02050303403003208180d112020791191030040744480031081c03400005d42c001c00207807104a58604e030141071150310040100380d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 154209190 1250 154207940 154207957
    0x9070e1003120c0501020d0207060f14060d0302160b040303020d080601120b0a030c030b01170307051b0607061e0606030209030607031808030c031803070507060f02151503070623 78
    0x4180f54580d00010340a00103440c0b1003041c100016100c060340e040a0040e01d00503007990104501d003070080515980106500394201c00180c8400307054101918050380340c01d014800d4a03d010b11440c0b030000e200300280c001042624400d83c29076100900303001050701d2800c01030b501540854582c1150404081c180d80c090b01c24040c00802190400e5600d07143c141860009800540707111280ca8010302043c01100c1ca01c4038640e19050055150031890303202e142c1c66816105100030300000e01002016a40e07680011b5640082d0080002c02c6803110780c0c9400300b0a00100340fa80302070306040110000e0031501a01c02d60300c0841020700a059581c0e201380c3c0440041c140020640c402602c18085440440d50000165100c0d00400075625905e0501b45407484541c0070320080c0c1d8900e0f600402c09000040d4012440c1400c580700d9003000099450004e46c00d170b0074042590707036515042c2c2c1c0c2c00e4108020140440414100e040c0203605561440d80c03140c000300c48100406900c208800e0f2b000040810600c1840005c00c10320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 154210440 1250 154209190 154209197
    0x90e100510050409060b07020301360204060e0a0c080711070b0d1b05040503070e06030c120f10091205040320060d0903020102030a0509070609050607260309070e100312 74
    0x19413542004003c55035a504008090341c00401e00f842181000d2082070058070100c0a039085000140354907603040c410400781003881c400c050095200319190390300040081e040d00c00c1030168a00e0080c406200610f0b401e03a00310005083c0c64003003038041e8020f1510200e0b0101920140072075500f00302d000d441c180d00215294145555580c01c80c201d042c2c2210190700210b500b40d840d00c0d6124504001c040c40e00302d403500254070000110060003690381c4c00003000000f080c4d064840c54814800c0e1842c440c2004c010380f070110f9031401100b03d01540b00425900480003640305d000c41e0305c840c180d0b0300002c075102c1c0260302009040d41145c03042c00815030748800820500c11802400c1c9403400c1800d1341031174107980141c201140580e40100510502507014003901d9030195860005240319407615000074000c0d03000c0d00c6034a02505002036040240500048580d00d503240303ca42c8090100003200901e1034a41c02203400c44074a0041c04d101003900d1148403901070190b90300919403c0060f05644a60700b05031403025000090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 154211690 1250 154210440 154210447
    0x30307060b1504120303050c0906040e07031d01090201030609090209070c0f12030c0f031b05070c0506040305030901081602060403110f010e060604060b090d0605101d0601090e10051005 81
    0x300d50381005001138074090018048070041071038068141d4402400172080548240107005c05605c0700410707141211400000707070055407607000013a001002203a0300017110710f4440150b1041c0c0304054212860040c400ea9041218998030390602e000c580e17054000030743c880d04003004100d856105900008070140603e03900342482c580ca540d10002103d4000c9a080800d8071120300c003050b141c2052070322005c000076043c02c1c4115121b009011103d00410a10720044c4100421082c00340320f45ea41c02d04000d41070250030243e0f5207460f81466542d130b41004084600007031040b0005800d048000900f42c1035091300703400502d1103850382e075020b60f0b010f4100510160786200b50404501c45450900030001400004006000142400b1090100707441c4990084240403404000c0850151144d0201c5102d01742c20a000041030b131902001f0501e1400305920002140080d42c202e000355080c100b10043c042d200c01d0301e91100065a5000c540356005c000c41300c16022501040007000a401c012440e07441c20840d51410918 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 154212940 1250 154211690 154211719
    0xc0909101706060109050102030c0703061107060906060503070501170703050a0b090f04020a0801060303080c210c0d0f180303090c0801110c0f030f040330050d0f050105030307060b 79
    0x4a8240030102190507a02c03110912805580042c4048040d103001e00c080c5107404501e0303c0003944c075119403000502031560f8110f84d041c1004100c042c0e0f008680e03c00800d00c00c4140601f0203070b010300400d000315442401703880c1e070010b030700d40c02450358140401c4529a50309240c0e803015015801044020a1251480d0710307207190409a0f0b0720300c040f151040c0e4803103200c42c160703040c180140703c0070140a411071041a1f24028042c00441e0300208030640c032000c0340b08040c6d5200d1f45101100112188074030080c89034141c0f0000d008612810314003500034541c115400b0003101c036100c1216801e44c0d5409a00d404802e03c120f0040c00428800e40200144a0003901c2c2e0b000e44607510302102c0d084480b41301c0c00b80c21616010442095030360040c040b0312080a20f0800131400e01010220313840c5a4403851200922a00c0540d64945546c0c0143d0600207050388520041d00c40320207010300141c099070060320301419a07454483c000890306142d00c5039506881c0f010740110300705a05541c0b41001040503506440d803242c52030b144c085 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 154214190 1250 154212940 154212959
    0x1a0a060506071202070902160b06060405090f19020702010f0302090f121516020d110109050d0302030115020d0f050702150a2f0a03080703140a0b180c090910 69
    0x340d07582c86103c1c050140320700c40034020b05114942e0010304000740100710142510401c0c2c000c0c1000250045584030703441d25113800007400342c411a440f5030f40042001080041072100031980c87e00c5032241802e088094031304440c0b008100c3c810070000902050351203e00480d181e00c2a40500b03440900030f890103050380b4030b420020f401d00764200c0800a25510650041c20460401481e241d00180800e0440420003004d5034042e4440200d0f01403d810042644040380a000c0c0075003003148080e030040282c07107000d84581c030002d010354003d01500002181c08081d002d6601d100280500101d542035482038142e40510004030307219800304400380c1c0d000a041c00e90f1142e212039803008024504042d00c600700d400030b5140150f03101d9140700d00088c040d000f41d01807100e02808045919000141d06180c80152507a999406800404040710000000100f403810480241e00590003452040c2044500c20068802c0a10f800c150340c004603229103007088240540301c030909082000c01c1d0050b50800c01c0c420202d48441a42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 154215440 1250 154214190 154214197
    0xc030f0e010b0102070509060d060c050706060306060509010512060c03180f16050d150b01050705060f0708010f0501090323060a09020406060c111e0315100801091a0a060506 76
    0x40d2020796689542840940c1c040024000810007512130440c070785404000170740100903503040074106c9601c0300495910984128102c4a0b000c0d03100c4020031056441e42020b47c0240300d54011907008203520400401c0300c1ca841c00c5441c04c5800d81c48010034069a0318150704582c1e03000a80448003000090a0340300b540003050051342c840480003401000030300c42c62618000c8204413580030500030842d4040c4907022440340e0f901c01d609003003914400300e0350410354801202c8900c42c01401904038020841070107a00382103820310314090152a5103401c2c0f00e07601d540a0321000d90a9100e0580402c00c042000c10004a6000f50240007607011100e4aa01c201c0341c8403d281440f034215000b241c000c0d5520624000c503e468490b4002800407403404906082c17540d40c4002c0c806550451451203404c000641403102540a01c120790b0412003c2d0940c1d1500324200742080c4503034025107050b030441001c041c010506040511803008482c0d0014103030307691000348108526000c039010b80b5101e000c646034540440e0a40319400207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 154216690 1250 154215440 154215461
    0x80c0913023102130b070309030803060a030f21050903191a0708040515010b090d060f020f0d0e15040305070c0b1908100b0405120109060509010504050f1501090c030f 73
    0x141ea1102d80b200f0b140c21205242d080300c05102d106001500c046a4454402c00a80380e000cad0200e6a261204000150071000b981d00007440c0c40511b031940710800c082e000d05030080b40b40964844400414070030080e595030290440080d0913901031290104102c40b01c0106402060042e0340d0362000b070030b43d10350300390007464101d0314070000c20a10740520003000b100304042d000c41d010003010301909505003420f8500501c00d0324200d51090300d200714810213100b082e6000c00300090240d0707000c41d035a001048186240b6080ba54010340b0b000c0c41d04181d42c1500502042c0160500c0d6019419511503849540c103842d150407044050303030f10702020070010600a450100401d0301c80c0001c40003003250703158114020080f1800801c6034461840340c0d9410071181d08070340103803030907510700701c42e502408814558250f00400641030040d00b211b05103404d00c41c0050040d07020754080c3c2c1c01381c0c0a0360391060030718450b203503640220b442e1120401508801000340203250b91000140c07040a1030040b0b00e448122462070246d6417043c0380d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 154217940 1250 154216690 154216789
    0x170a14030702070513050106140d020d0f0614180103080a020a06050c030a0507020c0d080d0207080d060f0602210a0908030d050702160b040306020d1d0304080c091302 73
    0x41402585800304c2c008845c603a2440b003c1c040c43d810140000c12898440810900f0b244012481e98a442800d070180c910680c100784080140b04120151880a40880c3c414012861044c0d40c42400030b0901a00c51890400c2c2c074002c100740e0b64a15038904c1c0701d90307000c12803a00c11401440c100400140341c0c0d0040601034012a054142c407410406488400c80320041c0c801e409544c4400000d45160315242d00f42c84003c3d400644158643c0c2e400c140c1c0c80080d11802c4802408030000040f80440801a40d00841c1a035220341c0e401c1e0002030725524180d85c0d41040c0c0c0c0f8070140c07078180c2c8404918407640410041684040c240780940500340e540b501070345141c201703941c444940d0751a4001c02203256810845058007446100821000c640f07008010651441517001c0505400e1b000290480d104002d030300104584031884c040c8000803405005002d444e42c0140c01051114000c00421a055103031900101c2c0c0146c60340899604c0e1450300c0d500300110074030a0b00d10410b00c01108001c03c1c580c0746012030390b9030b40410940c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 154219190 1250 154217940 154217953
    0xd0506070201050912180d080d0c030e1203010b03010905040203100603050312090601050a0611010204080a200d0803060d02010905100504090608062509050d080d1404170a14030702 79
    0x2201034106000e4410721710480380188a00d5400740d88681c03400c409040151448032a1410a041c0111248154030b0a54000c40c101102900e00f268554050340102d10b40070160f42c0e8207050021f00c007015100170320400382410014001442074400e203034007494010b48010121000314514902090646146900c140c030a0b410100352141d0385140307a030768183d00100b031340b020349290760510300000c0c001078240c00380200b00580d60710000310f400c4096040350003800071141103410a03903d030318101c0719000d1050000340d52010300c140c1030860b80c2040c82d81d0358201c3c0c0c2c1c000d281da425651200c1c01c0c0010300c1070b80c1c48240d042220003000040c80e6124401c0302000905603a69469071641001d0b42c09060b03400c580c0c0044001e80c0008100821100342c3c12010507681000c811060021004070300403200c2d554984c1042c3c0d40b002041c0414801c1040300002000c0062402c5400d01400c0900c3c030170b0300081c17101220007801c050f11080b501d40c6c030050a20000d00e10911a400e10b1103481c7c4010103074004a810807503003900541d0010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 154220440 1250 154219190 154219201
    0x10050919030b0f060901090c110604050705010909050708040f1b0b1b03030c0f0918010602030a091403120d090606080c030105160509041517060709050d02011d0d050607020105 77
    0x16600c6544800311880b040018203050700420b840c10014070996151a42c0c0da07011418070b84c401e05020b227400d410341c0116600d03400c20f82001920352006120340e60105030100c0700060000c0944c007400d4421001c40e1a4560b4940e42c0f40c071070400110241c5004c03661020003c0504030500d40c8441000081c1c510b0501d45601c0b4060401c4009500748100c0070194958024010003c1d45048901110070080c1e50050090704c440002d008100c80405682014880ca400000082000c80d4000040e00b504403072aaa01c0c0030740c5655203034540d50321440c000b4440c0c260b00861496031a024110380140203001301482c00040150054941200f102c0ca15040f00080b900008030b110b002e45424006c9070b030002121007001da000d544048001d407040c40b0b808040760080d501c4908581803400241d0314080100321920202c038454204010080e118001102e071440447e0002c400401d11b0f042980c1600b03042a410b844d19140c000702c121441d4030b0000d0020040b0390002c81c03100b032800001e00c00d00c0001c0c0510060340007c10203003040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 154221690 1250 154220440 154220453
    0xc0e010315081b0402160807290402210106030302070302040605040606080f070215041103011406030304061b0f030503160507020901030b0901110a02070e09010c020c1005091903 78
    0x6244400c4150780c0c081814080e81d0000703d0300c00d038507052400d1052808045000441c0107401884c0c80f080030504a00781480512000000400c800c0f80f142c0d287e903041007040710001c9a681c800d200901d00f40b1482d04001001400c20905c0300d0300784000c1a2401c095186610301e81030968030309400482c01a081401d040003142458000e6101134107085806000d41c0c0e00381200201a110000c002e403005224120105a0183c006c2c41500d204c032001000c581038070314280c2011071465810340c2c030341d6020350701c7c220b90503403248140106a8003a00c0010b01841c581850f0810860303216034445002d03403900e010280c00e0000034100c0c103443c102e514030a0b1a600d49914200d214a01d041c008481d6030001d0000403c0714800603900d01113258152a07004503000265141c0c020301d0b50043ca600b0419201078800040c9640b0420340024800c01210250110b164060b80d401e41c1e29402e1b281c0c030000481c0941d0028200b2820752400c0c48000444001c02d140050a01494800250000700e14580f40402210741c207205205100b031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 154222940 1250 154221690 154221701
    0x10f05100303031409061605090303030a02040e070809032a030d1b030213050904050a0204110c010b15120615030406060501030605030d0923030a08090405061002070303210c0e0103 79
    0x40380c404c204003074509034660755140c503001805840c0b14800c10707000b403070389a0081d02950f00c0ba04014040b02d03140d1500c081840000d5100e0302034642442c40080000c3d01c42449499524821002c000c00742d0300344404022010b400c0a000d0704801c000500d42030141c00100c800300080e1140300c410420105401d0609c0720020310030b03118070300c0000400d801002454124046582003004440c002c3d207400c40d04d43d456041c9141865180724000b90702c2806c01e15a00000d42502c4041c18810f9072400007040b10726150020014184035a505042c8c1c101e60034404280042140a03907142c0c0581c01902402c40c02c1a000036051449d40b00b168102c90041c1e5071003060040f540e15120b1500034000950007030100010041000c5c2c41d4204500c0b4200741c001c2c500032561000c9035000b09101d44080050100d9647e0700e61072400d458107030054451580264500000120145007074070706250326500f543c003c1c3c149582152400c80301a2080d080650302d854140781c00e940c8150280c41070800140899540340da113011001c0006040d80d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 154224190 1250 154222940 154222961
    0x30204360e032709100605090d11060a210c081302041409070f15020318031905061605090616030c0c140a051f03050a090b010618080304060c080705010f0510030303 72
    0x118010014001c061f00311045501400c2d040b030f02c40754400d009141c0b1040300b03c0b00300e21503a007000c808900200c0c404e07008040c0443c4100040b1151040d45416003298088940c2d00c0900c000103013403d0041480307100c21903101d00c44280080d00c0410340d09180c001101d084081686d080420f07a00130403042001c1100001071001424800d000714080e0500c843c4003d41d41e0296140070001c42107003000401d03181e901002109030b16a4012070f4a0000c00c890b0804070380362703d4219420120b0341c54075180e0400e4248640112a8810300c02020b96041003681c4200b4403440c4800d4078210309110000010102203041861b003034000f00f040044c44104840302c40140007105119174400d50084c0e51000c40c0500311080d00f03201c40c03070008075450005026600e00420a001e4613030b010703018042090807800440c00300da100c10160249070420740054582c82d41c40d4007566480c4a944141c1001924503071003940055200402008824010070020607001c01c00c0409a049400039a240154042076200420402d80c25004005005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 154225440 1250 154224190 154224211
    0x10c050406170702160b040f050303190f2109061b09060c080d09140708160b0307180e060f03010203040519080d020a030204360e032709 60
    0x140c544200940b81990011901c0d00907a88440081ca40900c20014007142d241e441c80b070b400a050b82e9140ba100d00c0c2d40b06004480408145030300120706030074000100d600c04d143c0801090103542000201b01c0c0e101d80c130106090104001e0803220300807030381d90000c000c04da07091000000a42c0074851034400103d6200309407030031040025182198065410000010171503030f090400341050149480d142490784110102c41c0c140070f14210380307603090145405901003100c90071400c0318007554071096140c1d60340d80200362451102ca07010006101284041001e90341124550401000c60002880750392140304254210341d0490494404000492a004201d2059508254021407440c2040d44a451315400b1443d01d5490309603140c0c40792001c1040307440840b240461502c4c1d00310744616080100901940c894403c5282c4240c00e0354000b41c03036a4000e240301081000e81501c8105078409030101001900b00304001e031100e40828030100325450300c5258a0415406038001903040325101c0410450200d00240510009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 154226690 1250 154225440 154225447
    0x10801060305070c06020c03070f0c0e0c040f060e0a08010f140a0603081b0c120c03071a1207030e070b0909280b0303041203110615010207031e0204090c0305010c05 72
    0xc0c0d0342c20107801c130307202a040440965984e8100d155103186114844e0000c0c0380c1290040e400c010b0054a04201c0d068441c2c40f40d900700d00342c079692a0301446000e10b018400f903001c80d803003040201500400319140080406003828540316078420880342190711a648100444e5181c410648a00654107100303a0300c5020214100041030458072030000501800c641154902d005685410914004004040e03217903500030b00c072040700e2404040c0b4940303505480b20310a0103441608c00203e5018403058203010000100c880c03441c145203440d140c0800954001e444602450380d00d458080b0803200c00e0100310050161001200c4d03640708044240200ca03c4001c0a401d46841042d01d0112480caa840c000c442c1c5181082010480510300710000c2e040d1710032540803070840c44401404804150b00f040d09a4501906c0030f042e40d901d0b030340d017481c4419080101424180140c101d00b00034400183e141a030300e021360500324899150708038030307a000c42c0c21255080720a88490001540c100708100c024041d20800c5100c3d841c00506 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 154227940 1250 154226690 154226701
    0x6071218060f0506190b09040914070e01090903120c12060f0806130503191206030b0601020d03060e07050c2406190503030904020304020609030105010b18030a11010f02100207050c010801060305 85
    0x45d5940206c0c0d900c540700188410099549821115160307070442920803c507d2007205241e5030f0070301c1e40b0a042c1d5844c91000001402069071244d0581650142c452407900d40c2ca03408148000c0420310045401e0015607603480307090002620658020300582c0c2c44800100d030038841803601c0c2450040990814100159903440003940c084256000c8072811194070400440391007041d61b0134403000e90f07000b00540ca070001c00000d2001c0c10207418001e000a80988609030180c00c0100c040d545a800369520041a840c00b1503240342c400d60080503203845000c140c80e6001c03402100d4841c10440101d012a58100c01c0007403040383d1030001070300b0a030851040c10f1440c51602c2c0002007500c03409030741039052146034080001825920354008a031030680d0020001c02c034668480074003907040e4019860105100f0a41078010201c0d040005004580603001342c4092040f0001e4001194102d26840c5a00214007560b0342e420144000350002d002d2143c03081d4090a071000b41c100004080b0300d03059001008040c240028404c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 154229190 1250 154227940 154227979
    0xe0f03030c0a06050603071a04150527120a0c030507050a0e010b1605030c060708090309010c11030304030519030f0329010e0d0b0603060a06050306071218060f0506 72
    0x400b490740110085100d03034410780040d061a245e070340091080580c00c0601c100034409a0001c1c1700340ca20049003607110320f4041504076124050f81c00c00351012a90145540d000e510440762406290100904075000381d040070020350300304214840219009503401e80288104107080c016040603000c04d40309070400310716004520f202c0300018800c006403000002070084052480b4900c5218250300001100e917a80101903c05584a1086035048001404800483e107415004811542c12601c140d54600040c0490384031034150f0540e0f620090b5252008010001c001070b4184401c0c0c010801003c20208038000a0601070000342c90036521004042c6001c030b20b020b00c44000c3c00070340e82c4002c5400c1120700f249022001a80e030b4001c080f540c945d02034540741c100b2040104218560348500002d409039a031a44400244034152132a83c0552641742c0c0100002483c04d504c11107100300d1f0030746005400b0441ca003890180800031400c4000c01e45209444101801c1869403d000301500070006640000702010300a0a92 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 154230440 1250 154229190 154229203
    0x1305030c0301051909170f1306090501020d120b15071a010f12061517070e010302030705120102040302061b061b030106030e07051002010204060807090f03060b030a120e0f03030c 78
    0x404c3c03001d5403051100103110510210201c404081c0b42c0e4903541f80780c40c101c460440d4104000110000180d4000440c025118109c004119070060300241400703400081c05681000c03441d03040080f00ca644410048282d601c020711201c03110205860170382c0c7c661007814a04801c1c15511024055040b242004016501c002d000100817188101ca20b0aa41d041c2d9150100103800407080c0301152081208010400105401606000300060011500015500c2030f1403140900e0074440030307505800c491010001030400309918549025500300051034991268001561078000d8090b4030380b80d02c81c030f403c4202103050402c135003900514020300610144000c4004064a4030050180b8410941c4488060080000c1040554051300004041c103100440e4100028000e400c40d2040b03000050403074012414050007024000c0c1954260100d50246c2d43c25904c410001d040030f4580140c02d0b03c6480c00701400304d810300900caa0003415a0b07669031046a100e80820905100d180100c1703201350420043c1c0141c207100051003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 154231690 1250 154230440 154230481
    0xa030305071b180207050c0d0c0512210306010210180c050321160b010b03060a170303010911091e04050106050a0219060e0d03020d0501091127061305030c030105 71
    0x345e99074185141c1642801196181c0c4c1c1d800c501d0714030509080081d900300c03030300c141ca0056070191641c0321142c1c8000d07130322401c01c088940e62400d81104484110020001103900c100c043c0100d5401124441c0d03010100e50b5217042c8004008150719081c0100401c030721090000300012002020841200c1e0004608064982d00f40b2542c01e40018150218418000141e0a132980000c0c103070205683d10040c80d803071548101d500c10f2151000000203c2c109014861600030004028011030640c0c0c00c108412004100d03c401d01c140d503017028001c02d0b00c035a441120f821006200e486c007000e10b03046008140300545506030087e500380141803200c1e00c2704640c005003846c007210030302451401c150300d01e01701040182200003500b2050700403070001380051909600205415003580e481046280c0c1d84030740315003ca986482461103c81001c01a03c0700c0180580c0c200c600401c1c58030841028002000b0001e42d080d4030400c0d4500d2907418004003000503140500403110307061020f800a1000340340110054030400c80c0d6045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 154232940 1250 154231690 154231739
    0x305100501050a20031810030e2104091b1404150c06110f070b010503060105090a05090c030303130302160302012106050d030507050607170106030c05090a030305071b 73
    0x20144d200c8400c800402110034008040d2982c8403101c0d49895110742594a403180100b0036142c20b007414511030300c0703804da2940c12803000d00410342e00520704403a8088089402d2500c3c150034080030400301030502c04d0b03040c010143c07440c105110107201c0c000b410324050004509929142070100b00300881650035100c100c10900c0c5080082c07800c99281c29401003052006100d0640e20101e80e02501940389802486141e0141c00d80704a560398070380c1050b90303500c404d0044641007550440803a180d940d2a411a5811961800c00c0d039800d8802c203408a4a19081110b00c5100c440003c10581b0a058042c8803207440092013040445445040d60006000000e0105481511101c0458444039001841d03000310080c4c2401841c04688040301d04006025402c0804196481e010340808036440354015107907008500d40e06142c11034560719118064004100b44410b40b0280001001103050640d00c2c0c04008000d50320a07120145c0303517052810000d00280b00c80c1c20381030800c60100000e01c80880340c0364640005400207503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 154234190 1250 154232940 154232957
    0x10c03121112010303020105060a0b030103050c060d09060c05221a09060409050114090c070b0c160b13110a0303020c101202070b0105030d14030f0403090506070804060305100501050a 80
    0x19100200c40c420b20340c1c09640e00a41c40d00210405034190040d81c020b071400c59003042c8140d207613070070340d60b0520003071200600030741c01000110789605010b405010400400d420004403810641c503540251590241c1100010380e0000da2610107407100012000d04088110008180d2800d01b401c003070b551207108494481c00d810101d04485030741c3da6501114041c01ca01c0d8021722480d40c5d02c001b1030340070390f100d500c4251042003d440064607511401c001e0f6195950445007803851519207803a0980d0680c040c003000c190860415000b58081405002940c3c00348441000544c115407150030004240b4640c110210f100341030030310080000c00e5000525820750101142c424440b0410804c05480d000d4008003101040385c0040342d80e000348010300356000c0c1201d500342d00b41d48460012920440b0484611000c0c0c41000130103001103140405113900c500ea006200e030400c0b0645940b03a0000078881c0c4c05c07565003202e580d00005014892591b0501500b50800b416030841c0c00001c0c10400042c001c0d000c3c1c000c5070380c100321560 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 154235440 1250 154234190 154234211
    0x1203060307031e150b0105090904080d06060815040603020a03080f0d111201140604030b0a090b0c0310061e032a020f012a05030411060313050c010c0312 67
    0x1d100480046034800c0c222159184034108070916200203070710a440103080000894681c2c4014001e107a40007405948092402d540e1204100341c1c1c40010b07005490708a01405640c1c0f5401180c4942d0010b0082c680f40c80c015490004464079440800d1600a4007660034480200010707141c00a00b50b040d030398404991616500c4944500d60b903400786d07208824020781003098984d540d440e640c005040c00a004c800d154541e07030b02c03031000c5140788409070030301500074030200f104001003049086075607007210801c4008aa81c07803c07a142c0e041c08030000d4075200c117070000c000144230204400e401104c0040c980c0d402e0142400e011900105245025400f0702d109160700d0b114030305a80b4400c1e240070184082c01c1c0039400b0a8408180340250b5507203000320a00d90640c03034803e1554070403c86c5152808a0782000310b0300d0303009024090b4112001c1d00040c1003111800850114032034903507510009584520f101c10060201201c19040452904123880030307030740c14010300040ba840404d500828006115030b0350b081c0400d201240303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 154236690 1250 154235440 154235443
    0x150304030318120305090c100f03090506070305010806090c0904060b01020a0b04061505030601080705060715050f070e01081015140c060901060b0f0406031a130507080c07030212030603 81
    0x21420040b0341c040022400c0000c00c4159907901100c043c065030200110b075200c00f01c045d0754084552110f50f01003144502620a83d00c602d0350701c01000c0d03141c41c0c0030501c48820303907500349010020340300c0a0210361a40300502c2812400c2004c242d200c40340f00004c1c00011415000714040c2e500140c009045070b9200c2031105030603402005031b030740310310742c4403003450180d10703050911900821014a588000d0b4000e024001035514000580605030b550f150080c1010f280b5110070030180b5400b81c2001c59190304495054459105244143c1c0d20030781d001c8000c0e0800d45401003008204849408100d03060003142c0c0c0c10b1050028000c4208002e039a284000da486145020381c1c2900c500848040d10700c40460005240d140300c1c0404100180203000510081c40b80c5902d03080000c5082c09082c1d1b148082840500042011500c80d802100b01c804138006802e008440c2140442e2001a0b00380940844507100c4061210075544111002e51120b040c0303010b14102111503030003d4840b80b0503526150b0380034012006c00d1141e47c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 154237940 1250 154236690 154236701
    0x60f0f0d03120b01020f0c041505060301030f060b010504270b03010e100606080f0415093005091e0f03010c0f0813080904150e0c0d1107021503040303 66
    0x4140d03840490452500400e003200400c4407150071820540b40d000b031940000b03091b44041c601d00000d0001e125681d0280402400c80302d2070101300303080400000417262500310080d8003845c0200d00403e24a4881d09085042e102c0380c000d8241000020041042540c3c075050b03141d001e8480b240c041424000e05914030a028100f400480b075030552800d080c0c0070300141c0008045403a1248400c050150603510a81621100021568817111490940003e00041d411415040c011108103a002441d20011384a68003840304000c10311031b1041c1d240c0d0300c42d00c3d02070007008280b0a54126280c41440e200c1d410012400607241d00b07a0380b2010000c03c060040d840c1d665140c861031984030141c020014420003640c014954000103500e540894880008192540c0c070141900851903005070b041c5103081d200300e080c4030080110503a10200201465408552141c1d40d4181500803040c80c1a01600d030010101c480c001c844803030340c44004090080007500e0058660345c5005102555180c031840e00c9640f40c0c00c05602504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 154239190 1250 154237940 154237969
    0x1050705121614030a02030304140a0f080c0606091515070609050127020102060627040b011502160501050912190b15030c0609010302040e18010e060c03060f 69
    0x10307800310b40c031142040d206426800060040030184108030101c007800341c4911503008000010f80081000a011603007200c04101031645010441c3c00168840d15816141030f440705049605090004040e60a640704100c1c807608032a0880703102c1305504203d102c034082c0c40403500a0600407070110000003d0012030b502070341c4e501034002c2400c1c450b260721440c00600030000c58401d0482403c54040300d4150001443c1b001c00f4056040c1c000302002d48690041080111440d800d0a030424645c210340e9005003020b000050165104004e80c2074154103012007001d540c4846902803007154000b0301001b03045103c105c0440221142820b2840e40ca00c803a20215420881109100c00148181010f01d03d040c2500305115810038050104c51019840e10611110344211921000d90b00d6480182040010301d482402807041003414100140b9003a81e4601980340d40710110ba05c05091410011400d41d03024003070040c0c0c0140c0046001509042c508042803881d240000303084e45000d80107481c1c0c8104c090b00c41014110710034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 154240440 1250 154239190 154239223
    0x12110d060608090a08030a0203060609030a050703020901140109090b03010608160e0f04050c040506040213030c030c06020a0510110d061401030b0a0609140301090c08250e040201050705 81
    0x804864081901a119a114010000302c041c800aa0054070104030300b150181d00090325440c0d41c68134040304002c3d41000c0c10141e4801d60801a44045540402c20341c08550322840240190714036600400c142101c0581c4000c2550302000207941607a80c1c080040c20a440f90800c000030000c0d842004a4014462500313700a640701c0c001c0754943d60490146164121103501c440d9400710343e90710b032165070304410580c1e004244c0e5103c01110070703031407a06800c110f074441c0c005440103040c600360740c40b28000000c0c154401d550701459030070b01780188038105040d200035046a000a1148070b2440d80c1d070342d80c2c5907401540011a10341c0e9580c0c44402608110441d00c0e00e0140200c03c1c010700e5180c281d140e0b2041201e003e0305000c40d00c0c00d40c0030310b440d0410314504001c40c0d0044d201c204001c0e107440c18020b15109644c001551656890882e000020a0b21110790b02400380d1400a0403c03c0603000c4803d149064450840403154031070b102044003103580c1d5043c59110364286001d41e00ca9403289003180c40d05456134001da484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 154241690 1250 154240440 154240447
    0x322050d0507080f0102070c0e072a140307020906100e030a14010b030d0203040b0a090306050411090a060305061512060f10060314011a0706020d0f0c030510061211 72
    0x34018001102c0d030503039000341e06a03203041c0104004a070807446103d000410300105004200120286d5400655101f02c80c0d051044040b0580b070908541034000c0000d10341b540501c1c04003101800300d4030201802c4030b00300b06c3c000e41ca09200d9400080c4041401441c5501c55016510440355141c495042d0b0743c100d00c2d000c3c00310f400c520788038507001000003941625983c080d840c1c41080312061a0025608080d200c40e6000b41d40741038202603412400c1ea01c0b0002020038060400c07030000024890f0322400744201e020342c030f52580e5150f40c41e040281c40c0401422402205040200510106101103a4035400c1084980c022403042d480f03401103104c01d01070091340d030658000c0504009404001fa21b00c41d10a1181c8180e04040e03940307c020070340865030b10b142c82055101030302005010203066442e01c00c03034000204040c541041c0c019a181c1d8140c0e4000d921440d1810744610105551462070701400b025144c0c142000d110902d44080e100c80b4900a03881a80100803405603014101d41444c2d00080005c1e55101100303a6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 154242940 1250 154241690 154241693
    0x80d021f0b0d1b060e0303030f040b0703150b040e060a030c09090f0203151803040b160f0813030606050f030322090603050c0a0f06020a030c050c1e090a0b030322050d 73
    0x400080c944204070110320501003045c0f01e460040200c0348580d4100d42000c0c42074445458141d00c0000c001d01035020300d541c0f981000c8042003a80e0410000301141281240d469040c000d0810020b0806407103e4002c90a6500031700000e140c0d0340c07555040d0f480d07021001502d05105e003448000260402d01c080e4040c0529001c2c00c04403110021494031940c544400e6200e0581c02c1e80341540c3e00e10079440742e0401c888062104849881c004041816494000e03490400145000d450300880c980c0020b03222000c0d119025420802c00155024010042c00b0444094088003008404039842e4815603c0e100d81001143e1746614148600754490f401518541c51f041121a07280c1c9456a500e10a0207002403040344000c82c005080c51500603240103440c1140d010f41180e01c5256010784900d0b0309960704403014080d07491482103d40f02c14101d040c011108030311800156140d003090210300c02025020b4090f0034180f003c0c40a29480c0001283d80c40117815110b0003408002056503400e400140d0801c40e07000307002c5080d410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 154244190 1250 154242940 154242983
    0x50c090108010f05010b030c04030201031d030a02030d0f141603090501060801020d2a080408040b0d0603060f090309061b06050a1e05040f060c030e01090804080d021f0b0d 75
    0x50f0b112400c400401050741ca07601075040c41e0004948840c050740c8100030a000551007900018410100080c00141c011494070307540f400e42c4c2001c440600140d00102e6181c44000c0e49014484c0c200e04210030420684881c50610075004100400303007a290628200728126451295200c803040f00d811030000c00101d900c8070489030103540a20505d400707103030500e02c4d401400e103510200102c21008180100b0003428000006a031240c2c001481039a144805000004910041200030581031460800004007142103203008002c4551690400c3c02c114500f03140c0100007030304113a008054a042d400c0c210211441500240d80c04491034030000c21003400d0000340310f2a005a50131051460203010b54603a60312507001181c0c01210011180901080c2000b82c0600124650341d01049604015203008208809000c10700b070f00b910071614040712040000a070810109034284682403880240d440680704050881c0d01c8070403500c4208504848042e0b9441e40c14800ea691441100039541d40700800400d54143c030448038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 154245440 1250 154244190 154244201
    0x30206011a040503070302120f1c0f050c121b0102070503030601080c0c032b05180706051c0c1b0b010e0c0403120815030703061b05030405070b07050c09010801 70
    0x18961101000c0d41e609104401c00291003e896000d8018800140b654080050b06c0340301c540f000c0641e00464414030840ca109100001b682d269056070020410030458000700640c020340b0051041100074400703519070200c04540102d030040c0f1421000e45420240100442e103400d4480380e030341103610000700d40040241c0480a18400d034401d0300c41c02c4066856810801c101c2c4182120443c40d074000b00040450628005c04040788090702c0170140c01d0b59501828958211401542e603001070f10700300d8140c004180002c12000c80070b08034528010341800b20020315417107440c4209000624040c0c44045a2080354810100b0016942141c1c0080540760414240301d41c10300300030f0154151020104e00020940c103680d0703040314100c0354004102064661060340c102c0b102180035018800000034040c02580682d020811400074600413100000c511a40e4900c2d01a015030101011003402070a00800c40440c902080d60700c00c80385140d81503560742045107405810850440c100c00d601090a030000306034a030701580308 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 154246690 1250 154245440 154245449
    0x1214091002030d23070903031b08070b09010506041a0a0302010809030f04061805041109010c0c15020c010e090c0906030a0b0d152009120a15050916031505070203070f03020601 77
    0x400003561214031041b18521741e0307400302401281c0050740c00d00301018004181580d950258003043c1c24941140e5403020f80500688401500782c0d1110b00b44030305450103200d04d00885011510901a0520180c0442d20364183c6100c00780c144452040080d140329028421285564100c1c401c02c0d686640354039000d40f0304980442039444492440f080800d49050500c03503d60000c00103105e403400c2400c3c0c98011643c1d070054610480d943c40310b001000a040c507050706042c02040076600a09540188880014800e03080f5000d00b500c5080395005201e95a0610011541c02000a540096490341c130000b064025200001d44540c1020090028000780804170501100b6900301003810712280d44800c01100900b90511450882041c04120394850340c50b2030815595030910a4083c5c0e01250110b80700d030301d204a132048950000d40c0d101c104100034110309010b000c0450401d0080c5290090840d03d03a04840c140322307a50301c0078065640010a50a90081050300c0c0200d5110b12009440c0183d840c0080d2103040a208 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 154247940 1250 154246690 154246751
    0x53c010f060807080405031c0207050105070f03110f03040b06010917060f0106050c0709180501060b090a06020d1205060a0509040f14010b0d260708071214091002030d 73
    0x820300003441013449a00454000000714245524400e1a8410784142c40c0e940700483e90030000308000030401e0242c2c900c00c40550b1902c209000d02b049003d01600d21403040501ca81000304418028582101c1c1640e4219801000340c601c103584401c0161520226500030782904200030302565012000000c09520505c148402072111341d0303a604c0243c0c0c1e40c2c02004090541500054010700031a400c5900188020380c080d0074021040c41d15840b003608540683d0050760240100142e040e115080c8102030500400a81c40184101144848010070100f40c44040620164076440807801640e1406400302c06040300500b00505400c3c10720302801032143c8048121040003204486000000301032003400d204140140042080070550313a5000074401103c50742c00840750f4554005901003031504058140c8c82d21850050342d43e01c00d0340c10001400003500000b501004405031484054806140584000040940395000200c0c402c480903402d42c098035a00310f039001e1400c496003060b040b401e11381c034180c00107104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 154249190 1250 154247940 154247957
    0xc140a1b061d01031e05040218010b0706021c0c050307020106090c02151b0403120801050301050411040f0e03030c0702010905060301150f02030904061401080a053c010f06 75
    0x415400d82040e144240d00214800110a0904040480c4548690303041407500080303141210b4203002ea4181800402d11450f650759040000b181402880c1800011904129542c2c541c0f41442c10380e40b43c8030b0008020300040d000f0401c0d00100e04410319001605200c5e403000c0c080c4114024004000d40c004a51f004015820034000268005075445a0141c408150740501380c42c1011080c0746804403c05000c5440e242058052a0341a084220140c4041d5200780b40d08402c0302c440d00d00c02049450b040c0c00c141c1c403a0b4541028000001d14000181d860a04107550100f0036030050415170006100c000c0001e070302800b0000402420100c40b0f030042c038440e4800d80305c03c54003c0d01d4206100c002e00090207803484800b182e2804c00803680c040c0700320000d03444807032044a00d047d41e400082810f507200307984190514841500c0a040e290381099002d035000e8000e904c00c109a26004100300c4a42e02003110391807102e080c1c1c9460643c0c0700095010680d811030350949408955944070280c1d210b04000e446a07800044828 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 154250440 1250 154249190 154249223
    0x21e0118050303190207050a0f230d110d0204090b0105032a091008030408030d0b090403020c01030213030209010f09110c06070806060910200d1409010c140a 69
    0x154911800c0c0c0750090019414008605015001d00030107103100c2081d44600400060243d444200500281c05030007080c2c51510302d0111561992881c258440d00703000401011503e061700e82c2d14080e07200640010f0001005100c04002c681c2e5400030280103074126041c1070000c001e006500d8102c3d03041320010b4084541180020820762481100c403540c40c407090007080d28004071881c05c0b41043d0b800a0040c2e9a104040f96549a03043c6903500c5540f2094a540001c0345040804080c1c0c81425403400082c0ca900d5160318107543c00030b449100c1c1041c4a4103140c0c0c0032501d000d800740749a1440700a5640500340c011596102c86044161244504c5110b0303c03036091507140c42c0f00d0380e03040041c0c841c9070072051b0091200e0345502c101581c80f44001802c680d04180e051120700d81c3c5585149909000340001d46518040504a03440c4100c0d554540798084036650011152a441d15445420b100d1110007040d8150349880102004a640b0350311404080c0c07124010501d0401219004503540c0c04440c400c85554084a80b407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 154251690 1250 154250440 154250477
    0x314090a0c080c0306060402070501020f041508060d051903050c0d0c050706090b070b1302040c110601080f030a030509010b03072d0e0a0504170d0902011103070c061407021e01 77
    0x19001d0564050700004003103440e601f000c3d0050a4118400d00001d400c0680c10108094070780c210707610011030502040c030004500c640110309035030030000c20341d10b9462400c00d42e10303031507502e50325480700c00400700340c544101c1c060504c181c0c1078901c01ca101509841020809600041044500b07040c16109401541b10004103540584424800c41d0f21089840d401c100081d2621401204020214855014090b461400696540c46000490b0301d0544482045c2c0038102c8070140307001710580100b0011383c4284080e100b40e110020079207014502e1480d0102d4641c1c0e650340002c0c050964400d20795014030403010701080d840c0041c0c0000c10f26448a101c03070703200200b48502d07080c0c001d0314078406d1080300d03091100440c408400640095601a003c0d00c0c5246d8500c40340181c00718254041045001459650122741d0115a030182c020403041183d00010350400744141c540d900c480345140300b02424000b010300da549489820605641f40940c005000800103188840309100d580d00a200540c0001c210089a00c1880311 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 154252940 1250 154251690 154251703
    0x91f031e020a170a120c0605040308010e060d08090616020d0c0e0f040c030b06030114190606020303160c150501090f0506040e060a0b0103020909010902280813030314090a0c08 77
    0x143c2d54004c00c1046002d40300c50720020781d0010540c08110a4a0303100c40070a0540c01001d0065219558580140d031400d184c8010101c405000c8511642031520384101007038540f029900c0c6511700311405652800c0d82120000c161081d008005e400c0b01b640000d1005200342e0b440068100e41c041c20740c0700683e5803000f014660109003110b0060a1020310082440803c941d41c0c00340b50b01c28005400000c11013070301e074a0713028a41011074110001202640800c074420350740303004a01c020246070005500b94100a1b44102c040005198110308000402d40020b0500640a44075031800e94601c40070002540c4a811700700203070001d90ba0594456041502003231444c2131a114240d0713440b030040003a00098035100c2488014101e103d840904040d000c2c4404d020759a9580c0080f4000d0003080c90050342e64400c41e0420303007140d0001c007a0a00c5a845c0f00d07a04641e80e80c0041c04203500c414411446005084c0c1d91074290700600d1b060500020515440c0d0070406095000035100d01101e00600641d040d03980d0703808902c2c1d038070322 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 154254190 1250 154252940 154252979
    0x325060516170a02120a0902040f090f1527020f0906100807030e010c02010509061003020a0902090316090905060108060c0405010e0a0302030a03050714010b091f031e020a 75
    0x9044120907041c2d015000500c03500034030510350251500d8080e200d0301203000001d5a0030452650340e0580e0804524142c40345020340d5418560070310101c00c16484140c43c0c5806070034094003400d9569460501d44407103a0144601b0850082002d03903400b4007040b22000409001c8040b802001048085015450103823031451003200d0090100e110020180801c0f030f50502c0113803036403051585560881301c411000b80540500140325070300002d114940003a0080c500340014081d6154040c83c200b0610150300c0e00000a03017a9800400302682c0ca28000020a15007480240c4c01074415403d01c2c008100d580d85070300200001c034001e404035135081e603c400f90980c990030300381c40d1624044030412040041d075000b00301c026100c1d907005007009000d9a494021030f042c111030450480000300009060010040c0310215115880b131a00b00801c03c4590000204003041006014450044030180d00018400d03141010704007e181d100e04010303204980c20340612819007840108078030800810b040881c2e2054845940d40081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 154255440 1250 154254190 154254197
    0x20a0503121c0603110409060b150c0106091808071e080702120607050405010c0804030203010c1815050412021c0803060111010b0306010b0304032307030e120a03050c0325060516 78
    0x40d10b5440030030004241461f4111401078403623070020b08680d6100710124a50701001800e540d80c2c07104100783d81c03c4a0050300701500c2e2900e804000500042c2a00040c225243e100748196a2400e050800d00758030140c0c501498459034144d500d810070405208080d1148074405e88200042900c0f0140103629202c0403125103000500c144020049580f00d03003881080c050180e04164030b000c1d2a900800d01f543c0f1030701190000700c0c24200c02801e038110300514140090187d99101b0b010514009002807503031184c0d120312500c003107400c2c00900c20340d500c550207942c0c07071000c8a0508003241003e2800c3c10741500200d9606000c82e902d0944624801c2c0c6c10f0043d450f0303403c4000d000c0d01c2c15a00f00343d003414454001030800d40400c403021a43d48861070610190000502180c4034207503d540390751600828060300500c0e4180548586594403500401c00120140c4903641410810380f60b9210a0a0502d9400740c19130744039410395050509074140040750250809240502000d10a40d40d800e81031080750303898544020b001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 154256690 1250 154255440 154255463
    0x60e01031a06030c070f0b060a1509060e1c031d011722050f070816080309010309030e1806120303060105040608041505090313060305010b0412020a0503121c0603 71
    0xa45015001154442c081c0c1382000d081070401d07202c448581c0301040d0200d445079160030a0117090b181001e1604010148802c8455103203401340001840201d25120316018010f4100c903d0364685c0e80d82d41c55500324100805003c4100120307050042400c2041300d003548480c070310300d010700089500c11380035642e1000b0b03211080ca1243d280e4801041203c5410100349902000300596000010014080d0140c3c580c240002442d0141c10086d2040c20514007603800c2d04403002c00101004140c0d004000d4441545003400e00180b21a81400e040d2400c4080118a0303612120714104c4800e40c80125540f94001d401c00e48040c009581030520580d601e00c810390300c460101e10284010400349110340141d40c4d12900c80d59030001c050910b00b4030f03502550010340d072501180e0030200d0880300e8503220304403d100400e103502c0d00703101a5241408103140d62043d80202085039202882035411354035240001d000030300d0043c0450b0007a608a00084080fa001400105000114101200c030b5030304007402032100380e80d04558030004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 154257940 1250 154256690 154256741
    0xd08220b0a02031b010b0a030515060613030209070905030105070f180605092b0803010e061815010c05250902180f040e0d0201150e1306050915040c060e0103 69
    0x10301040210304034140d9216011b24075140c4845003601c0095102e43c1c01402642c08840a00d0682c441c01000b05014070700c10311121040d0000d80d00c103181180d0f0103580d9002c460300d5240302120280301c150056501036080100744600c1c00e83c06501d00800c05a155240c00d5401d5000318102c400f00b550b40300c1c0c00000b400900c8003988503d000c3d084d0b912140081c17400814411161030443c400c110802c1c6098404000100040103d0310300c010002e41e101e0300880314503e1641c402190f001e0020009000c282c8686007800d09188143d0148840d0404950040111176150706596580c10050031a684080220f03203900c900080c47c800b90f802a1850034003a044035940b201c8121050001180c0c0d07450f26107901540383c80411005240c10b0054508141f0560700114030182030a03030440c580401c07130380501d50740c01c8203004010b086070101d071103546541d44c4404003113020385481509624019085121f06a5040c540c1c081c081086600485401191344035100c0c142c40da42e00400640071034500080c5101030340b419070000c90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 154259190 1250 154257940 154257967
    0x50307050603040b07051c05070e09100b0d11030414120403150504030c060905070e090c0916020309120303040303150509130501110f0d0b0406031a060d08220b0a0203 73
    0x945c0031280b480e00d1401c005d502d1007c41e2408200581941050707640d07005010060740c1c0001c50102c044400e60706000d541c20881411001801207202d0320304407101c04900640040425000300341c4138900a425580c80341020708111140c85400e80f081d07a01e80c031910001040a03241e00060300e048a41200602a5262090100344050180180308508000b096640342780040d21038480d9141c0c00d40100d00501c00300e401c04400b09181100035000b54070036030087c0f442c008291342c5d0310103042c0d110b22300075401400d0701290b0006910f103010310b500c032540c010b491228481e8103450000103144503900a07139090244158140b03040140715103e000c0d10740c2061a020000d80d10070300228000040f00d1180d8000554424000043c80b00e40c0c20180750781966520010f0215120000350041210044003100d04200341840d6544440c0700c8800b5051003c3c1021443c400200d29680c0e80310011055500b2800e029035412246205c0070009039007113031454104140f00f60126401e420f05041d614041c055070000c61900718680f9420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 154260440 1250 154259190 154259213
    0x106080d170c120117010c021606140721020c06070c0323030c030a1d22020f0412020316050a0b0d1107110a060e0609120f0a110a05030705060304 64
    0x14509a10704202e421103454120f440c482c000d000b20304d80c1010030102d4120035803e403041c103c4042d0856100c9070740491070b441c03101c8905c4102d0b42c3e01d0410802056000490b46498042c40c100903118444803901025060080080e24514046584c01c2d103084945d907604014040c0543c01002e00140c0704014107100242e0b510f24110104d8401700031070110b07400700c11000303807031688011610101904042608500990424004101e014000325012820032030361b404a03144161020010034102007045c0c0c0d0005584965040b2051600502e102c0c5544945034255401d04407000c907400c9019109810311283c402100102c4682610401000f9410a500c0e19000800136006610301074817031707662070a9490640c2e0605009120075480342c620700800710310704020481d031181194841024030006001c8142281d58100440f013185208807001e280c0b000c004403a0a10344800211440c02a2050308443d4003800103107412019282021110034100549503401d05845001c0b902ca507a400c2102880404c00103041ca0070712 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 154261690 1250 154260440 154260451
    0x3020c07060e061201090c2607050306150a030c170f06011101020903061003020102071502070b0a09081e06220f021507030909110702180a061d06030106080d17 70
    0x140e6040105030082c041d00a0300a0703001c04203940e40c0b2500f03443c18940001c01b08c515200c0303d100c5203ea003520346080d6104848001c0881082150000000305542d41e00090441410601c04070107446078407040c000f9008000c44490080801c8001c0f0113403807041d01c18100980305417107028001c030302900c1d040010351b100b101400b007c550329502402101802d0310304210795031041d0009000350285070f00d10700019081c640d007034004110000e244489440751503000170306501152009508581d803481e500d18110b803580e100d5000800c0a00402542078007050102c0c100a004100000c20781f049600c404020200100310104d607a515a00e101d000200410350003800c9400480c0060040003205000720000705190784202c1085002c6000d0032402d000c00d0b002449034071403061441010034a0020320350005051300e2031403541e80115500560000b4030b00820345c1c006100500c0d100d0200c0b5080b642521046140004c2260071a00a41c40d000c000030303034050002402c42103250a43ca9941402049150f0108880c10003440b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 154262940 1250 154261690 154261699
    0x9100312081503010905011b02010207020d2a08030304200102070501050c03040b070305070302151b070507090e0a1103070509060d03030b090a060e0601020f0715030906020d0603021003020c07060e 86
    0x2c00c42c944003070040001c07072845900001051a1075074140110130326628840f03801c5a105000306070061f00c0e540d0003004c00940051170b1030950b9030b4006142c100700701c1554290080e0350100100227400750001000d54050303481201a00000d01810340041110300600945c0360059108604c1048254000d0f0002c2c807440001c01c050300d1400e612200700c41d03416403107008110006500080c405d0709142e414445d94040044005241b03103581804020b00b05000992030403001c0c5050001a06420440c04000140003840214000e0000700d00301c2000c40d8480d803041900ba95096411243c4503404c0c6404100321066030802020b03100203031185014005240c100c204100e0500d035035070b00041826a02c104034248a00c015030f03c003264481c1403d017855503c01300038005078155400300d000030781c2058000c00c00c2400e40c2c602c03a521040203c4038080840c0036120161000d8000f900c002282030090030306822038070969000b41d822420500405000710100e100d00403440986800c1290309010b0f052103540c080d800018003c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 154264190 1250 154262940 154262971
    0x818030a02190314060f0601030b13060e090d031b0c08130308070213231f08010207050c0312120a020d0e0105160518090601051204030503060910031208 67
    0x140411600b01404942034018284900100704000c16248055060054400038100f5400c120300b24045014000c0c02c03044c14941c40e41103020494032100030413101100c400005000b0983d540c0803283c905001610301846a0145040c20320446000c0c0c00744400704400c0e0002c480b044202a102101c881c00c1101045586060805c000407034010840f0503800a14001c0201c00d6a400d124410000e18020380c155582900707080030b0034402640d01c0301a0440c103605c1400408181a6101c0e0340c03000c44c04c240314502c405261202900818189415406070000c988101c2c1111500c00341c0f202013550710a0002c0322a502010100005030341a000145c00d1604030b40b0040016040214a020042c00d42d44048060b280682d90740007080458201120700350682661418800c3c5004407900303c5c6c0303160b44001001b25001b05090804035200381d21910496564228600c643c9e03180d420146001040c0d540141c44061007942a48081002c12468202c2002202d91120820718030005240e8261903020b0000c20000c07005082782c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 154265440 1250 154264190 154264193
    0x90403091505040819081606020d0609090c05030601080316051c030911040b0109090b13020f0d0606020c01050d0b0102120c010609150302030c0108090c040c0c030210090818030a 78
    0x215220007145519448050702daa00301002a8544141d16049400c03042e08401c078107010030070050031070720340841e0714500f100001503c1c18404040e200c0c2400002074a031405000082d03480e00c551044541038404c991840c003103680e9200f0555a0b140070702450300660800c200205850401213408001c09126070b00b42c8250300c0000540e2401100070350f440e0004031b81c0360382c019410800b8214145001110848040120a40441c002841d210203030081c441a40e5999403c0c00007540c13055501a45501c00c0d00e821341d030307600300031441c0c00703064000c001e0450005080c08008180c0500102c2d1110301da0300107035500c41c00d24280b803034140081c00e10245003a06502400c000301e03142c00b00c140c0040c44445c0e00d190020421925000d8420112940203d842d07080314041141440169404103d560441409280c4a61240c48028500d410040c031880100d03803091405c5035200306039800562080e545070083c1c0940700c1c5030030061400d100340c45072820010b00303200080140741e1100403001890700851401034100d41060840703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 154266690 1250 154265440 154265459
    0x70506072d0503070f082511030a17010602010203060d08092815140906071518020906040219110304030804030510050108070f03020f0d0501021603021b010206040209040309 76
    0x40035820700c0003032030000800044a03000301c851710010050749454a8640b6081811445210031440381c80c0d1100480401d101066204068020038801c4032003e0b00c1d03503621f001740e02811480301041d00c050345145403400096114018401d4030720032a809400c8600f0b2503599a9040300c20b40c01444007580c0100039115008199603c8644d80341d00c080810800c480407418421141800e0f00c10b12112810042c285c40da420503100d0242c1030380e00003582902c03416190f1401d071a0501c100c0c80441c0030300520754680007200e40d000d201040c80c8081c0e2802940d440c142030b00ca040c28441030303120310300c8905070000c07513604d603169041d22521808050f103a0410038cc0e030420f41c07607641d41e240396405a0700544496103c2c2c106142d040c00340b88512401400710030000c0003540d103805100c0080099910010b032141040000b501400e0b00c4101000130007e0348034000711342d20864421081556818001e05500610880c140c118200907059010680e101050b0010021a511355082200c0080c00610803000c02498000021710241d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 154267940 1250 154266690 154266767
    0xb0a0f1803030f3204030509060d0209010906030501030807141e0a050c060a0f111018061118040b0612040b090c100503071d0303030c0d06050607050607 67
    0x82550041801d068020300350040d00c4070310304c20391256036042c52030b0581400d0084080028068070f2012070420790316428182d88901076004101c0d007160000032105404015503000708516034090701e40c0705c0160f8a4010443c121542404020303c1d6400400000c00401c0804c00c181c410300452201300d58114444081c50f103442c802c101051080d40c1c0c0038081100412005200003444404251261b509201106c1d1000340040c0f000000f020601040f840d0b5500321400038008000341c0c50705c0c490300340702d485c00f030800c2100c42c5a2090001d98981e80b911401c0761020b41050100c903080210060f508000d0420413080100415600400e0f540c0050108146503010b1040c01c4801c2c4600c1c00380084030414070f0200c3c0701505082d0b0201d0321034445c41024400000d400c0d0040143c90301f00c8014a8818100410020316044640d41e240c2200d07890721010041010240d00807005082081190000b840110383c0d07001404990b0095001c0140103401010018600700d04c103002040c002c40981c4891030242c0c1070071140c5501d048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 154269190 1250 154267940 154267943
    0x2060d02070507050f01020307140a080f040e130c09020a0201090b1501140a020a0f0201210c0f050702030c0d020d0602120403080c0a021509070906080604051501030b0a0f18 76
    0x1a0045103076018400c09000c0340c0010441a14000e17816001000000d44074030916500a280540240c050500c80c03d0800c140d10b0070a41c0410200e40c0c0e4000f80b4583c9001381c12500c2610044035a450008100700100244000b0300759110745801032071418005100065001800b650003107640e180d01c040c0120707014070b0105008a5020340c00c000e16020384c02c001071844002181880c0006000c010480e40e95900051041c4125005022400c00142510040f01d0401c804032155070243e403082d00700803021019500c15036440030b154030703500303004252680180d50500038444082e6042d040000040c10f181000628440031074030040081250b800155240412608810900000388030228108810150400e0b40710740c000c00c61410290a0581c5298025501c04d14a80c03210440c8400741301141c02808200040405022003d1040c02170b0741d144c105007540c0c0e0108841c19280d510940002c0c5001c8003d000c0307040e0503039402810550b02030760b42803601006401e450020b01c00d00755440e40c0403058004040005400c41e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 154270440 1250 154269190 154269217
    0x18070b0f0c060a0b0405100f0506070c09051501020d020d020307110a050a09140a020705062a0a0e0a15051e0f030103120815030a060f0204090e030409140112031b0206 73
    0x1541201803004907003004050200d01201f158051080a40309174140c81100c408480031503a640035480d0415400300142e1000303c0c0281401e061204c9100a0114202c070b86c0d20a03802c88040b000410012650355030201d04e2403001d07800401264004c5030704400080c80c50000600b01c030765881d5032000800c003a01c2d91540403041c0d503030f51400111130084101d0300c0140c106444520075030420420340c98080e225080540402039001980181000c510a800d0700345000791034090303085459010741000507003144103c481c11f51260403501c801081c814106400350203507110039074820341061490481280c40c440103980691541c0300501030320701007902e51001540a90b10a00402250b0001102c0140165002901030885c10051011048054400091405026401c0311002ca5089404d43c20100244281e400c8400c4641c101928821000800001801243d1070440d040040c400020303580c1c2c055032401e0051000c06010480c10402092044800c17418030550404111010300140e80001c1d02c541c0a040c052005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 154271690 1250 154270440 154270451
    0x5030705070608010303120c021216030e2b0807051f2016020d0605090102030610020604020102070e0402030313180c142512030b0918070b0f0c060a 65
    0xc012051100c84010091814004499415a40c02619490b00d1142d44100e05507188220740c281d40c03080011441c1240c58a1040ea81c44c0101901950745207040ba07401c0d4007103110480c1d00c5100d428000c0e4a04a1350b007514000c2e0310785a00ca040094100d054546040d520950207024000c00300c4c406200741c500703039403d007500c40d0340b0801520140b0080e42c442c840346400301c41c2802c000704442450a000c071200d041e141c16650186238214400200702d589102000b500c618a0301040083e80c280c1540118000c4904a03a070140148244008982d034400489000703005230054401004000c040d030500c280c1061000303055074148008070399a4000d102195020100b421503d41c0f413180c0c00c060798030440044842d146044410725241c82c980400034031072814403948003070340c1c600c9006240508814460b0002d5202464010306c2e001d507100200680001c0e02e05a1040f91081c0114080d8100050741c0540b142d00d03480540155072820f1411045030f00b00e00000c4507240d50401106114050501c07509210300e000702c1c0001007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 154272940 1250 154271690 154271693
    0x31b071505091506100f030f200403033507030b040c0816090e1308160609030e0a0503150c160c181404060c0e060301090f0b060a0e0d11090103050307 66
    0x5800504514040c00f070b40c00c1030b5605c19a10112000b00890141004074400c00d04031000350051010170802c605c8685221442420298104001c00c01c076070007541e03a0780d640c201c0071002e00c40744038140009031507604c91003e0b400002030594140f10f900c000a4100040d1450f842008681502d032451710420014106904004a80c050440e402103000c40742c0c03608020880c03c0906100b583e6101030015104958003a20001c10808a2002c440c146504001c9680071302d41585040009003000e840d0071000b00c1d0172030034860b18a00f0301841c1360088030401001080d081041c045c0c441d181d107501070300d43c07154414200048900802e400e02180821403180301180003040c40e0405100a0044103100e103061142005100c90790f490072010380d40d8019030400c20016040a44540c15125901698403c5070001390200002407481401e901c8a01001c00c26601404404542410022148074443c0c07a4404101028868100e80c00d16941c403040b16441403020f12502d86420000541c0f10400f603004480c0d40e44000f81c203a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 154274190 1250 154272940 154272973
    0xa0801080f030901080c0d020703020f0c0d11010e04151412070302150c012d0c0305040201080a24030f120f0e010f0302090d0804080111031b07150509 66
    0x240108010340240000c10552000c441d202d1041042081c1000800000314018003109402ca81140b900d1403011580c0c1e0560380303000783d16140c43e034154982a00070b00400080718203113002680035641d031100302c02c041e0720340b810019501e0048070480340750000e956030f1581d52000d68025030040540840070003110030001250070441c01064001c2201500e030003c080c1040145c5640d858803004400e10f120642d15420802c2b42c0c2401042180c1244091151b4090f0000106080c6417a14141980f10042401400c038038150039000d9520030b450007400a500007002903404030300b0740c0c0412030355171070002c116524a1801d00c5426006080c0d42081d140b807120b42a84400308040362001c5003207030906003440c40340081c0344240908800140080d1a05019111100d0920544660b04072442c050740186050040303021070034080855085402030308110741c0f034211040011200700d000d8a01c074010050840707803041240d102c00c21454010f43e004803a007500d004071491020a081c001c8502c2138038035800034005158040c00fa803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 154275440 1250 154274190 154274207
    0x70201020c12031024030b031f09020108090a0c060f0201090212070509060904030c030507060b120a060f27140d030506040b04020316110c13023f1e010b0a 68
    0x296140d041e500c545c440c409900211110450313160900040f0306886070042030900013510a088180d210700c05032044c130704010703900150200c1c2c004c3c2d030741804556440c210750350340e41108e0f0405085466422400c1165a1141a80341080c0f00c039840082010003642c1c1c042003c90740c091741d12200b1600030850910072410142000307648070504403000070141c24542c5014080c018440d002800300100041c00109005990704040b202d0701e405010301034150340705207a554403880200012544035050001229414000340114a10420ba55071140202c2d01c0810341c42c1498203010b1002c40d40040c1d00c014032a8082c02c14010580b2558441e00c0c041142d150950400003100e10305044584624814824031842d8400ca003411a809042420000c5090400301a020703e07004045140030f074000301003060202e0f10410394000d01284084160905080c00c080d030382c64a0410a02c0b90f80d03031980f1072460540043c0d00315410080f074201d02c00070305580e0420803218407001101402d030480300a503100060403a005d5036000e01403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 154276690 1250 154275440 154275449
    0xd270308160509150f07020627010e0109170f010c080106090b070f0f21020d0e0406050306040326010312020c15160804080d0908070e070206010e070201020c120310 72
    0x100e0300c1c02400800241107500ca001c1110071030000496004805181002214007564000f080c00d52900069803886500303000001444101c0e80c0342680c072722081e50049800f84d0301440140c403041200c504007030041180002c8005085200d00c41d880d1400c1c4030b200284680c115030915943c825040750b0411902030060f03030f000d40c08000c1c204810030034000440c10a26080d00c103241d00626010100c0380034100742c22038082004040042c401c00724035155140303800140202503d1810385500c25006078030740030042100d0140c41402c0e01500010009030000344950318286007046520958101c9103a080417100140a0980085801c01e45c43c2441010003901009194180c007800c481c50198031180400c0c0e54210b001e411402c20010070404411020011070005841c0a042020708469048074110f80c01407a0b511a845800c3d028000c4043c08146020481111031041c0c0f4681c0040c1016483c2116403915a0402403001003107540c00d00881c000171a040c0f01c40c103100510041e40a44a0a02c50341105650005621 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 154277940 1250 154276690 154276697
    0x1c320708070608010501080603030c070608060a05040b0a0e10090501030b01050411090a090e030403050a08041d0c0306010f0e0306070f02010b120a06050402010e090906010303030b010c02060d27030816 88
    0x1002c10000742c1c0441d103241501c00c203103818441601d40c0008289180680c1c0500c7d421402240c9001c41c40e9540100e0b194455101180c1805050fa0b80f1030500c001ca40412400d990007800940f000e2128070500d40046402041008030354100c103680d40300b01c0c81214403c1c0c00886998200701d004026071301d054003648503d00c8402d1714251902039400c1c0050301020243c801c0c0300341c181d00c4030b040c124003500078802d80340115084020348030720401c1c034a042c0b1000c4e88280281451000a184401501000e00c140540700d01d280d0740030702d440c54540c0001925828951200c420802c03c4400303441c02d4a44050001c4d500600d000d403605405480511800f0342541d400b600700c00d000e07680022020801840000f1400f00ca030344c01c817400107040d40b1103000403203401c0c0b034800d070b20ba400401131010300c41c803e24002075040c100e034000c3e40c0c1001440d4200740111000764403c1e4000c2e51122050244564154040d0700090a001d8000c1c0440e080d8600d42d07640c0c0c4d0110188176000d41c042124541003025080346882d5a4406890914 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 154279190 1250 154277940 154277953
    0x40f0203060d111f05041503090804060819180201090806070c02040f020c0106060f0e0f0904080a0915030f18050303010303080c090a14130504021c320708 68
    0xc01050032076420150141c6541c000900e002c0c000d44860144c10101040421034080d0700c1c0c0d810401501c5980a48612001c442c400720310508540d10a215071544583c2c44514507103818500b14040350f0011000d050002c0d0030202d041840c0d4004480d21958840804d4003e030502540800c0c0005400c0300b078594480005a0080c0302046001c56109d038880542030350456000904100b003e4803100240640d0518034419841d0000209995401000b541000d90455845c0300001199109000101d008004000c4d003144a41022900041880e8094201400b1901e80180c42503070350a0019880502000b040000c00d64401644540342001c0c02207210403d083c00c00320003608070383d80c0c5807662440148006401c21000d034020941a1b050002129100c440c018070310492143c482103940c4410a6480c4107522500d45086421580705a40c082d581c4540d40050004d00c02d08500c91356521070101d20312085900703d54181b002021448120015801540c104140780c100384035085d9914500740d125005020300e9030005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 154280440 1250 154279190 154279201
    0xf0b030c0f10020109020d0b01030b091c030c05070c0b040f0807030506041209080d021b010305070e010e06090402070503090a0816050f010c060f0b0a0504020c120912060f06040f0203 80
    0x5080707468024509640040d4501c0c41a01c04a004103064100254410740d035020720320500800c4100e16058030300641e01101c0030746902103003907034070100f03480001841c074030f110101d0305020b02950250b480c00b010340c1402840c1901640d2202011242e94006007110780300400d081c0f04907003011440202030800ca1006040d1141951541d0342e0305c2074000c1005003070590240210002520030102c5c1002086104116514854003d001079100c506100c0c0b0142481480d0010342c659611a000d038500a003019202c10340409420001140d19143c1004080d0300008100036003000303600c441c40281a50350081e00a036440300700325010441c0d8142d03d81e1213080180d00840407822401e8001c2100e00c212802141e26004200b4941c006a91404150001618040c07512002c0c40d81072519402c070025922080fa07152290b04e407103c08100c124041e2880107581544112400550301c0c00030401007001070001000198449440c025007490080222030050f09001c419091103518103150241440f181a01c0c0010b60562401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 154281690 1250 154280440 154280449
    0x1020c0304090213030f06090201020127060e0304180608071a03011403010b0607050105091606050d050603121c111213020112020313021201020408030f030a1e0f0b030c 74
    0x25800740c00410b6a0000f541c441075500ca01902004540c0542d00c40b242c041c050521500801410301c041c0c1c05075003800c003807248030043c403030f015556401440448103503c0490707115500109028032240707644d0300c070800000c030300210701c2408088100309200c00441e1550800d01c44906056684d0300130342c06410003032500e0101c01c030302400b0b69066841501c081c0e0b01d01000b06002034007410039011110340201e40017400034140001074200500c01d030004403c89039214500107000691007554460400002c4050159012450b010340160b41c00500040403110011452140002c0c164420302a9088043c424101d0b547c0611070f6000d0140d001d0303110344080741424500300082002d43e00c000d0900c0400491001c400301107a0060480c1168050b080604540f2458181401395840d400b69106034450310f210100003803240414021030b010343d41a880554105516040d0348406600082d00311107203d6124240698101c2c9810070907a12101c410b1004030700e508898042c14200c0b128520298040d82100c641d0f180c59403607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 154282940 1250 154281690 154281697
    0xc070519030c080d0c080c0304030209100311150901031a0a0b03010e101409041b030b0702010605030a051b01020a060507020c0901140d030f0c06060b0408060c0309190305071509050c010201020c03 86
    0xc1000784195182c7c1003500705800c41c41582c2009602004d440e05100480c01040003440c1130f20b215902c801c40302845941040a28145d9074101c0103403503c01c0120854552007504922150840d820085240c1040300340019007c0103207800c01c409000c4044010441590f850900741e8000b00e86040c1221181e060110302d0504056600c582400b034000080032400300000710a04131000403030119289042d54591900c01c810030016502a40150f08024000c2081e00d0045014180c00740e11000401c10140700003018421054040c45103415806401c0411000c64018010148a030b0000c1c0d0203040305c0700c0d1480400034141c4040c1c10603140440d011074069210345410742070811440e05820981d844041c0100d04072140644924014416810304200060001c0c6020240083c0c4207514180c9030360743c1c0c1e8141d0820311800704aa07000ca00303501861901c00d41c000c2c403203960031640c0e000e0b20b0700c075281048945502600340001c40c0d00401c829615031606083c0401031040c501554002d2009526010240354096641d01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 154284190 1250 154282940 154282943
    0x3060f0f0308070804050306150307090c08010504090602120c03070807053105040212010302040c08090a08070204150806090c01091401031a03010c02060f091903050c070519030c080d0c 81
    0x14000f8031502030215078015100108070003001c0340c403503292003018003060380d000d000014068401d4450100302210180500b0320130b06040c3d075035034010b6840c000c10030000d030035840c00580c0c08650801c00507040a89100d40d40f4868043d41003510303660b0403d02001442d85d48020190310800405006d05a1081c003061081034101c104418032900d10904000b25903a4441035030b00482c1d2261000940006540c040750296048138002c650400410407a002c00380c42101c012076050302c0325004034002d00000f40b0720350b01a0080328005480080d0010b812450801c00c0c0100390002c11441e4050b400f007054072801005500c0c0006020301e000c8140518014613054041079003034920341455200c4000c6848500340c040c11140241008001348040250918040d485d0030b02a0341010610f54001c000540007000041c90103110103111984400d44501502d0448994011003206501402542000966070361020081c82c200000400617469040c40c0d481c0100b4200342c0c65110504541018501000d01f50704110014800c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 154285440 1250 154284190 154284203
    0x623070308060609120d030f05060a0305030417032205030f0c0603160c1704080d090506030105010c0312050f0a180b04020d0c0b0a030501061209020a0b0c0708120a03060f0f03 77
    0x258400c00c0042d0038600e00c204542021b2081540321501250b064014000460000303004100d03985601d020300440400030b000c05007080c1e000704820030640294080c9081c400d451013041c0c034107003000d450700a000d8104800200303003403107943c40c13050095140a003c0705d150800700d03c006129501c2e0b15400b0940b107002c010328800c070b484100450145801d018082c4907035000e07807000c074040e4652642e0045415a41250081c103035180b00785444254094011030fa01401d580d0001c10103070640c2e1a100044405000d1898100c0070003c4031205500107816900540340105a107269550040c94010b081343d00302d80c40c02c03d00d5201143c5001c0c4035404159190009600f182c1c043e0f035804d0110326a410102480d6010340e100c4030001c00c000070500c40c0960f040d480203060314029912001c0c0000842e03400c03001c2e03600d141400796000c12100c0d01003154100301c0c0014505901c04c02c0a407003850f6a00c04415081c40724606180c0c09a41c0d00056140d508c9501d1300c2100301821700801c00f8041e41e8200f900d41480c00780b150000901c0c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 154286690 1250 154285440 154285447
    0x105151302070816060501081203010b16140a031d0603060411070b01090e06010f060e01230406090e0108030406140a050d0501080c040e030301060507060b0a0f06230703080606 77
    0x64500398048075a81d541001043e0350f901d582e20384d1030741d0540340036405449403490302002142d0701c00702041c007040725040e031000c0a041d83d0a0462040407a0f10806c018104c80031040c2d10040040c102c480808a00403c1f0409004a00a513050140c440d09200107002c0d1400c05d00100d0410780e0b0383c1d90003035940040040e00e00145600d0840c0003d043c0303200300303140078094800c0c240c000150260315402c20810800c00505848807640d86079010a00f101c458011200440e14a00d851205075110700718401d015901061160b01031580c0100400d45a40150070980010f841091309014003884e10302c84e6401001c000300118940f034544140208007031860310784002c080400050124000c0c0c800c00c02d5454080c0b95140070000307540e441200550300c03803c20100e503001e181442032200d000200841624100c801c0c54403a40d10b085419034600b0010704000403a260b108121400219265401c0c150746405446541c460760310070b210901d044645035a50b860b820040d1a410080c1400180c0c1c0705140f2a004041551038a0320b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 154287940 1250 154286690 154286719
    0x906060c080913020c03071104090b01090c090509090c030f07080c0603181603050c0409201305090d1b080703120207170a090801090209040f150203040305040501030b03010515 77
    0x50808040d83c2c480b01450001c034104200314030110082045034865640c4a4013680718005000a4610300080900030841803401080480e9590b08001c00a40300c900d000e054068681002480300003042c0d84086d040c0d0301600809001d4242003180c10010200103000f00300e01031501c000140d80c0d50700c0e6603080f4011b50010002c10303029607038094031070601c05000c0180d5485840806a101c0b90042e00c0c80103440d80d101d4010203004078249442190211608401d03c0e4042150850040700e9002102a109412802d15041068000705500c91103020b02c501030060b012903101032000420300081c180c0341c0b0010308807400d04030780010340c54000c5901980e03040c03c006103101c003200c00e090300a0003821805420146483c214401403c82c0c1001000174001d0f0740c9a40d042562100121402c0303a601031002174103ca14140481c2c0440c40750400030419a220b03000004401072124110000e98000307071821008200082002d22096826000c0c3e14945401940200540e2400c0000c445101c0117407002c550054000c0c012009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 154289190 1250 154287940 154287949
    0x50d02210a23070807020f18040b06030c0d050705100f021005040f211103120c030603070f061815020606040b010306120f110603040302120a0c2405010906060c0809 72
    0x10400840301c10792512400541031459181d0700c2548206e2107041c284441d040c0500c3c0c66400714241c00d1038405098010380e10b2b591000d8503620080d14403641886408001c50450342c1b00d41c05004020f106801601ca0a8a0403082c889414100c02c540d105000d01000071010305607000a0821500d01c12030000b00300780d2034500f0910700040d801c8001410310403154400000400d00b20507000724170030b0541c0d5002d202e2061040c440380c5a004442400202404050104000202e00e1000d0342d040240101912081c941c1c6414070301c00140507600003008206008001e86200030324440d880000d040502f001002d04229000080d2500c0005118521940d07446140c864244d1096000750050714101029114000a500700360500e10443d8400f1100e255a104054859040c190107a9001d01d030305800800001d000303080410140d4004404800c100160850800082a800d444400841103041000c4100080c004c03200300903600140c00200c0203608040d4100002984070022240d0fa9402940841d189c04a00c00004d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 154290440 1250 154289190 154289237
    0xe0102030c030703151715060a0b0a03050c0d0c0c06050709050108070f17010603060f0b12040b13051005090f0601060905060d021209010605090709060c0b04020607020409050d02210a 80
    0x802c12901e50741c1c0c80310708244001a840d0060051f060400ea9070340c0d5160401603c1100c0d030003405400f030000d01240401a0094011580080152200314181107010681400300c80075103070103e0025141070494814861a8415035810100c0c0c0d2070002440750510002800003d8080c10f1881002042c007407035103080e8820002c0c4210700300800050046965070300001805070199000328200503003441c00000340c103018402280e550412920032000d1641c1e4640701c2c9281200300800d02103500714800c01c0d2100140b4184800c42c90301445910005944c1400072119150095140c40d24481f84c0c00386c001070003020b4125405104840003129991340e5080c1d450291806030090512040c110b090b0701052250011041d040300d009e1790070a89a06540c0d580c0c8042c1284c7d40385e000c3c0300322004503210350494004103020064440d03210740064507152405806501140840e459040700340c4654009070740c0c15800313a50501500c08011550681e039414240c4d030038415a404d11a050f5507100b40900f003518040c1e07a04603007811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 154291690 1250 154290440 154290449
    0x7031109011407021f020f0102040e130c08010509030d0e0a1502130f030b09010e0615010507060204080303071d060a020c0904020f0a0305010603030801050103020c0318220207060e0102030c03070315 87
    0x1709a03001034004c102e04d0400f40d0412001c025001d80c0c510205080c005109480c11260880c00e201c880d070321260f0500c030514880f000c05403003000c410840854116024000c1138007035445000199613411491012004403404459002c01c1d58010352108408104200303034010200d00a03032001070361481d1000d0442144034440c2d1002c1c1d8080c00080001040c016501c500d540b05040020003886600440c845440d1100b600b1140d411440110a515105552080001d812854856500146095201c0340040d2860b0011114400000c44a00b070300c0d0850030610441c0120258151240343c10440c14040c040c3d00d90500036443c40c05000c80200007025980c50100b29002c2200140c4046066030301c2e400c0c914081c00b100c1c0000d80100381c504000240a5100b442201e000e0440a0003550a0050004264824000c0e81c250550311460401e06e00707034250176020070034500700d141d02c00050f07580c072841c940f11f010303180380601c1c540700c0742d10500030840081c40c1d0301c00f02ea0744460716180c00200740342c0c04005c040074100300707402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 154292940 1250 154291690 154291699
    0x412200411042c01060c050a06020f090102070b18041e0e0f150f04141002030c040905090706080c0a0909020a0801050f0f061e091905090703110901140702 68
    0x20007800c5034411002030040c3ca00344400d248107070300300c16107101a0024540010740c540f0803003c0100440c5200700c02403900180728009461044620b0b883d10030581e0000042e810009000040503002c80d80c040041c140140306405070a03050603065075074024800514494240140d407150120000400201c02d1204010f660400400c41c444041c010241e40340c52244c0622240e1280d480189010500e000101c1c3c82032030306048507656541c0b1581c801c3e040c240c0d0001403240a00c500542d00c0300b0200a400950b220390081010241c071a8508000c40c82a9000035042072515004461300f4801b1a40c00408994004401d00401d96140236013107040343c5009080d40716492107480802c2e07001807587e0101030b0364101c071012203128101c000180100508400c0c40b61626a02240810010710940c9440300125071500800b10000d050035a544040b803075100014070b03844000032080e1400e005c80c0c034001c2c0096800107070a180400901350510752200e010312481c000d903414410a07100c5038040c14020012a500c1683c041d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 154294190 1250 154292940 154292951
    0xc070803030c03011e150e13050403120c08010b041712180a270c020106350303070e0f04020403020415030308070516060509070b07110307060504122004 67
    0x80c68019507400038044c034490007081c06503031424124140340c16402d0702e8072000704451012102c001a10412404040150040c2c030004000c02318540d640f244600c02c0c1e001b6207601100122000840741125032106001d82400320341401071090382c213807000b602d0694001c1041c4801d0180c60324030305450f218400080c402c1421000490f40004103400380901422034068506054282d1121240041c441c51540b507103421001c11074540034581c2003908512819a080c0c00002881619080b070700b000040420150704090708219001210304502400c00140d00441802a41c10341c20120380040800100030b00162142d80c44407205580740d50795504440003147e0040041140c2e000c0684d0b0781c03461116034441a000714080b0303c0000d8500b1b00890071151001c03003d08552003110400e540f1071001303107405040d10303025100307806001c120916002c1c010312085c1d00500d031102c09410544101850141c035030304400200720042c40104010034007058601c80090703010a01d84141c00380743c1c81900a2a1500c0c0400f5070060914 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 154295440 1250 154294190 154294201
    0x7030b010f05130b010e010309020f0307081e0d080117011b03140f10030206070602040e10080d02070f21020301020f09010e0904050a020d050a0b0a060e0604090b0c0c07080303 77
    0x100114115102903591022895110400c101114100c01000340446d02c1c22139000c0e880d611075071004003002c0c401051511424203040220b49408540c1d0462620744d440001a074040a100f50003904000141c0801800c48942c10100101000c0c818890410019104200104910030a401509001946942c112007040102100802800000b001c40f0704218201021503100826046018070030303607410201c501200d1959017030040940c000345040d140d480d424400860300780004078095000e040c0f4881ca0800d06404d200000d404c4c00d00080c466820741d84809010445144129081c000316101580605d6002d0b113a090f056070380d4004c6070402545540300154000bd1808e8010250a80e201e085ea035581806e8000b006100010340c0585014040f40c1c003030401e030001880c103001d10042d5244100240c46528407036a40d514080c00d0b0595080f4100c076110081840040480c85401e43c0c042c004a80a0200385d081d074690700c4200c4005020304141301400120380c014484100507000c0100042e4040b40d94a10f002c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 154296690 1250 154295440 154295459
    0x20d090c0302010314060319030201020d0606050c10090f0f0f0210081501050c03071202032205010e0301050709090b03070506030408280806040c0c08070b0403020d0201150b03070207030b01 83
    0x1070108a000c80d00c1d0120407508000d0300109148918006030040081c00d40300890b00d8444c200340d2074100c0442d0b40800c6000d004000724000c510091103503444103a10381315a14030a03820b00303107005134090130303e0715002c19280401c0408000050040d00015520083c02880c10204044c404a02000c1c3d00310050300441c3c007441c0e9201e0b684910401803001294400203c0e07100445071440303003045940556105120307000c04107a0f41030340c64401c81c0180c0102c0e413400c5020b900c060186000400c440c54584003480d0108090b503006041c4009840046008020314940054068800e154a014400300d26039201c00b0441c02e41c9080003440003030b09000340441d440345000c1c505100e00782c2c0309171019450013080c404291000365070042440d898840315140c14074140da0310ba052000034010000c9440401c8002d81d01040030a504200400c4241d018850707880791450203040103850200301e039603035208580c50440c0750324403001c5410b40036007030301e0035040005e64903100c0301801c9140c4409900080d010151010000681101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 154297940 1250 154296690 154296713
    0x30c03081b0c1b040c050921070f0806060a030201051909080a060e1203090607110c04021b0625030b03030c031207090504020a090603020705070b16030305010b0c0c0d06020d09 77
    0xf41020382d660485501c4180020b5031403030440840466014081481e0600e090030125140310b150b60b0b00e1000400c40840f03424901540c0d640000700c1c0140f0f40c482800181c1c0d0030300c0110b60100d420f0340c0121000b4510f5000070140c1c030030480812109069004803458003441900504014295842103522110150a005004142586c55980c1c10b2041c95031401c40c840b1904140d07446150b171a00035001654480405548182e960420000d607806403030394084441e51144050245062401103149a452420035158585407010b0030401c09030b0151154880560f00600c1401d48d1040b40c0e15000ca403c400ca48082443c50042040150712400041807400d0a141e8410302030740f142443d41c0c2c4503214944e680c0103010803480781207210000a059000706001050107600103140f024071941c00c599080c1c1e0781d038101c45451740220b070102120030186e500501c18941d1501030b19003d0480405050715185801c200706a480001002040c01041094007040610601e0f0f4181c0e03100d044400401d0000c1c29141c600b403600c482c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 154299190 1250 154297940 154297963
    0x150a0906260a030e0607060b030a0308041101080103111302040f03080909010e060108041103150a050612070f09050403050c10050109180c06050d0e03040b0403120c030c03081b0c 78
    0x4441000030800c4040000d42c0010403505901d8401074442e015042c0005640900e006644203500d42100c0b0005880c10004014180d01a655150701030905140401c2e00d802801c003e6410400a81300620200d030009008803040f0344211a80c07900c158a5100300b1000c0d016903808118402010a0000180300300300004080e004000c0b50500500d0380c80b195143d070050300a991203400074a0203000100044c00402c50b841c14150020216440904150051940b0500460300100c409031208140034140c148510707000341c2900408060724200e0b01b082960140c00040d80315031248a500d84e4081800d0600a034215081c0c103101900340c5810f4031041e443d0304040c20b42840360200861402000407800e100c00451600d80c1540040740311001880c0410460355030700300e620501c2303106640300340d00780c1c8640c02040104028060140e074152940d01d1401e00880d03c103619507614061080340325820340066400483e6203200380c4c0c10f0503d40601c4c1c8985409402d00c1e9101340054071090000600c840726110001590701005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 154300440 1250 154299190 154299239
    0x10020c01050f0114100e10120c05091f050c0f010905060114130c020c030a050c1f08070f17070201050f0a060b0d0504080702090c0304140c0108150a0906 67
    0x1901c607800c25100b60381003442180307681601c0503a07075450f13481d01e43c0091180710b0a910b010324a44892400040c64025504d5280c1b02081c03d02c0680800020940124000d0506c6820700368240840c14020400c14251a180300320100301e00c00070184120b000f8005e031030300b400802c000c5506420303d68480b18000c0c00070b20011f595038454500006501d1031040703851258500c012b000c10072000303804900c81019101681c010015405044620411500e003040000c040d107004000800302d5a4021040c00040310341131421007842c5410410000a840d00f00880743e030448410318084411302900f24080740c0300169071805000c0300900105100307440342e05400c45070041f008103459001f1511081ca003c41150100d103e5041543e6060151403207201155002e40d074090300460034203240070780b40e81c0055048031003200c41d241c9030b03e000b0091005100740002040d041030680001008050310b4540040c00d5420024680c010b00301101d40c480e121502c0e030032603400c001c000f09007041c000740d0384450310049001c0040b1620404ea = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 154301690 1250 154300440 154300451
    0xf080703020a1502040501120221090c0f03010902010207060c151506020d091410030b030a030306170105100b0904090b0c0c210307050f120f06100305070e041d10020c01 74
    0x601c210303011290161280c000c0c50b030354800e003231029400690790350b200c10304201d090041c0c44280c00c01e010302c034204810140c40030111840400c980360186242d9280240c0c98845800010f0760009804415a030540c00c24140c0250140f07424080003044410b450f041c0c505040c9800203a92200444a081d2910b903001e03105643d40003041128066054810544800c0b040400000c1605146d045c150090b94289008a51881030401003468107020700c000702d000030364500e005c000241541c01201d00a1901500902007810400c400311846c4a90340543c40200c8400203150030160f84581c80a294640c1c000850340091409420168080c0c01c01c0040d01024045d1022541280d1840418070142688850301c050950302c4c1c03104100c60030f80280c0c0c0c10100c00c0d1805c0004a640b8000da1b00394501c10800f107515984c81e4681181030000100310810b001050600340703070600070229089140240c5104060b9030000b00e09485114108101a040e1902e132624080c01400303c804140b1782e0010301015040740000d016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 154302940 1250 154301690 154301723
    0x3040b04020324040c1e171018050706140d0513051515100816030902030718060b0403020904141c021006060f0203030424020315031e12070f080703020a 67
    0x11b48980b03102c410348580300c0985042c482900c02a105040340b01c2c20404442c08546201448011100d8444d6041c02e095140240f840811404021500241085203851120070b003040c041001980036240342c1134038464907000000d25442401e4007211071960043c2c00c4403403c000c00900d01b50081c4040c1d60a0103902404024041c0c0c5040c00b0326090062010f41c0e1b01e58a840c0e03a0501c034070048803115041c4508040d2540d10300780240e501006110090300a141002d45d600d10030107848000c564480d0300164a151081c042000503036140d0300500c1e40710342c12244001454401c41841d904124010036280c0c3c541840c000322600d92540000d540399141d2403950f08105039922018141c604d030040c00002c0c0c00503482000014001815103c04505d0740403450b55948992611600420603600200c900d410800382002d103070308039850104040783c4810598000c0c0e80111110054082c0c50700440c0644600c500c90015500041100d51040000b41c00e8002c104281c442c20680b40094903031021460582e10101204000007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 154304190 1250 154302940 154302959
    0x50102010b010219080c03030c0a0306050d030c0f111002100e0a050a15020c0d0302030a150312050702120106030803100812030109050c09031b01110303060603040b04020324040c 78
    0xc05600c4143c0042015a40010141413900070010080781c2010f418882020104800c0010314000c03480e4014060b1141106030000f42255000d0740818800d4407031900c80c5c00466003244c00300e14400d803c5000340b040c0555904141070084a15401541c000e1049894018019408151140e044072052414071011220b007020700d03944e01a640c400f4200350820880e0720b0004a905446000b020490b11026040c441d080d074a0900b011802000300000c0385e000010001c40c24140e100301444400803408100d016415512002d060540c0020140103124000451100390b40d02c5615858103020030000a20100e1345030300c1c207013450f50400d4034080e02121900e03c01044101011840c0300061145181d241e0641c1c0c030304440000a801c1c0035105003500c100030042c130b441c580c8040c421044484440004a000440304000050008610021456840e001401845174560798103040780d80164000ca010143e5031a903000090521101c552034038103200500d003035540f00c480d41d501881d10450080d400c0301e1300d00e9a00c50414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 154305440 1250 154304190 154304201
    0x30c0405190507140712090803031b0a090e090a060b031b0607061d0d201b03012304020319110d06060b0a032c07060f0201110316020705010201 63
    0x14000c815008440d40703a80756441e40a96840905880c1c4800306060b07000d00a206030b03014010641d000314a1000d08503030145c1207008100101a510700640ca1031900303103c4042010b040b040c107031070603080c0003d1807034507144540401c0d0007808082807000414240b0717418080e500c488107002110a41c4c03c1011090240ca00850b02c0d02103116007441e10321912012404000e1560700c031081c00c503143c0d0390310171114038140e140720b6128100d9000030009000701c10000300058110301d8000c1401803884804a50016a10000b0841c0310702900046500040500a00002405485a1640100042003403420381c10640a141400c1c0d000741c4c029800d440542c9012001d20b940300041090280c103a1002c100124040e080130341c00f05001e907029100c00500d01d500c4100c100c030190301c031040000010751210b020b44004104248003501540c095604561038805400040340c41d58214850641030184461403442164003e4200803c0fa24865149507544d14000c02d0310121400303c0c4800800500c11002c0c0400e1950052050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 154306690 1250 154305440 154305451
    0x3030702090103030e04021204030c02010824131b0c0c0e060901030206093601050904032c06030408040806090601031e0c09050921040612050601030e100506030c0405 73
    0x7848210781c00c641382500d2aa011341c0b421504664200040e298142202030000c0c040d603c039540340c01c400003850000410303c1201600d018104c1e60310190b828202c010140f000c1075144000d40c2c1c401704820301c01c2d10160081018200e0000103139008041002c036198402c1000b100c481c40342080000d482c0e2030b8803060107980c03030486099400c850042c00510152810001400e01030500405110b03a83c103000d50440c0900b580440400b000740d908a0603494060300d14150a805414260707011109881c082e20014016480c4442c882c0d40080030406140500b0450140070403001d00c007500080d03403402e040c923061080c2da110b0301c54040980201c00200c1e16524000c16414103d98201d4165102c440f100450203160240e0740d401200c0e1607140c52740000c0d802d01700e4084c0f50711440d00600644994894030f9440c1e100e801c00c1a44003101ca03402008140109a00b107600c1d08004103502c2c4000806688440c0182c004000c0d58540040520a5201a95004041fa00210300c501416402d03a07550001c541e080c0701c02d89000751355 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 154307940 1250 154306690 154306699
    0x31308060c0f0f071b030605180609030d0b0a0f0f0504050703020307090513020c0109080304050606010903050d080a1d010f0f090305040b03090c1201050403080105011409090402031e030c0c03030702 87
    0x40d10f920840c010003400c3c4c0781d4003a41080c1034118400604880002c1154011500643c83e2020049108030140e4044002004000071b44581d15001483c0ba860703120750f4864446140c3c0e20b050b4501c0c5500c8041404015005034000b40440c503466001251441e02c480c41100d22640c10200020000c80c03090081c2c90152a0702d461b405030325414902000044d40d2155040b15002c4d0342448690540b0200b4000d0508580c0940e4806a490800d4100581090001040b881c18002c001504000090b030024010051901d107241c6180c41d40c0300c00f68508081e102617140c7c40700e1820032405441803804107507c0ce12804010f0001045004240034202007900c10012000c2c01058003803101f003102140c00d030001d603400040b4900340d540b003061800004503c00a01d0301400c0c00d90307648204101c201500090807902414003421b200d0030b07c88050700b1024552040c40b012074040c1075050041001c40d2002c1065035190b141001951084101c202180caa07a80c0055510107900c0c81002041e0702d160401004507003801d40c000c0d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 154309190 1250 154307940 154307947
    0x315091b0102150612011d0705030105061018030f0809040b010306140103020309030d061e0602060c040b0702040902150d110a2304080d05040302010314010e150f03031308060c0f 78
    0x1070101c108400c020b1030140c02c417031500c030341c0001c2c490284620000d412040b02c00c9444510050b409078502001a04013600aa00d03202c144000f9664440210034800b03401d2038500c20029040000244010240e84010070078004801a4400c0141d150040c3c81a5801940c04001d2068160011419101580310b009031100c0050011f01065100342c00955000d41d84404481c50911000420001c0b01c0d82a4450060080182050002039281c01c0341603005220904c02002d540c00c0c1042d06171124400e5219100b4030340340020f44c40c802c540305c681001d1611a0018a58914403a0f403046804495100d842201c248030f141c11452400f01102030b0603900300b40e0403581c83c61860404201ca141d841d1803032054003100c00b07409100000e0f00502c03c01c4003072200e00041e5100350701e940c40c41c4005400d60301c04051000d0201d41030001440390301c0540c007120703a0004036041074054501c010b101281c00200320a01490301804001500c0c000c02c1100814101100e100c007048402030b5030342d0036491710517000d00c1d84801602c11082 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 154310440 1250 154309190 154309213
    0x11d010317070309050a0f1e05030303131a0a0608070504140703051e100f050913020603071205040803010e010b03100608150405090606011808120304110315091b0102 73
    0x1c0098019584039040145580ea04e9800060034012907911440d20088541018846100b240d000381c025078145c1d0312800f000c6824100082c0d164000145580c103481c0500e940c000a02040c0303000b03002c0440c3c0c0b03540f90002d142040d0034080b0180c031842c007500c546403040b140e0019042c201031041224090000102c000341c3d45804504030050130001d0300344501d014400c03d5044000340010710160162103800001d081c41482c11681d41c294280075800036100f2610034003000942c4002c83c4000030429811200f4598a0743c4007001600e07079110b5100c090100b1440c0030204010030160200650607140a08954003e40c0c1c0c0c1c5202100540c4821241c800243c1420342c820403089004800c41d41d080f005031015035030420752101c0414220f802c11162903080c1e80c00130003400f41c40d50704a0300c0b0021200d410949205100e0400144990700c001200c404406524000001400d00c01a0b000030304160070010142e44044001010140c4066010340d401902c501542d403004c0d04c0b41c820182c0c00410a20f040e0003425800b01407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 154311690 1250 154310440 154310483
    0x3180b0411060c031801120b090412020736090c0e070905040c0806041a010504140415031a01060e090c160b0a06030b0c030709051216060503011d0103 66
    0x7501010750000b50900520001890500180240e681c00f08203500440100b0000141ba040803080300718801850885020035a03107400e00b80b035038015000055001d40c1040d13107800b03c3c600b02040e40141d07a1070740c0c0c0c0d8a48050900c2000e4001c40800c010032b0500b504103d0221604040b80c00701580100300002c0d00004200c0180042e00c80c5078000ca9a0810000c8680e5031800b02d03060354401d6985200103240e403000c103c3c02d460f0a2142d14401c041044801400e10702400001c0c12134422030155080c0d8604040c0d03030310916520340e00903980d0700300300d218008011a41ea00e051844032111404c62107041e441c000011a502e84071382c18852171844001c2c000a0b880d100c0040c100c1e1607a018502c02c10314170212054090114401015040c00b8115101001800503c1c0d03040030709803141c018150340c4020700200280080e1682c00001c0320103895007100c51220701031103108094030342801180d405258101410001803a01c1d04a40550b04880440341519420070000e10b0000c025082400700812a0305080510781c40f1100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 154312940 1250 154311690 154311713
    0xe010f020c060a050d140702060a0f0e0706020618010b01090b0f0904060b04050109090203040203060a0c090305060a200c0a06020f070605090a110303040303020a030f2601030303180b04 81
    0x41401500c010a40728030108038903610100031203010510005000018403400d03c203c1d00c200940c0c0300340d5011030a09a000a48542c0050701003618140c8a0780c03c0300902c49c4503885a0300070044103040b5580180d0311200691103d208a407100364502c0e603041902810030741801403075a02c000507510103205504088081509030070100c00750100c4035051100300c5140d1101d105144c09001d40c030700f42c43d48071840d000c001007000b07150782c00904840303005009010042c1c0300040c28030b8201c069003c0100d261146264211241629540042c15512070070041c402401c96035441042c180c05a080c41904840c800c1d00c050060344240c0c505481e01c0da0000344d10380080344140d8094601c0098400d0070364500202038413244203070341c01503940c09070a030002e404400404c40f0b21900e45a01280650155041c00d140d910b01a441e0708001902809008414440e000c000b44504185040301130f00c02030801c03802081c5170441e0f0710490f00340411004a841c0c141a014100381c180920035243c1d5000306401c0585d916551180683d42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 154314190 1250 154312940 154312967
    0x23040608250e03010c02071802090303120403030f050711030711040f110306040b0103060f0b0c1005010303030b01020607030e0309010c0507121b1509030605180d02030a090b09010e01 80
    0x1041d0448405000414500034411034896940307020308006224201801c4898540001095500c0100d003001042d0030080c4504090458400058913099000003182c110f01c1491820b41030854000104020903030168000401888820002c004958a010060f103004030211641070103030b40b003441004000b40c03000000411010024101140903c10b5901da24280c03009695116441c00d40803040249600b01403041844a9038246400d0280798641030341c140c08406a40504040000001440320030041c040101040301c10110404120641e580d0800030700910000c20018014042c2c0e20118120078800e0080030542c00501e00510b140c401030400555080c034403034804540c2c84c01034450000f40019500a0480c1d0039004610310035110080806103c0742e04003a4102d00f2040006550407140c5941c03000d2803409495006800084039207075401c4d04982007500414404a521070340740c04064099010028220501043d100e4100864450500344194000d209401e40002d5031b825100d6110342c442c01054000b01c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 154315440 1250 154314190 154314211
    0x20301140f0c39031303030e0a030206090d030903020d120e090601051602011407050f100905030702040504080d1a040b010305090a24020c030a091d010b0c0312150123040608 76
    0x285243c2881c2c500b503400900e09032032503c1d454201001455000111260100002c0351258911415580041c0c114050007181c1800344004020001c1050300a4518001544c0c000780070500f40c2c0183d01d80803a0484240075407a0000302c110b03e5442d410b081c40104140140e4050b1145402c00c454044a04a6001100002c0c0d04208501304501c165180610082c11018002c0380034040b030f002101c00031071412611380020000e0b181380c46070300c4011903004819a100c0540c104c034041140d45840c100030805010342968817080c0ba00e00300202195041c10040941d280209031001d00682d082c420054003190301c00c86009005811403174404001480884407540141045426400c1c603405003425807080360051101095140d200180000041e80c2111442000b001c3c0d41000c1c60b898180c0050060074548103100d400c264140200e440c1000c081e05005179004001d0307000c1181094505903d07414060482c1041d0903012408002c00c101010109040c0d1000c10100200346505e4a4034000040303980500042420441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 154316546 1106 154315440 154315537
    0xc03071203021507121b030c05090310051b0a0903050c06030702031b0c0411040f0504020c060c07020103021201032301051003030509040207020301140f0c 68
    0x5034540301145080f00c3e155180295403000c01c0d0055038103080d003000488841c054190496008118660303409009449801704159081d1003035040305905a00002d074580c5030541207812598011800c3c5c8851016034a001e0100c00304ca8000070030090001d1031042c82001440020052401000000c552162031820200700103543c1c0d11800f50325142044002e0700ca90312014040c884010030100c090b000740083c50780c4c0d10004003d40d00502840d00b142d0108440130407241002d00c01c1d41d000e0082000100f0061702d9401c0c0018443d001554100d04154080100e00c20680348030506500940c403641d22050081d8034072401d44074460300642c4018181e1316020030400f20806160f42c80c012070780c050500301d6039043c5042c04600640310b02c00010b505582004000e001c00040c0f01c490710300c01d8a4040881d505501e0f8542071034018811903804042000c1a25048810ba070f003e0ba0b05000a490032041a100 = true := by decide +kernel

theorem cover : BRFrame.Cov 154136690 154316546 := by
  have h0 := BRFrame.cov_init 154136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 154136690 ≤ n) (h2 : n < 154316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
