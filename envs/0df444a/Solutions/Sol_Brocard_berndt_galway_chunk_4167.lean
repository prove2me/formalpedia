-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:57.358781+00:00
-- url     : https://prove2.me/submissions/43a11e3e-b5da-4e81-bc38-97845a913eaf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 749280575 ≤ n < 749460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 749281825 1250 749280575 749280611
    0x12072c04062112051e1e0f0c01060b090f010503090109062307173d1e030b13030207030b1312030c0815010909020a11060c0702060a030e0f06100602010e01 68
    0x804125a5040d40750201b0400304d80840e980d0f40a5801c45c28070025998003030070695000f501e05068950000c10559540e03807102c900e5807003665000340c1e201148115400301c1d9800b81020b5a0003a01e80800000e0142c151340e01e803400ca50404503c0f101110900400c0d0160700740d9082c2c034030751150b410316210302e00ca1080140e404112034090110a81d07503c019440002c99035869581c0400e0000300c03020180e2049a0003644039550040c9d02416001100320340890010381c2058480900303c950000742c160243da15500d08154010101c007044085000b40b45000002c1648480101d0142c00641d803c90720172881450301e40c0b0850b5041c00c08400380f5060050740c0238240d03004030007154804a44090750100c2244980121405802d41e0482d211903480480d42000c03081d4045810704a80c00041d040321203940f42c800700d0501a002d110002984890100504c040307844c82074001ea440410f4200c122104100844402828030308100c40001041c02d940f50200300c2d066090281d2104003031100006c10407040003070022282 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 749283075 1250 749281825 749281867
    0x6020111070f02010e0916020c0411030c0f0f0d05150d0f080a09080f03031512030d021303080304060b1009080a06051b0f12072c0406211205 62
    0x8014030702c003075203425640203880c94114000c0040443c03c0614001c459849114070b03070080140107100b1021071481c1810f1502c204884440120001801d5590b00c3c07491405960141c041542504d8060240c50403100c4030714080e01e45412220808221480c1003c2680c288020b2804550b00c2012100f840e035001c07070700d074019200c80c070f5030490750315641c400196505645500313669110403410300c50490044140721002c000b031030081c031003516120031101c40c1c881000b40341c00740b0039404079aa40080141509000b002d07030051074003005451400d26810b0340ea4454008941003210260340340303a10b074504404640303850100100c02980b2070404801c81420244072550360301c0400002404183c0c0c90021030304d4441e000818003400041c5000c001e5440e030111803004065004131400b0b00e10300c4446004515024011000f4030310000d201111880b103c0040c00c1c002030240c111034020741e0415a01c010115001c1300304410b805201000e40c6210150303442c3c1d07143c0111070320300250800d03040102c00c3c05000540341c10010710606d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 749284325 1250 749283075 749283083
    0x11e050f0f040203030c0703060b10230d0605090a090201030e061b090a03020306010303110f284b02030a0f050f0d030603110334031a040b010602011107 67
    0x41e0364551000c03038a107200d071040c6c2c04e41900ca600c00002c00c2000940020b02106000e44d800300c00c07090500300c00e44247ca40e00501c0031244103a981040c541c607034100040d146034a0030703401c00b1420700c1d42c40000c21002c00c8251284c080f4140c0b81c2c00d0250a550301030081844d044040d0008003041c0c0307440307100c20004040c1c01c410f280c1600d00004001c00142d86188103100a1500102541e22a503945e181c01f4012541c1c85000407068011344440900c00071000c00c0340c0e003544c0400d58422280c841207a403060b4006440c1402240c5145206c0d102484075214848050340d40c8030340c1843d8000020800c0b120801c0056030a85100c185c00d10714824038011b0b100852021281c0c1ea0203a14002c2c1d002d0645050350400780c010744003c01b00d12a504120170419896000402241e0107082d00916a1400c02b0900d03403564008000c0103030148040001c07104040350f050422850048120541d41125100d5417210810072000c100361003003050b07140601c0240402111024010411070008020640c1c45040000007030150381c9003d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 749285575 1250 749284325 749284351
    0x18050309010f0311280203031b030a200301181506030203040f06020307050a080610021c0e0a0b12091b060702040e2d03090105031504180302011e050f 66
    0x400a4002d030411240f02e446544e0040e1201200107910410b030700600280300c0280e00250320f4280c054004821070740109403200880000490612101c1a564005002c45105d250ba0b175007204a203040103003910a40c00d220101e8940d9030351428801c000c003e600398819001c2d052801050785145108203039044121007141c01d02603142da50324103002100024406000d440d190001080000003a4001c00404a440043c1c0300c03e400e41d255242440582021304140310090b81c4502c7c0c58a8100070302c02618014078240c1d1a10320340c500541000f04503449499440350600080225400c1030b12419006403c0d88824154010300712640b440100700a80e001018015000d107900003020380954849402c4600711383c0d005c008440e517100108241541140a401b0140300b4040e0072080303c6458200803044850052050795020b08645900e104400a44c05602207150b20903035840e003a00000f004400035048035800790f000081d003111000c043e003004221a40e0601c00b4140f400c02002001808520280d4102500e0030600c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 749286825 1250 749285575 749285597
    0x7111c080610020a170d05242e05040509071404091a0d0308250e010e041d0303070f09061d010e04050901230708070f09091d011805030901 61
    0x81c2c1c1001001c413009409024105e02104610714050700412020603c0c400170066035882803a840d032040600c01900701030300886440c00c5040e280420748243c01990a0328030740300382610842022000c42e83da81100010a0020404122a20306001c07101d5000c41d55003064070401640104000040c4101e01038030708000c1e640c54003041140307501c0c038842d1503030b40003e4071007080c4903151705001d00241400c4904038136440390710f0720b04000000410300100d00d11282e42c903003a07040e9071007000544104074a00811a0059074500e1a0800404c103001051800201280078668070300b40f4030402460500c00e0140300d820b101502200708030845d4040b080d244080d1140410380242e403e0032004840e402402ea08113507001c0e040c1000d00400c20b006510502d84100000718000c1c0e0b08008a1294240100171541c0002140c040000038130003900035010360940c03100c0ca00c0c00b1001c5c55161020380c0304446d20045a0381942c0080405404110000d10844030589806040d00022850360741d00e840da030b48181c0e4069410440b8040d21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 749288075 1250 749286825 749286827
    0x1905071a040e25021606030e120301090207050708120f0c031c0e070602061015121a04062114030c0f0f0105010b0403051002030c0c0607111c080610 65
    0x10340c1d024000c59420080d2505010030494508080204a100e4003120007550307489884c00000c8201502101e038408000007498540d0030380c01070078652102d036800d010301c4620b80d1000004000860192840c07190060325000c4d10300302540781c511a030700f25120503031241c0f21048034000201c003900c0d1004020040f0555030f42461020606500401a1041d03042040c1042150805803a030000c1c05229048021a0b00241d912030007280e442e030042d240588861b020710f00078001d2000200004001c40c40c0360500039074008100c0c000e08200c6018441c0020400c0036400d6040c03c0f40707000d0044200809400208400c0341d01205441040c1c0081a8002040c04d80600c8a1400010091040e2003540d50b1003402d69851058407800103072a041c019403868115480e00740042541000441940c080d030390450300503d000641d40328a0300080d40007905070781624000380f26203800100c081000f40e109510580c3c80050f5404c0e8110700a140c6454902c032180d40890114611880640c88041da690246088072505211017100c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 749289325 1250 749288075 749288077
    0xf0c0c03160c120b090616090312020f1b030c010f0219031b0303090611040b1e0f0f070303060b0a05090d080909330d020d150e010903021905071a 64
    0x301c02d0141c00400e03d4240103100b00060441c2c03194007014241e034000e54520500100703401c401d081d080e0110f00a071806002141407054043c580603082c1c0101e9085da84001001450000c0315800389102c48440703e82036501c1d0509002c103040c482d4080c00e00c28000504031350043d4544000324412288204408101d00c1414440d00c80c0c400c0c040076001c01c0d0a41560075040044c0500300a8009507241401d0611400d0401644000c440c11580461030b030900308004081c1940c0301c3d0960710090320100509101d400441440607008021003c3e80101c51517032640ca600e0040c06654041d80f012942e4030341401140140d81c0c00508a80281d8012160400d61207040e26202800b40164402a5001001d20081041160b116803803c03a81c01d0038104c2d2800f007510a00c00b0316050b050042d40b110380100d5a80d200d02c006051440c080f01c003140c840c207250442517104048141c101c074450f000300c3e002c0d40c2d1a081c62005040d014000740e00141b00554417404500001d446d243d07074400c507503c10301310801c1e030001681c14107000c080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 749290575 1250 749289325 749289329
    0x70c06090803010801022d12070201060803040609090c030501030c0b0a020a0605040b220201020714040902040e1c052a10020a08010303082d100b03010305060f0c0c03160c 75
    0x101d00152a940c6a0a00c1d90013508910403c4400c0440383d200c80e40c41c0303403000c1a200d8891100058441c03916403414000c0c00a86401340010b0150341d01d404d800b240550091000c0c01c040e19480d6111407185107032011b11000d0300c0c0d40000d0082818907100050012030194248002910304d0b000440e50703981544203080307283c1100c1c00c0010700000e15050501041100c4441c2660140380015401100e414500326000c0000c510000b009015900003042041000c0200000480380709004000207490641c4e500803d00340c4500110f180364039000715407041500a8423074078200c11040070707151190030062142041d031007840b900b00c03010168460f003c0d50703860040c40411000464010351071055446607559000501055030030700045001c00e5003000007a1548059169025812104940c000e024483c02e0445d681d100402521031900111b84c00c01c08211a82d141c2e00a5000750b2043c001001340386811005c0a0009030040d214405003601008441951030002094031504440e10f40c13261004041071400c004822496 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 749291825 1250 749290575 749290583
    0x807030212010326121503030f09270a060f0803040302030c1216030f2303120c040b0a0e0405011a0f0904020720011205011505030606120f15010207030308070c0609 72
    0x504900382c1c5e0060031030600682440842c2540007a42900b0907890340070b0600034100c1200c09001400c003034601f10903400e0542201c0b414080911202110a40d08981c0c12a13100203a19100c07481082140b2030360a0034802080703100e001d1820141143c0c0043c1d00c80e0390b1409914410841c200ca0195070710401e01005184103448065640c0942d03480c070702480f41d10807500090320304030011a40203060804000d0340391046103030b5101561400b05216040450440d000d003030006000d200380000b09990031102d00a024038200d039143c2c2e116000c269001c02041e9007058100c200c0b00e215000c800c0b4003241500e42074a2003150440f011503180e10300340005c10021301403a0400380c042c4620200002d41c103004500540d1001c0d4080e07850b88282040034403400241d0b2800e1041041501c3c203140080c0c2c40b10301c510065a000300001782590700c0c0c00000007540d07400341c078207840035840070f00000e0070700030090f404680c5800c084000f8005400c10926507140038064000040c0a038041c05000341c03801c2c040080e60781c000c400c41c540c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 749293075 1250 749291825 749291827
    0xf1401090e070e040911270a02041a0c0705040c030e120408030a050c120f0306010215150d030c0b0103050c0315040803070507060207020a0807062606120304170d0807030212010326 79
    0x1d10447c80841045012a849a100c0040b000ca0442849030080b81d003079684107034490008254003d0f50078015400440344051034000c030301000c581ea994034000c00020319513558000c00e0045519200e10b060400080340605085002c000800510710080142d8518195504140b034840003a198000d060503103071701012070900703000100200d9a0154101450240b1400ea0881c0e41e2500b48412800321031100340c8040441e060050b500031030724a005070014151390301c24503100d50314a02a41d034a058501080c0c2040b217598024003807030303c00c1e41010401c0c0800d544200141202c6402c00e51592a95480003610113030401030006244014084a50119040d540d4050481101c1c3c40e03803211401e031214098051100001e1101c003c0751002e21a079181d26515521150480010b40c03034200400103c0c05041c24000c0d018041070000140001c0545802c01d200c060002c040c0000e01c40855006101d50402011501490f2050081e076642d4858510860305403640f0079601d04903407444203210f5400c0313010450700703800f1024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 749294325 1250 749293075 749293099
    0x103030306060305070c02030a02090705070f0501020409050c07080403020f0a1e050f03010204080705100905090406090605060d030e240a05040810020901080f0a060f1401090e070e040911 82
    0x94035078001c0c0112100caa5040000382c4800c841159000d2010202945c0340c0c0c40313080513601524000501c25080229030030310364588002542c45800d21304101c10159890f07540443e040100026902030182e0050780344d86128a480c0d0a6500c030746560040d80406401141d4100a410654031507051a1340034003041780b1585203202000000740c4000116008030350050001000c1c81e0311605050003600d0584846002801c013503030611042c84002e011844e00e04040018060f40010326444064945004500075500810380c9690381c20311a06440000d0540c500469440c0c01e0000883d40c084d00050303945500329800054915608640942040c0c001e20504840c000015244085038012009004588460050341e600000d0b00c100401240591260b00e4042442140080c0102440002096000c000302c5000070350592207130345040d030203080750300428001c020f00300e815842583c104103460300610884030010178900c1d01c44801400308000c210300c0d502654441850004000184140a0485c06e000e08410045c1c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 749295575 1250 749294325 749294327
    0x2a07050913020415051318060e0d030b011704021011030310030209100308120c0c010f0906050a0b0616060612030206011706070e0609061e04080f19030503070215010303 74
    0x2401000103e00c40c0c0d2400f00710180741d204001e800f0b07049420040145002e03408a07004a8003030441c03108480302003013282d1600c40005515100d07601c0120300800c001d101b180e072030001c007404840d000c0340c20a040c040f004003100740e1700c0300058410781d00960694802542d015010010380d83d110b007118204100303000110070400034500e48032994045030700071107610700a9140c22100d0800600540409400c28108114619174880c42d0440380d900201001100d501d0031587c0030300c182c03c4900c0b403400750342d01c1500c540001c0107000050044075000310700344030104240b0510f0000224584682402e1516820b4070303d44500500c1515840b0400602106002d2640f030101e6260080d181c2c1c3c42401400c0821815140080341d00000050700c130320901c82901c900e40240110000c210503030b00b0045003142d002c4c004104d000c8a10261500c103000710350f111681c1c19250b0381810800350400c00c1e4009040c420354400b40b202c4109020704403180d00d0a68040c00c2c0181d90b40c0311450124141f1a901007a50345202d10400008205 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 749296825 1250 749295575 749295601
    0x1412190c170a09090b0f010e120703060203010e280f0b03010204080106050103150e0c0d0905010f0b13020909011e050a030f0501140423071518050102032a070509 71
    0x580070603583c8141e55511880d4400485519030b8003144c010108030f15109841d400303484443d603501c1d0001c1000c042c040b00f03841c2651a240d40c54000305c4d051500440100000c0c00c028200f66040b08081d001c2806002140c003851001d81484c0202c0800d4680310100d224040c0441d42c8100c000382c070090001c0d0b64a9450740b4006019050f1480761a0000317260180076403000592180790301c1541c3c1211a000c2d03207030711040b0100045402c0303603031382d820003e44c1d80d000301002a509102d034001052440c100801e680382260304120708400341c1c1d400e04281374010400502644e4844e50f140c0c2c1990300d2002c6591072008100e5004e0345880e0240c010f5504a01049008814411721264000c8628801e600034048041c804441d04217080058400030050038100c603101c2d1a0440110b14550001003080881d40c105683e081071031480c8400030b051002091000c1c4560340d0b90900e401003500a08800e00046160025016041400d00c1002c801086000315880c0e0086107a441885110300409004120407107074100a1038001207 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 749298075 1250 749296825 749296837
    0xd0b120a0615050604031509030302090a080a0507050909070e0a09080a080132090402010c240e0d09150c021e030d030b0f01050d0b15071412190c17 65
    0x42d248220100082a01e842c004880589034010500e00c030380d444400c0c01c00098401c00d401101415000d100d51895902c440c07010000406070080203000700d0065042680c1010000e4200c0c40c0102e48980400441000c005058000c5a00c500541c6015940304004a0001c10700701c07100500402000036141000c5500c43c3d90076060342c10342015480e041003401c10b00e041500414654080501d1880e5031118203107044d11303c2e80d40c414010f04140c225005507a41d03410751580100c1080703211072100b50f00d05110701207910510307412102c3e8200420a114000750083c00d9001d0314440c1c0041002001005c2c84801c2c880c80c140140c00b94064010901400c6510300030b500d50000b5006507000c4d03c60040085001d500c28020380f404880041c0400205024010044603250b00410035075074042e803600c24510440d01c1d0310401c051041d0144d01d0207034403299a854084140e00071100e455005038000904600c07204809403c0310b01140014600500b049458003003610243c01c082c070060030301e02402c801d15014070081002000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 749299325 1250 749298075 749298101
    0xc0824060703024c0209300109022b0501021207030e0c090714120901020901030b030601030c230d0516060f12020d0e031605010c0c02060d0b120a06 65
    0xc1c043c41040200302c0c4c101c660000d00002801544212482401501c040310f000c050021002d0315091182011400600c0c4581d220311048807600f000b41d0032000c2c0e102038506000da4840003403040001a8000030b00705101208410000707070740002c2c0c015110300c074144c503107894a900c08000c1d512514028071301c11407100c0031602c1070b0200341408201007404e0f40100f07542c0b14030b900007132501c1d60301c0e02c0d003180071680c0d07000107000052842c9040000104401c1c0d288400c0344141d0a880c0090b070b4450b069000101600d9460211754040d030300450040c40040c0c070802c0c9050a445010804c18039142414021702c40e5100390040f900d8005c5009900c035030078000c01007501300103500100204580290f903039400315a50260344020030001022103880b0b0071015150f400a000c2a680d8800210341d2405515400e07086030310045d582036000b8460b941040c00c21600780118103542400e401c0c0182d407a41b4580101c1c2c06486500000e0180350340c2c50940120070354501020242c05d030150000c4500c1a010303480d00b14014050540f0183c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 749300575 1250 749299325 749299363
    0x60302090a0c021b06311d191404080706050106090b0a050c0a05150a2f0c070f330e0607060209060304060f0b0102010c082406070302 59
    0x24454140740c01900d11801d0590700400c0b1030500794002242140b444141c465100d40d04004641918a909000c29285241c101ca40b200498240101841c503d85e5540401920007101c0c1c0300000d4400e0501c200382e03112140150580c5020f991250081c000d0005038030103c80030301c050042c0014400040007070300425100b62000c02c85a40c0303c003415507080509102e1081c0d051000c20038110000e00c500041d2404c002201d0494008003900d5542c5400c041c0080d031407802d641c40042c00c00170800558000d442c0b204100c00000c6a80b81840c5034010b0020f0b030002c0a020803103e0000c0c00c948040c00804c5110010b000506010302c0d100e840310000005020040400360703180f01c1d60b84000402e002e402c0c3c48941c01c0071182e15040d00d0f4041c01301c24451aa0800241601ca0340c2e07007440603505ea038480c04001c0d0700c5203206420004017080d80c008850300302d07840581000c0c11a0701d82003078025250b810581c8143c108051850702058481d003c0781180700e5500c0d0100c031640000c001b1411400709600001e0680d4103008640c002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 749301825 1250 749300575 749300581
    0x60d0605120c091f1d1009020a0e0103020c0f070314160530030a020c0901090506090105040e0f030f09040e0303040b04111215012322150906030209 65
    0x2650b1881c07440816030340200c030300012644d4001222110300d610320841142c1c80c100ca035255a00c084419840c0c0342d42c00e050300300784108044504083e006001138203541000b14201070350380071700805000352003045a060541c0010410a030940c200100b80a20245c401103c40050703c034a800c00c649481602d400030f051181240102c0303180c520400e05020b4030805002c00c0700444086030000da41020a40e00e942c0111454030031014401010b000600280d2141d40041c20141c0c102410b200d6112816071183d003c0d81d00d08805c1c4510f941d25440d660341140c104540202d031944050820b6400c100c44019599400e01c00042c0b2800c080300000c016224200d400ca408100102e20000c1c055140d200495004126241e02800600029401d000700d00708407801074078411280480b1481d01345004504018411826495801001003a1000e11801040c084012100c0c0c02c840301078021a5903560716a260503041c4070780e010f8446040c0d2050f807100803c6030584410490302c99031503130f454004044034002a40103281c84800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 749303075 1250 749301825 749301859
    0x1c030e0a02090c2206020313140319020604050402130e0c0a05071e022701080f0a03110a06021603020c0414010302011d060d1401080d052502060d0605 66
    0x32420805401521640031952240c03810507166100340460040914440402c5680152200e8898080c083c560011540d405507020102e01200032a440405924181b2440c80c1d0130780c030040f42d075090300000320706010740800321440020064000c542100386c00501c04280101e4610b648010300e4100c3d00442020944d036102c115007807456102e09149500811400c11080c0009040101c116040480d0b0410204551110303034000340c1c0000840650030032500281c01c0001030020080c0382c0d00d0041c011940141000e0b5070842c0400c3e2548000400a4144003060141d24550071080c42201c61003540031000310344d6440c41881c4c895068404050542c018400d41100e020f140c10a4810790101e089104010040e1368656801150700c1c184400c00700c0ca582180090000d103c0e01c4003005054804001400400c040002011004080d04140d0041d095640b1002e000c242064000f41121a115030300c150204050242c01004001d00c580c01100035041180000d074240d030421241d0141081e41c02c00c8a0008807423041e101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 749304325 1250 749303075 749303083
    0x30b090a061103060f0909070b03011202010e10200313031a22020609012f0c180411031f0f0f02070c06080612030c0105070e01020318040504080702031c030e 69
    0x6012508000c0050441701d00d80ba00285403540075589904403a031140d201c1100d080f442d042a40a0b80c040d0800e106850115a004243ea00c00d008081da10946c1078004440c00410040e41010106070f40d00c0424041301c2e1100c024403c580325400706281c0c4d60242584c1e450118220075107076103c2101c000b480d1012030302000710681400611522855400154803054003000381c107034800d017151411f00080f05685002107800300d20340428002c00c10300300f1699682007034209051078142c004032482071401c000c0340801e42c40c0c035404698010b5000900c0c040004100c001003442c00c0d1400107466103550078611442c00f50801c941001e08040c142150074407130f02c072500585005034050044010078000c0001801c0c0303d0180700d12001c990110005000441100d80142e01c5421540203035004103150351100c04101c034440c1c0150022002c80802c1c40190f18003502c1151800000c04c45011a0703200e40e4450f004242031140f0003003507500c042c0d0024169601e0030040c605000690017201588004a420491280e080a2000c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 749305575 1250 749304325 749304331
    0x7060f080f0703330807060f02030d090302010b06072001050a0f080a060f12110f0102060a090807020a090e0f010c0f0c02041805030307080603160b0310030b090a061103 74
    0x85071000307503100c0c450154090107075207104184a010881a540000240e00b00e0604130700420901d401c201414140010f0800780d09802102c00d2000c1e51840029865001007211044421201d00007600d10341450124050251109100c7c0d00550104620050200090070005452006842a040d49032a84010343d4180640281007000c02d141e400325440341c1b4001d6045a0344a001c0310743c00a582615254484111001501b0a083e41d400320b01c03440d8200b00c0c10b0100b43c1c0d080c4c2c004807101804280d50800007941d6030340082c0340c0d04020b51242c84840402120320292014503030700400d8540b00c0c0d61244403c0e0000c004441e002c0031184521583c4007562401072098103146001d070b41c1c070408003c1d5164001d42e4140288402240c02c07e43c2c500001c06440104035007507608a200d800650390b0303030030301c91002480c0c2c440180c920752090704146000303144490360130000411184001d090356166a03d010714080d110145a101605600f040e10801c5114000403c3c07081c0d09502c264010040e40b98403440e01c0f03020b800b0031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 749306825 1250 749305575 749305591
    0x60e0112060911120c01030b2416050a08030f060a08030a050c07030f060c2304090b120f01051006020601150e030f15060a09021c0b12010e07060f08 65
    0x5994403401007030668200d265210301403080c502c001d10030600491140052802a456940c0000e201e92500350381c503000c2c4441c0600d084920100440d204560781c40710740c82622074010305040c0040c5446540e41c0c5001d899036540c0d00407050350152925800d105025034400c56507004a0508100010000d14000c6008000e8a00390401981059085102502c1d294808034900d40244505640000040c1e0240024071f0014455000803d82c0140c180b0701800482c41c0d211203080855500100c03018501440d0140c4e0100d582c407060100742100168081680501c0c8000904c1c0a0b0080c0700c1801610201500401d01420000c40c0103190341b691880304070f072210001c1c004d8140e0701c030100000c00d248511500a1482c86800181518000107140c0e9a00d4501244601c95a841c0c0c18500304002c854500f03d030903c03000b002c14010035803501c41c030345000750914201e01d20070709041c0d503490080320460740320758017050b10100e0108020005400190002d603900c0d85107101d400c0004106a0240780311500c1400c16a02070028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 749308075 1250 749306825 749306849
    0x409030206060906210d030b0604030807032a05010903020601090b0303031807150f020c010c1a180a050105011a19050328021902010506030a0209040c080607080703060e01 75
    0x36182c108007071910003034206980610030040395441141c0d56945050300f05035a100400b40185010380c080c05075444001c415200342030501081000c140f412040342c40e5254140390407030000c448040d801c80c0c880b901d90080a021800079060904214055100d030355141c3c00f0340c00320f0b44144eaa50b00110255081103251a405030030502c08a5054504051400e004842c11416161001d44617840c86501401c4070043c500050300b0b0304201e181031030f014020188081c1080c40c11001d0544142c40341a05554080100c8440d005803000080c24450380341500d000044141090b41d0f005d014904140b03010b0042030007002d880407161110383c0002070f1031504892107000500701c07440d0006117039081624107400042034000e00684803600038066180003250b4160080034074500580340c0049420a05d150504494088150ba161000b4004540c2c0e000404109655041318118402d0390b80e45810ba01e01c0c45658420b070600e00c00c0f0004c1c8042c09800030a400d02c07508182d0b600708005a0b4484000001c1c01c000e2183d09402c43e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 749309325 1250 749308075 749308081
    0x210110c12090d140c061314090f0f090106180b01020105010b0310030b070e0907270612150902030f33010c031e050d0f02120112021215040606050409030206 69
    0x6114500310968000c44000e488840d2507150214240b9400000f00d018250320407c0144035030807040d03001120a100540704982d040c542904c0d143d040032030180818070450034900c00940d2a1409402000140c24018803c2c005154000c0d0000e000d420040c003901d0140d4282000410210004015644103048648601070341c640344d512125103140001c1d1a440402240840c50380b500c0d1202e4003102e00032002075451031052980400d10311785a10101d50702106c8150f001804005142d81b280380341415480881d00007541001e60030081107544110351000312031078004410004450940d91180e4403690720801d030401c81c580303801da6103900706803035016400000c80c50400c00402940318010080c5590b109003001d4090b40c128256000c01940c48503050300c001280010b205070140b00b00e02803103900040e01007042d4242040071544010601d4140114a0300b0b081c15140a001e40d665000b21001c201c0853342918485407072075012249105003282c044e079002d410064005101d0616105040301184c1560180c00907403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 749310575 1250 749309325 749309333
    0x2010507020a0f03050a0b0a092f040f0b01020d0f120203191b02010c05090d15200a090b0a0806010c020f030d17161e0210110c12090d 59
    0x24005120990b08440304180c0800c1c00b0940b1001e8034061070151009010305d40d5149080110128005d0881035268140b21100000885c10741040c0340341c400070f032103200300350f02ca0311f61040c0c50541d0290426401410296a4019002690b201300b020b0003081c0c1c02e42d01200d092800503600e1000e141105c00010b00d5901800311103403e00c3c1d0195800c040b041c1440c51520710b4001c00001a1100300c4000b4405100701d8031010f410f07075024407843d80b400078141480ea0034245100c000441b201f0541c48054090b45d2102c400140000c0c641d07008203803802e078074442503444140c50740d0210900c0e0004044600030600042d8041809500034060303a2981039517644030380d025034030900110383c3c3d5901c40d00c081f40c01180140311044540d40c28000c0c0c0c070000d40140e0341e030500c3e60f0324103000085915002d0003842c0350914020146072030940c440c2c80c3c8074034085142843d8481150030718040780343c46040e880e10400c9a142641c444184400f034002480444030b80307011509400307041e00f84501140f04161400d60f01500e1603403400000703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 749311825 1250 749310575 749310577
    0x30712050a05070c090c02070501081603110c0610150801030b0106120b1512060a03030203040b0a090806010b030702060906150d080904020d02040e0a050103050631060e07120f020105 80
    0x1c003146803003803c00b4040d0340c0786554110f1542010744041c0d00c601200c010a9410811100148424a403066203400c01c0312105501c1c903a000e250408042d00c4880140207550040203c0d0640c807403481c11030300c05152070b6410501c03c0c4041c0c0601030062804d8484a910301c1c1c440c4040c90b05a9400c0103001d86207903e0712400751072000a01c0b07118140b40d500c0c4c11030000a6940c1c0034042240c0034451a026958281e4400d9864004000602041c40f58080c85002c1c40429800070940713054030800c04030a540e41441030020b49183c42d0715801210343e841070b03c001041d2080d0400145010b040c20b502101c500b0b844040e03a1a0305e500341214910140a5004003110317152600401c0c0801445c040c01e600c5203401c208202050582e404103420f1212140c002404008a07903443c1000e903403142000c1800c200030b50460707075400d48400019180c50360a0105440310f40b041213104d00340c10406d40d2811f44800f03208d0010310300000038103a8040710941d507014600c40050a4070780c140030000c11a5001c400049406016801505d907 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 749313075 1250 749311825 749311837
    0x15020f100506010c120e040c031e05100e0112020112050601020a110a0b03010e01210b0718080d03090210143a0204230121020903010c0e090903071205 66
    0x4001540084401040a44a004401c985c0390340c0c4008950b91618103200c10749241d121090201740c07030500d8008100c251442440c000c13164048000c40c0e15256800a0550f80c82d040d000014144cc403400001100c0c025241320002461013a03e6450190329a0001001140c604584d12400344c0c0011816100040070217116503005e0500802406481d602c1d040380010030b4009811039a0400c42540045c400820f080340109003d010140644804441958503c8180c120140c0204240502c00c2d80200035150500080c101606901c1300700d402c000c035180c0c0020068580318205a002c0c0400324502c80f41d461248071048503000c2641c010038580310140403585403020719003840c4414400b095100d044040d43e202c818000301d5983c2c01c000360300d540c180f00300d00b404900d06445820400c0d911b843ca00b151070f60000d0045055402e1080158240c0303000780700c080064412401229070651802c011000c02a0b00545200302200303055501e90a1551801c41540c3c1e20701c12250b020b03107070851600c05c100c131042c40b4000500c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 749314325 1250 749313075 749313077
    0x70e010b2d070308060910150f17130308061c0209040f060e0f010c09050f06070302010f1e061406031f030506010308030403110109020a140a0b0f030115020f10050601 73
    0x2040303400000d000c54142c200c2142200000c00b034905010340d9150410600340c016101c2c50782c1c0c0f14150320b8204d62050f01100420300e002449950001719039903a000700040c00c170f0b9000c120038030280c0d0b1810088120b4180407109084003c5250303440420242c0c1424618142c2d05001402c180128512a408000d101e1100134800c490a00302c2d01c452500180090140700910504a0001d120940350400034a003940c01d1030070560f041100403035007002640d5607051810040442a508d0369601c000314101240504090319110420f81d0403c00b101c203a405285203c039004110400081080c0da031543c40f400210507080c140c2030b0b032080051000ca00c41c06112000c09442001c000041c0342c2032035699484608002e802d90080e600a4008010042415007015900e1130180382e010080048902c55400135225217428054554071410f4107484d448207898a2415802030440042201e8442907141d90081c5503a009000e080d1005424141c00000c141c0002003200c01c0e48000d50140a4980789640c4d00802890018071b898 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 749315575 1250 749314325 749314387
    0xc0306102c0d0204020c0c1f1e020a0615051903050a020127030b0a0506040b22020d0e03040305160303050d02030c0409050f090d0f0918020712090503070e010b 70
    0x300c01a1358a200824900144001400e840390b812820481d45041c036103030b0380d070300401451031400c0c84035440034001c011500c5e00d000b600310160f0441022440c0c5042107500030710381440c0c0b200480341d00c400c0c44090812640d0458585a00345500000c8460060042c072001700268002844500158042c0c00104804001c00c00341c803003440d070008103000214090398400e48000607403500340a20b017402402203540c4010291402d0060f1142c0380041580751800543c1510007030f0041c102c1c10b411001c25011506011f150710b02c1805207010003501079480742c2c41444200d80f070703200d41340c24403e80c000ca00d1101400c598040c1c44040c100144408e80348040d502c010400000d019040101080800a80c0300d00ca014035416039a03000f00b071038910000d5107440c000c1d001c20303000e10502e0344024210f141d000700305606688200c0410081142000c2000000c2e00481d040145100040140d4031510b541c894401011141c04404035800346640d4010030000100a000d0b0100e025020021600099044001001594040c601d80c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 749316825 1250 749315575 749315599
    0x50f030a0c020f0d030212060609010804112403060301050109110412020a09020a2732120a050606040c09060c05070906090f0b0913020909070803030c0306102c 70
    0x3c142003101341040400402c0c0d001c20032410441610304200d6000000b0f480161800b0066000a820340c440100f0080c000300758485000c44585510b0b0441c25007880000c24400d01c074032085200c40c206d8108a890500030341c6880000a00384200d1b000d00e5200c3e81ca607100d014038003814041036080007400b0100c1a41c110001c00000920103100d4401094000d9041d920844c101c1260308034050b119500020343c0e500f80300d039580203101c501820140c5010101520000b400c803007468840411040400c15849580108020291103428501096500c0c80c0d911070401c0d10311554400040008550800003030100284420b501480300e2801086404151740c0038504a80c000c56031400381c4800e5031442e030080e0200b66110300e44912444028007035894490821140c01041e445c0054580c03220101400c4040c0c030a06a18000c0344221406000c003c1c00b40c070445c0309495891404220b1040707141d009955690060003441a118000792152a005494850300c108041c03c0e0010010100c03103141f10b012415a10042d04005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 749318075 1250 749316825 749316853
    0xe06070f230d1706010c0203011b0809100e07060c150c050d060e011a1b0d0c0c050316170f150a05070908120f1c1b050f030a0c02 57
    0x103151241204a80ca00441054108954108901e005614041c05580f58072120200042c280c0c0580c48242840c000110441900019025103c50341c0102e1000108002d1a15030a5000c55018031602c030000454804154046400c003c03a103982c1e0050441d0f1b00300702c0052054511904081e50020b000b820040309005000d5030403005c89004000345c1000c01c1700050144d2400c0b030503000311070041008924048041d85890160402c080070380b4140c0c5a41840019080780900400f20304041e402d608070125000c003180d07600040c010303118048013540c440041c101e00080710310303001400c403031a000c190100d0091a03191030b00141d0b01d8140c14081c1150b6000d040c00d541c0c1d004004024210020f104480c03075030303510f0a00104c07803011074201a14071410043c00302e20501101e5000075400302084442c0c04a40c1e0383e41131214040e05c00b03000b2030081a020140c0c2c2c001030180f80314103400c00c041030f008a400b902c0e98581c2c03644055410b071007144c2914038100c0090000490140c066400711481c0c0030381d401580c0741c0110000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 749319325 1250 749318075 749318093
    0x90c04110c01051006080718050d14060106080f06060319050402031f140a0e0312060a030c08060a0b1e090408040b030415050a02090a031e0804080106081c0e06070f 72
    0x344d40c04640c803865804016881d40100d02c19007006060429031640c0e102840c0189984507103008890107690503c908004125100360140304020150050f503400d940c603800004c1c181c030800d030764400d00c524a40020415038980308044071701030344001d0700c0008118014030501c0f0290200074400e0364180925010700e1111107007460528141c02031400005900302c80c00049121a40002d0024000383d407810030101c0d8210780000485488003280000c52000e0b17520b04001503920030590700001c0c00a00c0c0c0c0080061001c4001407140d0140280990600011303000009028a00d4443d01c4080900d100a81015200d400d00100c400c1d00329000389502c5244c03039207440c40380d501035100751400c4882c0000703d00990351006007407003030036046050040194a0314030360200040590035a8007001d03100b1140200400c02c190b030803a03403840e200d40c0c0c007d03482529240c0c1c070b809181c000c05261041203058003c0f211040380603420000306e10a00c0140e5111066140729140c24090660011402191b400702100401008201114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 749320575 1250 749319325 749319331
    0x1b09130c081b011b02013c0306030b0a090b01051003020d02030903040807080c0901090c050d060605130501050f04090504050307080403260c0705010e0402070606090b011106090c04110c0105 83
    0x220101e41800315100018450300c01c90601d0891851411550740050703030301c07008800c002d850b400400e034041048003025030042c54040640020307c1e021001d04030310740388d0581c0248040701c1c00381200f101540c0c1d0720a4034800792241110010001501c842c01800b942c40c00c0d12441c04c10042926005061100b201031072401c0743d000782d804512a50000c01c04120f420810002c50001d040f01101600400d83c0c040c012903030000041c0240c858442d102d824104a251282040d15641d10324440c051000302e0b500e54000d095540f040c00c0308a2132000f21107004c58154018400c0b01c00040604500c0e03464985400e44a40c01410040c000b221140420081c8001244d44171000c1d1000d10b01491000c120742481c584406c403c1c0301c1c89086c1141000c400c2c4072284c0405004140c00049030030030b00b841000e4608410010700280301c0d03054020302071441c003907010071501c155a2040e0b009043c281ca4a541e0043c0d908071042d5207402c01c982641d402d51110740404424146604410044180203422608010800d042a82554011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 749321825 1250 749320575 749320603
    0x103060504020a1a0f0702040b09280606020a020f150c030903010f05040305070f0309090906020309070605121f1809050c04050702121c021b1b09130c08 67
    0x810600042d40740a071000340003803644e50211010381051021411641c040c0d000441d80c10a0089500d0065484c1c2d508032440d00c0c1c0740140f94040500e01140405282c42c80310070800c0c1c00b001c5035032030180350250f01c2c400e04040e83c046400a101c80071095082110903100c0c0300809400c542e044502d8461100410041c061000c40700d03004d1074843c02210700741400c50300c03018000000541400b041c8030200f80c00c04102c1d480c8581106852907101064101a110303d6603580c41811507078944450322007844580c3d406180103141a0f8103496900342d40300c4048409015100b5200929890f10700420040d00303e80c40420108000c11150002c6250307180c0c642c84042d950070200e4000e05403221440b40400200384080569490100d50810035804c00700c0b002580e07540b40115a5150480020324000751107036105444c68000b00e40b982c25550b80810400040c01580300d41c0d040f1625115001d80c0e1424580c2c3c00d6541200e44101900700043da42e079600301800c1045010000f9500b41202240205a451040c4021840d008070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 749323075 1250 749321825 749321831
    0x51501020a02120304081906150b0d050a0b03030309030a09050a0302101b0204060e0702101a100e030f0708070605040803180f03010905010515030c0604050105131223030a02070303140d05010306 85
    0x213241054006d0300c00a419542c2164180c000600c0b502b0141d90a0f203541003890080085c13280d858983c800c005181249140d545440080b00b0400c10740c60010040602c2c000c02e0740e468003010364602c2804000000f50200a601018bd41440f00146208007980704109981507800000c080240c1c001c1802c894003078110070407030720810081200b0301d80c0410804441c0c01c0c40e10320400843e0700d000700104074045092103107840780521640c50309005224030003003840c800c0001c06030340c0d44030a080c5c40542d07200b8040c1314074040fa002c0d542c000100d20340540103440440c2c6145002d549040440d0040e0340c2c40300c50000c0a01d41c007409100000c641510244a40e04006208100008460a1002e9454030108060300c50074825402001c540324107440d40f905840c125402800e00d59201c01c642c088441c030303559040c0c0044444813904c10803401032154a0740070070400c1e513000344149007280141a5817500c4c0d1080d95100c4000d603101c0841080064032a4070740c40c840b0400c6958407030030000400f0200f41502e901b07074030507500692 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 749324325 1250 749323075 749323123
    0xe090c211609060e011202031905090102131d07030c05210a150311090402010c0f0f1109041115041e0807050a050a03060e01020f030f040303051501020a0212030408 72
    0x6000080070020340b101d810443c0c0c50101034130008088030955505141110b8010000c12a188454103046007003211030001031005140c0340008078003d401610110241c40d01e00c45000030740002c8440048004443c07048980500e5507101c8041d0050700c6452a07080c100f150030030814021030341200c100740180d855580c02107554140386844000b0303248030148400841801090810004a20070203c1444013401d617003060300c554690005039402021541c014124483e0035409008000c007418822402d9481001030041c035039001014048200407c070b500030111005005a50750300e2070a07610b00070490400c2000302d80791544a14022004810741035031954040c16803681844007581c00d20665010380000e5804180070b0b450040003031845401480050000c941d035070012500d048080d0115046508925103596403410806a80342c00c50808450960029281c41c01189505000440c5915601416402019020805c0d020416480744102881209104c00c00001400980500018404c4c0004103c0c4041c282 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 749325575 1250 749324325 749324327
    0x6051b0705100e01030c09051008060a08011b021009200d0c2304140c070c0b0304151a3703050a0c090c05190e031b0f010e090c2116 58
    0x790382419490034010701c7c120030310094403000400c0c60042041d1404900544502021441d540c510307030851142d070f50030400c1641590810741c2c1500030b0048258201d0f00700140b01e80550b4200e40e03507010018032000354070080000c0300b0f03a405842d51280000601b81c911101984d9550110341c4440c0c0e01911011440d840340365800200d04250407520300042d6401d00401049110054003074200400540d55110007040c1c0e4014408101c01007005000805c0c1401e6807400c3c6400c0c200041031000c1001d03101281800901e8850406000c41c566184601611043d50707064190010600e03205407001000f400446c02c00030300c001c2008400020001e41c001d42c06441407403200e081903a06650160494101d4070304100f00f81118907400002c507181e4401081c0741c0384131010b2640080780c2c41e00e903003951540c0c075200702050700c1c0e8420f00c03c2450f00c40c2c07000c1c120345614854460000540307031090300780505a0301c44034200004080828401c01030182c4000c0c008211705126a0b03a00d0041165000d07105030030540355031070f60b1403031203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 749326825 1250 749325575 749325581
    0x130f150c020d0b0903040914061302180f010509030a0f02090c03070f0f030906140a15142815020c0d080306041a031207170406051b0705100e0103 64
    0x1949040c60001840304141d004140d80d0303942204014901041c090000d00307002418000c0d00c0292460740010b100101385110164403001c170990310103229403410408000c0003032052007150f60145180104104481140302080001d10040641c68107000c010442d0701c8241c0c0c0d00f0720550030f1807071140102105202e0130740103201c50f4080050100720070700420814002110740000360141c40c161103290400740f01c00c81000407800741843c020001c15050030000c7c5e191a0142400085108502100c005c1260b00c1070a06000e00482d9548545411481009240c02d80d506041b11081903400340141143e41c2e01503212034085501ea61540040401c0c414981800d1105078180300c03504c01b1740b82c100d40312810f60302ea0351641d00c208c0c480608130501c41d503919041c480d410942808080c0c0409802000d4403407202021862822503809888115640d8820480612150a071071342035509607819959600c0c2424001e150700a110341c0000e00c466541e1240c903c0c0050140c0d2201d0181408004c0d698500b445038000c08009815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 749328075 1250 749326825 749326859
    0x1e050109030503030112050a06051302030607030c050d020309010617060403090506041503180c0f09060f080a02120309031002071a04020312181f1716080c130f 70
    0x10840c5900042020900000503213065035012441c000071940e0500e0014038086032520028000f03030416081080e120181c16500502074002c0e410b8a08a0f6a00041242181c0324680c24402151301070003000c40e0b0144580c051907101e1032040c000109140c40300c51680c1e241031030074240381c145c1d030000c020072080550011220006103400d40c0c40038182814841485510744002c5990b00c10180c1c2d902162200c01c0c001232042907a02d40061011804c5a190907a0108502c1540181400d490074254001050b145065461086442c1100580a908860750070001c3d03402c80d001c480d4a03030744024880500c656406103c40c90003040d03a1500141c2da121240340c0b5100100e0b4640070b4445011880c806c00c0b02584020600d080384001c0c24030011f58542a5810b030640d07144a809003140c0026403026105000842c801c807400c544107107a20381c446c5c10f82181550343c1c1d9050341200e90705400c1c480a910346289a00812582c1d80150703400303000310700b401032000c3c8090b9103002ca6408043d4001c14803a04100c0884c2c00305540030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 749329325 1250 749328075 749328077
    0x60803040612020f092b05030a03150e04033504030f08060d0b100e01080a020a0e070c060c12020a09052b0807031b0302030c150103211202041e0501 65
    0x100706907900046444c03c1c09a0024280a404180343c25100221400000070004881407200c0b80300d810300b41812a130365003048008901280c6040000200000c158003e5011208002604401661280c2c0e049a0740341c16040020b1080e07000c8030000e02008049001844171600d440c9803007069250a050042800040410300c07814000d0b00c40902143c0e4036028038070114950030040380229030301c2d52010500e0341542c80d400024401e409034000b090340304002c640002001d000311040440107446180d03048111400359028804542c2c102d8000c2c000924030b030042d07040d0f0480c40c181011000018a107a0041c1d03440803007000d00080d1000402c0c009894032806c4000f040f001e041c07109000c0c040403c0401c41c003410102014104e0040450028101482010440c0821a13a0803850f00250f01902e0040e60326003022000030120300640c1e1800303d42900c182001030482c3c1e04820030740790025148282804c0290001a04030400840080c401a07801007400100000c0c4040704443c8404808180f426032418160340200d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 749330575 1250 749329325 749329327
    0x2011e050123060f070f0606050f06041802160b070f020d020a02010c0c08011d1b0108060906040e071203020c04150302010503100302210c09071d0d0606080304061202 73
    0x1001040a40c200d002d4440800c02c100d64610742a040010024090300f964403460060000380c440801c416407100380440351086105100c66512682041072a034942494950022024001048090107514605083e044488001072418008005084580014000c00d032303223811503c0203000700e0030382c4020304601e00000c51000c0c00a661010000075140e4504041c0a8100030291141c0b10500c80c409039841c008000340300003040b1200408642c1c2c100034070003004140c8a8014501a154400c0700100c1701c2c00c01d102c0503510090341d03686200400c4501c0001520701d41c0c0103540c810007000f015108010120103071018244074030b00d07900701d850001e180c8030030340b2581c41c0100d0400d15000080070b0700140c2c0f441038030f038242010764407548e850307440506030039a0f40d2000c0d501400c0c074514000210b18904d0a03402d10506072080d40c52030380030308007800234160051b1428000980c0750080c0e0131641800c1000c4103c280c000905404540c00591a050306403006900800c07226000003034100401d40d0003a4800e1598420701c1c4081d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 749331825 1250 749330575 749330579
    0x18021020190506092e0204090c0905100203090306010b07080702040c0e0f121509030d052703160215070b0a050a050708130308070c0204020c0a02040b010e09160201020702060a02011e0501 82
    0x720442c1c0c400b007401e801171103482021080c283c49980d0180c1c1c0c054011100c00700720904403079500408018a9100b2140108903542c024840107101004440b40a50040c0003400c10f81d29001c05418194000c40050380c02220500070340c00160f40d1400b68410b280215130303d00800009400030801025038bda010750744541070404015081c002c000c200e10f1008a84102c07840c07141d64443c2065070840c407a2078501410680f402d810005126034802006040c203c40000071003000320b0344c2031aa6542e100d000e022410b10034a2454640c01841c12610b103101044442c106603062010325920390001440030340d0b0061800d034817482000184a00c500c595a030003101850225580d0400c05403070741c407050101f54041c003081300340c000003028580034642801c841940980119610001c9070b62040e10f80080c2101284142c0c108100106558428032005000500040c011300b06a264840600e8040b0301001e607102c2503540070720031980942e8940000e402100c1c1726800200e10700c03081e8000c6009a0000e00c40b600c040f07601d05001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 749333075 1250 749331825 749331853
    0xc2406100206040f0809031618060803070f05030409090c03140c01120c140409140702011a06130f0e0f0f0408040e041511040501031802102019050609 66
    0x203160380050f0030119140004c20f00303040a042c07500c6107803100e5030144240305c000000801c41c000c00303070101e441000100d0b140d0881c440e10300d0280d45070f0f41700300c240a60080c0850030208031221240c0c900706201d2003c49284c1680e840480083c0c036003100050380d03501d10702c10041042c0504013815400840c0c3c00c00141015850354000030f404800c1d001c40c0302d003843d640d0f2520b42c0c05441c0100d8a001c04003605206040d11150342c0e070109405051030000c1d000214602c075001c501c0310340c0140520940c40050000880f0154080014060f054200082c5141041040364001500074200d00d00c00b4050426415800d010345416000b0041d071784800341c0500031b500740727003010040407404540c1a40c1c143c804ca800030018984039428100040828482a4080f00345480510b0308006003090052049a000313072018452524440c0d02045040a0b446d0040e400917910201480341c6407292800d501d0541c1000000d61228460080d450b1604021400d0310b80c0e0040707006401810b111081191582c00241100142038411150704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 749334325 1250 749333075 749333083
    0x120403080a11010b030712060b0909061b040e04050114010e040b1302061e0301060207060e03030d021e0a0509011403040c0302010509120f160509010e010b030c0c24061002 75
    0x4190390410034402da482c444000b003034120340744100000341100d10f10703034840e039000003064009801140c1c802e00e004200c01490810702d101d2441190b100018088664404070700485d80c07100d052404025407003c00010516090318413100d07004500030000010564101901003061010681140c3d841f91907003410400010000034010340d0050708540300c0c400004142c80840c800e1300480741802541051190008405032400018604942090b4200d0b054107035258010b0f11101c03184010345805800402c50342800c15000d40050131420001d00502948824281a2903000c1d0031140c41000055030001d080b000325a07002d04201c150080e5400a0391450806030b0340c02509010ba031100031706001000c1381c01c1100396a420204061103021405895803020054160358a58001c07a111500250722050f01044908048616a040c1d03100100c2403c41039007050400545504001c1c007205044400300001c201040e4244a943d90301b502c00f103608514500309140c50040840e00400c1d0500511030104401c540a034006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 749335575 1250 749334325 749334337
    0x7060f14090f0418061b03020f0304020405150a0801020a0e010806010509040c03060506040b030f0108011b0305090a02042301090e1902042d0c03061202120f0d09030512040308 77
    0x49542d800b40041c0d00104001d0041d01014852034030f5200c0c590002d01c0216000802c58400361400c200f01d4264084041e07049001d0160142d000c2c2c4401d1001030010f05080d0f2009401c418001032503180f100c190300008103607a0440c4c000341c00c543d4000c19007490303c076040103032400444024207200d03090785012000203003140214641c3c0d5100395101c0c4660025240694000005403002800c8240c0d10b9454a410015550003030b1092400b0780d130440e0001400c1e00061240d0200c0d5201440e10304244058800120060f00010300b1502044c05820358a0005990b80d100300400c2140750407407481102071041e5001203192050380000c00080c104801c010304100b001c10020984081d01010008a0303986001090090050048410410104083c0c071440c5c102c83e41012441c00c003040505004d07440840c3d10480c145c40d0310b485000100d00c0b04110402c0145000307402881d00606440841c0d00003011800e10034900842c008003c0e01003000e8103010b1050140a12126008c1c444610620303103094916a660302c5240b26007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 749336825 1250 749335575 749335579
    0x8030c030709050a060c02150f03040f050c09070306060201051e070302160c03050a0b01060c1110031e0e16080d03050907030506010305100b04050402090403110a1407060f1409 77
    0x30010720400d0189011034080c0001404c1140d1460302d602010f0000d502d04030050b8861081001041c5200010504a81c20a580705c1c44d042e0442d1103c4d80c410302819080d000450300390103000c07041c034035680340e801a45221361341960f000300e12203143c400c01901b15000608101c4110141e03e400041210b6614030040d0841007501e801641c0301d891010003984c080c1410001400c00f4442d950000c10301c0000160141280d000f040e140b0903036641d802e02031300c1075000c03804014000b12000c0000c610714604864001510100d0307041c007280d40d0440c3e528000702c0030848450301854954070301c21039404a0b002c02c106019541801780803074503642480c070300f03a40c2c810740b1904107000c054403100054086101880400003d5034048200c42895849150040e01c0320382031000748640f81c0c58000e440032249490b000e900e002c0ea40241004020341ca440c0c4084034006140080000d071032144154103030019049007030300400d0300401d00207010040c0c10010000d002c8803241c00b24204100c1c00000e80c0d845418803208541c00007200b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 749338075 1250 749336825 749336827
    0x2b080f041103150901020d05010f080c040c090e09010c09050f0d142a010f1b0b0705040b2107090501090b0a140c0f1e19020f0306010b0a03140408030c 66
    0x79100000e03290600304901141e120b00d150052151840b0150007034100c0c0680004188481da1f2100d2400c042c0348014440c4102d9030740a06861461802e0a50000d04514607502d0b1040340541ca0f1110703031110140030348004290369920307110400015845030b426809440d04440d10064001c07448001400c001035040c01402980040340348051062040100d80110400c00c4844c401c0b00044908101102c40c214207070714003260302907818a07112881490b02460300b420761540c01d03001c5095030315000402c0d41c00074062000e1100c10000400c403c1c81e01c5002c2c02800b504100260b6942a07118203400ca03000020780b904042c4000d074007003841143e07081003643c13003034a040c5106162508030802040b05c80034110f11003115000b80002d0b04039042200070420400a0512404454860144001049020303904038440d040507080901c1c07100303d4208031414220301d18001000321000b4168038002038140701080e030110f0030a18001840c1380d070460700b5005502c0603c605654181d00d618050326404c40520000f0040040031350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 749339325 1250 749338075 749338103
    0x60a03060f0b100807030501140d031b02121006090b060405060d09080a08011d091e0309040203090703140303092e060e0604151212112b080f04 63
    0x1d640d00c403110100c40101820012150910050f02d40c10701583c5c08000a420b00c000402c1501c0d54441101d000500036003139051121a54504031400c003801c880c0141f203c004403000078056a16401c0d40020a04820041d141799005000c0303100448201354020355a280c146102400c80366075210a81c0c2c02c40e02d06851040d69205c0407480b00e8010700110310000d040d00404036203204071640c85040702d810b03078034054250b001c0070144080d0102018401c0302ca49040d640458039407000490002c864801e0044080101c0f802c0c881c405002030242d0300110f4810b0250b5020881c10400d00c0788211013402a081620050f520f0350030008455074a03070b083c4492445143c4004d044240d1035050380101c06800031a040b004104168480c0e00c142d00505c1c0544003d0301c90742c10000341142e40e81c0020100022903800410349140c0203450341c0c17a8010841c041c0d4010f01405840309210050b0702050101c0c0f401d03408003410f0502d030070040e101c800402040c1c00c1004010408201d040000000540d0000c07038003c0c0d00f000c1091300c106 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 749340575 1250 749339325 749339351
    0x31b040902031014010501030b0613060f0c0c170d05040609090c0c0b040609050c0402180909150a0506010906030209090601030f0f0f091e03050d02030a0f0603050f01050f060a0306 79
    0x4043c8164114110b4601011004020007000d4440d0595400b640c0a1040140041c20400c0d2801340c045520740e000c0d8003ea04201d841e0191005440e07400303080c00c10080040c465160180740c0015035112001c00c65102c0205001f100003440035044403915401d205040c14200b00d001001202d1038003402100558505400390854000c011141409911040c080030034509803508201803c491201200c403485012100303211b6140c503000355145444c6004200002031041c00030080c81c4140503000312041c5c0143c400036601998110421449071801c0000400c00e410078000040c011081c1d5480364003094418000e02c0c03a241d075640c00c00783d0040c0342481c1c0424100c810312103140c001d0181401a114075494100d001455845580000404502540000d98442c0d0f02d1400c24000441e82c10004000074000c010100c80303840b007980a160000014040050403003507103a540c0045400d107070401d072090390100150a02c0300200340520380d40800200d920300d616040147c00316400d245640000dc05e0681c403141034000742 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 749341825 1250 749340575 749340583
    0x14091b010201020d18030e1c02130b03060f010315090b06010c020a0b0a0e010e0a0e04120c0507061707180b0703050904112203150e160303050315031b04090203 70
    0x10030300786420400054480c0d045694a0a001c8048001c2000c00c52100410b03d40723503000c4424124222540c0c400302c0040d508100d290018640410500741d50303245241866101042450711175805490020a5941942003898100700c1c003596820100f8280b031280c9000500290300b0a030002400e0900d280701c50b096100103034408155401800340340340e000c10703a1016541c2c00000020803010a80700c0c201c8500071a41402440300150180e174003468076000202c0c0001d1a4050701104030740c1c0790f15007210640080d9440c5810041c0c550f000100141200c0340c4544202844d08466400985a04041d640c2911455403001b503c140b41c03081c001c007104041211002e050040342207914800c8010410001954441814141504076900524140c080261840300d02c0c940c00c1c0541041d41d410030003014000303920916090141545607071452040c05400d0312480904c0d4400202c002840c0b00f42c0b182c503201c0c07801c0e1400c0c20b595038403500820720a900219540e80c0488803881303104030369a025240410700440a0000ca850 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 749343075 1250 749341825 749341837
    0x13005040f0b0a02270d020f0d050312250c03081902030a09030908061b1c0513050d0309170a050c0303070e040506180604050402010e060f040914091b01020102 70
    0x282d88404420051001035550003052403111008128010402040403107024440c9044850741209861030035401614240d90300c00450b185c01411580c2480701c55490504680250100b008003032880c8041c8218180c2c141d4a1001019400c042c141d005090200e004150308450007024040c806038102144034501b0014480101402c40f001c19950303401d2400701000101940402a0700040000d0740100300d555010030580d0095075008039034415a88844100e008a900070100c5003034000103c4400c80c2c2d10b0140340281407040d00d00f003414080680450070700703a06002c40c2291000803d49400300080001c1c4c801000b001080401f59005611034031400713001d17100340c0700780c208422041c0300101c00c01909d02c4c0d0001d5452410802030310140f106880d0041809030222004608045100500c40028000d0501e948020f0b1b11a00514000240703000030000b0400e0341e400340c0e03403030b402c0a48009010f100c0f03c5114011190303d0a04504005036034a80080b800c0c0c0c82d20040c60724022011501c0400d03c945d68030035010f40791 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 749344325 1250 749343075 749343083
    0xc070201030c0e0a1e0e07120b0f090c03100902090a06050711040e1c03020f0702102a021e0f06030907030b0c0c0c030c1f0c0b04060b013005040f 64
    0x503aa9200c80040784082c1c640005040007506150000c01c003407803501c1d07042c1c0c004d407c292101150300b41e50000101c0035100c1d0030383c039a4120818040342112a902c9010705800b07003c100c145a540ea050003411500088900e8000c51010f900400c5042801e0315132300b20400895809180654540c2c90600d483d1030346a100c2c0e00144c0d0300908120000076002004150225014605443d00c2d2010804000503001da01510015180b10b0806200302005428910107440c6450300360b20300308201e45a0000000d141c00d210140c81d2400c11502052181142070041e250002041082900c0407103240c15400500c015400540040c0117110201c007045c901c60007004000040c503070000211015141c03076074030b204060300f0105414900d8030841e00d0456060401080f80444000d01518240d280c031348c810112010741e078020380d804081209072840000450400110640614480c40d8041950100d0350001031041024084501005110030a9900301086800f0300c1c149030141948007140c0d80e81c807401e150200c14201e0381c001d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 749345575 1250 749344325 749344339
    0x50102120702010e191805090d0e01050c01060608100f0503210c0a080a17060901060f022503050106081f0c0903080a020601051e0d140322060906080c070201030c0e 72
    0x140d0b036101e80d07405d880242c0b15407003880c3c50307107019505460302510016110707500b10760000c65251001904c07480070006d030807106040c00d40c03510600b031050600712134140d4004000120907000340999820011080030060000100700a0b00c1350130704000989510480f020690107800380065091064020303015110140000401c1d949a589941460b00c0290b0100d01c1e0840021f4000c0d040601c603411101e20f2a000da00040c0c110310300e036804c1900982c3d000110b8607110741544180450030204011550082c0c0ca0703032032512500000302c0d2031850b0150a596040d00610b41c0d9411a003210020b02c20b0070400410500781001d00810010704991003507074450040d41001e45804400120100e13110b03000104a07048900c141d60403848800d1410002e58403280514105910a60038002c21000c540f09040581000ca00344050741d00c3d00500524140c0b12284d110003c006058042104110040d00116030724003e10582c2022003407807034003408100980c0300d0b0460090625546101682c42c00d80705803601d105906000d0980c1e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 749346825 1250 749345575 749345599
    0x3090114090102040f090c080f041e0302070510053406050c2817090f062a0304080d050a060506030c04080f030f0909090a02061b010f06050102120702010e 68
    0xa8040d600c54025031a0250300000006040c0c6c40c2881035060941907503030303480819100c8602c1800031000282040d100800c0c0d1800064851070003a4031042d0141c03080d002010030900d49010b01888007240c961203006c0c0030b414400320360324404c20301c1540301c42c4043d50b00d22800c0510094220548248001000d0011890401000001760909008000041544810301408080d090f03a005030154840c10403000214084d0500314000c40303020b404c94100d001c00040d6503007920601e070010318010040b5402c1541080c8883ca240c50405035400ca80d10400c6a0f4284900c3e6150545a480c59482032160128083d030b41c0300c0002d81d09000503031050010345030041626036203041169078050950418010305015004080800e224003c00000b1100c00001b841000c80c2040310041c20002009402030071208680644034011005a48803402481c1032005603050104030340d5217801c1d41e421190b00c01c0d0036400c118a40107040c40745030380014266900c0245070b2179550796105240700490f000304c400c410050b003003103045041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 749348075 1250 749346825 749346841
    0xc0c033a030e03130335180405041b140f01050a0210050114010908062202030304090903020106030b22060b210a020f0a0b07020d0609020d060506010216030503090603090114 76
    0x15a07005c0368014290031281101030105288103209880214030b0144204249418140040b409081c2281c1e948010314480086100402d06413081210219807025442114803001c00b8281001c2c801b50200080d00780303d45032554041818287d0001c115410321601191030010b1038420041095036228000052209596038040036402000280070b544c04501406004034616000094652003460140100c0c0d1400c102c4d82c560f0301c0500d8288000b83d0f01030100300404104590180610020795219900004119241d400c090f003942031701400c08501c076154103014200c080b01e0a244220000d80200c0002419071206000524540c0310040303500416075100e24003000d028020840e84a424000d6400006901c1c0e0381d0100030315050070703015400280f502400064094186000d09101080c8511030002d0358400725000a40c1015000f80d04030350a5464070100881c0d56414010119030f803101252021380c00342143d4866449004500945007e0070000c40010b00c1c07143d01350441c0d0700c8840e684902c030081c1d0900e008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 749349325 1250 749348075 749348107
    0x80109051023030609010b010e15040b180907080f15280317040312030b030c040f0504261b120f19050f070f0201140c0c033a030e03 58
    0x10b41c4030340101c500103071840406005408564405a580d164808e03188420003410300680c0d0300d1213241090901010070512000300080402100c591001300081c502481002041c4100074141b8040104507000c1c000d00802c01070b41c098100000030040641c82c0c1240d008101c42010385d1221121440349078589011310146850b030348091b00c0c01043c0300c2c0951000c8001401440c412440b000b090f8401c1d00380100c0d5001d100f076001c9450074800600380e0b0f2068040070001001d860507040703080390095a070403d00007000700340f0041003000112008001c205400a40c10711010703000d12211500d4501c0d4918111a18500902511441c4070030302d10021340342c801d800c40184040c4c000ca241c10743c14178134100c1695422070040f4241c07030f5650308503504e05207012150ba45843c0d45204403481241844800002404610f119032b0283c0301c101c608c02d009150b940b501a080518011941440001c19803805480c03100c013000382804186101070300e0b0705103c05546000811001001012084a603600001c80c400403c211640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 749350575 1250 749349325 749349389
    0x120070b06121e030c0307060212060103060b04050f030106030209040605040b070c0c09020d090204090303020c010c0c050303011517010e06151822110d15060801090510 74
    0x450403400d55522030382485080529141060903561001d44800206080f031480345000e1403000d401e803030400034000401861a0000301044412603004a41d004507003807400c0e801540100c00b46414017a0901e00340303201005105a01503140610549544400603803401d400910080d5030241c5400366918040c10030030000e2006507001c0390408581001f01d002107210315554521243c000110602491030003820400960140c41d00c2c4a005441c2d040d134002681e55031050807a4103001e501e002d070f61505045000d80c2144c051094030820300880c1040403022840010940741562142000b0b61000700e10060107580c1c03080c0006030140c0c030168103400030a0760140d80c2891070082d5015110502e1080b40007e100700c030b07809500d41090071030301d00c1140003d492400402d655203001c0d442c204284401800c20046003611031401b8000007801c00012216002c0c80301b40300e20408406204000050f1a08002c0c008014080610408218544070b00c04103251610710348110740104000c0c00066990301c41c1c007a584810f95281 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 749351825 1250 749350575 749350583
    0x91802220e03030f0f04030c0b270109030909020304020f0603041412090306041101110d0e090604021e0a09150e01020d1e261305010c020a080714012007 67
    0x41424600307558000000d89001d11401c1001900d103039128411001c850714001d0090742084954840b03080804c4500d800d1a02070894400d485010310340244c03c00c030500c0c2c81c0c0b101c7d8404580c900185000807980c0304d041c20054940c1000c01507500d0300c0d54000501c1d654045103e09034080000424001040042d42509052034098019940f00c42c1490310707070002c20701030418030036090f03004a000180000d1509001c1c1c03843c0e0b00141000103809070445d00480c6483c211850840100b8400d54402c80c1900d80440c8080e4031000c100c80c19403034100d083e4a002d002d811a00c00329644404003040079241a4000c09014010b0804c50926101040706240c1c02004440791600301c0b80980211711030303801c0a520450340d8a1506016924881d6070f080358080c00c4510400540aa0a404842502c9003200d4400c03a0a118025103040d43e003244821202d0038854211880c1c1032004056600490403080026961000d07100b0040d00215000501e08000e4411405000301343d181e1005051000c0b805001d40c0e040501821806020b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 749353075 1250 749351825 749351831
    0xc1e0d061e12020a051002121803061b0703140c1501140406031e020103110412050f03070b16030e0a08043002120a21030c0e0a09180222 60
    0x5a0400351801c0c02c2e0502c40650013030140f00c414003803804c000c0d02108081042e44116a1000c8010400000ca5040900f0072400d0300d41c614441c1e0820f280801c00c5581191803400c06030800341e41d455200d40544100b1170000c040c400e030040f44140041800096902d2405504241c6214410381d40390845c1e503d01c24041c910090b0101a6100d01c5803c0c00e210b034200303403540a43c1c00741821b154001c9a20f071b03020100301c040381003544070a4100c4035840b508000c1c100074000041c181d401d03a145480d24a0801c10805010b0260364001d20005c40429131550885801100601645e050040c0c51017080b0f000c1c220301c1d801c5440030310a039642c840800880c10700800032600709040c3e0740001b10500c0445407000e0002034070f405c0008800c46006000d0710b00300d80e15a240420302011521111299503800c3c1d190950405682d0003031101c0d220000030541c00d07002d000c0100c0c50301c1c42c01640107007541000484032004c901651143c5581e0302014055109111000700103da0028174500c011840500c0f803500c24011004012240c44c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 749354325 1250 749353075 749353079
    0x31903170a1a01110703020d0c090516020c010e01050c030310150221030a060e04030302030105132d3306030524040f020708071a0c1e0d061e 62
    0x2070240302c1d09808141c009000824410302c00011618090314640030b80303681c01442000001a0358028580300101c0c454800c21004510786541c4d081203560003000000b5803a66490940e02c02540481c41b00900d0390242070008484002c107004a541b8060441c01c3c1d64a88400024014070104c4802407008460318a160b044028015070001c0b6210390140d8100120b609041041c0480103610a0156a10040402c00022100c4d82d40c0509000d46c6004e55064010980c008018040e604041c0034141d06120404c00030b12039010480c180d4681c0d500d680c01410360710390300c1d40b40c4080041c4481d0090840200b08007040c3c07104e005030444080c02d0150607061119400644040010502e01a0181c075100341e801340440d080a108200c41c8046105c401185980e11580d101c0c0c0305810315080748041e0940e80c0c05903611644032421440c0001d545160515840b0303803040030100308002058554104c42ca001e40803621107021210b04602441180140c081d8194014100300020660f2000b85140d100e00201618105982075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 749355575 1250 749354325 749354341
    0x308031509010602120d0e0a0c1d13151d011a120a0305040e070302040e01090902011106010e07031a030706050c0601090c0f1b020a0308090f120309010e03190317 71
    0x20350560f64800e4003031300074000891b0412007540f0441c81c030741401c4103441c01c0340c01c90303a00c4900402e000d400101660303c0328030043c000c4266188486600c641c0c503151021108066403a40d03030b0001d24034440403d40c0d0740c03610b868503d60704000d04105098a1030900038031840d105066051a081c6c0340307c2000c4d005181c50700d42248840c1000840c9068213415454203441c01e0304140e4002c40d02c800040c445030030b1507001c00c40000c0001005036080d00070402c100c0009003041c40d6100050408400025120003035001d1401481100346c0c400345031703400124500700010400040041440701d03da085000d0340d40760050342c20024610f80c21000900789400600b09851030380e038071342c0c0012007101d100c501003c3c0065000c1007030301817980c080d0f100324002140030070a0021a40f03140d400142e8030105d0740c04c102c0d658100030400791311906010000003140b01007151044800c014044001d070780c0c0e000c0c52080c43d040116922441e06180c400348601021061103950b2a140d580c5942005440ca0b00450a500d0440741078100040c0e140d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 749356825 1250 749355575 749355583
    0x1380301020f0301141f09061b12050d0f09120e0d050a02060f120a1b02070803180d050f0f0c0f0609310905120708031308040308031509010602 63
    0xb5820001440b4156401e02c8454820042080001d81c4c00c0070480000c4480e01c1c010032140883c025181d41c80410f42410440020403200084182800034072022019a00041d51204840b8407003c051800715102d00e00400d411380686004140c409250345001c0e080d4047c41500070113442a40200e48611980c840c4150901ca503108000c070014016810412500c0c2c018581a8002c14201200c900c070142840c002281c1004450b0098691520103988c0760200300d504d02032140c1c140c0d03c420960000d0b0240d00d00d414503150701e9116984542d0683c8144042d00e0300c640e59010340c07400400da0440102c2d8410700c036951420b5511402c1e607604807810322900074000c1ca00e00e810104c044180601414550034000740b002440301e10040e104090390f42040c20b00000b00d00d160a4515411000b40c0040d020803c11090b08100341400c55071900891190344c1040814041010a001c4079000024a50019003026a40c20180c40c0c60007241c0000381002000030911600c10104c139102c01114030115550415640c0c2c0d00404d80e55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 749358075 1250 749356825 749356837
    0x60e1503090a060209030a0c120b16021504020a09090c0603110a0f030b13050705090112060b0406110a0c0e01090b0a1a07020a031401061e0609050d050138030102 71
    0x50740c00b82000400051454000e40392050001d0129048041c107651000c50140c0b0a820000b0003960349062074040c08580030103c0c3d00a15030b0b4081e5403030543e904800030749604080d03024032000e00c2c504012a00b1500c4d00340c44a00200590441080b41d1140c0786008007103900c0b544640c03c006401c04036034060030402c050844084007010f032100c85081791250420741c0681034590000381d004031f250350000c8910301a80900361080c9020ba50b902d0b9210fa0410001d00400f250142466071903182c10401d0006a000c44200d6098a0700b40c2003420a4000c03060302245030800c1d40c1001400031340c19020014000c240442c074036050310010030003030100d800b4030000d00c0181240351140c00d1100c08800c0004550059450007000282d00140051000710303204c1d1038402c0900c00e541c0714003145a554140801184074084100d800c0705080c2030091101d2031804200038403031602401a14800d080f11104d41040010075845a002070220032840c840300886041d0700c90001828040200d0208401c4080503100d140610854030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 749359325 1250 749358075 749358091
    0x81e040b0a080a02130305100c0806090f100f0e1608060a050405060402091c020109051c060f14042109030b01030b0a0207020303030c09150313061a0a060e1503 70
    0x10070812007450440b0012009446071071082c0d820030506010355501c80f600c4001d14003900080c0345010243c1450003ca407040c28201c82040f4018041c000150f482e0004660403d03903400c6414201d07240c51000c0c81082400b640500041500c480c0c00240c86600442251700c42c0e080c1008903681080c91900943d050001203800a62204010406002514103a07028030b03003141014100504018221020a20412200c1c00a5490307095540325081190703808562000a80000d64070711030803804180d50410007032640714004000070744038004140c00703228a80c050311181c660843ca0b01910304182c1040d15820600c07601844050b014900312034841401464100100c90b44001710328804e80c0782d030b26400c2c005a00503100e4152180c0070070964016036800c0010714001c0d618181c0080da40c00c02e5004209a49001d000e082641d0241401008121038008481c400e00d550054404104035980840d550400333803486030b0450340500780d030201081199205903c00111081910220203008410154280501040720908 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 749360575 1250 749359325 749359327
    0x30f040222050f1608340302090f0418061a1c03020d0504060906050c1002040b040f090b0105190e0a1d220813050405240409020f190305010207081e040b 67
    0x1981140401b0209440c00e100724503020704910140348504c1741c1882c4e9402040c0026000700700d0040d946005200180020700032a010131825000b5000315030040c059044c040c0c07080380d443d04100012900062111034000006000866020388503d00340101580a4015030041c8640003550103d140038500321400e80b41240c640d0302e4000c0c500304046403e81d0044114404e14003d00d810304c0c00c2210203002030800741c405800640c1d01c03070781440e8848e8501d00d141d610501c0a24201000e071451641c12408848000c0013012942101f100c45480c01e441840e034401645402030f541607000200001c18444111402815410400c2c4940355414101075481400048414130130f020b901d47c1c0c0002d41100f0040c00c4560fa20403201d2040355a8400182c200e410480c0d9102601204450000408000641c050005182164100a001c5642c2c010504044100300e940d40500c4904031032104141081304040015079025009650b034090b10b180410040e0065008050783c00001440079000d154030800340e40565420b21001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 749361825 1250 749360575 749360581
    0x303090317012d0b0a020303010512061303030b0d0f0b0618010315021e070503190f2a080f04050f0a0e0a0b0d0204020d060302090703020f030f040222050f1608 70
    0x440c5801c6040350803d215420608400181540c044d000ba104000c1a80c000d1901da40c50031080c401104100000000c05411000400c4581c940c44d0300c518030b8003038061500240e41048103000c00c40700b82140e00f02034050014000307840200811021f00fa44200015a0450325141c07000048464410080c08009c00500c02c01c03903880c0c00c80c09154064481100401c40305504002e134400b8440340c42d801641b00740c52a40000815045000001d070310089050380c503140c45840d181da10303000244110801083d1400141907002c050080c035046d0138040308169005650355070740d031200c0180f69100c1e9205108182c010104070b282c0d883d040c9880c040b48400c070b9000305100e009a913502c0380b414004100d02901140d0200e92814000050703140c2e0301c06408042c01268000401906500410a684000910400806004111200c20a156081540d411440b030705610309607501c41e44001604a003404112216800d070130106e9031741032091134200f80e000722007100302e0300260303240e0405502c845480301882d2400f040700a804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 749363075 1250 749361825 749361869
    0x3020c040908310608060f0d05070506040609080606090903030c130f06080405010605060a051209030706021c06060e010e10170108100e0f07060c0f050109030309031701 74
    0x103001e00ca9a5110b03d020003681d80c0d80f0605800e54140483c48055110350020301c5801c0c1d400f070000d8552030900010900d4840300080c450640e0f0320002d070103518400c49100c2040000c04c46000504002000151503070303120000201003058511640c1442d12902c0d0102d40c06080c00d8129500402c40700340a14036559485011115a034041d02d44003059030110080050075404503400c81f80900030a554035030782d0b41084c2c14040e09540c4e59800061044600300003036040d40341c03c40119110b40ca01d03443c034002d80c0d5442c070f14018250f020707403400902500c2c00050b0041540f40c0000c0301443c0c01c0d05015042000f107842d8101290000720500c042400329200c00740c1a4040e2900039001101c510b03044c9071100410850900d8070380e001c20280e00542960748440504512500c05000d4415442c0082009100500e030043d482644c03002544585400e001c0c00b5581030060148001c05000b040f0780282c028004038000b840c0050090846007810380020314000340c500c8001c1d400c0002c00b0304841c0c144980760702c0e103119505 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 749364325 1250 749363075 749363081
    0x1e100504050a0b040c080102040e06030105150109061101110d0e0d03020f040b2d0a0201060614031611070b070312020306090705030901090b090c0a080a2d020303030a2703020c04 78
    0x205030381d0300005c4c04000030b640109000030b00c0548058007066006040040900d402d40b01c014011000703218015900310130030b90388000300004603015440c05400c1c96918200035030050100442285880b80d002500c80000718941d00000e8a02880804071200c801c00301104a0490107451b4500da00c83e10100300404c0303141418006010500b00c0100b84481c629021b00301810002044040c0e0312030382030301141a090854080c030070f075402015036050010f40001900854403041c80000c240480c1195007150150f81c0a00c546120304610020800b00c0325042d40340c01c4044087d0b040368900b100020016030741c0400580c039034003e0324000c10018203c00342c20b865041c1c0558150304010481004c0f5960361035410042640d4102c914010b000100c05441c0c103141c80d1b400c1c080040c0040d0000001e90740005a0b1100180d0080c06240700060700039240740300048620241c107010034080f03501a5062102105026000480303078000030b50240c10701d4420a41e035031070958030207441104c5003010b405038204103641031450070190 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 749365575 1250 749364325 749364331
    0x8120408061914040b100504090b0f270a0605010605040303020a171309022104020a0e0603030d020a0503070207140a0e060d0503120f101412010e1e100504050a0b 71
    0x101000ca01c100302d500910b2030061013110300b40c1704039000005000181d981c00b40305001070034082e1414042c800307003a02c4080503444e000d484000954a09000a201801c00b42c0c00c646d002140098210040c031490b0400b00c0d0349108031300e01600c442e4945000020050f0081c0f040740c003201e5264000c2c0035403620070b4584000401c500b5a11030b82489041142402c00882d2503100b40242039914001600d0f00040c0f145d81d000b00c8842e1405030a00350a4005020240e80c8803c4504210303070128000c0c040590f203804c00709065000d00901800043e0020920f180c0460300030001d94801c0b8801d9080b00d10003952281c25205c443c42c1040050b0304412780c07800a00c0b501c00e405110300c7c0c1c02030340600003500e0700e10580d44191443d0b1111850440b41c04601040c0058441c07001b01640c2c00c0803460070303807158103404d0401026889034a0044103202c1c0e000c146401950078000c6d0802d080c2104d0300001e6440b550320bc0c02061400d400c2e0402d005039640a070030426240a15a4860680259040001416412803540d90704413814005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 749366825 1250 749365575 749365621
    0x1f05060703120204060c14060c030414010f05070f03050f0103170d110703020307020a060e0a060e0f0a2402060915060d081c270605060109080609070812040806 70
    0x3034114810102c640001d100a0105a44040359031140c2d040400c0035441300900205181c00c140148a012000201980d400c541c004e9030504030284280302d814014040c0c5080720000da0f003441c0401002d507810007840c510b9440180c90900c07090f81c805d070121000d81403d02004004141c80401c641007003c001c03000d00b0742850b814100280002c2540302000c466007000030100d0050380002050021418560003010044c11942840c0403c0401040000c000c50420302441d0100710381c00e000000c041d0b440c80071207442c0941c0a0004c14540b07881d80d86401c0034424009000d03001c03440a1119080f000d1000a0341440f88600c44040c000c0070001003010087e400020f00740b180c0c010f050b1000b000101d59000002d1452806484d40b03004034000520030042607528594817280d401c00d424078161181107444142c0400356510220029490ba6030703000507590021281c11000340c61003001c0400c0401100098507034241c1e540102100d00c2100007409801c814800c502840d2403030b070404070109581180384124841c3c001c40c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 749368075 1250 749366825 749366837
    0xb0c03181c0f1404120501060f0b160204180b06010f14030112030c02030d030209130b1305040602040f03050a110d03020d080403140a050d0c1d15070f0510051f05060703 74
    0x142c803440f0807690095000003014401540340c02041250034454a4000c2c201440206200c510b4500035240c42e0050400600b1001c018444120856840742c0c000b024070461401e0320070351038540b0b082035080c40310102d41c00c502060300800d03841c0322580581f40c0741028541c01a05207246038200864a0001608401c01320180f00141032170000694040c0b000f1841c0710426a00142c96295000411500410301c1400b0303501c552400600541c1a106c4a41b451608443e44030702090688032403071b02c0710081c4034a920840c2d100c440d00030040100000814440391040c0518081d038502c01068003080800c0c1c12010000700581d0007520b841c0046401200e401b42d1060190500503194500c5000d4000a5030081003058001440044c0d500c8644c0c80c0c0d84540c030a122100d280c42060309240c1044996502180c00c0480c1c40b41485100544040c2c510304204c40904d5440780d002015103415282559903201e0455568034000e09110000fa0071100c5200081484404001840103180c50507060165035032000718203404100c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 749369325 1250 749368075 749368097
    0x122c04020d181209050109120809030c120d12050112020d0510230703050f24041109090c191d040903080a0c1e03020a0c0b0c03181c0f 59
    0x40c1e1041c0c04207040f806240310000e4480b003c0001800d00516400043c1480384840044c03100e14031210100003019803040c00720fa60b0f4258140081d1500c0242c006080d4451000200c0d191225800b08800600c04265146d6056800361004098141d40b024001e64030040c0424040c04090f241c054414042e55010f141942e02030300c501007800301a504440d5800c4000c081d030a81030307025146c0001c00b0719400740c10342c982044030341000708980b003130400b0250480318a4028510030020022504200003040d05004104000c00000d00580c10015045548011310480340c0000056088600c5400c40d440d1a03880d004245c0201c000c214141d40500b085000c0b1300300f141ca40c000d003030002d4486100d441c514601030b031103401881c50140894000d9428800041003040560303130304020107690103115020300004034100583c0b035000412040721021b40c1000c018040380100011311840302001402903004546d0350411100342c1c001d01d0a2f1507680d811807056030b9000100b1070140210284605042c0d2035044244c0740400000c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 749370575 1250 749369325 749369351
    0x190506061b070e0f040507170708030409060905090d020c240a031e0207020306040b1f1503060b09010804030315083306091305120304122c04020d 64
    0x188546618455101c02d8051108118444030168492040640404c440c94182d584035143c01091080d507240d800c540485031a00241403100201500c0320404980d1515501d07022800988500c7c031407000720360300d420b02041d50b469010414071480c2c0c420740c00030881c455504d0f040c0800e408181c1c0140c0902c04440b01c1c40180c0000410007400340f81c11f15038010402e4035195440d101003072400a9007503203a5204201044c01a00c4c0801c80a5202d500710543d840c840e6518010302c076402103040000c240500e0260301c0130a480b20f01c01c001c400c2e42e40c0d03180e80401403182c0b5009410650b200300b00105022440c02400180007901c0794008143d00c00d600c1000740c003a2542c52401c10b103001c00d2815a8228525881d1141280c0e1269900240340304003c4202200351b82011804950542800b8001e103038035030b00f0080381009010b410483c0001400507000910f0b40d03880c0600b0003000281ca403520610010310556444c01701c800f4040b00c0d042da16545018900240042401000001e51000c0c41240c0c51701c1d140d1440044030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 749371825 1250 749370575 749370607
    0x2220204030c14010801050108160e040e0307030c0b0a0504150b0a03020a0b09040e0601470d0e0c060421050709150b0304050d0815031e0c030619050606 67
    0x400c50403c115841c01c01e014005000765005070070050411246200300050808084900385000d052402c01c4502000c221002c640940f0400d005444907100018846003016802405540058010b0505003190b03218041414113490068030041d09991100c0d0032840250500d500480920760000c007100c50b25581ca034040342900685c3e5211400341c032400315503070b2914181402043e1a200c40c0b1710240259604001100c040303814080a03043e4207526000c0b030030043d520b150411001d12030300300c59413074030b880d00084c100d221582c00300c1c4544144605100c612030311302c240000d4050f61403d00034081410181403200981c040110815002405900c01742e03a0070105100b40701080140003c64004168403045109111010750f0590100100520800401010800114540c645141c29241c003003015181c1c00700c01e040c240141d080440d0f150241013215402206800c0c0141c2d40c20001034207a4030381c0419602090384651085654018a10f652840510b0f002601c0c1d10140c0e01c040c00404050402c50f0313080c984019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 749373075 1250 749371825 749371829
    0x1a01120305030f0c1e030115032703090801060b0306100c0c031e1b08071d01060c080405040c020d020607170408070c0f060908060a050105220605120604020f030a02220204030c 77
    0x1868400100502c422a2039403215141508203007000d00ad8080c403d511028400c84000780340600c40c808420201c201440b61000760000d04607200203000194481540c0d00c0140c1c025500765105032056004060410301940081c60200c0c0c0000040010700d24548801e14643e00d03000f06c078014018110017080c000707112070b2159032840d440e0786d90b20140541031562662074a43ea903002121154181c203d40c0010342d5001d21600d040d21460316042130440c2c01447c102e601c0340101d170405940107013010141e0711202d0f80014500d62262003582201c0280d240d00380260307500f80200c0031080412503400c0c009008074441c2d0700103229203031290303d4010404d1b54a400a840c0002c59400007030000d01450010400c00204000e1150420784910081006525210000d03400a003a09400121514500d0f6504980292548031000030070002d01520110039880c112180c507104100c4080307200f1101026131066504000a00401d083d030b001c2d0601880300d0f119940204280c83c406c080601c0141c081001000182c3e40b0106580 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 749374325 1250 749373075 749373127
    0x7030f150312050c0d030c170103060506040b0609030c0d15060f060801080d0813050a0519021203030919170d0f050f061f1b1a01120305030f0c 63
    0xc1424154540402c040352541d166508001c41803000c0e4122081c0802c040e465903d40d4200002c052205420560388624900c00b1461000c0070743c4000400c5c01482d4200303a2007004116810407442c0d068008100741c038050010800c0e0594840000c143c000d081c0501214441405003500c03031800303074071443c0359070030703250150000c2480c400c01560402c4626040341e00c1a01501ca510050311805000c05c0d4000c0c408080200851100300c06070a101c002d12030180880104aa008801d03580301e44c0c541c0500d82c800740c0c000b080890050b101c00800020101c4003000b0799004061801c0a0420680c03040c40018030764050002c240c07a2082d421401e08174182d203820081025881c10300f404500f8038054500c0c1021660300070504d0f03022501c440d080241d503a40381a81e0202109244068183d4151400c2040380c184814803100d159203042803030b0450502101d4905803002000345885080d09a0300c410090700f41c0b040149005010400500200d11400c0d454507010307500590b9102002d00304011a0300e0891007071010b04843c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 749375575 1250 749374325 749374361
    0x120b0d03030b03060a020405010c02010e060d290d110f2b0b1305060118020f0c1501060c112103031f0609060c0b0606070c03080c160e070807030f 64
    0x1404030308041c010f40340d01c6170548000310300f8646803500190009a01a400030b04100004480005954414043c0e44007003801c4081040190f540c40c925120089018000040c13001c0c854a060030785281c1001d46c0d0903030a50018141010700c8103203040c00b25049800300400c0e07105011002d96000c01e000c0c085502001da102030381041e80c0001c3d0781040001010301403c2e042c2d400841541140118500141c644d045500807503201d034504d03c3e552030b4100207024009040700c1d82e0702c002400b0180c801c40014045090342120005a540e41d9840c4000d480f00b1b6104a030040c40880c200344150682e2802080300d00c1409002c91207200a0010000c00e1411503004540c07502040404c061030800031030b265480c1c0e138064080b50515545081c107102000d880a9500781c40285031440c1240000c40710b440d4417082e60b061b2903108208104031600c1e464040525000100070360245e1207200080311800f000800d000003101c480445680e041e4407130b2030040300e0214004020313806040c0c48200c99a03150348a84681030150003192880 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 749376825 1250 749375575 749375591
    0x50709120609020103110a020d1d1005030a1424010311030c120105060c0a0f0f0c0b070302060f070e0f0f120106061418091503010903050a0809070312120b0d0303 71
    0x941110322100386c41c074079003034103000c40400c0c0c40d000500320080322420b013800c1c1d800c0b030200428140c0012188206940101c459462503020580000186018800b030010078400780b081c40c524000c880e58120ae43c4a006010902400c50000d64042e074040d0b03a070018500450001c4694120418503030050b0b58081d00c0315000241e41404021390500d0f00c1c003401e800c9440303610300180d0200c3e0f907681e56456440904a0034841d0b0403201000b1344200b0b9104031903800081500e006030344100e00040b81d0020b0f141503015000781000603000110040183c0d1040d80203460791400800d1000c180030b804001c40c00000d0300414200b40c101015914900e0f4801e001c0d0840d0004290281003083c01040004d41a14406800b03a0a01c6003c04014400000c00c0346800295001d05042e9591440743c44110007519003c0d4255103801408028540e1120040c070016180d40c076502c1041d140c00b80c0943d1f540e80648000f42c03949041d900d403d0006417061b90108004031440c0b101042ea00980f400241200b42080f40c102d010030b81e0f030110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 749378075 1250 749376825 749376827
    0x100507061503140708030d021b0a03020f06010806130f03030e012a0e0906060705150a090c140d170c12091503090309040203060607080703031e0e100507091206090201 73
    0x1a10300040d11103c00751a202d4509405d09550b40625100520140d0b0041121200c030f16151303181d140c02803028011203a4100141c100030351207080035882c6918501030180003180503000003549038001c0c0c1200d1400100f00c541501e580000000d841c0c2c08a04050b11445e0b8000413400900603124483da05405100781c2440c0c420001d071035034042c00c443d0018824050b070306c0d020039030350002c2c5150f0103982628501d40e10138081c41c10a0510703175402c1c000102c5012200030300080c198240d118010b094481c80d030a2030340c180c5826403400ca807184500f0507a0f1100000d0742075030000d000c080d11032210102c03244070700e8140307901001d100b41026001c804102b0000d0011450440d0b51804511104800c3d500c0d080f2545182041601c85d9200d00c950340700240110b070004041003554558104a55080c7d4118480c10386611040c50024041d1503040115a141d072a89101c100c041804d901c140880420f01c0c43c02803074944070240b37911018050060600c01800010340c07000484c0c1160100d01e444052003a28009001a21440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 749379325 1250 749378075 749378093
    0x50610150306300807080711060903030a03150b0408030c07060305041709030a0b0915010905070c0b040f0c030308010e070513050d06090c1805060f0a0302100507061503 74
    0x3000c00c1609102c001c02580214042d841224114000c3c1200c142d201000707540da10212440005182510004211041c410002d0150055070310070f90428010354698020401c01d030155204066064000b0020280060b003c0c0e40810b00014400e120362000e079030345c0c41c4040329075040b03548418465000001c01045014003448000c2c0a010303181000c018500341500c0c1d00b02403c501c140342c4008403100081c1488070795020840a0350555010003c07007080d00c1c18100042d2551010f0b0141c1c0400c850740d10001c42c041d007603070040d60b02c40c8109a5610140040ca0340303600e40500c40103842920101020b0344540082400f01c81000060b44c040d032601547d82d490503000c0c1001c104002d01910401900380a2894190501500c85048030000c82e180303000c580301400c00d42d00074482c6030f03001440c0303941900c1c00161140c0003002e9841d080001c800c0c03c0060350b0b40c2006025000c0d5120070b0580e4001c4d182c110a20040c03411011004101482e80b03003050406e0503940d11307001148c82c1d5110361070342104261000c2080140c110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 749380575 1250 749379325 749379359
    0x501110a080604200f190e0906010c15090f0b0a0501060f05040f1401030e010905070602011515030908120f150409030909050603030c0709140112030f1b050610 70
    0x920b080209401400700b40002c403919405190400c01c0c0003030210498440c00086d981902c402e0302c01604a800c43c01030151400200c20a0640030344900c1000404540c0183c0158084a030045030700001c00e400c04100d080108100702084843d549440040700c0842c0c5d103948003500c114240d80001a0650515101038940100d8800d030200b0084104001e003c01c10307100520000712a40c1d80c07507500d2401112001039028040c01450304049610f01a19202884030000d030b07503811145c007a0001c000c14100e01c00000c0411b43c86000703401c0b00340e4006182010042c8240e0040460501802c031041c1029481d080840c00410107640300721441031001e081c04a0070540d85581b04182d0030441d0100202042a60090640089031140c0059241d40c2d50021710661404d10071070b060050000140e0380d40d13a0311050058010800900c45030082c03c00b05001050001c5864042c117915505911106810018154101c0d914581c0000c00d80840a000001c600001c00070000c2c2030040d109081015400c44c2400c0310301c00500284 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 749381825 1250 749380575 749380579
    0x90e010615021b01030624030e01020c1c14070804080709141501020f0102130e060a03022404030804060206090c042f070b070906030c0201140c09030a0501110a0806 72
    0x41e103200d0070140d000280c241d542003011850b450002c0740301005800420b03099105082030f074a00b81e8010b0f42d000b4101d210802c1081c6a44041060070061030f00f0600700d002e00b406c000c0056010050350104c0c210001400c281100700c610308441c051800a00014040d00720301411141303041c01290500c8000c009101001c0507000d0300004200c2600070140d1701010201c0a04050552401800c0c2196164400c0c4100c2c0e40300355606000f99900c800c443c8210401041601c101d02d5111640c002041c4286410b44404040f290000e14000c2c516032851a890300b0303003420003c0c948210303908100000010300000041c0000b404950060103a0f40b901210040c103040105a01d18801c900d03060400d014041404800b454600d0340442c800b004c1906c551801003140311f04000a400724010008009503a0740c010601010b1b5101a074003808218540403081e400d9400f0301225040c1401901c0000310b01400c460060000d02d03c0040c100d800400150719020700710365031130400c001248400903407036502503045101d0030f412000c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 749383075 1250 749381825 749381849
    0x40e090613060e0c1c030201110405090c0d0b1c0b0604111801020a061812020a081204050a0f0804090b15190c06050702060726061c0c090e0106 63
    0x1040d0150541c1c00c0c0c100301c0060100ea5207000781c1d29450003c020803600c030a030180066440403450b4000e518401600b80d0124010342c00c103103124140315400c00c240d07400c440010380302203131039268888120200d400c844001c00d5000c0d600ca140e03510542d1008081b60701d4510b0303403164040c240042d0a01c9440c500780200700601807414204169801070b03000044460070820303d920807640000c1440100d04100718502c4c058104d0303042c004d00c21704910b0f2078086203031500e2040b003441c2d00208904000340e8440380b03000c3c4040d03c0c40307009101480603104001c18541d4428800c0003a140603d015549569207031290403c01e070b54418000c6000d200c184d42034841d0345d01501040b1180711420009030740c0280580328220700c840701c009405020100301405000b07034140d81307980020107104510b045140250b56450071140710300000d903401c0c00c1f840071400c4199000d12030403010101e401c1d59034980040c0003078811080c481c0031080310025a0b02c40410101380c100c201400c0b504001082030300f80703c02980c0c01c0d00c6150708100c10a40b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 749384325 1250 749383075 749383081
    0x30501060c11040b0a0512070504050708130303090c0506030a0b24180105090a03060209010f08010302100f0225050a0602061608150402040306020d0e120a030e010209100203040e0906 80
    0x40e400c0c280320b12214040314081034010440740845c11a48003680b0985d0080869980c0ba540c981010580394281c0b2010f070b40c00c02c01940c40c1042120000020391307818012944a005030000710b4440d400042001e03001e21201d060032039503000820a190300840d1407000c03240d501c90100040385092a8111000c64801240d200449443c020004052241540340c81080100c41001001c0340d00400507902240d0000b040c00c1c40e110303a80e0500707074080c0d8400c0c40068000740d601c960100f10103000d0010705058030b801a0510844030822502a1a140300d1505080c084d40700d5102c0000041d00d0045081c00c0c82180c1003100c0320a5407508043c0518910660032000954118100b00010816060200e05484000345031205e010348410b298402d2900304d1590840e04180005004024021550000d0201e40418041001311250038002c1d95140e072183c0d4001d040b680c10410140b80a0f0344607401490841ea4080b000501e08240b01001502c01e502440d40c0d400560004507041002c01000e041e55903200d4940c2d4007802c07440ca = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 749385575 1250 749384325 749384333
    0x170712060e0621070503030c0616051c0b0d0813031109090c0d060603020607030801180506010806010c05010209180103020109151e020319051309020f090f011b03050307030501060c 79
    0x440c0c05404400103a585903e943d01c01d40c02045103c004180160a607640e509a441c0c545440f604116070369419074005103a45944c49209408440c03c684620b000400c8205000c18680058808011019030250301241c1000116110030003d040054075440002d807030070315502e050040030401c1d1079124420020103042040c030440c0400d2079070101340304940d125010582844d010008008942020750440c102003070850030160810303c0305058860b13000b4280d4458071450668010340350b0840390240003038540e4011036940d500400101c040c09205200142c04d000081000c0340b801c907250a45140341e008020b00401c19541c220054070b001d005080986800454001c0c030140c1002c5c200500700b03c81a05d0391290719152442070081d80da0040c1691703c40c0c046818520002070272034200d90a15503e101d050f07480043c00c02e000f4803c450441100192150800d998001003142403003115690300c1c10b004208a080c000c40100342e040007842482a102d0710345a051800c4024115001608100107105001d030b81d0a0100b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 749386825 1250 749385575 749385589
    0x601170303130b07140a0302030a0f0c0f030b0109050405150411031e061f090f050303041214120307021b0406260f070b040e1302010504030f03170712060e06 69
    0x982d4001c2c10f51840e540320b100040b102d940c0300030140d2010701008103641e111b00f035040d0000c50044152940c188522100a05a0b40868060403074200200302c16192600d50140290010406250141454000140d41710041000e030341c030464030000f8210b8507500422941c1341c148501c000e8400d0700039040b400c515255a04841c003081c040103410b1003d41040000e000ca5485042014029010810254540a01d25005449440c1d00e001c3c00c02010b021324000704540c14000141c801300c401c0d81030518030080140d09d420a116004294219150281d1600d030b0301c0c2c00c0305031002540102c2d1964010100013010702038014500c0f456400301486141028420041d42400342d000c1442d04030344c69042d50300c2c05d2080051a103001c4422000e04114040c41b04002100f07030004001e4002c0f13600c004944480c0b5503945005400d2a0a5100001c0c04071350248018000700d8135a4442900191290400b084800c032100c6c00413450401c01c40b0507900060700802e200300004614000d02008042e641e4800e012800c10a000440d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 749388075 1250 749386825 749386861
    0x10f0615030b0d0f111f0905151b07092909070909020d0e0d0e011707020604080f0705070306061d01141003110706020a110703020a090906021b0601170303 68
    0xc0c401c0d15150130010311062a40340c20407010010080c421101c41845004100e03903040f400b64000c03401c0000c0020340f03814804c40fa540700c1021038907480d103010101803541e600710003110400d60702d0348a4180003003030f0620980309101003d240310810502284044590f140d8040c000f000060090750344c0d10a01c074001341c10545100607222180d002580f00c1074826940300080800503001482d610480e219a00707000e03000410105c1c016000c1e03a40c1700c014074100c584e40d466400240d40440043c1c0c0f12900246c0450890005408580d00311035021307280c00106d0f11403500d0114a41c0080d200156500d60401008001d849000c00301101c02000180e190b14010030304603800c04000b11035024080b540c080440c4cc5109a100f500c50019130074000c0e403600c0f000d04240000350000b002c1a000304a003140380440180000407403000b2242c0c002c000d0100a428003241c0405403403080c4003141c006401784015440c800d400d5000c0c46210045030010529980b4203240485030850940c5004000d410410901229050850840702 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 749389325 1250 749388075 749388083
    0x2414010203030c0d02070f12030c05070c0e180f0d030b01080609010504050a020405061812070305100908040905070c03090b180d1a090109060b180403031d010f0615030b0d 75
    0x184503013005130810064443c4a070000d01540719924408104000c90151001c860102d40c0e003000400c1076401c00380c0e45842054005003464440d01d20801040c00b0b051039135540a0107669100050114201d5402d01d09001c814004120340c0101d0580d04030075515108a85101600b4640a500b60400002095030070700103008141c01161aa000511030901540480d4000e100181046582e02d0842c0d822840711010112040d200d815061809401d2810006400c020303a07400c2070103031951290701c8419500a0071886011584400203010000340480d0350700c202841a0b442d41c03681005110a841c0080c9084040e0b00044000032043c030011615505400d40e0a0f0113000036900d010750a040d90a000c00d80180c407000400c0101c649408211411a06401c0307001000c2c031956041c05080d0003082008104c29040340000c0b041138400303000a000c0b034820781001c004108810380c0300f40f40824125100e82560184c8034032403081503c5100c01c000c2c1e02c0b5403041c100000001d52400b000a00350100004d01c2603480503002070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 749390575 1250 749389325 749389327
    0x302092d0705091002060a14041a0a06090e0a02030d020f0a060b0316180b010504050f04050a06030b010f06140708041701060b04090506100f0f1d042414010203030c 72
    0x340c07440d004008503094200020480e10310380c054090001d645110031120f0b80003450801500021402d00a03613914055030307111802503410728207850201c03d0400001c0c0010000d0381c03255000106440b051183c140600c0300c060280840120600500d4a8103d0010004046602004801000031400305500c2440c50b032040c0040b0f0040d00740d000092400c007048104083e004030150b0002645d110080b10b0105680d005402801024482001950700d8013071072140d1600100105404440707440c06030301259000c2651580054038517142d4951040303001e003d070014068540d801c40d0501900c1c3c0c0291030b01c2604200b8406030303490000141d90380310b8180900e2240d24044a4405500003101400390000d00180c82c8041b40746860301d5a40b100320000d040140c8105005d00c20b904d404110261042e054400507000c0c9444030f600c5403203c168201d070104032100054400302c4072510050350507900e902440211a00c420384c0180482000360086540c07034140c1e4481c000428070703040c0d80001070760040180c0740d10010001d041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 749391825 1250 749390575 749390581
    0x40f1b1410020307060608010e070e04020603040f06090b091b030109020607140304090c02010603060c0e180612100501090e0a15112a190507030b070212130302092d 72
    0x983c40d60003150002403c0318203280000c601550154441c40031031202720304a5602555031700418650450030344000c0d41041c000c1001a003c2005c40d208001202d00c28000004e0203000ca449404036020305807092030103904141c43c3d1403c40c80c1c810342c80f00900203049008010084259001a855100d0158018070741e9070009040d5040e00300500541d00146070912040c030204401a030002d000300443d010880d011417500b400716001a209032424503030710802810100050703403103915202c54144028022603000344010102c06081034103020100703510580703200110301541000784000c280c0b424903da12070203511281c088004100100a211041c0740c17079100000e820300c0150b040904034465050285009401c0c95110301e144102c100c9914003540741e103025500020710441c00090b0282c500480540b49138400740042c030109452058040d0881c144d401201c4034801890a642d0b016004602c11780380c008402d075800c0043d410400c0855074030410ba001c0154a1000d00111300046101141016001c000d882c400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 749393075 1250 749391825 749391827
    0x1b040b061608091005040f0e220516030b0a050a09050a030810030b010605030916060e0631030501140c191106150a080f06070503100302040203040f1b1410 68
    0x21035030034490140200700307200e4080201030510386c0144916040b8015982000070b074506411646c0c6e01490351144903c0c00b02d80c628500a0303052031800405d0300c0a0040c0c0115040e82442848032600852054650a249140001c210400c551009260f490018240f2407103100240010500441590703140c00c004545849540c00303030348602095000200340caa80d085c00070412075000000340d0701c2001514200c4030410000942035003144085c1c400c03100854041e50301c1c2ca14502d0030340094440e00c40f00350403019040071403595030281142001c00070501c00741d5a903018014004c0038000d128036288418498022405e01c0e44d4510154410040050001044a00c40d040303020311444204003c03050300c100f01c5801c5d08151a0500c10401040170444c42000d030404d00090003140801c44150f400b001501038002d0f6910307080151010303400201403610020000030040f00694403031000e140203d00804a882e140d1220f864500b14000c403049810107080040c02302000f45200d095034800740d117242038030061400000500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 749394325 1250 749393075 749393077
    0x100c020d14010f0b09060d0201020d050d11030721090b151309051014010e012106111c150303260901050403020d05040308180d0803091b040b061608 65
    0x401c40c225400c14000e1a000d2a440c1c003c200c0d1810300b117070b520300c043d01d80d001001580522140c001f40503801056220b90544d005801520711002d0001000c9a4130200035420802d5500458040300462006005400d00c580c1c0051000505410b0810800841c55141c075850141c0000030030341c8002e10720200a01c200368030780e408030300d448510000050180741a00d24000d1b40b03449903885074420461814840c0729165030268610b80c102c4000e2144910964200042219050a100804804052003040a1300000da5a00c68425090382c1e10340c610741c466450000b1001c030303807403000c3c403007074101e81881d140011442082c00303030030100d80c1e0600f400c10000c0c034010030515641003d8070130700b2145c5080c041001a01c0380190401b40c8a6031003942aa100444412000e80320b601481c04060702c914014420316900041c0c48001d04039101d0002c00e140511001903030340e0781c1c2941c821990640650085e0040c04035440c0303980c20402880301e085500b4441c2000d08030120307800d40188090644216a06a0703824140081e04c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 749395575 1250 749394325 749394353
    0x3080d050c0307082701050a051504140402040f0b13060305010b01050f0a0309050c1504030b0c030907170c100203090436020609060c1c0309030f0807210b0a05100c020d 74
    0x40024000c0e4a03010b41b448c001407504445403500411210414580c030328041c4159182900c0c48440a40d01307032615000c0c000180003001c4860541ca41e9944da10340755955010080e40802d10030f40d03020030b0f242d0079480c4c05801d6803c60500c150500c841031200000f8112000255412080c880c5000501104141001840c2c0a820384140c2e42040d00d10342c00d1400040250010016070b8015458a805510354441c0e40ba40d6201c00c40306100345401642c800d0000d0603982c0c0113108405482c50444a240d000e01d8005103402e01c8280341400940c1c0b0003d134a000a08041c0213640456608401c41d25108040403000c6614044c035403407020403990743c09841c00c115650f040175a0803558010b0001512288101e0303099581d841010032188002c613076080c003010313507900ca4096408030aa25540d240c4107025017030f40aa546210140c21642802215480d01d21505801c4a11401c44510319a021981501e028107210b40724403150400c502038000c0030325000410307411483c00d4584a40c1652858000300050508280840f200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 749396825 1250 749395575 749395651
    0x40b07140129040c12020f071a040c21060c030204081c021c021f0b011d220912030b0109060504030525030b040b040213200309010605030703080d050c030708 69
    0x204460003403040d40c10290400f24440d81c213040c100c0540d088c00c01e00340d141c101c5e001868160201380501c54100c1e00c00e076035440000c10000e0b0600030700d00d40d074608003a90ec4494210b000603901013010080030000300490740c1c81140202c5890b0340030403d000029240c60280c102558800007800100340060b2080014102d541031000614401800c450f41000141200d0b80c1403071300150041c5961311542c42071001b200000d03040103240c035007070403511601d0040d070003c003051036081290b032144c0880104114407070009112000c2d40d00050700c4407a40c00050b01300c0e94990028010041c062100340006500010814880e00d0021034071101d1489508800d442d984003a00010084d14841042c030040140190160340184c0c821105005807008018071780084450a205082009101880640c20a400c05c0001c641003c0480008074006072240c0220b0700c3d114a07540112611080000c1c0e91480b84494410243c120440c2800c940c9035041c090710003040d64501611111036240304c00102994520910358a02e000c4c03080d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 749398075 1250 749396825 749396827
    0xa0513020103050628090b03071401030504060222030506070c020d06050c0c16060306050f010e0f040f110409050c070b010b211513050921040b07140129040c1202 71
    0x401c903e800ba41c401c4c4070340c014090803c210410103240118840090350550b08030ac1100c411110011400340c080030300103407103d5501704640d02d003481001c0c41c241d0500c0d40c10a07030701d4041861840c4c403a03d0402c00410413010000d05080100050780c900030740003100c5420901c0860151500b1455100e68440e103603500b151440340704028081812000e00d180112940d80c1c030100050f55680c001d00110340d0418420351f00240004906000601c0d1200018078061030203040003500c158407100d4a03041b610031909003042c4d510003007002c00900d1a18022a85c0c4000901d0340b2508028a507503074030307820702c0042c052420042400310342c2c40030b4a902046103c22003014216040218140b000c440e0b00010110b07100717a4000d450640700c0d250121018024280030303907040e900078040341c00512020002d4150034441c8201e5803104010025040b040c03103016100030741c004c4900e4100140400c1805084500030001100c40d417034101299041c3c600b0202200398941c40c00d84020900740c0c2c1000d801c4402d145450480404a48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 749399325 1250 749398075 749398129
    0x527040507090605010503191808040f090609020702031c030b100f120608030a03090f061a0a140d0303020304020609090c0a0f1106160c08041d0a05130201030506 71
    0x390001d65034086031084a41040019121030046500f88421120800020b6034148441d511841c0c951008104091842030095048490fa41d02610f944c4640e0010740707101c110301402d00a19416124440040c43d0041085103000c0c0340344d0110380c950004007210b0700c10000d58980c07000c407075019402c803404240000301041c3c1c10b0541400e014110304030300702e005000984030102000d1070380c00511441c0107880122000b5418013640c81801c5020b8007045404036605000c0d40d28900016280d0301032801d10001c8000000c103015018018008040b01e0359105115890312140004d0942c1c5518444105054061501607036a035290f001003003551250949550700001c61130100040c2c0c2c50040043e14000d00300b541e40c005940085142101d1100a414400b1032681100c400310300780c2010642044c0d4a0b000a003000e0820522a841c3e003021500650300400303404055000d61507031122101507280e03104103006400c100300d08011034007060040807640000e0500d9a943d0200d40c03ea034071380481e0000b194011401da04d05103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 749400575 1250 749399325 749399333
    0x6060f0301090f0605030f060412120608030307020c19090b01030b03030309070503060c04050a0e0a0603080c01060f1d060f03010f09080c010b030a1e1a040f050d020102030c04052704 80
    0x101d44000d4589813842c2203000705071464045081d0030503600b040b00405040e11503072101904424440182810302c404a004000b1200440c0540300040c082e0001850f101e1410300c0001c2d041034541400c3c0c9200b2424120b20164200004050f1700c162102490009610b1040b41c1c0140c00502d442c9221036410302c4040b08000703205100103155025198190256100350f1140c402d001042d0041d030182130340c001600c0c6000d01440220748140c6a102d4a2100c0c04549103aa9403202c241e240c2c0b00c1c018000d02e5035100c02061003420850410600102081009050302c030703820000c03d410005010301540e11501c05400300f0324a40c2d42c01d400c0305c407200c2801c80080140003820b14040c110f991100c0300d20034095007040b1400a00307140204d843c2c041c0d60303089691111071204a00c0c450b140c90b201884100c0d020340c00012002124440400d1851140b07105409040da034603600e06110340f501c101d0940403401c681c0100304000e61146424151022201d040d40c18044800c80d41034500b14560b00b072000200911a01c40812080c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 749401825 1250 749400575 749400581
    0x4e020a090c09060e030307021509040504030908160b090d11060a0e1c0f121112030708090d140f0913060f0b0a0f08061f0302030108280b06060f030109 66
    0xc05240c035508032083d541c0302c060f51500d05403550703207a150300b05205040150a00d0030700955501445a030081c580399880340003508444054070244e000070100300e000e1102040410800f01855840001e2044842c549683c5141d03a105402c8050700a07540501c14008001030340c01c2075221043d005120507111401500020208082c031003d070341c45914403401c40b0440c105c0315008030029a820444901c0120100c1d11500401111440780c201084840780c0b881d000340c2018040015280101440f50760340342880540102085c3e0702809001e00703038210503034421402c2d4020001c0520200c02e1200355440ba1500205450280982014580c0055008451203c1c0d0007255100c141500e40450082031075940303a4010003c3c80c0a4044024045452601c01d01d08050051307441c50b41c002001403807081101d0841c5000d4401c005450714030000f0980110050155400a21a00ca50800803c03007501d41070780941daa20300c109810900c06010103040002283c800c0c0ca440c0700f06d840c100c03040c000180c1d072075a44103806001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 749403075 1250 749401825 749401841
    0xc0601231806010e01030603021c08040b030108030d140603060708060d05060a0504060c091203050d0605040f1a040905062a030c04030210030204031109061c06064e020a09 75
    0x5080d8500c140045d8001d200d204162900500004007450400c82c2c600105031a103d4181c0c0e0442003032000060208000000718007801f200c1e0003442c4c072070f04001401c4c0251110f50329402c4001e4200b400304102e5440c00101950b1100d45480c01003001c4d00d4500c0810a415a11000a0818000c0c1d404000c0040070580100d4050b51081c20100000c0d01c2a4404480803500c42c040c40c1d61241e008640c41c00800d10450103040485800380f4006409651000014100d0b54088820001144c036100803a0707203100c008041071f0071010705913410b00c0303000d040d0b550705900c0d410001c080000da40ca070700c003552048000c402100400d24030404603051707a80c10040c52101c115000303440102d11449800800c002100d10a009071412240e000341d408142c52959000c1000305240289400e0300000651144d10814134015a400f040740d000e810006a020b08115882190f0003043c40030700340c074500c450324100604039100001e402481c00e8403802d401812060342d1040114100c1039010307500c0584140003086c0580650b129400f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 749404325 1250 749403075 749403077
    0x32031e0106121e02060d0c201c031e0504060f150501020c210f250e0105060a1e03090605060a0e0c03041a01091b0f0207050f030a080706091202030c060123180601 71
    0x590030b203081c1e030403594420441103c144009c0c1c4424520840601a4016101081007607421151040f1a0141003007140d00480d0180e5465803260043c183d03403801c500c19202140c1e440010320ba08541410f0000c0c0d41c51507007800481c0210b030b044418603013002040c80e82c0d045000c3d010094440500d80c902c041595180740d444205241351b04900385030790907412140e00c0e00484031034000783c00050b0b180c001040816002040100103008100052090000305c0100354540c0300030540b00040d02002034280b420803128014191030095036009001d0049983d060b070100d40c40f21407242c07219601e60351407800c406001c40c20007410710b50941c482d00104a00315590082d4030317100060480180d801c080702c401119090303020726070000540c01080341800740d4109600305100011014045030300b4402507559031806503000110940b5a50342d90164041004801d042243d1101454801142404000c280082d21614103102d10a484182c0d11500751124442c4041c24010b007038000c01d01000840200449002154200e070b20724 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 749405575 1250 749404325 749404367
    0x360b01020d0e0904030e0301091a01090606030b060d0e10021810210e21090109120b0105061e160b06060432031e0106121e02060d0c 58
    0x1c0c054070408000345544001864001551150303102a0b403891460144039801d952541040c1011840700d80e001180150403200e5007410b5854005014112359003500548105420803107000310a9a5517400d492919200001c005180204503000e18035142c0c50081c4800514004508400f803114062f14040c05a20140c41854149a5090701292038188245030000d400111124903801464a91301c100303c120040d0048503100305c490990344840f10201003001600440010b0015620350340024000000e11214000c2c2c540e01040384d0b140c103012041402220700035070022640700700c064511151034648042d44991300343e0b50700a08002141e406540c500135241880c2000c0425000d0804400304c0703040300d501c0310160351f61a401d000c082401c060b0a10595250040500c01011180d0703061084c01c103507910390096901c0c103904203450542514031940c00100c20784003400035100130854001d0440010341104203400c4500e50780b0303c001031043c01010308040b80303a0b151a040b1150f140e049181841d442079516494 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 749406825 1250 749405575 749405593
    0x13030e090606310b0d1406101b02091311150a080619230411040b16230606030102030402030a2d0b01170a0c360b0102 52
    0x4010803000503a6102c0c2c02000c10070814079000385110480c01d11081d502d50074869060320081d1490810100d0300a0244400002400c0000b080544105100340035101d00100840c5440c0c0c000507680b100c00000c010910100326200f61092110403080c2078159401000500c0c0e50400351801c00707801100407000c41d220702e1802440016440e140072150340c2c0c6118030500d0303480e00d2883d00e0304440300180508401d0b04482881980203004800e422540046c00c14110321440014005143c6009041000c1840d030145107055805d28543c0242412182501d8840012a941c2e4004c100c2031020002c502070040c00d00c00d0020300d418082c00944445040d00c103008003c0704d07070a0b103903101010300302d100a4500941c10750044042c8400609480360780c1c8034803903401414680d02c4140c510b800315610f00402003180c80154072401070001c0b00034140a02c0864041d00000d0104242c0384e620054003210900941e14205c01090a40b01a010f030010420826078158100b80c041041000309800503004010350280035006510314 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 749408075 1250 749406825 749406829
    0x1302041a0c0f0109150e0313080c09070e010906030e0c0a060e030c041517030c010c09030c14010c060e1002040306060503070e15010c0f1208061309051c02010e0613030e 74
    0x854110030f80100944603c1317400501158020441000c035038540e030005211040b8603011a00700d1200615501001e0b01c4503080340d2080020504004102ca014001c1030b4902e0440e030f9030703c4450a0240e5045040020f5a8a00b04442c2e03071900002440590748481c0101002c58025445184440300130420341c101c0b08012900c1c020041548c40c40c0f0701d080d850329450001001018001014030740240c104400340da240c00d03154036409003583c000200d48004200315010030010890048035040c014407511040002089a400000305810803480c0003618042e2209246181c60368203003c03220106018510843da42ca03900d282040103442e5502c5020310078069044002074408914407400e20a403101d00d401ca80092003080152101910f08000360b8000300428407140028203142540711107090f8503101e5003035500d040e800b00400d038610060415030b45410540303a4400580700082000c04607503134020b0141400c403040d2080b0700400508200c0082c074070620040c801156458140c07076032114001e0f0f5400078000f9900003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 749409325 1250 749408075 749408081
    0x4060f0c06090f021314150127050f040621110a0608100501030c020a080a02010b041e05090c06040603050606160317010803071e03180f21111302041a0c0f01 69
    0x14001401c0307030b11b003c0003800e00350500e1000700074a207050400b41c034214084042600001010540610b45515054090215103040b150007900c80340111400e002a41c1000315801e45211041c032003050601462040c1c004100040d905000a0b080c058080440250340b000014021030342542c9001c0d0041105102207080d51290050400c840b035981c0040a00c50200c1d5150b00880e44005c81400841d541d900c500f100f90740e120700803000c441c02c007101c601c0c40311020241031703408580d00a00300c1885d607445149800c142c1e44828050f10704031341d0103050004d110380d291008a0050701c42e4401c030503c11f030103094a0300e08041c1c000b421301709107030424000c4c40c1e2243c1c0c0396070300c460b541c2c8115200a40000310300b0940d0f020041c00074010104040c030901e450402c286044d00421000d0119401002c03010094600c02c0c01010b22009106226402c1c160b00b01c018061035480300c1c801c0b88102c0c01343e20b02942a540040107000f0503501110014030040c401020200c86d1000e02d010650001c50400032103025152101c044404140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 749410575 1250 749409325 749409341
    0x91c12120509070b0f03100e0c091201061a0703050702120106290f0307121506021501120204020703021603050607111b010e0a030605010b0a091a04060f0c06090f0213 73
    0x84c101a1402d10110f5404400d40c0009004000b00c1800c060003180d2003841a0391180210381c441011341e115034a40301041b110350605040c244c3c440e03140c5501004900234090f042d00c903181070305d4141569007241c1d04048074607105045020350008160f02070051030702c0c01540050b08035030885a141e07282c4805015070049006c0c85084442081c0400e110741c0f410390003100011900840349007401440a000158030900f5030b00602041d150310b040c800f4003000800d805205400b52207034607611000c100d40c1000c2000c06858020756019014550114500d01010b0007001822001c040300300d40200502d9891030140c1c3ea5580c21500d03031000944800c001c03801680b001800d207000d21410002c910401131200011503684d503400c2d0111340d010000c3e0700c0000201c0c0311031058074041d103200082c26036240ea0300c642c0178250303400b90303881040f0906012344103d4840c14846e00755030a442181c50643c0800d040803008a8000d0300001d4003410046c42c100151b01004003400800120a1082e507020948404941124007200d001d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 749411825 1250 749410575 749410589
    0x6090105070206130f081b01050a0e0d0302100b1044040312020909040321020403050c09070906020703290f04020108090c0f010c05010e0601061805060708091c1212050907 75
    0x7000c040c00d0701d0340c024006402b007480140341003035400801c240050324813051080243e015070070904520304501044c1c020b554501c182611007403648040b0800050100301e1140654085d200700300c120140031940d100403a2440c2c2c402c030901c4000c01c100040c11004a08050f074084001c240a900d07031840c07841e054026145101c000034095204d50760790341c90a441050000400380500885001d00b1a0884030500c041c0c0301442c000c000608103008a41e05010f482e42c0090242810f006050a01300319003580050801c09499001d020642220070103010790b00002c20b0a1003603050b24403814208109010766120b010301c0b841c001d83c0e07091466140c10507420384906231640c140c2d4001c401e0f0491910300b0750043c4074121801e4030070030000809041c40502641011401c1c9c1185001801750342030440814100014000580400c503441490b00c4040d680d00801403007003031a41800349424a825210310705161030641c00f030a030048131300c64241e0000d41c801408000c0703c81d900c1d00c282d03181002040c03403030000190b05411382e426 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 749413075 1250 749411825 749411863
    0x17060c09091302121b190303050a0e0d03030c17091009050a0b04050106320409060e011e200d110d0606080a0c05030702060606090105070206130f08 65
    0x810103000340004010000404107507000b5150005855013401c0b801040c8209000e8025410103080c42e603010303501040e080d03115803440d010b02c400d0080340f600010200c9a0609045035616403111080c0d907003410281c0d52551090380c540c401c009250701904000f01580765550b03003d14401903401c80d006400300c166120802580034418442c4071840c03a51002c6040c502031400c4484080c580d64481c8032403001200d040f103d503512804100140111418500c8007440c2900e80a880c94062525400c410101c038a1007a2050f41c48601c020180542c0b0b5000c10205440c0500921200c40e880324500ca01440070702c9002d070424034107100c80c0c05050110790300302015105058142c0c42c00c6030f0849451302500a031000c15000050401001071140042d12440c8010807044d16096003919015600108a07007240140310180b0004000b00304410b41d001c0f49031680460102d0349203860ba80381d5070040f17895005130b0030003e4002100007080c2210300741c02600300c021a40700394000780e01192160b0401c1d454031200c85a000d03031829 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 749414325 1250 749413075 749413087
    0x9070f0b031b03091e030405040e0c18070c200d110108070507021c03090510020615010807081305010615020307050c1005070f260921030403030507080c0708030417060c 74
    0x18012102101719184408a90034242c5a00c00201260200249448254869074081c0344604261a5101410380942242841442d100c10054070880000100030209101840d1203139079002d40080c200010000507044001414072450058080d170005904c20303000c42d0405c0c001580302ca2080007200c280540c003510651511800e0074040959034a801070071400d02054040119240d01e40c050301c60f07031620740366008016604000c0005004000c08070212410400f91008010380660450b44e82908a250b148145140d0896424198010043e2750425201101940c0f10a100e40c2d5002026148540c020410f440b07101160801300400c81080b50f080701c0c04560148499800309808191030442c90303002c9c01c010000e44400e42403022200602560030809403201191801d01810060190b400d02c0c00c020700408907241d42007048940d05d000d50b200003810001c0000b0800c00700728160003038520551405c1304442c1040c0d142c1c07d089440781c016008606505809034110030030302e070340002c0e818010300d90518603901c2c1031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 749415575 1250 749414325 749414353
    0xb07090803040f140607021005121b032202040f1a120c0d1a010608014e0b0c07050d020c0a05040c03150e06030709050405060f09070f0b031b0309 64
    0x800215602e55100105010106c05078583d841c4a10401e60135a58403a61408403010040802001034100d846100c09505030b1591012000d040f00d0300a280314040800b868001c0014124000c0480780081d0040d0034400340318200d5030940c000400d00b0ba005455046074043c80310601c10b100850b00c22001990340321644100e0b048c14600d02007440785028640000b40040c070b400040b890408281d01050010b0b0083c001000080125142009103200e681c6a000c03940302842c424030512004103a01e040b0080c01d1a0f200000b030b40541c040c40c20915886103090401e480c020301c003580b480c1c102d02011b0b1083e000d000a00302d02c40344080f039850300080d0010402c1c2606800d00003804000c101a8114205050f903645402c001180780d1000070b00140f101d02c050018a152400c04d260810042c0d03070040d0000c0e4203010a1100140c808a08a40d10944c4000742140070303a10700c1d07100b40c5440c003280d209006284404002051240317000c0000c40c0704110000381a001e19824003008280c0d848102d503296100d4015030b402002c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 749416825 1250 749415575 749415599
    0x9100f050703060b31081c030f1e0b010504030b0411010e1207030f0201200a140102131a090a0e0a06060e01020a020910082e090312020309190b07090803040f 69
    0x48001500300c1400507840d40041c03841c00d40940c0702d0000300100210f11071f00c02d99241c06480403404036500c0070700c1484c41c0100c0c000c100c050b400b40521241900c3e0130f05400c40d030344030344203490040d504079071001c0503410142001e245c0e0400d416045800604c2200c041c8010b401c00004d00505050074000800c401840e580f1101c02c404080d5104a040003a00b48420302c1260141c550441e507030301b41c900a07006176a0700d464483d100d181d0580403106181d0041c04810b008000e4a076404045130fa22050007a2000040c211441700340c4107a200d4964050001030011840d445003014942c0706d6003050350200620b03611643c050354182c0859601c1801680700640d4640141061580c0b0b6400c0144180120030031380c0c64140b02410041000301c90b600b0036101103440c42891b500081c8001c071034000c510381007058030001d4500400c81c12410320b80c0c0886540000226103201e400304401a10500c02450320707046040185425480c00d00107554100001d9035599000c203601d6400300442341181c0c8641c002c4c0210a1400d402c1c0710300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 749418075 1250 749416825 749416897
    0x915020a0302070b251809020c010e0d1205010e220317181501080c1c05010f051f05030d1209140a1b0501020c0909100f050703060b 58
    0x4041c1c0901050700001d01c1d81811502070070302105c980c4001e030307400401c24002d0303100c901101080000103a41c1c280c0700f0400042c3e21040c0c4101040159039038001136070950160130b00c175880004a210b5050f501200951000044d00003055690003844540d98543c0403100b001c0040d42c0c400c034003141c070380f4441001c2c0d0510340f11050340e2442400c0003586414042c05d100c1c104041160009002e0a0340d40e5a003208640a00010f030b0641040c503a0442c6070750421034215560354400c00c40501602110444107004030a090b012041c03164804024005111a00014005000299000c4c048000340f482c068102150b4040c41c08155200034005146108035903070106c5502800d0f40700c401d60a40d654180d4001300355035072941046031140074018011980c0601d0090b2005000c85903100e803039050080107202c0340c2c2e404640e1114490007240c503a40141c07546250f560902c403520450039001d03807400540c0b8108142a8000520a08a0303031020800a070703451403000114801c00b040c5000c0c1031040714001154166845107014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 749419325 1250 749418075 749418077
    0x70813050714040e01111e040e070c17030705040906050612070305181209030610030b0601081915230f1c020603040305180d050a260d0e100915020a 65
    0x3c0c80704c104130310941c2122000300b012a5036600c00200c07000d00186018140a41c0c07410209901d02d060b15104070142c0c5507501900c2201048001c49000060200040c0c00f08044070b000c825044d5642031403600640568045e20403961502d04110002499141000640e00c4505034005003151698498404500602c4000c1c000d030000740038132440d014403102c00c100c2640da00000240441e501c0c0c081908151a002004103180690f00340c1010a20000380015401c03030300500203080004543d102c1c1c076442e541000ea18402c1c1d4020300e1a010390760742071540300034090301110180c980000c0701c820340d010003901c402d200b4400c09810140550b8044028241404040341c08102811114100c243d10790014844e540191400d40002e0000700d41308528039900418050340c0d94046600c1090100140d0700c0b07030f44031544400e0161118441244801c13000e090400392904100e090125690303242d660400c018020036065410305c0b91807241540036000030f044c503c5072041e910740040002c8214425208084046e6024500f020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 749420575 1250 749419325 749419331
    0x14040617060604090f0501230a03030e010509100216090510030201140f03180d0305040b1f0b03090f0715021e0a0f11010e09040803180705090f07081305071404 70
    0x184284c85840341000d0402014400304007540340280880382d03c200070340340f03410003071522141002c9580c8043e06902100d0340341c10b000b10b01402280059401b40101c0342d000e0781004c03a010505c0415640030550007503100418540c40e42c19038450301e03d0002c54208444101d501c040340c1009002540c040c190b8100240c801c0d09a07207123041c03900c1a5580d0340303800540e6a500003030000341003000304500031301c207003c0003005d140740401c0380d40781a0f101c03880c030310001508920312542910200302815080400e101c002c0c00701c400c801036480c00c1076550307259621400510b4200070b0184034008a540e1100140003d80a100d560040581102b0802044100314220440c840b880c0310751a80b840006640c10084140a8002c01614100000580024162510342c124107841110040100310018080d50107881c1c21202550750b942c800b05000d8000c0745480102e4000302e601c00c0b20f030410402000000c0342030700d00c0b406040ea1034191580707a8003070f0340c1103400d03c8080c0201180c00c0030380240024403000c040122882d00007070002c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 749421825 1250 749420575 749420579
    0xe0c060c01090507060c030f0c05070b09060702030604151a06090105210406021e031e060102100e0d02070509010e01090209040b040905010c0216031112030f13030314040617060604 79
    0x12440c1c8022580704a0114048100f11b41c1403680101c440c1040003103c0c02c0048501aa80d42c50607120b8440f03024480203100046400f5084d916a001a110095806001c862503800c0a00788201d01e074511000140c1414103104030b02c07000715543e00c0581c03060b800c0904624104a204001560349800407580d000c06104000100f00c0181c008102041c000c90040100503600d00c00e1086184415006441a03c40d10700d04000740700c032506403040f8a00100c24240c10024080c0c40d9840100d050000b04200018140d0a000107002c1203040403840440a1500740c084a5083d980e450601040400900c250001a18424010003004610360010409194000e01c001000400f00000034103c1d00f00320f8042c0c54580d505e00040749056010002030b0009101e45100310807140c0345a446496001071084018021031078046c4401d00b4000030029545048002c40728240c80e605030314020aca41400605c41a0001200f03040102c00320500e41044a0607660309036201400e0f03100c0d0345010042160040d2040750040c0b000c06c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 749423075 1250 749421825 749421833
    0xe0a02031501030308011a0d150506040906090b0d0b0f0703090c0b0309010605240d09170307080f07051614070f08010e0106060207210209070804060c02010e0c060c0109 74
    0x880300c4104003203009401c1941541030003012400141c219a680e500540c0700c40d02d0300740d410415a08261464640885c0d00c4003a94121703001c2e000c00c0c1e0310070394204401041c082a0301c1003d4000109075a800c42c41082019800020882c03c10500c100140c0800c00c4440803458891601b5001584040d880c180400c80019075075650700781d01003540c030801141c400801440060710080c055a0001d22049413240424a041e8001015180520034010002040020b01200c840095001048540e41019520440c0813000390003c80541c81110804000380008000a1070b84203041803c83c00340e030107941c60504007440c20350307440d0315241031178030640b0105e0f004a80d00002030300c1041007401034089405084803151808410b03509440300010001c000780d051402c140721040d8000340d22000c542d1045880282e000c2481d10041d8007000c07040303010390440c1004007040401600031408a0060f44a0784040160640d8100201e080740c072040a0020320303400c01e220350364007403074520007900e100d4654400000f00304501342e032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 749424325 1250 749423075 749423083
    0x30609010b0d15031103102706060902030c210705070221061006110c3a0807200901051011100c142b090506040f111002030304060e0a0203 61
    0x40101c45c0c002c4101c00315000c078101031207840e4150b14000340510200143c080144500700c000510b0303900200c2d860080340144002e580110004000c120000c41d6a400c28400c0d000340d03940500c5441100c401c02c1c051640c0001c00f02c0c0c0c000c51141c1c40c203958540c00c3c42010f908004101c9410001401c54140c0240022003e81c1d05010040c024084202c0c0181c49518049020301180c0901006c0b1007c0d0b041502826802c0c2c440d100312000e0050440f400700210014404801306072480700310031070700300c14209507440708000ca100002c180740c80c011090f01c001d180032451002d4929000d03480351504040b07090300420540c28130002e01d002c8409281020401607005000c2c003407070000280744001c0215190b1900101c1d903604002c03140008040c180d101498950170f11001f4103510f081070140c804031250f03078045c00101142039101d69540d59101c1d0955495061038101010407004200d07040d9802d95501501080a1600b14000381c2c06013000e80286083da47c650710384400400342ca004d00140c5014001d249401039a0500c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 749425575 1250 749424325 749424329
    0x90e04031d090a0605040606020c220e060c181c0f151107020a0504020c030301170309040204030515070201021e0304061b0f1101201c06080a050f03030609010b0d15 72
    0x2590004404e4503050401090b20301984c403503403d40d00907600d100c91a8480300d10044084ca10711405580780d02481c1d500000030302e14505049641d004003020b100c00181050b000f803499140d00003244e0301c4035080d0001c102440b0359400610200b0b510050050000884401d503000d41940100c0e1014910038080301c950050b507485507448405500c0011b00d036001c514010003c0b2340030f400165030031070070007014682c1940c3ea444103009446c3c16000c001c800d003508550400c1200c03540302c40a0310554585540e032030041c0c1d4401c43c0c0c0388001d500c9101c0c0c10019464500c14400d8a981c441ca0083c1d1b42162042c14001021039070004d0400c1d1016501d03100c141084035004100e0013400846039403401c11f401303a400c0000346040600c0c20700307042030390412810649002c25148080c0340c80c4c1080b44c20300d030354528075039a2180540b80d195082103200e007070205c0004c13052000308000c070686016000346ca4000038111074854507448100c036050380c000d120720014085c445081e006000302c90184180014050500000c184018820b6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 749426825 1250 749425575 749425591
    0x403200303190e01051b0d020f0f09040e0d021b010e0a0e010302033c0102070c261204090203101805060f030d0e04151d0a0c090e04031d09 61
    0x510007078060041d0b01d208481c001140c00c8020031413410400e039000c12038030794040d0382d807400f12012440320b85d521420390444100c000207081d45959044041000900754110609691090b8a0180c2c076075a1480045a0042c90a1242c0d01801c090826400d003a0000c000c064000c134100201c8206040841c1c9507602040c0c0a80588800e8102035855481014034203016242c0d040f40c0095407000070014810303109400400f0095134905440600403902c031041c020700501c900036121072000c0a0004414402944001d81103141440f01d5203419002d000c41070b0b4900e41001580360441040004101c0c00d440340e8050764011300c13100000e618265441030150507022280482e1001a40d907031003840881d2801e80102c1800c0b03001a00038004c3e111010700050280001c840c10540102d481d106220480c60402006802030f1110500c1d170b0241101e01c00c1c0a2020490813224024918905140340280c50700402091040310707100c41001850756180d6504483da8034449055424450b89034025900980d0380c0302e03030244a0506 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 749428075 1250 749426825 749426851
    0x30a0603170417030f120a0f2405030c0603060910080709141501050a0c030908030c03030f06010801050d0f0609080c16060315090506030a060603030c06050109140403200303 76
    0x140b250300e0501c400f454414282c168000c12041a111098406035404c000c0e241c6071144641d5500b1413400041d1141c5850740c41c800345810f07000100700c1030038072200f0741d054841c145450450741c5030028595220024998207600c00410300000d182403805030321282e03000d410750366031408095580410918149450b006050070944a0b803400782c0c451083c0c81a80d501243c081c8880f90340e1005040048e266108040000d02004000d007242c0d400c0c540136000050080c00c0a070102d03981c1e145907030b08180e100d4000752070141100c240b80b40071034155881003050310305a800040441d600c014480e82c0d4201e500c1c20481c81141d419841d190840c0105030854040d101e0342240001514102456040000d0940301e03541014045c145001c10601c07440000900800aa4000a00008194840000080c0f41c003000c500700515190502e0000300c00c06610403c00e58030300707108181c00e01c11713662504500400c3da101c0401140c44074010000060120744142190440d40084540760940203031400540c60441d807084075401c1403119 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 749429325 1250 749428075 749428079
    0xc070602181c060b010906080a022a030c07051e09220b01050306060d20042717120a050601120c02210f160507150e0405070e0312030a06031704 63
    0x1160f409620b0329400f0918040100c4d40c102200035102c9100a0400c0301c103c0d6000c42c1c00d156500011112f41d0151f00d59001c810b10b00b20360032400c030342d1303d03800220f2b4070409018950000400b414a00824504211082030a108040118081c0040420020f010f00c0c0540d00580e4400901030081e10781c07103002409610904099810103040c1450704402074201070007106d4204032103000c04c43e4181d10302080b03c41c2201d002d01461881c0001800b40441c850b010341454000c5109550104000051607540384c0304807041c4040300074080321401207004440071b810000170304500240d405109640b08d10741c42041418012030b004140c2c40d90f401191001801c590159001c0410303150301010103880c2c02c0000c8c0711a895146410744c2401c0310600c2d0b0268070382c040794a5003041803071400c01406106c00e0002e09000ca2000d0300074405154004c3c018104030010501075450031021641d0640b141e001f080f2503100190061a51201c420403480c541da1000300f01d07104040e9580384c08000541c214036003821b00481e40d1000e585440c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 749430575 1250 749429325 749429333
    0x302030631051e2d0a05010905090d050403080901031410050f0307030c0b03060307080f010504061b0e0906190605270a0e0714160302070b030c070602181c 68
    0x180042c203081c50384101c980b14410308070034140c000c990040f03c813142840d200404840020355101c254600c1041c00303420800300406a9820380c001c40c12107034912000e105545400319200c0d103d6410310059000100b00b04000c0c00801ca00c9401041400e030b042c0340004404200e070b82e0311004032009592100724422030304000c00c040e1510510290104004601a14a462a684d900314a01c0410701c00c500264802100103016a80d051101c2c50040000c0000e40c0c10550015400e14000c2804480c00c86040345014003841c140610f140355400c41003840d03101c1c1041c0042c50030800c42c03100350040103607030b01039030b540e200c3c0c0c001989103072105000300300320f0700c50a171941a02c00780440301c2076203401020240490041c1c4d10541d50386444000c011585014054500c548444d882118200e070415031100103030800041210711310704540c1d0710000e030034040d0b8241c803c4181c885401c00341c14032040e6030000c83c550013031103400c0124000b40d00600d10445424411070081000c600858110000d600c41104c0d912603141d41013040c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 749431825 1250 749430575 749430581
    0xf08010b13090906020a02070f1d19051f0b0a08180c1504032f0603090109021903030f03110406120906060f031407030506180109050a05030c010606110705010302030631 74
    0x14144914441c07401a04200d02501c1ca1081884c1a00702d0103407a001080d031809071a202f00003030080080c2c0501684c9030404441c800b41014a0102640c692030b5a000a1180d1940066507050041c4c1c0d540c40300d242c0c5450301d103242207a04482e02110203001c2c50002502c59601d04c5003008041c1d4000ca0440d461341e141d801c0c9028401c03c0d00020121204454002601900c0c0303104c05c50003c1c240c1282c8154480d101d649600d40106070040000b50040080031030480420007d003201c0d002ca0744203a44501e420320310402d040b02558041d01d18841070f41024401800454000e00b544946c40142c04000200d0949035120391003950060380c411080c12191540600034404c01101c19098078051000070f1500c149169a01a85c8600050080c100509060b00740d1105a500790040e403085034000049842c114010b00f0019240d500402e030344d410030340c81c2480c00982d207402040408061942007001d0800c0903d0180190080e6200405e030f02c1c1d1103400600300d11b00006905641042c200d194068235013000381c0d0700c0e01d25021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 749433075 1250 749431825 749431829
    0x6030e03120610050c010905010617010b03060c09040f050109050601020f0a050a0303050c041518090c0813030e03060a021903021206040f0e01020705011b0f08010b13090906020a0207 80
    0xd03041042404110740401d008150008001d403440700e14030091510444881c0180d1203405125400e10408506118054000c04c0940c0c5004000d0f48404c95640030480c05c8602c107150242c0c150f04030b1000a00c038178500802400030392001034004140d80c0100f107075400c100c0f0000d03004103644c203984006001e00303568104914403005403400020120000b180c0c80c1c01e951442501d2000341016180c4001400c44441e60045d10003e00140f0280c0c0546036a1400113400401d029841c445103d1880310001440712240c01103c0d019036680e280c000d4181c545030030700c124000400b0015024450a0302b8030241c192000c220749480798102d8100103071100780e0a00340d641341d400e001035494201401404422424010380c041079410481c112400180100040081000b42994091502c42548080b85210901106411804042082c1444860660341c405015104040300101c504006150400144860410780e002800026110202000400c1e510f14050342561620300c4c0440d1010b801258443d1030b15010070034000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 749434325 1250 749433075 749433101
    0x103092006090d030c3c111203071a10061409090f0414120405040c03090b0a0e0601212307031202011514010f1209050a0507140609010305040213060f0603 68
    0x803d05250300e281c6e001084000303205500c0c01034540305110400c9030030b21b0500300e0803401a100110700d481c04d42c281c0362039400c034079810354100c0301400c03034100c01c40b084410603441855071141c3d052100e130911408448850015424141102c41040005c409680d840b414512401000c0c41c000d51134138061800307034003a07032440303840f0051640a006040031540c0c4420076141603500a840003d4040c0b480101100503003004000500200700d02020301c80c0b0b03280c841d0410405503440c1400c0b148a40d981d0304400301100203181020b500707038800701000b40000b415030701442220100c8210858450045580d5603080003240c2c0d008586841c8910307104e008007a02802615440c4800742d0014911502d05002c0d00c03a22022407011904002001c10301d400307800e016440ea2000705860038410448012945002036441d076101030241e03160f104280300014121041050114048006800141010a00c00040d0042e000141080782c0c4030004142ca04004070880c4078090090171150130b14010a0320301100038048030811844a2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 749435575 1250 749434325 749434373
    0x9060c0216061403040302011d2113090513120e0109060305040506160513180b0a0303050906070f0f0501050a0e0705030718060f08010501030308060103092006090d030c 74
    0x1142c0c020800101d8540400b109503913a035140d140807401005039200304088442e5605441000e00e500083d8446031034120328152044004c659030381e444d40d00400c4e0756a00b503611040e41c01c4c03000300c40e19008240c200c010103210300e001148664448088034400c56aa1000408548082c80d0030340c0d0100d00c04004050b17a090400540c1400c3e1580d6847e050000c184035081403100c1e4040725007505c10b0088030304510503440615800c1c1d07100e007904044140b4100b44000140d042c540c1100c12460b0440710402100c0e851703240c130781c5025805401e0016517088007a06030761610b514691a0b02080340031404042c6103100307400005045c603042540b0740031142d4200c0e080c1c070140e220075400c1c88641c0f0001600020f0320401c1848810000130301e80300c1070140070250444420029103060024100c5015007000f0b05881c441d0304c4000d180d603a19401101225900c65014001040030f072000c0c7c410921960741040b09800141084c1e10f000722800c08103060182d00c079000c13000213062001c0306080c08450540d40c01c2540000f401c0c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 749436825 1250 749435575 749435579
    0x60a05040b130c050c0a0804030605180604120909090b0f15030a3203040303111c080613051302031c020303040209090307061a03010b0d02030d1409030109060c0216 72
    0x314034649200549030b00200d940310380190441e030252003524000085a021110800300b02e1400c0310480c2c000744811100c035420b180c04034664802c10300c1a001201ca108004005c4d5544544804011184d041c8004051001066001c0b4200d100360003585070407030140c13002c44a039017000408240c0c141e038000d080d114070218041c019611513034081800c01c1c205070041c2e00703007110b80d00d458080d400794440369170800300088140300450081c4a011002e002142d019885d5444881e070742001c10b81d00e560342d030404c1446000f03218904201650060200310740220028010b4000d2031001c288c0c032821688103a640501400c85030040204500e420403048048152000d240d0f00d4100441c03c0107562030101600c000d1241561000040d2204010400da640c0d10341c101900307120001d80c1080e5260b44125804150380a542000355028841c2082d141d940f50555006d4001e100c80254041d080300c03002c0003203c1111494100f00300502259409002e124041802000d001491040c0c02e28041d2420602d400000300c00e410003201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 749438075 1250 749436825 749436829
    0x602130b0705150402031f0209060c010915050606070f111201020415022a060c0d080a11030f04080c0f01110c070f1202010503061305041103060916090b04090f030206060a05040b 78
    0x501071001108040c7c8a44e6071141d06c20410207401240326180d045803002c0390720159140c0540121080c3c6004140c0e0604503044c085504083d00c00071191030750003c2c410003800d4000340003c21500c9005000301e1424640014202c00610503e0761a50252200d0b900480d040c0103115618411a0148405000078a548a00c0d882c145408084002d1049000d601c200e807240c00715141c1c1c008940c0004810026540c3c5440c0b0250013a0521200b0303111a0318091800748008410049002101d028640c0351a5022807650355580b001e07030641c4190349801090040d0351020300d502c0000d000e1501c2c804402540d5948170980300b076a4914220a035845404504640c0f02d0400c040c081c290803000000d6028a4059985d07528040840c00c12454000c48507030491401081000b840010300400480c800d04805036010340d282e00c510180d132031182d4840c44a40750140d200c00c0101914544c0718980010001c0d10200310b034075840e100e103501104005016000350308010304000e80b07450b0460501000d08805c07102085031141c1c0d140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 749439325 1250 749438075 749438083
    0x1005040513150305030d0e07090908120702010b131d0d171003020d0510241e090c080114040c0815010905063714070602130b070515040203 61
    0x6201c031541c59540c005090940e2195142074091a008012640e540740d500040700002c00c5101c01d0244103019400d00490030b4070103800350061043d0020f0701c0508003804000c025052800140884080d9943c5120810762078440c2c401112200b4210600054440b64502d072039848101c0700f4030003800a4210070440c90045420070841e0b885c8a014044010a60750350510188d40c0c0c3c001380d0000707075110940c5024a010490001220955000f40761014042d000745100c10030400d4103111945035585645003003d100c0c00b00800300001c02e02d20003101d01d020f41507a4003015003c881004200c0400107020400600400302049070903004402e003581e081001c8110460018102c3c00c000e80f54018885420040700b032242c0c41400f00310040d10004040316035425240703101c1188180e41e84c0311601502c40f107441d0582d40c80e1421864546480d00358480c1c0100d44004099140c0e580d000707281c1124501c0e030a00c40c94140320390540151000c2c003070318401c9603540d2205080443c50000b07600c4824108107020420080141c501003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 749440575 1250 749439325 749439349
    0x7050c0907020d0f02161419050a0b07021f260f0c031f08010e01110f04050103020903031c1e0e1e0a05060901051029070c0504090f0210050405 63
    0x40f130418070660485030b00304e041c2500451280380513080701d41d002c01c0443d50034001207040e05003102d10b43e00c01401c04000c074030020a00d200b040e03400310404404201e0344035080000c10600e44005c01c140700112074a584816100710070301500002850445065082a98240034a8030141d08509114014640016001e5000070b0080648640d03880c04004114030540300507843c191034100c1c8504d00700040d1038856182c002c0042008401080d0708040308001d0040c1040b00700c640800b2218400382c0f416082000542c00795100c0d81030303a500b62200304101e41034903829a40742c07500306013030b88000b04d07100140312004032102c01d0511410380c0c0640b9241c80b03101d103c240000d080010012071488241f00b1002112607a003080d04411014100c1d01941d010045a03110643c0414480c80e0204c040941d01034490007038041040d8114450f00d40300c0704200484000e4000309002d000402d10840100d041940c42e1408502a6030081404903070b6135000c62503000451800c18001200c040c0145060b40c00c2520b80310000c0c040c2c0c40c5d58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 749441825 1250 749440575 749440577
    0x80405030304121103120708070c0309031202030909040501020a020d11190c0b0c07080d050c06070810212d080c01060305250e150906032107050c0907020d 68
    0x2d43c4941c0c2c091801030858444140481098a441c1c050050001e50044001c0780c902c00060200c0c40000c92050003030b00c0644040d5011750b500c4c0f240908555031016000b0300241104250321041c4800040359540400440c0305911810000da2102580140640b620200480420901804801d00c40c190300700002d24100c03001ca18070319680d0104940c144100240b6040c0c0102a42c031200140040720b000000031517030111103100040340c06880032024201d4042c041c03a50384e000660040008110007078480d1160340c1d00009101503c0c05070359510f991814050000310300c2222200729080c1c0040600c20500c0055403c0005511420200c14030800d013000e19501d40e0200901e00f40000c00e0101016009500a0b0040c1d98800100c504a110078403200200760384175920204100c400c107601207049541c4462950260b5030240084c20001c036a4020450300c09801002c17950544160f01c0144081c0706403034881da082ea00c0d800c104983d40d0041d42040b506000e031000c0c02c98000c00c026006d01100960029450504841c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 749443075 1250 749441825 749441843
    0x40e010609230117090c090c0a1e110a0624050603130336090c080609042103060612061505030408040e01030308161b080f09041401090b01080405030304 67
    0xc2d4034010386114001d4242e01121003294010885500000684885038070422609020349507039040280400d032181400400004541040400d09440782921811200d40a070806040714041f00113511f141c05242002654160b885402c60500c080a180b1012403507050403d44a0140c0d08100c08030745140b2000c3e0241400c00e02c4900d407002894440da00c011041448104040c0e41500e42d46000404a41c00b00c2c407040c4601c03000b840c0040d0366281407140c56152070140d101c504995582070208910fa0070000e009a403002e80e0065503401c6140340c96007200d10300b042a280001c4c0c039410001c004104600c000480400399150000c14001d030405400d601c0e140040a1034801d980c3c0d5a545031030160b501a0b6440083c0120303036000040304041e002201d0714407a10701c0c1070008ac004030001201320f5030164902143c0200c5400d0801203004102400010050707007414480c0913141117065030102d01140e21184009a444989400600c5208160301901549110034a0082c40606207501c1c0c5503280c3c8000b034801088215 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 749444325 1250 749443075 749443139
    0x4030f0e040b0d0f030e060c06070f141207020f0a02010509100c08041415121303051312121412040f080a0302190201060803040506031e010b040e010609 67
    0x14503a0001c034071600000e000c1c5610070354289011311001c1e100f21422008200300f12551000b5050a07029580da6504110040c40d19864062080e030307802d8004003540c02040908011882d206130070790014214096090010000c0b0b180110340241450340a0410f02c410340c202302072072030150f039005041d01c0300800c0459651000e1a070440b025616030280c0c02004110351000b050000d0380041c01890081ca2010949030856408000c0344014924031030407191003e42ca40b20008038198451080304502003500c00d0424a140100c0c030b440f0540c1c140e8060707018501c404442c0c0c0020723080140381800e03400c600d26141071240d0644120307242e00309a4043d103031610180904ca45d00083c140300001c280b480815070095800d5545401e40314005000e03500c40c1d0b0700d4484201c0c40c481c0b07240045205125500848507100003960a0500700810418654009004040100b4420ec104080c9010f0010705500078526800000c0d0f40e2860040c1031240303894140c0c014014045801c00421038400b100241c050b410b41220022000e0130 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 749445575 1250 749444325 749444329
    0x501200705040908030106090603021611040b090a06030302211905120708060103050f06130b0112060b0a0801170a0f0f120e0f0916110f10020a03060e04030f0e 70
    0x1035425030046500c541811401803e00c10280700441c141c4402d541c0d64420540c0b070300020f400b82e00c100c030030103140280c0250784000480c1076010780380709025000340f000c103201008070005200404155401400c070b9a503a42d0030800c041d01003041020788034440d00141c104100c0750558850324025110700301e4480325049146260b062040007112103203c0380c000000194141300c43c000b40032a508548541c0842d02d04030100d4a8035012070015031180100a114140c080340400d10080a404d9880c2001e040c403010000280c613030390090080d0702c082c121b468805131f1500c3c0035000040c5402c1040e44260903a80101002110000e00460700030f0300d1a801c100c0200403110285404000151180c4001e050040c0c1d240003420050f41c403d5142e035545400b206ea8a8030b654880e000c20070b1504040d46c2001003a42c041c000d50034603500510306116040d503036009540034005024102d03418400c42e0300800050f15800105698101d42511415029210003221040300b03140a582c00380c4100001c1012800388a8280183c01c416 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 749446825 1250 749445575 749445583
    0x4031403040e07080115181e090e150f01030b06011815021f060602190c030f0609051614042c0c031b130f0204050916020c030601050120 60
    0x402c1e6401c100740032407510050050600c4030a004810113410303600052103007140f10307524483c2d0202070400e8181348103141040c2d09021120050100c10b100c1d900c5000052403078103d02c603049003070341d04e0009000c48400081600120030f40060855403600304103401400490f00880d15158000004c0c20325100201e07416035900444082544100c284008072882ca0790103c1e4042044862461200c3c80d1103541c01c139072014142501d0303a5010301d60050b072140f00312a1309840b034944801c0b1100d0203030702c2527002940c40780c940340c0d0b03002c020b100241e804584580e02401000300070002540010344220942951504000358904000d010703280040c440ca4035160364101141d20038800d14440184400921000780151070710684a40039030503140d200740106030fa001070203800100001c0e507800005100c2c40d0101ca516019200426003600400580342e820700c00803c85490304084e050041d00c070b010040e1b00042070103600034985036036400464025082400100042d0760030104060303800200c94030328901c145012420b10700d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 749448075 1250 749446825 749446829
    0x270e060705180d112e051c05011d06030319120e0f0a1401200d0605030703030507020f031b04020c0f0703080721020a060e010207151509110403140304 66
    0x40507000c000c0d05801c018079040142108a000e4032080e0080c0c2c40b5808900b409800c085100e4103858041341034114451241c0001d241601c7c40d0545000214400d903101800c44200741c0120000c207246460f0612a51510110705a0040086000314035023030355112071900a808607030a000901040300080020302e0420340180070f1040681040f11440c5082c030b03041c01d5a440321150161815a00301204001044041c0106044140d00d0040c0615140d03591070401016800004a464069070715100401c5a035410302800380114000d40d1499103a8445004020200d00e01090191003503101e1442001c160f01140a42c0441c45022180142c446000300d49a82c284811307448802202e0150400c08410070294401a00c1458002c041e811140d4400c5010744125902c160030202c0075a010710700190002d4601c0e000001c610340b000c4005411301143d991403013840220980885d05883c0c450b10300f20308840840342d0240c020b02c0382110a1150708114007080f10507115600014103074104c52000441d0b001010021200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 749449325 1250 749448075 749448079
    0xa0f0f05130b1f0e04090b13030507061b0e010c050a02060f0405180906060307211106030a0e010c03020f04030b0c0c03070f0215030f070324270e06070518 68
    0x925031450f010014a0702480c2280380e40440c200da0184a400d00b050b1183d00241c540c040c0c9042c0407503c1c1d102d0104190030542c50214200070042000800181c124000d0749990340303400001001490710818080c10184600300310a04121001c403545021400018040d040e564058601c1582d540c0d01c444101020300c1907800181e0412800751144c0ca114450041d00c600c95600c0c10148c2c1c2e401d80301e500400d5101c1003107106000441c0c0182c00e0101c070200c60f0340f8507041041e1184480281d010003240109003a034101b00e903007080c01136661180f00d10f188801e00601c940c003440c5d842c0440c90042c50707050001460146d80005440c1c84010300c00102c2807e011703012141840e06403412280c84810700e107003800c860800c01c24201d00030b01c55a2400b804407000312068078080c9200d50807036482c0366510343d0200d004080420300075402455a182413509800d001d035044001d05070b103941d20803011401212940100c241e444449988915100211200440105a094201030289490307a55481d0207500030112404180040b5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 749450575 1250 749449325 749449339
    0x10e1305070f1d15151b06190b0105030721050903030613060b160c0506040b0309070e0412032003070201290109050d060b04110d1d1c050c060a06050a0f0f05130b 71
    0x80d40946c4002101071041e01009038915001508a9215058844d5201410b02080062010030300090240a0360b1561900ea0411b02c04e44640e40b980c0e5005660b41901c0035070344c9410010074019642088021000d54010503601407001e117281c0307054900113200d03c3e00e4075240030910041050805c41c5045d070220040038000c003069183d5454000c42c080c2a0b105072001801489810400a500b101021010f0700c9150840113020340a4804002540038050111880c400051440080e160364001e441c05940900d00c141e00004180c00680f003c10b22000742112488201e00081040f03c50b00da90001d1548182c0700706441c4450300303005a180c014081c00d4019006680316046c4206140e0103021280a8030000034020070a11400c06204c004000303a44a1820780b050030303004585012811150802d0309806c006040c60003d18007400b05120a080800a440f80044540c0700c1000f04480c0c5801036064001e080f00781c05102d44185464512491504640700381401030381040201c1c800d4041e1640039183c2004090300030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 749451825 1250 749450575 749450617
    0x109120303061e230f060d0e1e07050108060607031103041205010c141303060e0309150403030305060628050d090b040c0906030506010e1305070f1d1515 67
    0x80c610851113000d81c800d000012070301200f00000e100d41034400313414003800f003028103004107050041e0b9602a000c000d600e1503c890180300400c01c00c10800f07840ca182c16121082c600d58000041d400c143d00e075480b603810130046005100581c0e565208a0304829458185480d402d541c1000300703800d43c09154800c405140702c3c5c42001d8103020041d00041000040c170307501d800d290860002844504d000f1540b003c0d0014000c90740c10300000d610fa901016841c0d150301c00f2a410411030f080011850301d030002c03c0803c01c2002090800815405006598004a046030080d040c1101d40760f20607880f0541200381e61082983d0031031303402c9040c09030f4121040c403000312702e0602070311035182010714604000381e608403401d2030740d002c0003d1915950320845050303a0740000a419603074030f844c0d190f8800610180601007404120350301080024805c200560061540f605000c8410b443c02c04226440e5000d19a29032446074108104003004403000020001c07007501300c4101c2e80300313188030444c4403c40c01801c0341042024141605 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 749453075 1250 749451825 749451869
    0x30c03241e1a13090501180c05041509050306060d030f0e01180b0a0906030c1202070512030108070320102607030608010608010e0304050907051201060507120e010912030306 76
    0x41c903510200f06601c04915039910380c07500c2128000d02c281c01c094811a0348407101c009003a0454811295a850484e00303264a8120a446035404050358070003040c1c0380c0c0000c011078103091044950000341100e0090143d0b645442c054401080580640108040d16008022680c000e500c0250040d00c4030703103400042d507166062440d440c0d2240c600d640100f00d2113800011072030312034054005425a1030703650940740c294901840010390403040003102c50307000d0400801e0f0070807070300800340d4001d10341c0c1e100400d40b4520b94142030004074804960345640034401c20401207079840e140303404840300901e8503081c286562400ca001030803200b458180e00c05410000140b2030300c5903058100c41c050341d80d401c0003044603558030046d450883d810442030b0045604103000c02c0009203081000d0551012590400300d20740a0480500d82420b01c098203d500441c0d00401c1e103900f400050070841c2c3d05c0e01d910b424403940103049200040e00c04002c1f482b40e02d0130007031403680c058100b501c03941198000b400e00491203440e022101074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 749454325 1250 749453075 749453077
    0x2d06051303020114011a0c0705120312010602011a06211501112a060d0f1a01110c09060f030304092004150c0c080607030c03241e1a 58
    0x40190010740c280b6024841c41c10122005134121b803545071007000703107104100090a4940091011160034060400000b90507125045104107040302c602c040c41d96100452018172800006801c81f00c1160701d04000078590b6040600c440d4840401103407001e4841ca035804100601010040000207101114014800c1000ca2001c01c40e040700c4c400d80b1480342d88030403404203956811140b03a12003940d85284c41b103178807800361010b001000202c0240c019460f0405003016070083d9902260700d080456a9540310b80b0b80302c1004140c610000c5000d01e01b0306c1031741e4400c0c0c0340c56075030b07400c02c2e01c003140309000c800045501c51350b5441d08040c0440b40901a00d444070b0f61804114001d00480e00c1f50b09002e00410010b0001341701100403102500e0f03580700402542c1e0015001210070740c803502c40481e400e180005021902c0f410401c0b069102d5000e9640216000302c0740304000f025501041781d04040081c02c0c00014444070081700b226025103480017869100941070364041c80425240c1d501203600724085140c00016500880 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 749455575 1250 749454325 749454361
    0x307120e1e07080c06070f051903020715050901200102090a0f090509010c05070b07120e0105071404050d0605040f0803040309080c18010e090f030a0302091c2d0605 72
    0x2d50700703043d03550700103903848119a860782580044100300750b00004000318060035606d40a8802c42e8180c5410711458400c040001400380c0c050381c03158000300500d042c18003113417106800343d140c03e07802c10803e0000685107071038a25180c601c1c030510811154045600b58149c40044000621105910359610185187c02c0c003075010781640542020002028110140115030381e0410b143d5a5624220440c3c483c0300e000c21029015400300100c44d15500c40680c1c590088003a0107500c030700002018100b49102400f0754854a0302c00c1140380c014881006903560750607034000c46503040f100100b2035584500d06103401d01340c0210000d0843c2d40120605c0207065101944c2002d0f110300070201c42a8158000400c0300c0e61180c103003c2c031382401f4042c00602c6015003007002c85030411562411600403004101c0318504680003903003602c0002c2e0780840c40340180d00d488442d00c4184841c500300e2020030202500d5040c43d2a1248080c69820412a58606165050400c81c44581ea800a800304428242200640d10300d10100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 749456825 1250 749455575 749455633
    0x31020c0c03010b0f0d0c092c060108030426030f1224040c050c1b010f080c2b060608010306050c2703010612050303010306051b0307120e 60
    0x2140c100300181c2014400c070350010328020b0940d01131a440104005590929802c00c40b45403041050004010b1100d014045459000036914504020800095140b14540c50210070301c83d03000500410004001004540545d1090b000d01413040b003030350092410906046540c0100f5100c0001c140a40159540141c0000048610749582c5070325041c104515a80030b481280c0c00400d4400c40d210b10619103644001c600d031045040c514180007120003298100541d02c40c45409807448690f100c0e05660b40a800da401a5980d030803e03502c1411300c032502241c94020004200c0701450300c400010307403410b0140511501c1881c0001c061102c90380701e00005100103428402200e4850a000104142100007000c0e2942d0600010b51100424580041507580198808030a1f8140d5a9030b040815140029041d40704050700a070021982d95145281000c00c55100900c00a0214103c64002c040702c0c040008490b0040224501039034941c401e6043c41c001403038904002031640c03190420304078000f05d42c8040c15500c0040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 749458075 1250 749456825 749456833
    0x50d050102070b1812131e030203010f0e071418190b0d0f12110109030503090c090f010b030603070e19200702010c06020d051e011505040531020c 64
    0x5044a004c501d0f1a06160030501c0b50071066840d1807000701580585a808101100c2040181e9119481010620407076140d82c9010b02494061055003000d000303541d2030b24000380f401c210220b44c3d04102503c5100e01d02076402da802400c010070615950340403001d80c1d01c4104010a20030350a040e83d002d540c01c42014000d01c030075404c003c1f5080c035502d851080806041e42020b080f000b1524507640d81700c500683c404a01e82071110b0351101c0c0c0c0c8854002d12403140158426154a0f549003040f0181601d0121074030141c900c5421010104007403001240c800604603041006440c0c1c40381c9440c0300003810583d8942141509104c1641046041e01c0c0322410300100710032215007000031010310100030302e0943c4070980f0003500c1c0700c3c200801070055100350107964071940105001801c2447c20910705082e9207003580c200e07a21324000a490451069444d003628014041d01c1824841c540c48918060b01900039403040038442d6000004070380381124403031840b00d846111140144001e01360300c100c02000f90031040d007441380e5110b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 749459325 1250 749458075 749458081
    0x705010206040803150a0b13030312022802121908060108160f020a05030d14090c130507180b041508010812070f0c030602070b0c07111009050d050102070b 68
    0x4000710300c241c09950080045881c0d80c0c1c40f05011310211702c629441640000711190002240480b40028007201600d121071007801d503245040060014100750488101c41c2c0c030400820030003505403403243d901d0660701086802130403000d82c1e0036801d12064203400e084107100010a0048414450301c8032110703418649a50300c1a454600044074151000c07250314001000b0940d1480b0319a000b521a850792501c00d204462042c8810351b125070464001000011901343c40307a08c00c40040c10315a060660145280b40100000520140091a0028501a1808030b1030b07076500460300b0702d03100b00b10103003558255100e0b10720610340e00c403a00011a0700130320425034140800c2030500e6045201c0e03103855040369621001081050b86d456031203c49503100c401c08a0322400c09010300800961800e4121000314040c17600103854120034201581d240c40001c03c6030526020810480001400c40e2a0300b9014038000c0e40d800702d02610703102c420349030403a05400c40390703000381c44402d510204041500202551f9100b2200b0355441d031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 749460431 1106 749459325 749459327
    0x9060801052412251205060112020f041401140301020702030721050609060603011103010b0703030e010b1302180a06050a0f03150602030705070f06050904090f0203061008070501 78
    0x13010301146803210324401c1c2030001419580c450a0180301181c3d00c1d191900c405000e13001448070101501029525054070101162601030402c0160418019504010303803024070a0500c00d40c066200e02c0c81c9418180203481465a01900a007136503801c290540840e082c0c4064030302c2c00401c8845200d00459401c004860081004c000540310a00301801803509403010404521326a110800041017982c1014045400e43c83d00340c5000110510090b00c0319000d800c070f040203264400340b102049414000c0b158001c084c07490854041e500035175009405c0c0500c6483c60700c03071940820010f000a4596600400380f401c0300c00c155150002c0c22403100204444e211303125800020050703001189400800604210a5010f0542070000e59101450600010490310420541c24000c54641c0442c0c1e0412444095100b0368940c0101503c09a00d003502c1030022083e064459584188500340d4000f900b5 = true := by decide +kernel

theorem cover : BRFrame.Cov 749280575 749460431 := by
  have h0 := BRFrame.cov_init 749280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 749280575 ≤ n) (h2 : n < 749460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
