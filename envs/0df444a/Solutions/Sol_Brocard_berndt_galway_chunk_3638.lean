-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3638
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:15:07.817284+00:00
-- url     : https://prove2.me/submissions/14f6853e-0650-4046-bfcf-e2c01a3a1687

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 654136690 ≤ n < 654316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 654137940 1250 654136690 654136697
    0x303010e070e100c170a122403060e011406030d0302070c0317030f06010f0f03090204020d090c0303030c05030438100f12081218060a06030302010c020f0d 68
    0x806040c4140c52040301d44501510034a060f03059440d00034003841c108401515260f141101554150b400c2c4004c84aa03011703142e44c2c86e007030920711512041c060b0000d000d003031400f40c003210782400300b610700400000001c512401d000a480048602030711f0035030b164021803186203c00041003000b84c0e10042924507032511a4540142d4480d61458030754034071040f94002900344101405034a02c0c110082009600400c09400900c104e0b81e6400c00441341515261041c0000400c0741c151540c5080c0283c200e418590701c000d10142c14481c0c2041e00c002120030082040e070340355003041e004006068142c0300c4c00b014040b951415924520b003d4071203182458185503914040307804141c0501c4445203902c0300c28614407443c4410039450070080a0720401914074042c0e266080d510a40008543c0c4c1d1010041c920960312900c42414120307110b00c10000c41d03d0080c02da039401300001412010341041409510b105160024001800909505000303084500c2405943c0665100f07a05454078548001076040c1e18581c01e02c1e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 654139190 1250 654137940 654137969
    0x20304080a11100f0902030f0d0e01031a030d05120c1e0913091b0605070c260d080f071b080c0a0b040f0203062a0d02042304150503030301 61
    0xa400078501540464880201880e10020101d5131059405c0202e10900131811260803041d024003154440d00c0d00162080401c402003c04a4154001e0b00484901d141c040601503248c040b4401007428182c0c41011000013800004000f21000c03020800507800034905280c460805440c05500c8810340c0049007040094040454400025600da402d100103c40700c0110512400455142510309030200c405903150241d51101c0c04aa884c1c4141e0960305039641014050144526005000700181c5c410701c41d20a6008040304021442001007002002c010903d58480b1060b14040b00e180000302c9014001404100d004945100c03294545d05000c19007a030042090b580c0c84807201c0016180c1250403100138400c14860042109000624941e220014000e030705403982640c840048203041040a80f56010110055242801843c5400007401c140c1152103401850315031141c1184000360800c0b041c2601d00042c00d0103490850410303004038041e0000c006000c00800d420640001d8590005001d0911a0045034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 654140440 1250 654139190 654139217
    0x20f0402070219090b041e050601020a080a02070602120307050d05090304171c0c030210050c0d02041e06030b030d0e13110d0b010203120103030f11010c030618020304080a 75
    0x250304481d081da6000b03100d1075116580c01c511080b0300c58548900440b0a24012099840d810301d4007070000540c0d1441000444880010711440003080003424040c11071007001400e80c001101d50004180d0b500d001d030000c0006500d8074200a01d020784ac8581c904408009209102d9401e03000010f45200d00c5141c1e101103603641c0d8104400d885c0d170083c0d13031040181c441d01c43c1e844100440040341591401003245c0c0c04060407000e1001c1601e4240c100040100140d01a4490312504ac4c0c2c1070740705681204015031210b00c1e051101502c1426a006a00f12104c07142c040c01019400a00c800d00c003100400f55401d00380120210710000a46031100c3d01c618005002c3d0100303540c4259034500340e060071501a0702908000955114074040d000e50422283c40c0051450004200040d6000100350303005140740c0b80e42008036070b0940e641103c0041c11108400244200981c1100b05034000b030245518415565a000448a00d043c2010300d4814012414400e10f501c100b0030b000105013100c0031118010b00382c0c140b000700c44001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 654141690 1250 654140440 654140449
    0x2301090501120c031104090c11010b0603040f03210c1b080f09040b1201200403080901050a030905010c0e211b0102030d09060b0906060a0c030e040b04110c240103020f 73
    0x41e00149000c030001d004034520f072082c0d01050340e545043c6c1e02c03440c50110302714107582201c204980242d40a14103000180004500b1140740220f81c0c840d143c01e0140002c0541ca1040103601170404c1ea5866442d042e002c2c010701e41c81181481d0303543c2c40d84044548042c0c0c03602c40c8002486002001503010b0000502d00d41c00340c0703550f0003105050001130b2000b900914190075980c0245840901d203004403100b41c0306108581815010f03502078907000751405203040f00328001500da980c401a120814552035000d040302041003031054882101c45078940168203c040e800f04901d00300e8100000204010021100c0508580000c0111500900b041000c0c00300d880d850050b4954003481c1101d854580c2490b5a103401c10509401504d483e00c01511031a40030303115401008428012074001c1c200103821034401002003441040e60389040ca00203000020002340c49404601904c445142c00c0d90a140001403007004080200000789110b9081080c960751413840c43e00300fa07000341062001070b10540050076000e40960382c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 654142940 1250 654141690 654141701
    0x41d0618180604050105010f080d1403060d02130609110c060604090804080a0602090102061303050a03110d020f030114040b0904080d0f020c0d02071e050123042301090501120c03 78
    0x200200700c2e165450a40341ca140a030509008011484001820001e070b40900000c07020514485034075040b41011911411520a82008021b1640300304000c01030b40158076203c209291008420002180300703410a15035105580b172440c451503803041c04001800c09490f020a807140c20034400ca0700400c0d00d62150074030060328001c1e60070007517040c010b18559200304120390b802441902801e800303880596951b06e544001b5880380076006404600100302031841d45210707501404425030360b0214107050074020305003030b02203802124a101e070120b80000103001005269a00c5842c0d8038003200e003800030125490108a003100e0280c401400420089054150000307150080c0041c80d01540302192210710b100071840e540e0214900c4040940142ca42c046002e40300c3c01108a000c3c55159100a1814985001154445c0031085e07000054001c0d0300c0d5000c0d034401100c005000078000803c0300d080050511080704c890722100d06e07105040c042500010421641c00c0034030b040340d1000182c1c0004e0710945030081640a0071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 654144190 1250 654142940 654142981
    0xd0c03050102030903040f0f03080307080603010e341a0d0e1b18070801150c1a19021603030209130603120908030315040b030f01020708041d0618 64
    0x14004410001c0351340e0000b020703000300c5420000f80d1400c143c1d989501903d11440d400085c0c0303861001c100140c10385024912990308448003500024032000e008444908140300240c1034030000a1306030803041e425018181d5144c01050711060402010314001480c4070300d842a40d440704911501083c800c031a2000c96020040450022055030010031003406802c031486d00080755540310394251001c84404100e01010244500c1c041c1d100d079182d41c2d080000648442618840e00020094800c000790001912009074594415002400103560b04004108002e01c0781d023008400b442a1043c000e00f4a8802c8c603000100b44143c0508005a507440c400d00441c030088003050320000032504080e0000200461091001c40b50151a03036030106054039400d0041d100d10094840002850703408541c0d03c0140380c0b0b0380c0b0848220b10001e046a8200d8408507a190990b040801c05079814140801c0070450141c0c08203407103000d188001a610388628000000403103c0c00c40e1078080901008840004802e540441072103110706 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 654145440 1250 654144190 654144193
    0x3a08270c092703030a0513050c0f2202280905010507150c020616180506131e08010c080408031f0f0b0d0e0c06190201020d0608030703030b06090d020d0c0305 69
    0x714850840940c3e01d0784282d400400300c0d454180003e022400c182c1024090651010203484000f1041007040703502c007249030502d903010f0741c0003a0800b1b04a050321802440c071841c0103005070b128100c0d4018000c902040c5050201c010100301003043d04a94040c10b5202074a009081c000e894034080c1c00c0181c1c0c503582e0b120b02125080d1034502504ca842d500081c10b0303803142503000041600c40c0301103181190499401680003104040d0700e40203010b945044009800341c0c4020841c1c0c0d00b42e85603030303036400009003501100a4094056484091102076000c0c000c51201142500340304500741419983c030107403448002c2890494496a03c100204001044280001401ca812914034156190344100c0e030746922402c07080c41c0e210303e841c40300180501c0115014420b00001407040341490351500c104422070040128560465500b0801208a0324081c820722028050105c001d40c4c80d40102c2c034000d0100c2d14014282840303060107000004007036031500e00e044800741e03040d201c55040848501d48110900080e403c000e00d20b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 654146690 1250 654145440 654145501
    0xf0307030c03050319060305060406150f090207110d0308070207082404061508030a11070b03180c090411030d090503030a1409310e3a08270c09 63
    0xa03c500014114007a50044c01c040041c40c0741d212419400c00c00c90300c10070b10a10dc0703458080000e074240f540030b4007100303003d0f81411401310140b60000e440714400394002c0380030400a07414402c17034544c10400d82010b01148001447c0c2101e00041b04540c022030b89044030a610021400282041115080304c0700401c14002c21a03002d0762503424060b00e030703040050a00f00048070003070054207007403002131000116400c80c0161480d644400c540c03da0348490829066245100c0c4000050598071140b44203842a0b005810145610040b0710825003000d01c0244040100b1101e001c041c0a955400700c200d4180c0d1342c40341841a09a0102c00846000780107400079980d100134466070301e0a22510500e920000200c6006030350a00c0710110301c3e030008550340880149500d904c4405032280c0301e03103084448610701e01404516540c4030b0702103003030040d8000808240320004081c0700030322040500c2004003ca80380703188800c2070711486800f00310a036506101c03240d440c89407040c5000303d00701202c892400034044410080ca01d50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 654147940 1250 654146690 654146693
    0x23060f0105040e070e0610110319030e1606080703111303120801181e0911091006020a06020f12070e0108150616151a030f0307030c030503190603 64
    0x86008091084600503820245916002d0001103a4202500c1070000840000d40352001441a04200311a4402c1444916000c00ea42d141c0e04101030720b000c1c1d5500c00c00503000100101c004090380e1040c0e00000955000341e082400748100b1101c4442130300c41902d4000810703034448070210302920101546440720740700010072688200900e00307020305a900a9030740f044102800c000494800d0002d20582d410f00d461084110b00885540e04034100c010441e01141800e2200007071000108da90721342007101c07038100c42c190119484c1440d905007603100e22000c6075140560310b001006511004003000080210364002002c004141d148400e82c1c1240c01c10700542400c0d0b1402005c003401030703120b10445a0115040308001075402000c0402080400b501404407401c01c40b401c072100f4400300b0740c0710f41120649a54060400001120b214010480310740340f0004140140c42d00906040021a4a0080450b001082098042600400195036140c3d261070603665039503900128040c8100312507892060030b03040c15070000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 654149190 1250 654147940 654147961
    0xf03151902070b04120908070b0904020f0a230406020a0b0a2307120506060f070f0624080f060f2203081608010f170c04110301060f0f08042306 63
    0x5104e1480354030b51050304d03c0c641d00162000981c034802d500ca9503010010034485500c0010240610201c040c0001d0704121446002465a0f0032032030b8003c0000750010903190800e01400030000110703418501d01132800e420803100035160f061810004d4200c0001d200172401c107031000c0c3e22681c80422500071035003074140d0600344000311202c01c1d0b40400000721550346000080880d0b00c5614015078000b4013242c5000d00c00c01c1150925000344000f82c4412500700110800308809024014020301805902d00510f202241006800d0003140c00146d801d84c05400c019100200002d2030300c1c0c21540c0c2200780c1c501d941c0d44940d0b854480c1c0c041a60000940e00b1880c1e60010150400044c03400380443c140050340903103000404880d010000d12a0f096000380e144030410040b2a41c80744104c0c41c000c1d00003980e650410101c003040540c0e03851003c84100945c0000100825940f000810480c0c0f10503181c65514040b07030810040000c0c1c0060409441100e4484000d100d828040c90401903450140c0142d98079440e1007410310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 654150440 1250 654149190 654149213
    0x9080706030b12070609120201110f0705030706110601050103090f1401090201090503011e0e01020c030c0a060605030a08032202031506120c0303071b1703030103020109050f0315190207 81
    0x24007810f8060340020a810010625034207442043c0d0b9001d14251505d01c422011660403103090b418001a8242032001440a206d0340450418400082c10442e1401c0c09240c5424000da01200402c1140380e10030300040c4002c03d400341150000d20340400e000328107042c02e8040110800d8001d04100c0d0a2411704c041c5813041d0020f4a0040c001d0300c503501096a69018182681d50b921148840c0101c0744d4a801c0c4403100039031220200c8000d040005042400307102c501851503002d891a007019601c880110030401003180980c40c0605070540c0a0178207102076130754a051b20301004c0c4c16544880580030440408140030304140c0240e41c0c0080448482904d80604002d000301f06480c118007070030a282e00710354400710009003e0b0032280050b0007180342c901302d502c9418198040c20f1505001e01e01000001510500c046048503082c00d074040a0f40e0380c0d5245200141c13001080307502c02801402e0b101980c03100ba40d070105400d000c100c13503500c2c1084a40d4902022442500b5000e0b241502288040390090034009903d031070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 654151690 1250 654150440 654150461
    0xc03012037080c070203060f0c040f030b0a0c0306060c1106091003020d05011a07020f04060b13060306080a0f030f0c0b0a150e060307290414011e080a0c0908070603 72
    0x82c03074156295401150b003144540d50b4080d4060380228042000450180c02e22030b407160400c8045410b25032151440346601d035a584c400c0c0d4007824900b05018020155215080441c141402c042201900c0c088002d0030111845502811025801512a1103602c4441c1116032082d00180003c601d5010b545000e40250040000ea00f001440c3c00d0001c02c200068142c845504c3c0c20300b4070220300300f001e95420407150301c20314000703907030841d4031040b0008087c0b0002010b0700382c071088024044201410150002c046401c0c95200781942c3d0300c0030143c0400f01f4442c019001c450364051a1030100c400100c0c1040e078130803d4a0a004214165450401084903616488804a05c0780c0c1902d14410650321030400700890350540e1045d900d0780004070b042010100403141d41d55403468000d40c0c101c040c034007208242001d40003503211100958039040480070a60b80440f400e103140c000d0a45059104a41c003000415085000788080921503884600000341c0f80035001d038500829020045072403458640d40018091722a0918 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 654152940 1250 654151690 654151697
    0x80d0c091712090f0301090606080a120c02060a030911100936051905040804060933030902120319090e0408090114030403110c03012037 60
    0x1001075501001280c0ca41c0300c000d030300324402c0c180000d480400814070203c4645690642d43c900c11180064400e01541009129035000b82c0008006411320301c183d1000030101c081044540310005d00181d6038402920b00041481c9030000c0c030042c40b450080c9013180c0d107000b034a901c0003000741500007045e404001340301524109803e079002c01d803e10203440010380c0d1803181c05401d10460040340340e04100c6548020b03845501c001c0e02d0703c1c180002c0400c2d002111000e5606503844500010f05200842d042004407008201c110b220311a060390403072805040340301c841c0c48440c4a14403541040400b40c829007042001c00d400070030080850034071100c60350342ea41c04010000881000c52203154007090103459035004031381c130b40628400684d89a54803490294002103401e41809101071440c00280d0022000d188038910980350702c04021521040103141000544096100b681848880701c00c0400020b91000c41414411603681c440303400369055201307120501007905064286981c044a04034400b1b2480002a11544 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 654154190 1250 654152940 654152969
    0x109050c072a0b0c03162f030706050a120f0e072301050306010c0602070609080f0a02150c041403030403081c0b030a0b070c0c090501060905040b0301090b13080d0c09 73
    0x22866005409134800d041c0c1581c1050000003139000346d948601c1c0c111442a1040b5500b5850400c5d0602c803880040a060071500c107801d1060f4060408100e601d003d0042d81c1047d60a005050400400e01c1285609203600541c4500d1014a0301101e0742240c0000c0301c103042543c0c01c030b40e15066180034080703520302400032200e00c20345220001d5020b001124000c00341030b9580c28410036980c4035540603603c8208215204c50b42c400b09000414055005408040c26400c0e0442e690340c00084002d02e0801c3c0d15a251a0003a0200e080c4200340401e04119400c4417106030048140e10f03110f0000074114090740c2e101804514001601031340c244075110100300300200d035050802480305490185540e039800708100a08401107100442c0c8014000c910699000f48030340354604903640c550706184c0c1603c0c0c082e40000c0104050301320178405454117002d000b04078a01600201b00f80038041e00e0324810742001400c400b040d102c50036014414008548111041d00c004a541807000b2074070382a0081041e55140b00d0098100d8101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 654155440 1250 654154190 654154199
    0x110402070c0f12150905120a0504050d03120b040501050f1320040614070210030b060714010c020d031b0804020112021206010908030712030f0b030a08090a0e0705030109050c072a 78
    0x40c481e05e2661600a001004031080c105400c9110b07074000c6030043d040c08014040041c107569540080700c042842030f0b9999a086915401000584c0c075085074441c42036042000501064880e240e5401d03808800700c40b0a10b40542d4040304600802d42c2044450b0140e000a11000940c541500108100d0300c441c3c1c1d8500d0070007420503881c03000e8018510300a62281030a005d94030090300c21740100e03070035481c0200001d10b003842d00d59030140074050313400b500c1c141a51511650112642c040c40064060102401c0500902110204084168440e5030000c818007560f14081429640700d070f81001901080c60b072046680d0308075105280010413040b0381c0180041d0750b145000c5002a0040142c540856000c8111612a19544410303005480c0041d6610070702d030380e5a80010220f5404204200c60140030340d206e0f03503035011503106101b024031440e00b22012581140007400000f607030100840f411503000c0003000030a62102105501e86214200000e410000c1000300c194900c0c410100e617100c5014000c4a07540d080d030b0388 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 654156690 1250 654155440 654155483
    0x19030f0b1803030721181406060621090102070c0807150e0d0b15100e15040f03080d0212070f082a070611220602010207110402070c0f12 60
    0x102e594130002424074028021040054003014803034025a8400b00e050b040201d030a442c2c4034200c4005442c0b0668490251000000c180b01040d00001c007558550300d000c00742044841607440607e0100f0880100780c001400d01c6100398103030341440350320100c10440c29984100c1c0302c0d03803040748ac051001903091110715410f00e0b03070250000540c12800641514040302c1d054071450f5006100811488000500442c919400d950b0710b002542014440e0b11050038a03500c8105201c0c110303400c000d41e115107030804c00c0107020444c5030400ca00c0861b075004120300e0b5205102e44015002c0e010f44840301654403071f10014004126005a030b038202c1003000b66215449030fa40c4140d075480c04c689040480e100545e50b00c00b07540903010b091008141683c0500404111180c0c0310301144d80c02e52080c5420805030214500b00080c050079404850020300f041c0c4000e5062410302e0319a0381503811101d0385181300f00c0d4000303030702030030080111049001480d4080030001c0c00784c3c2d82c1c054000180440c1c1002c441d00350f01c848400c5140d042c3c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 654157940 1250 654156690 654156697
    0xf0e03061314120309011a09040218090307020312040e130c060e01030e0d2f060a0207060b0409030503010611030f07080a1b030905040f021819030f0b1803 68
    0x451400000c203006a8403402c841c0e4100e02140b842600034040c4a2015442c00f030015800341550b5400001c043d0030082031311618100c170b21002446003c1020511025036928884450320040124075030740302e03860703e000d060315510910034000d4150040361443c00c100b594044c050b00896051f401e00381c01c039695080b141c01c00600d003007070020643d121448003800041c1c41020140e1490b030041c100080d030b103044001c0b0340c1d03d050901c00580d400143e074400c01200d006600820358010706640b1407100700d1810b844120030344401d002401080c1141d0302003510424809076803c6015500005042000741c140b07641002066135000340102c8021459078103420100c06000011130709104c0d00e528031390341001039a5071b0303a1385a0740c000303041d15080100180b00c00e030121000030346030509e084c400c2e20b5100c900c82c5401d0900040d50f800007443e1901a2040c0082030b241c200c401038001403ca01180c003515007510144050126400542014203000c100304040c00401611012080c05810607003892130084844d131503503d99074031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 654159190 1250 654157940 654157951
    0x4020307140d0f050411010f051c090f02120609071d040210030209060c0c010e0a03050d0c05240a060905060109170a080a031b11070e04140604030f0e0306 68
    0x1061004200008102030000d0214200100c1003c141445001d02c600b050703402c02c2d00c094031044041c540d10000c96822403488501042c076030505504208000d0b403501c40b001c1d00b4075950f240c8542c5601c0c3d42c4041100305440700c0d07000c5600508600c036130707100c00141070f82d1010200c0b640f640ca44903080001c074446400c07000d00c600440303904400c81040d95440e820f11800994004034581030540a0043d00801d948440c0507010201e07200009103010300180000422000c03400d402e45024192486007400401c501140040c15820a81401440c0c0c001c203240041c68040300c100b07080d03a258451441059080c009841d0b5900400340b408003032000700d8070354039900102c9209903801c0d800301f801e000c820403070b200b12510011b8450405c00c05660603882c41d40c640440b5688284c0401d00080e60b500c42d8200d81e0070300c3d28a85030226541740b42400c00c0d1400f00383c010790b03122904e0080e03d20501c15400060100105070700201c15019a49040d540346003080d10f405410300f180300491a0106155901580440c1000544180301c0c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 654160440 1250 654159190 654159197
    0x106050301150e13091202012307210507021b0a0b03070f03020c01061203080f061c050a140f060f060f04230c1b010e340b1804020307 59
    0x81c0c40c2c0c070070903500034003004031070307900b04030202c038002104500e5110311149203000e1001e05e800c00c143d141009007116200340c944a90030928102550340092030690455004240d818054901d0101000010700d000c0c40a4411808600708401c00c008540d002c01d0aa841d220810351043d20b0040300740c1003120762001130060210b90b041c28800a9466482808181c4800d0001d040061800010074201800d40c0c4054010b9103c2c2d02001802c42d0405600c40da00c02e600180c0007003448018200040001c1041801c502ea4000b50070001ca42041404014007c003016039501144001140c0c070b175168410b459a0a00040b8400390041d10002424a24101ea1491040c240285103030100c003084000c05c001048440e5903455580703600700701100da005c106101c00d40540344641b11551100031000050f8a4164510541201a41010445205407100155400300070203010382d0380111002c00c0750b0307820200041040c213a0040a000308005441c0b03d00d2002028000081e840040c0f040080e901880140d100070354564001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 654161690 1250 654160440 654160469
    0x20a03111810090f03080405010e03010b0a060f18170c180f040303020f120a180c0b091c03031a2709030c0d1101140402090109050901060510030c02060106050301 71
    0x54a842d0b1035104003400c0701c0c01d0008905455103292001011542c20480f03070080005414081907070018808511420110024080161803a022030f1841c0d0007032090b4824441d004400d001e4084c00b441440469400d854528050b0a545111201a1102c00f02c035801850049100b07044990900c000d0f803400b055002504a00c10342c440c05803a403c10980180305801b05603085c0050360310100400003c216418494110301201d05240f0f4050003150544498200a007910103120780018856010000464010180a94440c580364000c1404c2c905606640c0718110086c1c0c526508160f010b5000d501c140a032060030442c10310040042c00740b100170300394030b8002d082031308103900003000c01c22203080d03500ca031041e002d587c01e01c0312610b40d40d4940364103107400b035010a0790300411000c210000d10900240340301c0845a46030314101034000c01c2da50300060017440d460503180c50000708690001d4200c2c4009101c0030f400c022828404042c024001c14a080856006000b8200000340d440d10420650341620301d401c041042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 654162940 1250 654161690 654161737
    0x509070c0c0e060d0b01030f0b0f072307020406080d031118130b030105070c060515010f0f0908030706050f060301201e1b0f03190f0507060f020a0311 66
    0x207210b1001402d542d40480e4042000c00001c90301040e03640214451140b0002ca00c4142c07414990050004100140d16081c0d0b8080083c031a030301c624140215080c6110b0300c03140d80a002c2c0c0c003481a00c034403a80650800d0403c50000760840001400755a980071a0750700304038881c2c01c0e0200d9241489a18048510140b4a1805c0d030b03218074241c00d00d8413103282c1c4950001000080103000c60300f503039400c44401002ca82418589401c0c8056801041d80c018040f40300010201c10084c00030b002d10700c41840e000f08221140304401d910500510f03500000e08194002c907900c46a46d85030410140c101156a05107403410307100454183c1c2414001c41010b40304141075003d81e560229641450f40d0460302c07806540700290402d4112400d003c00050603820250407000c049521844080c42ca041e4602c120108240d01c20800c81c40c0140c5501d6000c0b14078004e42c6031101c030383c40101c10111001d008202d030281030980740c9000c0200c0b01c2080d5004000f02030180c0c43c140412401500450b60b031380a5510400025140c5200341c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 654164190 1250 654162940 654162959
    0x709090204050a0b034206032406072f0105030402090f150a09050a060f080604060507050c19021906080406020a1718070f0b0d0b0109120c0509070c0c 66
    0x194010303890010f103040d43e030390010541d1030f914800b440c86107131143c0320491098001091b010490100001c1d43c006145007480e002d0010050725600074003903102c15a42c5001c40b03030340d244022280b070030742c0200e90341c030601102d106d03405024200b4a88415089500c402c0101c0345502030b8080d80d05c22600201074041940c1c40c1061420000310007040782004a44c102d0a50000c0d80c2c1c2c1c4001c40d0084d060708140003402d850f22501c85401c445030b54014003100c0c110391703400300520003002601d6540603601190110700c0e9103428a083c0e4490003080011b00d142c0c080c003641c00c5a01600c2c10300c1c1d4120a8001c44251110071551250344001c0c04543c0615000644c070840000c01184c1c9a400429106500e490041c0390b5844010004a520782c7c291101d800c042e440c905007881c00c3c40d003003050307802401c0907885000c03a0303d1910140c0051889400d0b00c1009403620340c0e03500012680503001220003400e400e00840840405860a8034803040c01c0d000d1540300322101008190b41c944628804c82a09902050b00100c440c02c040309c12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 654165440 1250 654164190 654164197
    0x16080d14010621050901290901050a050919090b01030515010e0106050a2007060c0b090c010c0201030b0d0b192a080405070504110409182d050604030203030709090204050a0b 76
    0x17031815901e132240040d000e40850042c00c8a807186100c200f910501c420b0410144410607444a4407a0319840b00c28080c668583c9545034019900e03a40d040000d8041c07440300405007a00340b901031300300ca50701c10002003030050200b1043c0e107181c600ca40b042c1e00781e038840d40102400942030148a00040050060403000d5000714040415000340030002d035040c0100740c3e0258a0440c4507007000d000103061000340020000394503170786a040040040a41030b40c1c501c60300000c1441365900d0f0003070704054544008500640343d8601600d560340d00080d5507071a500d0701d1520117050601c0d8401000107149804070f04200100315601036181900c814004c81d0501a02040860701c100000d441540d450048000000d038654451042060700c00e00c540d0010b4480345070000b079000300e81241c0c586d00c2d44c035444083e8500014640200c040503402d00c2038000903d801c3c0c00b0180c1c04520340c2c2c81100415034860801032205250b0004095803281c41c240c0d8504007841e4440c22800180d000c0da2141c584c01803110070042c8100b6100c600503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 654166690 1250 654165440 654165451
    0xe2a0d0501060320010f0f05090f130e0d020f01060e01030f0c0b031501090905270717031201080d02060f280f0b01050403110616080d1401062105 64
    0x1156041d180e40351030540c640700381d130b5040b00c45402e1110907141c0e50b000f440d0340c9803503129030802c3c03011140c84503c090004c0c441c400b0014400c03513504a00c1c0200c0e0f520685089031541c4114000c216400c00c9091040e40e0b24405246400540305a401d4030205007014081c00060303c03000c1614040710b034030399030f101c0070500e82c824001c44240014600c00f0408010044c09103204240f52460250301d40c0000c8000f40608000340c0000300e146003443c3c00c0000345c618030707082903048506001c8080c9064003048201814010300e6002401e4403a24038555008034036001001c0c0400030820f2610030800d9030b0741c0504036a1400384203840b00160300a600050520110242810703031003d03001490440a0b4807500c01c000502c0c1c1e50701e00c52842640d54481c8420f40031414840d400441c0c0c401e0820a180a0554462100c21540300ca940b603c508000600b030040414410079014407030794800a07807a101c000701000705c005040010050880cad4400d19000141682c8502d007101c0b00142d04604d0b04420140c0e110240020348030040c074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 654167940 1250 654166690 654166693
    0x12705070519020703031202030f181c030e07090e060a0b18010b0c0d0906050412050a0b04050601061d0618031617190803070507060906050103060e2a0d05 68
    0x15120400c02c0022080980341425400362000505510700074103414002d20710500780503c180200000c140f01110320540049590700d8042d4000d008903030f4a0300c0c0424942c0c00400f15084a15160b040d660160401e0f00034651036016640369544035143d410444903100c821103100d601c00408201008001c0c0c2c042420782c407000c0c1600547c41c5420407511a4030f5003ea006101a11002030790b11100707081481004207541c528502820100e1030414010705500650083c02c881e20003410702070081007001c0100049142d44a0018912840c1508195844250134401c00d8042402c6034070b44c803035080d0f1242e11001516401000d45091141140b08400c50021070829660035200340303001204494003078072000005100000201c5c1c2e0091419940c41e0410402c404051145204c4e41302c5040090180400d80b81d200401e0300d0901e880703035414208000500321084014103850b01d454008418010542c0041c3c00010250080301c1c00b62081000d4034180302050300000243c00407030000301182d403525048030b00b1401e00600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 654169190 1250 654167940 654167947
    0x6090c061305060f0d0e2b09080604030918060f09050a091b1d0108250f06090e130b06060a030908040906172418031606050127050705 59
    0x6000c82c0c02e83e849a801c4c203100100c041028141942d890007a044800849805043d0309260740d00c0704450f03154407514913419a043d0442c0ca0138168403519207413006180d880102c4185040c541005081a14180158100200c050300754903002d1300035024841c11140042030041ea82450082014028040a0318180b401601c44c103030304c0701299100d41410300c0c010113a0083c90895160200c4045c0130011441c08090991850004202400d4081030082c800308094048080b0401898500c110720b402c1030b0803003000c0e540100c5010850b15804406801540d0400424195a48820301d44030202c14403580c0c020f0803820000c0002d1034070700b02607020300144a068140456003420b00e50b181c511540203030300041e880c0390361050304002c40301201181104a0343c26102038031000c501071454000240d0101e046030f07134000803c1c02285258201d01454210503030100d05403070706c0b50294601d00d90700c41c120180940b0100c0c2488004191009281c450ba074a01d1070320741c0413100c1034201145001c06400000e000c40d05000c404e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 654170440 1250 654169190 654169199
    0x7051e040c030b0307090b010503040b070c1a071205040807141009060e010501050d08030a050c0f04060203032e0905040f020a06021f0b1011010e03040b070c0806090c0613 75
    0x18050796149803450340300400c0c070000c440700b410714008055001c12100c90500345440220398106017100d40180c0c01004c141855990100191a50481d15000402d8407456480015101c408038105a02030202e40d6150300108180075121300540d401540c0191036484100b1410780001e83c2c032000110b080c50b4500903280c070316511412200c01c0b200700c0c01041d24143c4e11030480d00c0318444288116405000304452980c64480b203510707028042c0c0070040c010343d440c60365a0f01151800e50210706039402d01003401003050303449443e00c8000b5101d0300b00743e5070404c40c0d01c0091295150b800307111070601e0030303100d960101600c00303454490603002501014000b0703034000c20011100805621307000261805041309400500006c1c0111503582003480500315080c0c55140b07401c080c90003a5a54244501040d070942c0703021450100c01e40039075801092400085800c80c0300004002900b501c44401404101e80035954002540b55101500c070340f21102100c0d400c416070008a42805c0500d00400600702c520151b400d0394888540380c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 654171690 1250 654170440 654170449
    0xb0c01110406051201050303160b1b0d1d0a02100516150b01120203010b03010b180904030e030d05030c0f0f04090603030201050f160f05090103020d1109012007051e 72
    0x56003110000800016050700d44d030322100d601500418050380118a4080c0d040c20b13002000c0c20900008041810100109078511828101d91140494940344696640c4848210345c0c02070209803409295884880a040c1c1255004183c0c94401500034110780003007034103160701321002d80c488080034140d02200d844a10100d010581d5100351036502075400241000303c03070000342c500d00304102e4000b0304600400c018031410822000742d90449150115054545040c4e6035440c0004008a00164002003090108000c1c580d120500180d42c002c01c0d000d40f008000d40d80b004403603a2000b00c41041c1c4640c4200104110080d40100a181d8440e20088c0103041c5900c0c0c50030b800c1910201c2e4401c2e00145c0d110800d200e090240a005a80c00920101e8079180c68041140007822800070f803501e69051003008a040721581c4d00036012209070f901c0004080016a059600c8000d443d080702c9420fa0000e0710721011041c0c112005403528803642c200000510710607240908002004000c0403009401c00040c3c4014011500d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 654172940 1250 654171690 654171697
    0x3050303010b0421031d0f0402030a05010e0901090f020d051f0e0d110604060f0e030f07060e0706140a0207180504030e01030c05040b0d0e190b010e010501090b0c0111 73
    0x7a04075840b50f030b541c0742101e00c0710550709803030300d070700b02d144081031110700081d009400c40741c10b04c442c06881c2c0416950440000c140e0452489907030340140c000020000042d4090788010f0503035101c4491441540c444107505030880d446190300415400200c40c0303900c007500d4500403640d21a84500c0c01c444248021520842030345480006082c1030360344072082000c07480c2c0140900040d0110320314115092082451005680e488043d00c0602b03560307aa9000882c8640d85904812141000c28084903683c03411060030000a502c440401c0c1c4289107025501d0408020105281d030407a00c5595903030022520030180b140d500e6016074004c40540c442d0000014400301440c5066480c0b0842c3d0100040d036140031300300a400c200b041e060540c101490841010300071504001a54195111801410344816498400f41c005040c803030503404852085a48a480315000c0701c2d000030803248070300403000c081d9036554410000d444080c00303460f01003a607004043c490103043c8409000d45048180020800000f8102c001034181d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 654174190 1250 654172940 654172949
    0x216090f06081e0d020c091f08192907110c03100507170f2208030c071b050303041226030a060812030601110a0b190507050307020a15060305030301 65
    0x100700445003802c4a0034049400b090b21140040e21182c5008800a100e48500a240b04003401c000080070701e2307020111400c030010341001011100c040d00500f1403c42d4001c1200030480da0055001044640b04815509840d910380300c400394602a5212501c040d10301f2805200030340d0140c0b040b40c00187d00d580c0c00704008200c2d518004400285820908070087c940b26000c0891504540c03a4024014400603000c60740d940002e0a0f9120703000b1702a072240245410001031005031208202200b0b204800e90b01c14001c242c0e440c40b820028074404180b42c0c4540c5114005c1c4171340399054200344410440b4403115030420340b68a100e4070007000030441c070807a01e02c1b000c4a44030000f0119000030040000150f81c52107800050701c0480d00030980c3e0a060120320141d440000c00341c1d030400a0328501c40800030010070410504560001e141113030380ca0079481320044c200d82004910806420300022070182e40c02601124068402540901841d04d030700c0c5c07540c441075000342d03d034100300a595050000c049002403002c0d40c041c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 654175440 1250 654174190 654174223
    0x1203160b01060e0301020a120b0111030d0507081f050402070204110a020601030302101503082b0b03010c2105040507050307081b180f0c16030507060c0216090f0608 72
    0x1541405002044640f140c14a0341c080c1e841044000e504a80110401c411141d01c01c902140801080b4012103440c1c003000c081d04d055200c08149080ca40000d508072030311030901c990b00c1c580e0596031010344004006e40d07015031030f056000c0328200f882141840e4005080e03030b50000e44045480815100d2050032548003c141d2001a042100180100340d4140074414038181005c409119003211101c412200c2403052000421803540080d10b4291180c5045180403c0b03008a034040440350320400c88a009447c0c1c00420174402d500c0d0011114110313029100c074110b1601103090744407030408484107001c0101805001602d1510030301400080c1a40c04000c50307400342036071402410000f024008800880103000c01c3c040e100d005811341e680e04a0a6a20308241d004004102000490710340881010399403044070007007600d01500300d48003000e151700301c4010200c0500c140c10030016003808840c201d885011180244078062000101004646044d0308100c010300302e00134000600c1075550060602e0002c500c1803007640c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 654176690 1250 654175440 654175463
    0xa0b16080714010507030506031506040e160f050108010e0619210309050609101b0f030e090711031903020f070c0f0e0603030f030919031119020a0302120316 69
    0x2d41001c3c05015004140e6040500441c18001c00081e05d50b0540390320f281e01f0000032000501c15036216003210301c40c404944141c4800348a140042c2605840c00d0180ba40c40400c0324000045551181803450b040b591060702c02b2005032135407001c0000d206d00f5400303a194240701903080490703403099018540d040265607003405000110546405030241501d0b60003036104007002d2041c0c1c0c079a034882203040c4503508858600800c45c150100110b6041015900c07010740042030850070941055001410502038100865541000c0c2d61b400404a580e5070790520b0050841d0403c0c08038000c80440182e82c000054058103025083c11400d100704031050b0440202515118a85207003001910741d129a0080503180742c0b00c07000101e141c401e010942e64820b0305603400d8420000000030700564014010202d5070701c00d0400b2070b105400c3d1404e004100440240140c00c850082044214862000340f4013015860f80c040e2101010b14a56000c0004400380030312000c1060200b0803440e4040b400c070390703403039401c0b140f040803605c84 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 654177940 1250 654176690 654176723
    0x5040501033e0f07030201050402090f16050f120c03220c0e0a09051b01030f180807030207051f0906030504200103110c1014060a0b160807 61
    0x42c0d400e10301c104116040984908464420180d00d80616a145400d41030360462000c481480b481c424007038521881200410640c0416506402860045000b01c079444001c0d1501407824014807016560a55940c20340f0380036800c910700940103008103a00036483c040c181328982149c4c8602e10412100c0500300d290000400001d5140040014203443d21440d909030070b034506580d414018400c40c043c100e071156014000407252660b503000346800503400740549035000e018103400721240c100036071403902090511000414845c100c1c13041d01504800419605001906511952015400364000b9001c502030048003040740c6e240c40108c01c0b1480c0500c01005030700d00e91181e0080044484d0780054081504240900004c600180081c0903240360041d120600000d40b000160024500f03001c424601080c003140d040020700300840d6440643c4c019810512445c01c82102082306031030304807202980000070302d505208401c454030203480840d030030814808640340151500407041c1c020501c100d0341c50580080186 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 654179190 1250 654177940 654177947
    0x3130e010512150703020715020409020706140603030d090204140705040303020d0206061e03010906330501270f030f05151b13090603060c020d020a0c0501110c1005040501 75
    0x4101d4800708014000100c502401e5101844014213840e08058020800c0ea007440f00c180c0b40300c050b80c076401c0021580ca81e6240d03200000f07504480c40aa49141c03900c40381d05030740f5110003201c0d0322682c0010051454005072200c1c8500410b00300f1410390b0041c0d50f8034001c008141440d00301d035025107229143e003a2074910310b141c020310b041c4080103d4421904402d0030b01c5600d03141c0c020316254012100103500d0015003c2d002007070040a9100020f0102400d04446100c210303040350a0846440308603000c0c24400004d002140c200346100d20030030b40014030b120300341c00d042c1840c808050b0b00011000c00181201ea550034008000c0710b419041aa07121816500903020840200004010030a420845020750b207003030244681401d815502c16203084400040d81c42c1954607000111000d00100e01e801c009407612400d05400800340311180724094800d80e800380b0007079400024212546a8040d03070f86103170641044011100300382c004140c3c107064440c440b1022215a1801c1842180150399680c0c15200d03880e010005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 654180440 1250 654179190 654179209
    0xc0b0105280303020319053f1006030c09080613151a01200a03050a02100e0703030206010f030b160329090127020a020309060a0c0c09060b07120203130e0105 69
    0x34007d02004101104000d4280240407412540c2c01840c1e40c0d06007491107913000c01c15031042ea090070440c2e4100030005c800034120504030071346000765070402c920b00071100196060380503030141d0002540003100003000103900302c108060303491180c8803800000000000070703000d42d0740202100c8401801c1c0001c03c001540c2c031204c0e5490500c61900c60421541e44c040c85c031030f2218194080130301007040000d0541485070007002035461110113000100203186076103c205440f050513000480041c040d4800010f50310440744606401d0380c1d0020103108141d201e04021100d0703c400c10800105060311101c55030101c03221008202e651103007480704240364802c52020040c0c6140140c009105003116842d40015003074203040278034205d0310344580050f85c0c3c580d400c009134614082c1030344065103c400010100072031079004604154082c450b40001c000f058452400074160b4006d0b0040d41d5044809001c0ba9001c140c01000a5800c1012401640c1c0f6112000c058074452810341c3d0014041c1c10400c0c00100045c0c10400d00d01e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 654181690 1250 654180440 654180487
    0x2120a050a06050c1206010309420b0306280c03021b0106121b0b040314011103130818091512030705070e0718170c010c0b01052803030203 61
    0x31a152004440c5e50001540d805417413141019a2420050100104a50100300768041c0003d40b020729085852003140001004183e600a00115508002000e40714040c4c1041320500401510540d41d4600d22990402d14502e0410b80d0f0841c1d0710f490a03a00f0000348102031010096640241e07482d01c80707014603444540c400b80403095582c544581006410081040d14802d658049801e10812460ae02c030b0b503038211000d42150f5210a0000b4000041024102c0d0124294046030000e008001c420b05003181706010403141156032042c10049400040c0758440103080c002c40c0482e280310250182004210001c904a6841115000c13090f40e4140380d29182e48a8524400207500551902e22190313186034aa03942441040c401102e840b020400a600554501e49a800c01c20b84c0b000500380e0b01d00500800713901410b10301d10107010300400d00c0b0942d4421410920203d42100e91050381780d10788403d20005892010310440a0154000103820381c2c603070b0300700c420700460003a802192110b0717511100707030580c000310400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 654182940 1250 654181690 654181711
    0x90914070f03091704061806030e1509100504120905040209062b05070c021c0201080c03191401031b030f1709040e011a0607030e0d02120a050a0605 65
    0x1040051644010071007600e80d1146004908240389103008004040900200c411000c0081400300d61541d021942c009034100d001c5000c10401ea0b1050700f80c088440b001c4c2142c05503042881600b010311848100143c0050740340c0100d81c0020603c01050084a50648080b80c2c10003000365500001f035070144003000a02400c407002c45c94a203038000025118891816440d04603080b070240304100c1022030300c190380e40800300310041c001032800320300c0100303521420b5000324402c1030400c10701c401680c115035245500f194180c48469041d2189002d1101c1c0ba00024500c410180074002e00489514050042454944135000805074650451400d00791a032a0040100164441c404013000402d003074090700c00580c1d800148081c4116800070707256a062051004164201d400c102c0c0744482002c055020a0590101e2054036800c9100c80c0304010701ca01c590784015002032042e00e5000315901e40800e900400307a01c01411041070030040891182062500c4805070341c9900310010b950280221406043d900840d05203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 654184190 1250 654182940 654182981
    0x804140f0a020d030306051503060420091917280515040807060218091609050111030904050117010b03010912030506010c021507060b03030702150a0315060909 70
    0x225031a619030200c180030f485030120940000901d4001d5009102900c0301900c0e01020f404401d01d5802c46902c1560303003074001c0f850880c40406920844400c440492850200d0601d841c0c00e050030408400000c0032800c00d4015000070005507030031400c00409080c12746002506d4200e0200c4c15951002c50031a8100e83e0021700d0000ca4000140080703221012580f4913a07a210441e00c1720304000300a409401001010180300003004040c51100c02114060340c08201c440d26034940d500c40d566801402086130800114102c89001c0c412036000b00d40003a0004a02c000f100e0501d2051340000d826990280c2c40942941120b0003d0030b00d40f41c00b80201102d80d90154024404c00c1d2940d510f8100707d50902d801542010f81e90804a0b40b82da214220003a141d0382c00802d801c0907212180a1140d540e400004e0883d5824940280e07a0450b080c0031040d29851a001002d04445011149507103013940d00c0000701c4c1c010180d5565242c8040c80112072030b400940f08964031880040d0800d1104401c035100c0d02d503c9901e4030400f4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 654185440 1250 654184190 654184213
    0x106080601030b0c031008010c030204140301060e060d0f0b0c04060818060103030e01050c07080615093d03050a0b0718260111031b040b030105010507150903080414 72
    0xc074915500202d108841301e607240d64604141d6501c1e441c54200c04095420001e00714111a4150041c0c000d40e20154000d00704000a60105800c0321064400c90301e5000751030700040e0440c50300c03900e1110500e00885c0701e03401001d1140d9038401a40c000b11044520244040b03030a00c00645d12121a65004042c1c041080114807100300041d521801488003d003040040000c0340066407081040c5c8521161340c0085034802074030b522405482d400c0490711206800c03c1071803012801c1c03400051450140b1072002c51900c400003100e140210ba041c00103940c0001e001c82e90f80c283d44a80c5550081e400450044c07001d40003034041c614003114070703803805803d000c104412410828103603001c003002901100c4c0c0e0a80d00003640d9040d440c20b40800c0c403003142050501d519014100c200300340d4440c000d5100ea60000d01401003510007004003181400f8500030410740301c5043c8010f00555002d080200b280e140a54141801244070b003002d030003a22031000e02100080c0303194080c4800c1214904070b540d807115001c8080c00200c00c09 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 654186690 1250 654185440 654185453
    0x803090f0a050c100306031b0e090d050d02070507030c030f020102010f0506010f0305250305180f03220f081005100524070501020406020304030309120305090d210c05010608060103 79
    0xf030421a8880c00195441c0140c0074060f51240000f1903029000030045082d0300001520b5142901c6602102000d0f23500080e1705150201d01c3d04c0019616895560400c1d6221000d44000d412542d021225840b42c0d80000c07001c14601982003008520415503a5601d11030b520009003540c50f8241c02c031024601b0401030040aa03004010519890010320f00014580d54031400072032403004048175012692440d080380c90072681c1c5904011320800c400b00d0045036010103500c000d503132400c1000a81c0140d401c04d00020705c0741487e2170821802c0b01181d1543c0031a0945400c3e000290b05290340c444480e0f070b07001c505000480031250080981c0442041e60511405140ca008581d800402502c4070000803248070384034020140260980301c1d5690004001c5484503200d12000c0e5803648607000a50214222010008440c4444200351502c0f035855520542000f001da820300080c021b4552003103440300c080d9202c41610b520903896206200e26035a0394103070000c205044c094211070b502c0d0050300c0c15400520060003c03c45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 654187940 1250 654186690 654186703
    0xe07060f08060d12020109080c0d02061f0b0f0d1104080c01030501051f0c08040e0609010e1909140604060b240a050a090f120308070206190b06070506040803090f0a05 73
    0x8010500042c100031690b8200e00402c9010001030881f4000700700300c0302021000401d85803141103902129a1510341c2c08400c0ba800c2e048240000360b402500c37609114282070a00a03101e01480f80c2c04c1c440c1808480e020480544180c0031100303075540c002260400c00003104105500310f0300b5080c00d00304070399418400841c000070480350542031003110070341013811040d2040c10400e40040c0c110174807075219611080f09501c90b507000c2d40c01b40d10403a2002c00100b00380040c0034842d4016445125415541400310301c14901500021000340d0301585071001c640c03528107040c8a590310842c4a8000001c84090b00b01c10824010b55501c154803101d0b00c0c0c0d108c0440340c00c1401088400d5002503081843d12085a0b40c0200c0745840d140d040f100014030300b50000221031186a484074000741c420b4641c1320380c0341d071141001c03640c07540c040341d011200c9180951400101400d5a011040000b0003901852030400940c54052409000780e4003103a10040000c00c02c62002420700076100c00045c004041e28406a02d40c1b1a0307540caa2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 654189190 1250 654187940 654187943
    0x31201120f020907200303060102150c0403031d030109060506030f0a030c06051005120606012c0f04240f1703031b1201170c01080903070615090e07060f08060d 70
    0x1003c1d002183d030150141c08010b85568a100f0101030034503034010b0885d169041a81c0c514098400e41e040744014032081200540300c0c0f05c8030000f55040914544089a000e1921513101c06200a0400741080c252000e02511250350300500c4007041310b0500c0c0b000e1500c4d000c0310340301040c4980c00c990745000000b0f070321040001c15107820040205050700d84203461034040c255988110f50040d564030070040e0000d0046880703031013040262111003c5002c80c000c007110010000700c001c0024000803404076030300c0c44c203104c014194603000b41001030041c803038100c0305080054003c800a9440d0504004214080020303815401802490004240c03961181402c1e5075070b0f02020b400c0000c0801c1410442c42c62000400a8801034490001d00742404d5a448011114041088400e52042d00802014885c2540600081402200304400952824040b62980001050740703500c0c03101c0810020b0000511800b0328010f280e40801d14801070540c0ca45040c0d40075040761000c1920206200c0c03e0010040140e8030072406c9403045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 654190440 1250 654189190 654189199
    0xa02070c080d1d0a0815160c0804031e060f1a0a06080106081b0a030b040b0904050606100201090506011d0a0c090303050a05130306060801060b030f0c09010c050f031201120f02 77
    0x4086200c00511031034456048865144142d11800403441707114102c187c090100c0394001e40c81901d120a0843d411805150094101c1608102c200000f40801c1083c03408003039018181c400c2a07000340c1d640301c15a2500007810701e0b0291074848101440b081c0c1c2041e006201c00c1210b2b00f62003d450103030080d281020520601c2c0500500c20300283c85130725100c07521024440300030060760382d64a0040d0040c004003900c8101074040c07032514001070300350306080d01024015900a0300602da141d5480c0308100440310504450011552100bc8007400100100140b9010708458007000342200303042d210801082600406150a00782080302a005580d00440070300f041e603416182607a521100c21000307450600c510b0411340d00c01c06c02c0c010b001040c0f010740d03403007201581e00c0c9600a000c0969038510689281c001922030040c0e4811603000724228940d00700040c000101c040c10200011034550b1100ca00740080419400c0094100140c584101000c8070741881c05070406034a10103c1d88038a0b1a00e510714070001500900a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 654191690 1250 654190440 654190487
    0x50f130b0d06020c07150509031510030602040306050901050603030703080c0306150d15091e0f150803070302060604050f07030c090b0c0c0415051e04140a02070c080d 73
    0x241e07261510101d4629402c00310565543c060498aa07658144500c07460b044140d040300300c4002603120324121074914000400820b07508182c5c005280e81401d010b80b881d01c843d000f8600000005405001600041d40203410000b000e1410300d080c03600f07480303000b40341c54402d410401103800029080314a26801c505082c0c0d030940c403681c4440c08030722455007441010424100105040352002d0003500504540105205221480c5640c4c0480009580b0418101c200024501c3c0b24000c2004490b0b004034400f241c17a01c00821104d0454985c1c0703000e0f40e81d54022001c0c5800c0091301006041d010880142c00c00000d40d410401850003c4100e11664070103013401c400c2548902c8080d0003030b03204400c000050100311504907645d00c2d68041540d5504d034100606401281416205a036a10ac040e00c4a022510041c14015480358001103500901803d003000c07650155940300e142ca00b0f82c0130031000d079100c1c1914400050742c425160030f00e001c194008d0307030000041d5030181c203003e03080e664465040d096074041126403514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 654192940 1250 654191690 654191711
    0x6110313030e18010806150306100e060d0206040303120e1b0f0f0916031a0a0b0c01060b030c180301110a18080a0c1d070e090604180b10050f13 63
    0x8412a9420307000000400c018008520f162006c00c00074040e8a80e081d450789501e680384180360311000201e425440c006a10341041001c2814820599070140000f44609200b171420342c0000c41c0c0f5006504107400007101540d011074144860310400e00340040c607100418041e01031034101ea1018070341d00d032450700904a00f4401c41c05074440c0384084400190007000741c0c01910701030a0303d4460784452604d03c00040c1c1810792124144240703000003118510301070801d8682d2410308290004550014000c1c1000390369880000484406900245000e503444580440e541c00a0849024044d209800c48620903454190f0494802d0211812a8049201b60802048910b040300b603020200c482c036849008140160389080c0c0400c40003e403070005440020800c8078414400080c0130b209030804a890348085508080401d4840c0307440c004407684a0380081c408616034907807885c0716200c00c04141c8121901c1100d201440f8020440d0402000174000039591020044030303400000e6211040d041071400816030310700e010745 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 654194190 1250 654192940 654192949
    0xd050f0601080919021e130e0c0f0307030209101a1305040e06060f030a080304060c18150507080f160308060301021e07170307050403121b060e03041a040306110313030e 74
    0x1181c09000410640407d0480701c0d40710302814108071040054041c000903004980750403104c1b040102c04c00340080c5034440c04d5600b4482d18020280c200403d00d45050030005030b1340701c6c20080c0c0c1140316031200d4007600c0d2400000350380c00122541d00003034070980c01c0049101074600c00144155000408a07816808501c0d101d01103030408400703034000f402c0c5401c001b08210a100c02900034880d114403035582c6401c4401451320514000c4154000c461040d66464924805148a00007030040700e80a40342492400144280c08003450344205105540c01d400420207505040c0c0103e0219884041640250f1131b00d002c8030592410f0075103001c00c41d0018400440c85030180314031901c48801180b0300c0c06202d996403c20f108007a00980140c4822514001381f200c081e4121131190034a038003404040e51881c258010f4565079040600000c1181031124803080c000046c0307505141e200ba02c0e40700200b0580c6661142141409010341d0020100b0f0000040c007001401400103d03200907901079600341c900740007451b02281c0041d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 654195440 1250 654194190 654194239
    0xc010c060f0c0306030b0c030702121809160809010b010203040308130b0703050d05011208120a110a0c15020703050901081506130503010e1b1002030d050f060108091902 74
    0x5500082c500a102000607800d648103c098038014010350145980707007490500d5900c02243d0070f000581003101130b00901507007640a0010202d95804164100642c80086440000d003190f80000d40d8413503500c090852508a400c403a0042081030084c003e03c0c4103080040c3d5284200d100041060400003843c800225042501c08083c1602c80700045c0d5440050800424540203207030002545460000001030401c0058005500710340e000183c2424044400d0100d03800480041c0b154006903160b2220744189250200240344100c12a16110030b2403201c2c1c2480c240016603d801010b44078810840c83c00405c2c1c000b403c0e610504801d00c0d1181c0580d88008a0709a0300c800d81410745d800040c04a403074100424400006401d444e000e40082008040313000c00e5641d5000700224400d120700001c0d441c6442d50404274071060300c0c004240112460038610301c030740c40c00715182150203520003a4a601401110b42e07118a426410400d10f1005000d91269100611310303000e00ca03030009204006c1209001082608400f42 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 654196690 1250 654195440 654195461
    0x801270e03030f061002030c0a060207080d091421030105120f0d053105060a09031502090306280b2803050c150405090703020f0406030c120c020c010c06 67
    0x2526103d05100f980c8980c3c2d0041a15264854102117100301402880001a562071100860080c15030300e2142c4c41c0c44001b580100001c5c0c500d240308201009020f2078034010071000c01d11616100203240c050b5460300d4104204110380301042d1b400b00e2605d5040d44501c40549054070b80403078000034100600381c006481c00051300b0000d001409a08800003601387c01a029140903000c001c07020f1315911900440300c1048005031807008001c0800b22041c440f5040210151a203120709083c038001c095241d4680d0008169500c2e0115010303900080d00001e541014803100d500544040c8141540c2002c0c541500007d0b46080d01c40c2280c40d07600d07a03040350940c1d6540c40d100b8805029a004102040d910112400701c0720243c0000e0b200c07489229420110303810180d43c507034481594414464100360800e803c11130084000792002c4101a020b0000c55942407520f0010710041459440014001664810240800c8140c1845031283c0346030048c1d014407140c000c101412402024078104111625901e810001009c1da40700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 654197940 1250 654196690 654196693
    0xe0a0813080a0804050916021e031e040f0902040602100f1107060c0e1f030f060b0c030415170a0504053405030d0507080f040e10150801270e 62
    0xd41c2814440a40000c10030b840046e110384400e9501c8071500c44c02d0b0113040001d4030051380b264541c0e00d16401e100b00d000c0841a05c1c20196031034901c0b0b403058900c07a18a144000940300400080400224412a508038011301c04103600350708052030400c010b92038004001c131800009854200c06584000075510036104014008101c54440d61030741881c00090041c0240b04011607880d0000050a140c104850804148101701c40b21117a00c0000c000c4018002c44817030f004c091034541c24042032080c0014003510402d1082401035071100e20700340d8002141d0034003451103418840941401b8889243d603000c22540b001e11030350b0124198565151461511002d6042d68054901524141450140800707031601c3c028200c0308400110350301d880801d03480746884c498140c089a820818140015403001c0030b011a5503801840c0c5042c19a20b19a43c40500e104840341c1e01e1010640d0001d104501e9822800b0442803400c1c54503401941c18401c0c2103d104400c220301c10f500e0000070032030600210182c0c12140e0503003803440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 654199190 1250 654197940 654197953
    0xf01050f04020f0f031f0e010656190810080606102102070501020702040c032d0e1009021212090d11030d08190e0a081308 54
    0x42030621694015101244215195624003c0524000904d07a0103904010060001000080300188802207520404c1c00c245441d100b07401a0f0080c00c0c410b2350005d0440124408007120600806803c44a080c000c1031214440c0c1c000d0480c21040032040d20010750b90007000d5142d41c82e2814801c55580c01401020900c10080410305a2120761109000d40244422005c40d140b003034440907816181c038000c0712400e402c041903e8560780c285105201e0001020303100d090004080030340003d55400ea9002c08415141c40c0c1d000181135045051500c14a035a1004500c1c00308642202808000007211105484048640f09410360012401d0164811030b0142030200880320742a001941c44405400240026442555003071090601654003240c10b000c010040b085652501c2510410448003041d0107a082d00c0c08080004150816102040000c0f03901100b0348400e600303032400741e0340c90b08201c0401030385c01d038514205440307a04810320018002c200d065004100f00c0c0c40c0d0b010a20095040440c86d84800040c1c031400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 654200440 1250 654199190 654199201
    0x906070311010e0a0f0b070e0315040c0b09030a02010309033b04090b07080702030d1d01050106230306060c0115061403010f0506030a09060c0e030c030c0109030b090f0105 75
    0x3209031010110000000d2000200003102a44c840c0d01d0000c01420190320b03c04982c0000b880ca00401d5404401d40c10303d01c6c42c0c4070720078001c6890546046107030399100d40d11909200a10260712042c2c00140450040c0916140c82100842d40307070b0700240c00003410300d91900c200300d04141c0509103a40740005642000d503840f950b4a51150300c446480c5a03090000a4201d9040c3d007a030810740601d100fa80d0300a588080c85454030401240c1e14600241050110b0106102c0c411503100305018440b945481e42c001840d500c1d0001c07a8050171901d047c5c2c841014040b680e00003201454460340742503681d01c40d882c442510382c0d85001c0840c1c21885121440359241d442c03c81c1109a5a01065004041e5029076a0301c4800302d80080ea000100c1c0f00c06e0081108001e4501d0301000940f61500040d039000c0e0981e003010070564010f945000c00c0d5542840190040b8201501c0b400f0542010410700164034011002007054074014400a481d90116000240c0440c07041000102e44200c10004040c40300c001d1002084a850320 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 654201690 1250 654200440 654200447
    0x30e0f01110403031107050f0907020a05150412170c0a120c0201140a05090a0f0807021207060e0901030b010b0c031209012a0f0f09080f070e09030c0304061409060703 73
    0x20f010803808a8445a03403003051140c0060000180c4101811048042c411401044001c000080804046100e4180000c0001c0e0050094688000030358108170114141480d14000c5804910081c1003082240c4800c521041a404041500251090012540c03a5140364048604680c840039003070009060000310450240d05520492070360307a101002c0070440d1940701401c010390b1310948451426038803c60141000c5083c680346215400d00c158030491074003400e680400c0c010590185800c4454200103010401150030080c8a402d54104071151040c543c1144c0c0c42464100707040c0a20b29181401141a00d41c003d010021a001d044014400c0c0c011031a00300b240901070820f03402c19071030960443d4455488a054200080c0207140320fa00c40c00c48029890300100d403142e031507001e480e08000070b0310000031315070b081440792070094000d020140c60745a003003801510b480400508000950b60040103c1515028040103231002d4881514007203540c0980e542c0208018000d4074011a8060400180c0e141003540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 654202940 1250 654201690 654201697
    0x120c1602060c120c07090c110a0602031e0a05010f060e0603010e0627100b07021c0219030b061c1e05010912050316020106120822270b0a06030e0f0111 66
    0xa50314140300c0c800a21104a50981d148c3e01408926840801e0440003d500c1d03030041c550003181ea161807d0010140f60010700b1101054036100e80042e65080140800000200c420002d452070b170402001d043d0103500400e00c248014803401d00a0031150303011905554641545800545035a42240845648240d54031942c48080d00c004102148181000600703c20350003d0708c4060f50010802880d518004900d600e4600d90210201e81c00002d03004410303090318890501d10043c50240501c032000e80361080c00c0c4050b98040d0004060f0f9a04140c1c50100050b50040144542010051080b110f1050928200d409400204401400e444400461041e00f07a402005144210324072113142c14007280d0550b0582c01c0345d030381d4060101690500b1403c000800c180800820603080760304980340b0b001c04020082460200baa1304224186a04009445500280b05480b80c6c41c115409608020104008000505030400b903c100c0c028107441d034200201d060b1b01441500c0c81e5242c0b0b2402809696040c91000000f40d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 654204190 1250 654202940 654202949
    0x1208010609060f14090d02030d0504050306010e04020a0308070501180b0702060708010e1501050d021305011106221e0803010821041406040305010908120c1602060c120c07 75
    0x9455480019400c0c0c881c2405104400d101d07192130700481d040308000740290b4010300029401c2a4000d1004005031000c200c6181080030b2503940d540c4890410080600f8904c0603071103c1061b143c80d509010141e0740c0e02e81d18104690340324a40c25985c081a2614a01402c6080a50300190408108080c140081c0c03082147c4900982c1d402e541c0d05640304403007603136803075403c1c0030b4140429032800c00900d611f00c0030110035000c954141401418150b09056680603a4401507003018241160a07040101d075811800411b600000103020b84000e1500c02811038500690380b4000f0156090b0110f5141406206614085ea51031401da2101c858500d508002103141d10a10031f200c2c03544900210055148402e01c183c00048500c0022b4a24040c6420340c07140d007a14100d0038080c1c0c80f0b2030030400040050000d112317540c4c486c0e04ca2400c141e1603001d902c020003440d501c02003c0b00300154040003400140d15038416030788201c3d5030407203003142c440400c02b82c8c2518180e0b140800107085080002d411040c410009412030844 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 654205440 1250 654204190 654204197
    0x90603030905062109031b0705030d0903030c1b33030e0a1b08030307030501091401051012020405030a14061e0115032c01061a0f1612080106 62
    0x7954602c140100ba1003850f55110740f19504281d802c3c4c0c12405090310304e41048440044905082c0900000c01d110f6004413540741c503a62054400704941c0c1801c0c02a014480c405040000340359107503440143ca40e4180d05402407a243d009880f6442110301106c0302c00181500880e08410b001c0740020307607005c910a104600900400e00b00042d65000c1c0309014000002202c000584000e580964032a1111040c0381500950134200380b07804070300c4c1b0000304055881078015507000701740c5514106070300c0c2c1250764403201070035000240c40051000d61150091108078243d90328188040320412502c0038000d010f59086a07034103000702100c810a0051440e645000101c0001c1500d0312034650070b440400780131903810541c1c420348614004000c10219041000340c5580642000b04a200700b18040f01074031800c01050742e090303500c0390380c40c0070302058244034642c0500800082580b104203511403902c92402041b070401c0361580c0c00544d015540c81040c0c0803498240d48030188442c0c9401c001c9010703040c0c00c405d01600002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 654206690 1250 654205440 654205457
    0xc061113080f1b030c061804050f0f070302040b030c0c0709050a1401050301091703040807050a30051606060905011d1608060108150a0902030a1104030215130e0109060303 75
    0x300c03402d0f042144030241004000303182c0d4580f01c1d07050142c1500080e030340f003200084219201403991140c0c001d462191108940851007840c0200c4080500f910141c022810148103110034880550500202c03038026505150060300c9036000d0080340d2a0a1058010880c40f90502046c03120f2850325421410783c0710040303007010241c0d80e2680145801ca800c80c5c03034003515110503060344604003040c2000450700300d40100f01c8646411860b4a0340351400380304180486650000c0c60361819004040c050b0001d1000c408058910b5910302004002c1c414001c00e84001d1041120b07103001010042c040d8460401401d610030280615a5114100a0380c6850b08445202c080400400242d00e01820030030344104a040d5160203001e42c0f81c032070044031806070040104810f800d40b69040400e50713443c54102001007000c040e004d0381d46c0c41c004286c44142ca00340e40c0155404942030109000596610048030f254a0303030b0641842d1107001c0c4007001c452221643c1e012402c040e02c2940003148580441c2c1204047d0b9020b034540626 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 654207940 1250 654206690 654206713
    0x20f040f0b0a0941040f0b060d022107030c0e0702010b011e050d0b031c02012714031303060204080c180a0e030c0d08060f030d0c061113080f 62
    0x35201c00c480c24001c81103000c001034100c905904c0611020070010004c02c0044c8580148481a19000b5207040e40c140360b50100820400c80c4503024142d100c0b1040d50340c24480c000c103038042044000c880515604c25040c0208031841d0040401524004503005502e04898595800040d191101d0548240d0015420111003290b00c1d4000c11442103c01005072114802c2d468a2108459582149001012031511094170810540d010082c8500103889441500f0000c0b41240c400b03803c540c8400d0010420b000241030603031100c209070300d569a42e590040841446001c400c52000c0c154440c0f4a141c1004101000000c014018560b01402c2501d41007802c41e00b101a4007810005031030f00880e40c01c4c841101000c0081d0145640350001c2c01c1e20301004007107070f0900700e040414030300300540c800d25000021060400c0001a00c1e00a00400010800f41d01901106003181c0c4020114030a2440c0a010b054507004500b08803c905022540f02c040300e085140c1c07182c0d0722542c1150715180d01c2c0804004500c00c450301c412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 654209190 1250 654207940 654207959
    0x10513210e031516300213080c1f020712060605040c0206040c08010203160315090204180f0c022a03030d090b3301021908030117030c0c0d020f040f0b0a 67
    0x81005c40181003103140c415100c01000d890200c003c030ba404035400f44034208503641021506406000e405000d00a07100811050010702000f640d40b1400011000c400d0008854001c9a1b0304140e43c00301040d0100300105080440160203181c2c00700360080d00d0000c41802003940171030054012440340c03c0147c030300e91303507118200d00f84e00080c1c07171000f12040c9403088901803500030b83c041160781d01003d0581001a80d64401d6000300c1c0c202e5401500d42e07002d20f0f080d1646103800c0788a041c40c050703c0240b041010118841009584181421741084900700d280840301c0c2c1c0030441c0c0303010150500c005003103a90b504000000800a01b01980c4111000000310740400c2056020f20b0301601c1c0c1d0581414440b001d02c2c49521103d0090844142c864154059888282007000c42c0c1c000b5003c2c401c1c00340658541d00d500d0304d00704840e64048010500304541007407050048281002c2400701c400102115446404c0300d0600001d1690500803201d10307801444c3c030300100ca5548a0f600b10f4111000200c40744415641d5945000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 654210440 1250 654209190 654209207
    0x309050604030507030b240609130c0509041514010509060d05090307030f0f0c15110708040e0106141206011b0b01091508030d020a0c0f05010e010513210e031516 71
    0x15104406102d08071f030310608100e00a01003040f4014007001c000010461220229164240000c00042c000940507613541440d01035400d440d0290584201d0041c9029420704400100080090400000060788001a903801007038489904034103100f08502e08020300c040d6170341d50003504100c004c146480c41483e1541d0040c210000504169160450b1019055481c121108508100000c0c0290340d046401c52004085019001c8144114031041d0f039a8181717111000c1d849016440311081007440304032034031180924400d890404001c0400000c135a25000e0068901d4850001d1610b842c910302252601403000d00c41d0080d040702e1035844108002030710800303100c80d5020607018104150340200904405070317100d6030003480142114500401000207a44c0d4102104104040036181691a0304115009801c01e1081030340244002280034a00360b151341d244800706683c0c18006201750a04e020155034540140d1000e02885401001c0c0c0b0391081007000d004170102010344800250040321340d00b0003821800369900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 654211690 1250 654210440 654210481
    0x606120402040b0102100e07051f1407020f10030902150c120309070b0a081e01120807020f060c010c03060b090a030f15050f071115070c0309050604030507030b 70
    0x1854080d603590302484090300d940707510343e1304510488001c000c852401d84243c500458000003e805000d00d4642000450390000c00b40f644902d0a1900b601401a041103101e40c0090914840300c0d03c9250702d0000070120b000d00e84e1030a030020202c00f4a402e846500d0307480008074500c2160658400c03080c0300d201d144540948081c00605134006003000800c040d2000196601600d10400c5640302505c0324050121904582407890110301c241040c02403c103940350005203101203481c2c40d44075940c5001d041c01b140b03418003c2b003d0884440065540203544410248640c0800d002e40700a03074400ca21007049009040b00c50502c0c000a10300200070030343d400000101c52a081c001000c032811581181c8920440c48490b6508888040310030340010031341301c81401024425142d04030700000d40c2ca001d1002400381c41050740284074507009880d0041840c181c540f051a04000310740f81c60080c00e802c52034141c8011240b9041780780c0c420b9003c02c0000401c60005294403e480c453302d1514a1a26851114400038400c20350 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 654212940 1250 654211690 654211717
    0x1020d090f0506091207080f10090203031c150f21020604090c1e02030a030606020a0f060c020c0a0b0a0905060f09040207230d14120f2a09090606 64
    0x14100700714680782e006481990001031002000c061795000f00c502d46102d5502c411103603080407000c0b500c103640511108001e101500801c0c03084020aa0020361280709a640c989008400c0c507681c000761200542c8105c02126180c401601140d458040d0075211400500c5440d207002d050103540c4580390074800d5003490302036002e064a403c05050904c007501130902e0b014940204030300b10141130204a03640303001c4140f02d512038000c0c40d0340d480e40f0132005083d10702c6a0030060035540450000c40c00910002c44283c3d910703030010700000302c000441102700d0500c44441c0c0c4140d0700007101280030a85086140060030044d9941d1143c041d02c5654100340f04080c0602c41806000744428040d15104c0d041a0300200445032181070703024070651a64410542d0882640ca181c5403d90015400c0d5800f140c101140d0150002800c0301070b41030a0a11a421102c00402401c0701c891039401d40219611a82c05600140015240b42c100b403441c04900c0205030060b00144485442401030a0114400e42849021074aa908440c103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 654214190 1250 654212940 654212969
    0x190c1a0304020609030c030304060302091302040311040b211c0206060109120501090204061d01050114090415121a06040b0a210506010801141e040f030207090c080601020d09 76
    0xc0030843d041d0062124590140100c0750881c5090350b0074001000944104d88005032200122004e2003500c03069007503000101841044248041004042c503890340020803600802c4c199403140c00315608150104219500e160444990b01044401040c010b030741014191401440303484000f4200d9603200c007a10388c1404a0005031b01444403c0f5010012040c440c060400410101c1060740803408540fa91b600c1982c11551204e811518400c290015a0040c8002d2a0415000c0c00d0549010818468003034003074441c0e642c5200f1a01020b4541c2e03c41001040203080a010000d06400c002e0252840c40c241010691000c000242451419200d968a041d02c0500383c182598245500c3d41c0c140c03c068007900b0b118112100740600021070410000380a0107440001103100d080350706000000c0403024110402280f906142c250003d00b40700c0c4096406a00648400f14a034158207080c1e0034aa0b5540100e1121070424510b0b00582d0340280016019103020f0382181c020500e10001102c7d044114020a0609081070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 654215440 1250 654214190 654214193
    0x506010c02091008030f180301050c030114010c0605100501020601170709020a02011d010b1e0d0303020901111501050a080d020709050a0e0604110f030714090414190c1a0304 76
    0x10940d590f1001c5100c10801042d42c8407131a00b031854220340345046056000051403001600c0d80e020341e0703002c400140c00a10160030007070741203085804140074140500134418000c00d410381c4a21882580c480e08082c04008604090041c1070196005014aa0262262500010f5812400d841d0400c9203840e5001800c01c0074181846034002c0d500110504086640300e04600d5200c0d180c0c2d590202480c9403109c0005016904c05041c0042840c4a603403540701882510800812511a0000f8101c07082c0d043c0340041eaa402c0c6000140c40381c00703041915100e00c1c403c2c0f000681410012030b80440c140c95086542c07c03601c581c0c95061035620400d4850440c01a0051071041000d032800e81c03c140c1c1c01c0384c095280881d03440c000344255890030900704c8060750705000310320050b940da0405800d4005403020a4000e032030620308100581c0c800c2225003101600944500c0001030a002c00614208082d4551205490300c1c04910f030311865100c3c45284083d20b03900d819020004208040d803440c80c2108514401da5411a03969 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 654216690 1250 654215440 654215449
    0x302091602031c060e0f07081305030708090307030b0408030a05060607030c0b07050405060a0509040c0e09010b1602060f0a0f050c0d05030a1d06180703083702100f0506010c02 77
    0x40b0528100a611148040740d1401702c040c030a407140032507200822044c41c052500410251001c0d00c0083c84000d44c0018001080307001c401c54070300700e8202600594a810000210b4a84070241d44084d250000410a00042052020086000b90b000364002d00080c0c40d660108003140c0326484000700400c0d10f1040d4400001e110f52041980304002e03007449400c060740c8101040482c0d002000c0340f000903800245a04003480d0510030703070034004030525003240d90200101c0480c0303a24030103000700d5126085c04070310304040340300300b04082c0d1450394068511a142c0c94409010607842d04001003039000b04006040c1c44024520410594009420b500000d012000c5919010341e210360018100e400300689554000c2000fa00d0740d20484c2031804030300c0042000e0310b080303400c20504400b054038941658000880410102d03c216082d200715484000c1401a410510194204011960311108100e20b035060000003501c0d801194106148090200030320480c10003641c850220b46045030002d02080818180c2c2c00582071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 654217940 1250 654216690 654216727
    0xe040f120f0804061a031f1a240d02040e011d09060105041d0601120b1b090405090102190e0a0504140a02090d0b010b30070509040b1306030209160203 66
    0x145c0c000c40d100d00d06100c0100b41845200380c0c43d40c010840300c5440300360b80740540c41001c0c6400414030060816610f004002001d1588070700210f01d0388420152400704000310001220801010110115500d80c0d84241c201d10401007441014060848a1280044030220350b060750306c1000c44034090026a03007440c04110080c00504c1c502c2c0c4034000211420b0001482c2000194060040d000c11144010898502040200b40c020000315880c5261000b5003e099a41c0e425070b10602c0c011600440c89580700c00d02e29009000c0c8540d40d007803640240760001c0c0816040b14200324044003d42d895010541c54400707000c00c0d00e1404038404d00501c3c030700d40011300d104816800303003405d01c00040809150b041161104c47c0543c0081c0c02201034120f0008010b00680515160907060a8846000710002110390350003c88102c4001e100e403080c8600042c51581550703441e406480c075040700900c0d080c4000d031340165800007014940401c0b4010090003010403c003490322601c20010258035030003585451208185e0104186 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 654219190 1250 654217940 654217961
    0x102031003140a02041d0118112214090c030f060f0709050a03141e0d0809031b0a020f0321070c12110910150305040c0e040f120f080406 60
    0x2030711001801641e40c1d0007134081701441120614480403102d48410700f1250a2800010348145250982c0c000401c05a01480019000c8401da2b40091001d4407a01d90340380d003028a50042490310800d06103903002c4540541c0134000c0e100c02c4500602d40b0200380b42d81c540c0c82c2498040d080d801400003800015076035080a03480072080c03910101442c1d603800403e201551a0300200c0300940c0303e601c14181e103502041001040004000c2500c02d0340078031680c1075100c9842c80f50440400c0300f4200080d41c0c80c14100102c505d00c856808040d100c50444400542d107030303121352400300d1007410031040e801c09502c0c00141c071a0011078500300c6640040d154060407401640031000495180d1407203207001881404d02c03007a0490b024040c01c0c610044800003020854007140003000c5001214a01905200c02e940c2000030750032100e110b050000c2c40b910783c0d040c000550340d000d03407184121350003500c02c1000b040800c07800f03110f407184140030511585164034400c2d60180000610701002501c1580040d02050700c031341000781c64a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 654220440 1250 654219190 654219193
    0xa02010e0f0f1518030a0815060f031602010b0603150a0902040e01180b03060c07020f090405100c05070501051614090105190e0a030804080c060918041e06140702010203100314 77
    0x50700d4403000a06580041d01000301089141f001c11408114030a0014034601e000c03135855162a45058414107540005403c02c4d091a196001c0d18003ca4001d50041c400500002c180c60303120702d01040111000d41c3d001c401a4080d5030211000901c0007a14006d6605464003081c00000b66820107001800307030001080115942358580a11420a032014441140220101d1003000c0e17440c84039006100d000c0c10014006809444040204070101e60003050081014004140101e100e070813000040342c2ca03000700303000034105528000c1880707034030405032003076030901c5c2c0301c0b6266500090810303020440980030b40031076035000c0361040141000304a0182c43e00031402d24181405a400d00a2001080c01d020782900300715401035002034180002c0c03a040200b8824494210f50b00b0b480c0c20b0300c210202e10003541c25038a071104042070b007000c2170820410410040e142c800c03c0c500c24038917454600b4948c001c0d102241000c080c0c00d6058022500151060080f640f09441d111500c52550749141d03a420609851041030300a01e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 654221690 1250 654220440 654220471
    0x31905100905070905010b34200f0a031101051621021e0a02060f1608190807050307080c0d09050106050f030102130b0d0f020a02010e0f0f15 62
    0x501031074410841c41c0780c0120300500c4928240400101111010303040503985680c10300090b0a210742c80b14810040c598003642e030040801007448136031800c00400d4402841c01e95444e100b4410340706801c43c2070641d20411180b06410b55010000d00c08041c00d01d0001400c110700380d045d0740b0b0a550261006100090074003420400030035440d20b4801540d006107076030401c0e580b06141112a03644d4104041c4c2d404511650040712035200d1501003a03992882c4441c02800741402081181d46a910b60b400d98000050ba070103440307108140c9290000703440e889904900f000144402c0100000c920035030400d07200d4411510b4052440e280c4800a40e00c1400003003005e04031160410407013521a000d4024404036030321400020402da07052008022001c00035461040c040e82c41485806c4d000161680403604543d0301c210459a2549407003c020060820340000c1307c0c4050001511150f030b04da055000c02d00c500c0341101907680d50740900d1f83d41900c40207111803a801c07940c0200000c1d864092481001e9030000c0311232000241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 654222940 1250 654221690 654221713
    0xc03240609120606010e15041e0e10061407080306040e0a0203011506080a200a020102071e0213480207032607082101150905030a02031905 61
    0x1000c02c2855040d215004903060200550f0848440c0500940843e145510350300081d00c0c072580c1e4003c1344200040040c0c8903034141b01e80e1100c402c00350007030140b002d9400b1103460040c80c0280580000d20030345000820080310840004145d030300b030b0703590194416440c41c0307191903503810440941000010079a450141890b00801a0340034440c40c20f40c0481d50790b0742c181d11407800070040c024100040a400c12241464000800310700c0b030104026180354003006254a549558104030b00a00407020b0042210510080304003850001000040d0158421604c480044410402c007000303075110280708100100752100c540210303031007109120f03400c66000744443d80341c44400c140d8184080070801036600035800940c814010b1005000040d6007800f944e1400405000e603c200c0e00240f0b00c03800300b01402d000e402188402111103421240076415440c4141c412043d6181d6925139180350b090707885074000c80c00c081c0c0001403074200892500c0c03d4540040240800d0941c80c04041800c1491410442d103c0c02504034440303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 654224190 1250 654222940 654222949
    0x3020303030c0a110610060e041401030b280902130c09030b0901021e30190605040f0c080a090f0807030306120f0c05010801051f091a120c03240609 65
    0x34070a11081741c00e050664948000603220458002301c89000c2d0303007046c40000700f101070829541e04603903102403038008503903480e401580020050207c122201e0300102d8404021000c0740c02200005000712074034501c1c156458144c1e01181c000b0034480c00800c802180400108065485083e84420808009440c00b680d000b0300a030342c2d4030191060b04550340301042d00801d2040d08001140a010034000044c145140e055110301130310780003050901f4581002180e658082d240f170300300c03400400016000b8800110710640d207202800415482c1b100080d2502c0000700d440d00c83c3d000d0810001e40000d0385003640005611860f000e03622100c07003a809d1503254040003417041c01d4814180b480901940c000c00500d5818038000380c0d0b03545194441e6040044180040c0002d43d601009050300c60041140e0110ae0100030030290394860b440d520070171080700710b07220465441003050b0052881e02415100007080f551850516001800161a092454614904c0e14100283c1d01a902c0c544080700403d10303801c200807040082e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 654225440 1250 654224190 654224203
    0x12031b0503161a0a0203011d040302010b0405070806043b250311030a031706150a0201060e0c040f03080a0216090f0f05070f140d0204030302030c0f0703020303030c0a11 74
    0x3202c199030983c200741c10280c54000031981207606101e055145515150072442000c00caa00c0132810b0510035004201014001d501202c04070402510034400f0345000d202c003403c180300c12240c0300d01031801c10010980103001505c91680d510f1a0303440700801891180c0d0a030b5080400c60101c03d4041c1716100c54260a80400c4101c0c20040c1841e00503018490f08600d001c002984010300014040e5000320b044500094014482003101d102110b45640b040c0c3d40e01e00095940b002401c421a450000094906070840d07041d0012401c2e11644901d0072419202c0781070210b0f41c0c0c8140d2045074a41003400d401800001d01240042c850034481d03104540324410b07616007094509125030300250702141e882612240b40002e03070041c0c03a840f08458204201c40e20302400b01406039000c0505203000c0010305190641e201c40c01000f03072408021401e41c1191903c0d124a000307907aa074040032038181c141c800c2950400310b0400000b000307010380e40c0c0a000f840c25034840311500000d50700424200000d100420040640310941040103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 654226690 1250 654225440 654225443
    0x5070c1a03010815060102030702121905010506121f1509050109090311150a0c200f1905100209040e01150f090b03031c09020607030e0a12031b050316 66
    0x40d940c1e540351074125031428091108000c0c4412490003000300d0341c2e8010085c1c0f1003564040d0340070000a681c408040d410030101c85400842c90419001f100207000381544001e00ca1102900c0401440a031406040d64659200300344200b220501000d202104020342c020042d240140d00e9900c80d110744514144040d2a0709800c000d81c010b0380d402c080300074183e0182044001907905070103481d0040c101d03070140c600750070300808001645441e2065020b1a030300c9a1145d42c50200200d205420003401450707001d03150711041800c441070303205501c10b000d40c1e602030111a513425603020005204071074649054902a412174502d0300c3d4810795403184160304841c01e00401056900b03a162030100c1c3ca00f0080441540402600002c0c403070391810240300041e80700042140c0d8401818085071600c03194042030103000d4180220000d40101011420030101a00245580e1a00e20100c1e20100c006071201030b2810529000f59015001401c1c020b0510040351580d101d001d0102d008006407032400005da07442040100c801d410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 654227940 1250 654226690 654226739
    0x91327050a120504140f13020403080702031606050d090c05060a05130605130e09070302180108190201050301231f020c04060503030316211a0103090c0605070c 70
    0x441c0c8100044850b511559039050304105080508103251242000c00900c0d041d8010503115403207001e1644e070442680344801d1180020355076280c892520b8503c075001044124060b102d050030810039a1414400034060741c41c01e58545003030842c150004006400711200940d10b404c0d40c0c0308085141c1e10340303000078904101d06448456070368403003111303054401c40583c2c45003040150034030111003d40d6a0941c020b040b2201043c4840440c0c0754080807904080c881c3d80002d501058084000c03203c480b4a01019040b07a64400948072080d0038525450318868000000a0003d4802c04c0140101e9500010383c1203a200740810340e00d840c0111101051400e021061000410444203119030600750381004500e40805050301c06005a0b07107040c01095a034000501800064084020003075000340c4201d08c0201c070400c04990f00d00f291030000407080c00400425584900300c01200c106204954028091180c2042d80162000c03200c900e414011a0300c2d0f0001ca1086070344401c10b502c0007984036043d14005194440400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 654229190 1250 654227940 654227953
    0x7080a02070b0a1406040506100c050c04020a09031214040b0705100c05043012050705100603061103040c050411160b0709050a0b1206010504080a0507031709132705 72
    0x74400c940c0c4e01e8000f40002d10a9090104100154a48a4110740122000c0c203003411105541d107800c038208403000094641151000c151820200d902c03c1444040740d018000b2501d401c103148404030340e42d04924040004000003000304000340c95064009105070b501481c240c1c2d9a00710803040e48401c0c4c4001c1c1c010100016404201400b10182d580903103403004000c40d0f0500c1d08130345807044031070030444101000341c01041c42c032a5502c00c460280f030032500010f41c1700d4245c425901403080414010b0180e408103913485442d10903111504003045040301d02650300241182d070001e10b4082000041e01e004004100071907018805888404000280410b07424458800380d202890700f0703100145039142d039a115a2190791440030421200c14074908442002d1079450485110303a07522030041e9014481c940c000c10030781c401c140c1c80c20140803001c100c02c02039901c80c01c0003510fa10a545005c1016000381c0100b503070700c08850f001d2000d22a160741c4c081503012030001d01e054620400c1c5c0c0307046504418080302c2621240c010740b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 654230440 1250 654229190 654229211
    0x30711040b0303070201020c040f06050a03080a0206010e04110904021504300b040f02060f0309010f0609060b09010c11090403090911030103170c0a140c010207091407080a02070b0a 79
    0x90255048070501a0021030504190ba00000c0d41c0c0c1c11801c600b00c2c021651014000c1000200783c014001420015080820310340e620b00d40340381c10f680480b00c50001400303040008070f440d100301401c20780240d8000c84600b401c8401e0340200245d40c84054000c0368003001320703840c441d0220f44c2080500000e0210b0040031044080740c04030440ea4685000c031410300941248850000a0480c420040e0460707003040400340c208241d440440da483c412810324000c000d20220400c40803480540080002d10a003030002d101c6c143e5249601010360b4614021800b8801c414000c00406520441904142034000d5400c00c0b0b480c003a440218014034000e540550020344003801c01c0c0190203e0340141c2140c48240440d0b50b00c0c640c0355885914040075840c044810760341d00050003515000381000114040d03604400710400509040550941e120382d49810180540514400060106410f104080e00619080c482810399520703a4812540c00800030010080b1582c240b110401159804036401d03c989800c1400080a9016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 654231690 1250 654230440 654230449
    0x30c0908240606041a0309030423011e02061b040b0a0e360c2a16150e01120603030f12020c0d18120b060123040308090a08030711 57
    0x914241c01480208000c000e10428140400d0300c41030017000d029203070b88500c0301b080c7c254800d60b4005852040848412440d42ca007103d410321003150262141c841d001d00135030740144c00304251640c4c1d81c09a008030740060207030005500103a0401c1103200d034051500f82c440314080c0980d002210803000140c040010036129040a007000202c4844494010020380c002002181100c111a4000308407507400c8400b0a107251110401d58030340020320081507508050349080d83d03000b100340c90845017442c1304100010031f02400e03281400e03090702d2540140e1190b031014240190b8000390f4245d405030400641030580c1143c140c0f648112809903110307541d01c14501d01c0f038030350007024503016a4090300254410800300840100000d1464540ba8003401c280e40c400d88910010380c403a428541c410b14001078018054400c01a03506215441100709803103001002002c0f941070554032104000c15070704003904000500106202001406007403a004244005460b22001c9039815500040c07421550540001c806592070300d403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 654232940 1250 654231690 654231763
    0x7030603020a080d021615050a1407062a020705040b030f1605040b04021c0506190803070b101a07050a06020a110f030322050703051510050d0309030201030c0908 71
    0x6c405424009081c1811958100c1c0385480c8010402c1c003100060350f05505001e00649014121261503281e110103403800d000010700010458500c01e002a0380c0c40001d140381882142400ca90345038001d1582c5818402484014085011056450300c43c68200105100040012035244d008441c80621621b00e440140815908084c3d1050710442c014803044e00c3c10141d0364000d14560012500100d01c58031540d0214208422000782400025840380707003c2040d000c000010417019100b1030b80700d403641c0d40e47e1b03c202c0305180d950300541d0700e1000804140b2080c02e810382e0143c0100c900071010385a10b08107554459007280c1c0140d4030000840d5400b80c000340b4a45047c030030700380e515000c44051032962602007090404d502d00400001c9a01000e82c0642050150810403e8044c540c44001c50f00c0954010151240b807003002c0f0b0312a900720444040110300340c10300c1d01000300c0c41075050301c84079041421039005401034411020550100511410001500c2d0820400701808111500030090252039680000d80100c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 654234190 1250 654232940 654232963
    0xc0705010e0c090a0b0f041b090b09061c1103150108060d05030a030e0f03070602030402190b0703050711150307170105090412091a0904050702060609040b07030603020a080d02 77
    0x2041800300b03082684506116a91000a488002815000080014024014400c515034210780342c011103807203c0b80c4e0880ca90b0350003940c0392601c4110170382e1210746e01100d10400c2d2000382c00c20307414899641200c084c6017030645043c080c0c18000c0381f0704600322a407001c107410407103c80700c0500700c450b070414072543c000c40b40079000380c025100c1079541441078885594030711461001030101075850300c07540203802c010310041c2500580c00054aa565049040601c06034009840c103034410942403802213100001e40000c1c0d011541c80443c4603041403500d0318203032000d800001c019107014602584007100c0c0c0d9134004050b2804206400300d80e4682c1000d01c00200000c955480c070310311007136000d4014081541d40d203841c1d0f81e0003648041495102c0c405160300711900d0801e81d20180004c1d0396a01d615414880b072101038801454241c0d02040107940d600c10803641c4090940300745803c841180007007004185085c00141d4413100c40d04001c54000d9a03036001c554078240c5944100c0c603a8210081d20078005a05010800904 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 654235440 1250 654234190 654234193
    0x501060309030207030311031c05060f0d0302060103081c021201080f01060303021b040204150804022d01030f0b061204020310060f0b0a180b0a02070b0a0914040b04050c0705010e 78
    0x800310342c1c1c065614541da00014041c03010400d403c0920380700c100704807a2901025916103a1a544034035103900640b0042d40c0d01031040601b54840b1a850400c50100d61046400d40c1c01045540d1860f1504103843e03000042608144c50f41d00c1c2d040c20700c01201d00081138078075148141c411183d80b6000042d820070721040d900155990502e001000442d030300103805038840715210458a007400381c030350000c0c009104a40c008000126484810706c0c02c00d81008070240305078001d0701c00e2481100400c2d000c003040300c4000c4180c410170a030f0310042c8040d544a41d10104150226250014001d40520000303842a00000103010240100104200c21414280b05050001828840c20b22006040040004400d00c0a02505d20021804207107000c18522954031141c0c02e201d8220402c03105511032951203c19881082c2d040050301c200c03400012714540345000c0398200600c507550300409601b0000c1d447c1d260702200320642e1f400303904d0307000c0c100050f5250b204d00e030301603d1090f2809503103c400349015800c2d100300480c5103485 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 654236690 1250 654235440 654235451
    0x40213020405060901080a0b030105131103031e070f080c0132010b130906030f0201200c2e03090c0f05010c0f03170c1b06010b071b0b070c060305010603 67
    0x10b0f101c03002980c4111030242440303090b650f5205000070040c503090107a5a4558286000c0c4091b0082c065840c05007140900c5208040451701c0091650ba4401d4100380704c407041c807141400243c081c610005d080d000384070322103030b00820130180c580382d6a64000f10303101c0405035276a03e021031101a904042c402c0184031420703862034001e0004c0f14218040d105220b080000c0303100050712101030b480554240301801503114100007541c0c0320f003060b00740075009050481c0810070f60341041e400c14218401c000a00030f000402081c03a001c00d4810300c4205445682c080c4000d441c1107000c4920307001c043e060201441030303130358001880310b825040c40d213003000843c1d01961141c41c150b5001d04c62640d00c9585042c02980080181d404080709140446803141604001c0e880683c0ca0018000d98100110003019070052010442120766000809581c480900384510070b14010308000c0b010004103400901c24040340d9a0003104082030352624071043c140e000c03071000ca40007080060244005134052241c58003500345440d04200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 654237940 1250 654236690 654236699
    0xd03090b0112020d050f010207021302030f1b070c08060a0b10171e040b090c0f090f1810060f06090e041113020a0201050f0c03040c061101020409020a080402130204 72
    0x80d030358040c041c1c8006842e0782071a0030190348550021420442d03200c0201c2c0d59240702198200d0003504241402c030301c507075011070328911404018000c0d20f01820f0410102880c540b6403000c0d40d0000c407001d00000c00306560a001c0c49010a525080c1c4800600291014060500d042949801218032110229100d59600781c28030503d15889200803102c9070708480d904000c2d88070703120750810b80440000081100e041c440c0400c0208275007a40c15030b0203520110700310f400c21f211a200b088014800b681000f5004881ea50014140c031019699264100b241241d407084440c0004146901f04114103e003510308907201c8904100d80c65a003e40c000c010295460000a064209001c800000f00c0c054000760440000c0e00d00c01b0119504c0c0d55000c00810310207003003155101d18240c00039004e80b804465107008408150b00280d8128180001c99104940c08141c5039851030034010140c82404034041e10210540d402e020104810b1036500c001c05074510079880700106440e041c81002085080c0052504610b030050200f000f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 654239190 1250 654237940 654237953
    0x3021201060e01060c02010903170a0801050603092d060f0108060c0f040b090406091a090c040b250b0c03010e06040903050d0207050102090a0909021e0d030f020f0105070509030d0309 80
    0x50544134035203003000f050041400100c0c1c4000f0a600044c10340704c01181c40c8000c0040c107400800300b9140d0307501e030301c0070b00c1c1e07039880411606001c12103421b140c44c0c000001c0c01c101c050308148040f20036505095016074007621130014a2800908980c150b5000c0c1d80304005004160040210591000030007294500d0400b5200411240d40502c3c4100d0f0041341c0d0100c2c8a07211991241c00c1080900303001101049900d0703483c2070310982090043c0382140541d45101c04901f000c5080012a41074400300c41806103000d06803000d44014032443e0301413501c500310700c0c4c1c8104001a0076028240c0907540c5841d0094403941402c010100038807025007003600c00ca190441c240d0010f40c10034141c8030f200148510040e11103001d4100303240644120a0941e510001c09200800c45a1061348031904450003951100c8038140080300f00c5815907841c268241c2d00080e983c03501d81c00240b0400c0d80c040c425110f4416190f40201d8a9446825504207540d2040031400128010405090030072044131101c0d074a103014800711183e17480d4071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 654240440 1250 654239190 654239219
    0x6010e0f061807122f03060f150c0d202d010b220b151905071e031803020604090509071a090108010f030506070c050c0301060303090302120106 63
    0x1d0300c002c49200001d109107003d5446440c01441100b010b21403940c000004c0c1c00c1c10101861001c0c0c001c82139580e02001812902c041d0380c4950307070180c1052051700510080040c03414070318072240003c00041244040d05c84c001d008203128010645c40c2d11407900c061102150052041c0d8907400003550040714903d04601030b54491107072100fa0840d0498640e880392294501510a4401e101d80141c55070000c01c03042201c142d21014800c110407001c00c00d5901e00f07001c01640a0360003916000742c050600441c814920003c2000002e8103844c2001441c081e0700e95250760100c0300f06132107000080c440a141071f041c0350300020520103000005050712000742c00c0d54000385207402540103249c00543d4820000d904200c040240c030340034010824189000703400c000024009680038001c0d50340002e400c2170002450032010203001c0143c980c0700d03000c0e203610355580700f0885010b5842c000a80c1c40d03214407034a92000ba1428840c00e005180255a8500c1144c158014006c04560351004551075038074001c4104001150314241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 654241690 1250 654240440 654240469
    0x5031303300e03010f0908040905070311071b03120c110604081b0f06041707060c170c01200a030e0d1e0c170442050408010e06010e0f06 60
    0xb0084807501c1c1c0c01203401000f041c0a00301441d03151a0084081c415044090012940204018481d50766040070032007da0704d0100494224510901003540080c86c1250242c4880c0d010320140c008455482d1140c2c0296420302041c075010941c00890881132011601003159050402d0b030b035032440c0614100310f8507a640d113038102200c1100030724600182560303101403417207110b55402000b86848030703111418900000340e00c1c010042c00344180c01000828500443e00501c0454005c5621002003490a615070030329400b86100c3c0ca800e56031036588100480181d04801e9806044154254940018007000303411201456030601c41d9a10000307071000740a611440724139909004035180c00b86101d0340002900c2e00100000000c003940c2c0f510800c0c03c407200616000d401140c070009440241f0b0a800d603001c04100d220225803064144107070000045d00306c40c80030580c104002501d80b4610f00365842083c1400c58124000d40b00d46508450010010440c240905a80143c903281c6100040e0030a01c00146d0045090401e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 654242940 1250 654241690 654241697
    0x1050a05010c06140a022104021309061b050c10090b18032b0c0c0b010b0306060d090b0a060506040b19051b07060801170705040510030503130330 64
    0x82c000108002908079401c0d031059071040c2010b60030940d03081c0d0040c0d0003d00d05050070a01d00c280c00c01516003100343d400c0c02181c0141c507440c0700c446480d20b91000762070842c0082d81c40a854081224000748546500d0501c1452076403800c3c0c0710030354848040d04103900419184810b900305422840800d061080d440d80000c3c41031003003e203110740e418010782940504082c8582c0c2c1c240120310300c8151a0101d0000004151880041128141700b050079584040c485001410513591040180000c0105600840d00038000824244c10000703803280b44c201340c0d018144100d071101e13950740c18048a1a42c50207490050302c001c5686074109400c1911411290092189500a10740300d00d030038044060143c404c0b181481c410300403e030407002e412181310b981c2d01c2441c86a00006410400006a11421307a0542da21030b01d00b0001074104a880e1400700000303460060a0505010302813200000010010801022440300303038860b40071114a54101501c44400b10429901c03401c040b030b0084049a030380b004141c41203070000d05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 654244190 1250 654242940 654242957
    0x30c090f0a06031b0318030f0912030908070504050c0d0902011808030c060a05070215150d0308090c1c0303021309022106030705011e02120f040302120601050a0501 72
    0x400108003941600860360001c25005020680c66410b8200e0000c0f200905400e00d0801c080760341c11412144580744400344100603110f1840024420041c020f608911340c9402028103451b040d100e0f0740803ca1440440108a0121003009040c4c070922034a002410100d4040001c2d281c1000d1660f2640328001c09007445554800480c030441e8000c0d010b66003808040240002c545880700006a070726070000d499030341644603002c00200d03002c0c420700496200342456130280240c1d058503e4486800d0500ee07002600d0225650201000d9440f640146a0414000d80e02c800d00c0b03040c80c0f05101c0c1000d24009a25004500c900300440850903800c600c0340280b949803800690718014410481d5410150383c1107201034500015180501011034100e180c403213030b0086039a141d9601c40308101075440d4802e2003803c0c04100400107000703400104c55800401c50309240141c408400e003031601310443c5c0d40b21011040e41d101700442d0030b2055080102c1ea003c488010b8400509003541000c001840740010741c03080d28100201c24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 654245440 1250 654244190 654244207
    0xb12120703320a0504120606030b06040b0f060c010b030d0e0108070806012001091a0a060e01081c180602013e03090304080f06010603050603030a0c030c060b0306040c2405030c 77
    0x101d00b12401440b1b4040c20901d80801854100098a4203220a489981100001c29010324261241c00e070f07484401000b198a40c44140c0c14803200340c02140c1010115507a40d0a51901070714284542d1244c1241d50b560844c0c44400d1000141c04600050405030400c030b2100c1c10024166040309a401c411242030f40b604a40015841086001d000003420040c081841d801038412503c422000503401001c07805c00c14442140c841807005d4080398248504e20031688940d081d0700c2d56200e000c502084c0a00140381c8a91045400041a0244c440981c04200140e54801207629884e1801742d8082c41c810149040400907800b0490b24221211001c1100d07124400000c04900039000c10003c071401802014150f0340e030031200f1fa52003a1140002d10075000440c0c04c0c03400242452030084115003000101e40c441e11060001381e142245c5c451341400007200c0807983e036401001942c0d0108806441240b00b1511750f90f10030306000140120044c0e40311440b00301c0e00071100b10320065800c0320039258070690700300b1045c3c2c454840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 654246690 1250 654245440 654245447
    0x604030e01030f06210b150a09020702011b050f060a09021305090316080309010b0a06050d09020607020a090903110d200a06110408190201080103060b12120703320a 72
    0x280e034405d0b441c0314100356601044d02c1981e043d803011a40614032200d0780790340b0040003110420038401c400e580a5030701281403040d1881940540700d0b10340180f510212010f500000e404c41e101454100ba50b15900c0b0010b14580407000300034090740106050824440c00e00e0325408602d60322405034007180315586590001c1d090340c004005035a5200081c40c6025040c426a0604010507841510320410360750806000d440a030070700c48201003c03074031300c1c4ea5094074241d5261130a1b001001c0428049074810760401003140560f64540314000030b00a4042c0028100303065260291030f80515200912103038000ca9130b420446038029600c4d038004100e0071080100209612600e909015420000800881c58040c0250280300e1243c050005e0f51514401c4400e00250568100c2019010040003400102c4020041c000650150801801030300302500440300c0720b00d90b41c811802c080480e238a94101c1c00c1e020a80a0070f0643c411010140744624400887e096042d00e801042c0803440140c0c1602050000603038858500c3c031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 654247940 1250 654246690 654246701
    0x14120a0b15090405100b1c0f1514191202150c010506190e07031a03010609022a060a0209060408061306110c0c150c031210080604030e01030f 62
    0xc020076000c6541005564800e0581240107400d00442c43c1c880012081c0f1109501e800c10703540708500c031504003076a5001c40b942042088100c422034549401d81e140400c04a401404210013410081402690401507003290401c1d180351854400c10f04041c40c941d00021204040060766510b08540606040a0020a94101058494008004000641c50021881940114052602103801d0369191440d00c11004145d040c2e40941089800c0344808500b049010b079108181185c18900c0b50b0024810340800203085401640c080310311300790001108100e1282645813200440407141c81086845182500d15a41d08402024480c00d26400110301d035869881c103082d01c000340a00001c90320640b030809400751040b50304c0e000c1140c0c101e05100d40703007034540131181c240c62040e1103070001007540c25403510400001d807001054502c0090741c1000340c0710310b1500c01d00080c403150004080488480c10300b224071460520300780d4803807a00c94004209200000c1e03400050b40011b400240703008180300c03407480e030381600500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 654249190 1250 654247940 654247961
    0x3021e090102150a062111041e050f0105100309030203090d020f0d03050c10020403241512020f01020606060304240204090e07050306012d09020a1e14120a 68
    0xc01d804200102c000b415017180701604e494100040c001551507482014904805a008201001902581c00e003400d1a6105401c02186880340450b030b1140d52002008490040c0c400c600b0740340e40d010040c0b245081c05005100b00030302d64942041142c903941ca009450b4090028114801c1c0314031010401550348240202104000041000c144d45a042c50083c0261b40b08005203403040c0103814015011031141e1080e101201e401820351604104419101d040f0413820b42c08400102d641c40310101c40e8080540554009080c1c5511007040228050041060120f5804091411980090104101910761805907604280e02c6544039004226a500c0c219a59242a080400c46032003c54005a046040c0c1c000c405840a44416590007a8403001419101c0a00f4000e141a0702c08148a0783c1209011004190842ca25a1010f80348181c4908070380060ba409028860300141d810600c004202c60b00c1c05090803462881d05180e003041e9007590040885028014014400c6c0950340f00040e802e030056003100a800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 654250440 1250 654249190 654249223
    0x2061e1503030f040609090b060a0c21030e161410050c030a030501030201080a0b0a17010b0a0f15030219030c0c1a150102010e0c06070c18051603021e090102 69
    0x22500f50801c1c801a070000e11509001a02c4c040300000c0d0f25086100d5903800c400b001e4441403410000400944003580c1c81e03002151003c15000c6c540708000b002a5101c04078113038541c1c0218160541c0c041407490b0a007126007a100b0030314880020049102503020642e048102030b2440c546404018105907011f004042000307102d404001060501c6a40c140c3c040c5060364400d88030703503407140ca441100004171100310751074a4000365444000d00004403201e80c11a80c11100100100e8109489800720341c3d13903151503002c0c550781c80001c8010311005c40c101e050381c01c005019140460420700229071080800d04401c0503c8189580e0701240c004c074a100e83e5402510f42d40005088100c5441100014140c200407200081c411903c4102024158818042c984801c1c0129005001c5c50b103c1c02d0070803400f83c0c4801012240840c0502001890504400b01401c1e1904111070005241c40c240c0c00f4221043e0b40140c6c810304041c070410116100c4120292015030102c01e481149440b0074001d00142e26008000c540d00111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654251690 1250 654250440 654250447
    0x11040614120109091a0f0609073b0a03080301060e10020c0105161e1202030403050a11030703140f011a03032a0703050f07090c0c06090201140a030c0f02061e150303 72
    0xc0550300358071b4501540c1c043ea03555295507107001d0b00302d510b640d40810700500c013140740104840e510401d40640203000c040d1b1034204006000400000c2c2c0c410b0407a44110b0f4040e00110041041542040c0e140444000545080c83c000e0740c0240000d45414070510b04a050040c0070032012144040c8011078074070745034010030a0082c3c5858403201041c142000c2402c4904440c140c060151031807021086d134007107a520000515a00d0b2181e65282c0121028801d5550144030b881e8002021404a440002801412a01601007041001c01c0682580d070280c940d0001c481d000b019003141030f1030000443e900f543d15a0302c04180450030300300f0a1224075200c200300c4a14410550f000c4284440415441c1d03401d101041143e022a594400000c15034900b04020004190032059141c00f00c0e8a54000c00800c1d031051400c5211000e80f20160340c8150410740030480021303507415041d02d420b5000110000d081c8101c2c001004c6c5032400e040081908841d414095001c040c18001098100751003064104101c0d4004095944 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 654252940 1250 654251690 654251701
    0x9010905090601080d0f1b06090f0b010e040305040311180709081614100512010308030f150f01050c0c030d080912040f050d0f0611040614120109091a 66
    0xd0601650030032034a0203010000911608001600000000d035900c50008480164805484600016000340000c4421825110000c3c8440c451408018810f188600000c0100d0a103d880d800c816002440100c038410288000b2139045015102202d5006120442080d1148045480c806801a00ca000c0d03c001500784040e00703030801000d038180c4480301c007100c0ca2080c88261002d05200c4510034074884120a4890100500306020441100005c03800c00c0751030007100035030000305500240c0c000d454081d404024004019081400540c00101c540746082c1d0300301c03d0400198904944151944c10702c00b0010302500b085038203101402c6402d60090940710740002c18440940198402c42d6140c200340154148000640800401d440988816a014442050a000030b100013041601015912140e4a0850f0400140140684400480310741a0b45840301c0c98203002400502d00015507500740785092068407000d616901c4041d0445104900210380010242402100c03181d4400b1341100c00703d0250304001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 654254190 1250 654252940 654252959
    0xc160b150301051003030516051009110f030c01050915040b0a0809070e06040c11061608060d0f0609060207021002010b030c01050304150519150312031b0516020901 72
    0xd100e194061111204038410800301401ca03441200e80c040c3d9840520020300102c1e21600140a800c4400c80e02d001042c14140c0b00c0c01e140518480362281c00c0d946580441003001f030407140d101d81004c0240da0b28510350000740d002039102d28200c885c0904000001c2130505142c0d07a14081403801d0040221695905c42c0c4a0709980308a91180e070100703011030200e40c00301f14548070001c1d5003421a8a00b5100003040e03181d040420018040310705200c000c1146035484a02c00d4081405410b009010f0080412140307002140050701c103030030081044d07114407110711541020600e0407174480305155000c840010411034034036080c4000c5c06801c1c0081e41090000c98480c6549805600c1001c00325012000c0710841c61000c00111140d10003250f00810f412514038894009445a40161b80c102003240b401d8901840c4071030550084545800360029000310030b0004109001101d16031801003070107464184071904600f10341541c00800c1e85d005c039081000020f00f6105a038850110907144680c000c042c080156581c03034041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 654255440 1250 654254190 654254213
    0x327060605060d24060813060f05010b070501150b0a1121070b1506091002010b031c0311090a0e0a14180105070e090a0914010207260405090f0c16 64
    0x4030301c0c214210b004020441010094082290344546d50590141d0340c0080d050040c0070382c034000325035054030b03040150002d01c802e02405020381040414241c850941d800c09500b90b40f0b404207001d5031108910403d2007900d81074400c50780e00e0300c0141030150301175800107803c504d403005000c7c030400450300d83c0d81151034000e0640c0003800042e00810204d185a01c1d1b0300112640f144119039030a038458802c0201c3c2160b814200306240c0185200d000000f034a54400700841c0c108210b040b10508410000000d1328403e0344c040c49150009040e0f2192142010b40b000c0104032002c54900860301c020000c3c9002410354013190304030307103c0c40d54512900c0c11a401c1400e403a1640008120311007816508000015540d10301c92034846040d500c0040100d8496100c0e074211300c0050000c0712040d070320403030700311070f1b5041c010400d000034240d0501c07070035000c0342982c04810114003a01c8003c9581c080d0480070003080109aa803001d4450300a010003440405940b26800b0100c001d12035000441034448401400310203010f100c1584 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 654256690 1250 654255440 654255461
    0x6330715020301061d041415030f01060503060604020c030d1811010206071e0e120703110907051801110a15150506030f0a0e03190e010327060605060d 66
    0x240405110000090401da00003401014006020402422100d40ca502c2c04500f0f03074517000e08001402d619801c0d20200b4400d04840001044902c100e080b079032800c0800881e0001040309000700945404c000010b502c0c0c0368050300c494800d680110b0b001740f41020a1040714020803601800300400ca50609100032510320800c000d442c0e42c500c42e000c0009c55400403030310034401c00159407108500c4000380c000700307210015407500d5010429442c3c90805691204c10150940c00e60305001000024990b280030034101c130210171000d001d40d40c0700c4180209280c000341507408684548005900340c0300c09400403248001e040c40f03461010300ca100b0a80090148e5100305007141103201c00c040c08000701404114103200224484d00e47c003c00c04000265983c9070121441b83c014a21983c04100c21981100780791854010b503007565014040c4020004110380c000f00c060041040c20b0030b00740b00002c8a000803081c0181044031542d19200c800401e4800c01440c1d50021005d420001e00541c0c495510007410300041400a48 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 654257940 1250 654256690 654256703
    0x2030c0d0c030b0a0c050a0c2d020405010911030a050615030a020310060318031103090a1707061d09090a0b01090e061b0307120902102105010e063307 66
    0x8581c1d840e0403401003011007117058841610b401030103102191040d03403540068540700c600766400d604c046900c602020b19542003002c600108201801040100d541c1a8401c50000d894481001c01100c01102a2540000050b20009003940c0b240c000c298010f10f01c8c06c0c1c00e8000c940c0001006503a05456014600800904001c4000b41d6140c88059044904000d8102801030054400d030002078031500896410011400540c1d06100005010900024140c0c101a641038000002894059000c218520041101307150000601410b050600c200c17510030750203580039900d038200146902c034041040d090b400f81d101040c4042ca40e550705007a402020a070303400c2c150701d000713950100e180881c480d0701c420f1491004030300c03040c590f440ba03030401d03111100703410860844140c03100c016802698401c00c0d030400e104070765103071401884c50506410a000580040f10b02c03a207031810f17005000c40842a480190301440c00c1c1d903003554402c10400e0034000c03503500340130042b0441464503034100420710340780282c000d19100d00d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 654259190 1250 654257940 654257963
    0x30403120f0c030909021b030f0702011d0919180b0105030d051c1d03040f030605070507050d11150a061a1206040504060b130506010809070f030b0402030c0d0c03 71
    0xd2040b51000520316020f4002001401d050003440d0302503001707100e0843e4a40201c010303500140c000c02e04582146001e2002000041542c10941d43c12a4a80041949542213918841c00758000920000d1000d001402c2540a0024428030030002c6d5120441e80b00c841054110041120316001429000c24003c1c0c9000780070311a1100355480c0524140d4858001a0a503000c410701d00680e0345e0f00070860084581444124811500e0490030309200400142100503c580122415411b158003680e0000d40541d04101c810490f03040800e40209082404076403510b80014043c41a0146518242c0b405651850076200e034030502200c03100d01c0d40301000301e81081b480c403502030507140d80041040c00707000ca0880d8a0982180015007620f01079000c29440381c4034810001d4a4040d840108111401d5841c411f21416a148240440381da04445100d5004400741c0003007803060b0610700142000721141c0300c02051162004086800c642e018040c21000b1603014101011300700f40c40c1003c0b0012410307484203807140103c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 654260440 1250 654259190 654259217
    0x1d0a0f02030d1b020906030a0b01060903061a1804080409022a010b010207060305060d0f1b05150403020f0d080a0503040b0a0207020d080702030f0f010b1512070503090106050303040312 81
    0x44020f010701080d01180002000e0b159003d21601d5400280307041d40c9400381030404030004a82e4404c00e80a0701c01c50307a9150070a4103502d0b000c800c0302d502105c000803d10141c40035140c0c0b0b0740c40301d00880741910201c4051034103813220303d005a698040c81c0c0015031440c0c00850044081e01007401115112000017224503801001441c03101e0032103901400c000d00580022800780892402600a41c0e0012030280000d4002ba0068440e101c008c1185c00046170154105a0f444184040315444036010f400100d9640c0c00c1900e900000408074895444000d00030419a903800c503040e03a8604102c140e00e80c110b007209694040c4203c0c001c045905c1260101d60b54018400814600b00051094a84083e809004405892101c2c0c95004007038020361801c90345032103103070141e203a10075045c484819140300b04400440c15090400400a140c1d4210301c0c00384a000c428020740c0e4500d40c0d00403006401c1100e03818a41e40d0f82e2201801d0601421070b0382c01c0a030b0103101c0020000b04201c0440201c66410019503542a106200f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 654261690 1250 654260440 654260447
    0xf0a0c0e040c1203020a02040c1e02121e0f0a030603021008040c0501111c0e1305090c060f160b0709050d050a0b070e0405040506060405091f1d0a0f02030d 68
    0x107440260200000360300a203c07064a00303682d003030403078024011280c05445c0e03039000400b91282c200d0030740d00003070008001e403040d08150084051103683c140090001c60171104914400350082000094450b8848800d0b2000362510300211744020000198035541c6640ca058040c1c050201d51000300e01400b4040c0e1001001441560010300683d07010310402040d40c0380c44011118503140014060740d40c0140c10b9400e42e0b84600c0d292007091408591034a0040845d03040c00c01c600c00303092400341001e0600340303420401c04281c00700e444040c1da001102c2c8180c83c1c0c0c469081d01b01aa000d109291220140c10071000014045044210381c070a0308180c3d40d400c0c034940c42d031092004024180c03100030141da0042c0407000004c0d652121043c0e0181c1d1901c0c042d1488151040018291101500c0c1a04c00707400038400d200c10750615014051340507a1060040c2813204204000c8006100c0000c1c10f030000a0ba204840c3c4100001c107402080805010b2044900155a905000101c0c0c0301e11403080b031192142c1030360103030305600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 654262940 1250 654261690 654261719
    0x601140301030c29161106030a05070f0f0806100e06070c0f09020405010f0f033c06051507060f0e010b0a080601060c06180b0f190b0a060c060e0f0a0c 66
    0x199a1104d0705000c1410584000d0110040044034031218040d40070056884402c040c0d4491000d40c140851a42000e04000d0140c880030b815450400c840c2c00c46201705640c2040109030403040079100d00420710300e01001255400e58901c02e04d40e100368000740620520501c0005141641c064240842c02c155840100c48124401c620030f070b5010540070b005116409001300080c400000540c1001b15007040000f9000140c54550801425000c40110400040401c601150409080302072030030020942040b002910160034001c0d4200c41c900c000500d4000c001c4281c0150068281c1002c050004403170003100140a4001c001c2240d00680002200046007c03000a91034102e4507141c6030304503440b0362030302d641014001d407019a80c60f91a146001e80d0000b041d0004143c81150001c0365840c0e5030600c00741040070744000da04408466402d00d0145407056850020103001c840b21800c0894a11626180c40400307031080d000344c0005130188003c00d0400782004121032040b0351040e1054503e494681920080782d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 654264190 1250 654262940 654263009
    0x120206040303050127050901060305030d02071b30050a0f02010210060317090a240810030209010510020109050106080c030708210912060403031b08130b0601140301030c 74
    0x10700805c2c04500042040d48020b400000100004c11146d40720b4a4252455005c3d0101c1c2146643c002540c4080c0b0060701c0344a03001d000c1c82841d80380c500d4584040c9595502c01c081c400c054044034071044090300d003c2c9031040503002303503c1002d4030820a00d0303061030070340c400784600164003601442d5070000c0c02101c14801c800950b540001d00c40800b07a400c405500b0795400c180e82e6250401c03140e4201007500580310066001e101403861402101d92031a01c80109080b00c05000c0c00c0b42c040c03c0b00e0741400180d0f1034584d114192032061341c41040e84401980c0c03c0340540340e154009001c6520308000070030364410104070800800f000b581221410f5544500c031560328039408008201400d03a5411520504030000000e1911240040c075523104901c1044a07542400004e44040340440d43e501034001584042100c0d0b42645505400c100700c0c0740c81c003042d60303000507843c200c8020000f80c400b600080171030b8012414810740d940780011060300c07503840f4544888442c000340500f1007074840044480b07401c0240c1d146a192104c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 654265440 1250 654264190 654264239
    0x3040203060f09250501030b01050c030403080a030209060d0902030c121c0212160312050c0703232a0a020312030a0204170c100f0e1c1202060403030501 67
    0x942e00c8032140c10310703a04082c0001455004041000d03020a800c0e110350281030b0710302241541c0e2185000c001504854a920009052280503c16603208500100a60301120b800008580d0354030710f08581100244a890390700355010348085a1a1400d1882d40d01201c0540e10a9046136650380882042284d003208501ca6444a603110002e0002c0071401e1016042c1e01c0d1400340106c2c3e40440001e130250099401c0007045480442000c03c0e42814160701c600c61002106401508010130b09000c0d044032403030b120b551070103014024840d440c00a41c80400c612004417054001b1295104d100c0074140d10212900c0801200b502001507c0144c1c200401080c45151641d00038000d204009070f84070903050300d400040071945026402c0c040040c8410400300702e141640440c2020709401060a07040284c42401071030715400300a0b8920103801c4a03034000e003d09113003038022152420f2014050480f615203207181c40008040600f812070b500a4039400240450040d80310741c50a0045a8a68441810380583c0e0750600300034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 654266690 1250 654265440 654265453
    0x309030403081b0a0b071404031e030c0605190609020c1507090302030d080702010c03051b0705010209031203100602060f04062325020a0c03032708011e0203040203 72
    0x12901d000906854000d003042000207081420b00a00b452a10101618030494000400030001e80c800c0401031f00d248113400701c0d4101415a100e000400424856620105291448000606028034040c08103554441c0b4248040d00e854a240d440c6a41c20a461150070390400a0102e1115828001d503241044003200419296135011800b1038051405003c400610100041c08405038805002c080030030705017030326283c100341050304000342164040750000c4109843e100911551110135010000002c0307061200c0b139111109801d10030b0092280d0b8030a998035100d075000d070100c080c0061b00a144142c1400e0410038609654041c140d80b01d0000310b40e8861031141c1031000500160f03072a800250703000a44c020542203491015003464100c0b41c1604d412502c02c5120a80b42c552804c000310385010203110b84082e10711202503680d031108541d810300000b0140130151041240752005003490300340925105051500290b51002d649008000094410340c0007414507240c00c0440c21240201c9000d03c2d13024004100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 654267940 1250 654266690 654266693
    0x3090f0f0d030c1e3e060c0106080106081006060215010e0c041d150301060f051215040f03030b0604120b0601200f0c0f031b010912050a0204110309030403 68
    0xc0c40108400102c44c54054003100c11000d21950b107600803040c0c07041001009551040c40c1c4d101c0d09081410341242c0302e420312600711042d2014050714000c0f0b001d05403000744c3ca9041c0b8020586c05094240c1107440c80d5864103d001800c0e520000e00041e1f1000d4007501040096141d2804984840c4040e61180c0725190301301c010081d06400070741c0f42c1d034400900103600303003003645409101110540c002d24401c03d00d030000c1c040c0480704483c0350800880e42c00890080040614000740c503443c08600344102c0c4d00c50f400c078201c0008009001d000e08880e03450000b5255003186420301d0202d2480d5004d04080c0c0c0086d10f416044021400c1c00011541a03c00c2c100c003a43e00190b540d61201d494810040c503190420448200668034030100403007960308500201c0140455200751648580f4010380c12191a202b8019000d5102e9251000300e21100e610301c1a450340001082e5460043c2c42c0c0d40e100d644414884041800309009000300800c0201034184211424051541c035015244101d00041e0344418045c0c204110410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 654269190 1250 654267940 654267947
    0x303091c02100c051308012d1419050a061412160f0315110703111510180e0705010e13051812071e02030c0d030203090f0f0d03 56
    0x51210515104480e002540054078800f520031800c01c41d800701d0300104501600c406118070180142554030020800400c6140d4500300584c4c0d10f41280c000c8070419103841280e04115080144611105e2201e030f0700c181804100f400541941994121940c2c0c50000402c04000b40c03409103604488070711006004031412002000340d040070b00b90300d01002d88101c00d0401c1c1044001042440142003008100c12114510708041403821403c3c8039001d4100c0c58003c1c5210580c1d001010b490881d03806141144e800242c01809034607203800c1d10b07008801480348201700030225122804000664031380c00640c255080c4141803a60580f800c890883c5aa604001d405000d15442403000d584104801800e428141c038846811204a400c1600e40e407250707114805c4550700d900b02c200090818105c5502149243c40e03544c1c0c49400e801d40328220041d0242c1c80301201d14080d594108040c000b24800180100040c014501d0007035602e502c0880124003500d49403001e003105182c1440130440d8107501502040101c0041d903000ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 654270440 1250 654269190 654269233
    0x31003050d111509010f0608031e090913020607061b09230603070909020403050c120d050706090212030a030b0f010e03031b0a0f030e0a050909030702042d06031103030309 75
    0x40a0540d41e5280d446e1010b6040d005040003814210059617641035940c0101d00a108440688040302c0010010810142c40b40300c100303680505401c14000d8401d9451002a044e44038191020305020b04114202c122261803c11010382110700c1c4d180d0a610710350f0b941d01000341400c061520041c00030504290f42c50390038018021036009850345082000c060f00e071804407080b0b0b00300c0e0300161059440074091000a0900070184030845121000030178010314050b2004002e481003030707402007015032074080c007900b1511a8006a0803100008058a4079503108843c020014004d2040f5203214080c60030400e6855401944c46180104025008e14945404025414100d550b240000042c0344160310140000c07400e55120b0304070301c074805e81d904820707007000000304901c0310142d80240e40b241c0c041c003091000c0500004122400c25505071800310341c09400c00740d50210380e0002c40ba000707607058103040403004119150380068140d034410500a81c0f804500f00525a81340002c6400d02070513030001078602c402d08440c0111 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 654271690 1250 654270440 654270451
    0xf06120b060d180c060503010f090b0609150309060c1e071b06050d060f260c09010b09090c031006140d0603030807030b03010b0102250803031003050d1115 68
    0x41d1450805004041c900301c5140d8810498481c100301e040e4800c2002d101d4034480180141c1c9400c50555041910680c00040584224281c00d683c0c3d0310400c0d100c0e260fa00035591991401031134032115000340c24011042c1d500841784102c05004100000d915110320310b09070b51040c0d41d015030404000700c14072211981030b880020142e94490103090103201180511151201907c025a105501d5031807955421041c1c6206030020202059012000d21064003401e20001d15800c12449040d0310381000c49110307003003241d061003c580000c401c07000810801da94030010b10f81c030a8161419400d035960041030f41c0541c00180c0d0700c125503200f000d0040080b50312503071101c5058041074480b540340c201c501c4181c6049903001d510442c007042c0000300300040350340c252184500f401420740c028004e075401440000e4a4212200030410300c0c140c120306511440e01c070082140c015118804c2200d80c0e0703042c610100d9080a11600c01110b00e842802c6144298510403082400c640030390303d00070001015080030480030030200411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 654272940 1250 654271690 654271699
    0x70806060d050c04020c011b0318020d1103161a16020906060c060a1a091b03090f03070819090b120601050c030d0e07080d0e060a0905030d1205010f06120b 68
    0x9480c0c02c0b56130780d1009103440d240e880300005080702d900e4940c5010f92022a0008103061030502d8102820b85121418a865a4121090900c9403198900f0a03a41540b1600c090b81512480101e9900c05806015500c2030314081c2603d00e4854071907010780c4026108a603028106440c8001c80f940050030000f140c0c4c0c0e0020002043d181c20440c004c042e162401100b141d0341d110498940d00080b402c0e22546c44000b0240009540c9103446107010400c0c03070f180001c0140104202040000014854003040c81203034180c0c0c41140603a035842c070984c1000c01c41a0020710f940c68148802c0c14914125601840100c807c45404009807800c204100803240d045150052405061103010014089000070030b10003020890f4240f40001030f05500d40c42c1c05442c0041079000340300e4a501c40100300550540084a4006201040702c009a4600000f241200d407854594413154041c414190041349240d0070101d0070445180000c401c20190b80d94001100a0801d41d00c2600041036108902d01da00c0d41c01500f062118000c00351 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 654274190 1250 654272940 654272953
    0x50a0b0a0203070506040602130509071d0a050d0b011404020301062a06020d0c080702120414030a080304080d0b18010308031003020a1205160305061801060305070b07110102070806060d05 82
    0x2c60315424480c4c111030031517000342d000030b8540300f0916278000000a4a000d55100e2864070780f84401912074002078100407900b610b40202c4c0c8520f80d681c030001c1000390001038030703041030405107203000107030b80d0020300402d92140c0820701c850303005042034429a0704940545c0e6500405071328040d0501024001603400d84a140c2420400d0f50206103207000070280400c05940000d00c804620200500000000d400303002150015039252440c0c4c800c0e031050310305513442e40b8514007d0110200000e80b5000c003007500107000850100c100f0041c000d051011b000065a00d02d814083c03043e5510420811040e8884035803010305420005001180d540c8010315440014410f0305401c0d591a5000900d10743d00b56442007820501d00768024040100174028002d2100c50f008864000c28190340d162612000b006000001075558515010888e20094024000030340d00801a02c01d01038880711010038aa06c22841580c0c80d08104840043d00d520006205003202c1d040f03000b0780042d441c0d0404100c81166105026100c41c030425 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 654275440 1250 654274190 654274193
    0x30606181908010506030703210509040c09050306011e2d080d02071a040302101b05070501090506070308060603100e160809030c0c1c0f1203060807050a0b0a020307 72
    0x1400107000710807040001500620b000c4416007940c100510b418081d40001c1d00400c001a008844101c025031905120b660612580e5000c0307549010301c81c2100c1d40903040c4034148180130b40015090080e60016030a64005a0b00d448210810404138005440300703070700000d010403501d0004a22000e1900f0440600f50166000040154903490550494010f5803c1040850344c001e80400c5080002d00f41140301541d8032084003485060b501440c400640100d404002611485200300802003408200c240011142041818000c0e034840080c0561070102d40c01010200e40c0d840d162050320100c940c5951964000e65954040c00100d41010f410b0081000448101050b50344280380f16900c9044004080c8031508503441c00202460406031041c1c950350010400d94604000100f80112a4481600c0c22007801c0e9808007001c500f40502507001e01840c1d54074030310700200100d04a02c02040591a40c00b0b0207803503210011203803a00c0140c071030141d10120004042020202ea10058000c031500340c01601d003810801d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 654276690 1250 654275440 654275449
    0x1005031f0302060c07080601060309050309040510030c0e011505030c19020709020a17011401050a030513060203042f1806031e070612050f0a020d06080714120a0803060618 75
    0x51303000100d50b600041000e001000e404c0004500511140c0350a200c00f00c50343e26035035264468805020b004da40c0354000103112520807100e24004650149000e06142e98a9400a200300c1080c0209181041d003510030f0140c0c1031003042904d0064250711202071500d84504203900180300341782485800d50203000e0b4000762140c1284041d1030050040e8441d603040f04c0d80d0341d032044100c0105030004981541e0b1218154202c0e60f00c481a549140828100040d1031345403100e803003140d260407001c01000c20307000104100401080030340e07010005803c2110401e02008030840c8525242e41017140c1a00481c502c040350243c0204c16041b141c10802c05020f40b0080782600d9440e02c0c001510515003052075101120421502d60b221004003081e002241c400c0106041500b00b1f1140e140c405003080072003030303000706d00d2404450a40d0300c108000e00900c42150b00040d69414500300e805041c0c0c620521582c3d990360f0841c04020040750480055610411a624690750241001388507009184541d0100b242055042c2d429180d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 654277940 1250 654276690 654276697
    0x4060915020a0806060705030a050d061a07020306060f090721060906030b010e0c030a0c0302160303050612030309060610020f1b1e130f110f04080c1005031f030206 72
    0x400260355224038100292a501004c4d00f2580075050130401c1401240010043c0c4a03c10441c1ca0259036450003e43c03002c001d0310380354000d21070b0800e012008483e20300e13900c0000d0003020f2090341950712a42d15002000003032520340c02440d4005e1802c4000a84483c450400d1005e10007824003004c46580e4202d00c0301040b105c03036801155189544182c1402408140c004050040c0b1011884401910f0008001c009601001c0d28010240340c4421280075200e0190301646c00300a41d0040d189544d08490600a000d41001d66030240521520303001c1d8002a68084100c0e4843c4003040c000300990b8032a603050000342e19480c0d07603860841c090b00c2800302110380c00380305042c4a443c40a40d608100d06012003000a8140310040480704d02c0000341400a01ea22070002204000d0915000051603445000e030f0100a01035005650444000004139001c91410701c1300a4425140c000c4122114909600d0a201101d40c1c0707007240302c0200e9070510005125440109081e10142f00c0990b0516039241d41e60b000c58060741 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 654279190 1250 654277940 654277973
    0x5062d071505040611130e060f06070b0604050a0b0105070f080903031b06060f0d170c070f0306140105090414030706020c0a0b070f12020c03090a0611190c050405040609 74
    0x5860300c2c14803080c0711003402482d4428030700f00702251a280c910702280300c1040b61407003030300352102064002030210340d00e0040041059002610440d900c0708c562a11050042c1c1c12038405d48a145058041445821903109036480110103031120f44ca40311960321124108123161400701c4039010104500e04d01510240040d00c803031400c600001c0d0800c546c882e001c6080100007481c19002d400c0045030a40b09a4560001c4e4000c07a41124a01580e00b91644044d22544107041d8411082d110300440006c10000e948014811280107074803c01841007600011380d0501000c0c030491780d006168102007004103130031225071522160300d8003c82e85402c1d02965841c0036170300034120120031030700104031140500c040f16010319840f040034078144001c107145003409440010f40b071b5a0741400b83d40c04695000101001c004482405000518042045948020007030041910080c50b004c03034000c1149011040541c681e80d900308681c040c0074034002d075040c80d081c0b200a110042042c5c1d94107446940350b001003511000c1e4034a40340f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 654280440 1250 654279190 654279233
    0x313060b0d050106270b0a09091505071805100f08180115060e03010b060301170f3306010507020d030519051b070e040b0702160603140105062d07 64
    0x104203041e03804511708100003402c0c5481307041490392070655a40715070010558040e0940000c0c0d180d11402c0042c0882c0c2a15410401035241c002404a0250000320b40c00c10307003002c0c0c0800b182a036141d40a001c2d041d00524230301008542590000710301d29005583d100e901050101034110000c60711030f0481d09403054045142b4280d90000710a03c520b540c0400a03207252082500240103200d000b8011a010784014030890406ca41407006401000606108480b9052200000c9400d0071f03018440884000b0740041a0705900701c3c260b000c1a08102902c2d003514441c040503121a401e00e0340c00c0d001d00541541940f000c5042040c10400311041044a840070290840e480d0f9503070380c07a180b00c0c600740c0f00421180d269104055000c40802c005104950908640c003aa20014003070468441c1d80b800da10f40380000880c042c0380d11440002240d136a500d903120300000480c031400d21520ba41d031041800070a1080000c2d04401850ba00c00042c055912901c0340c0e0408a0710749071003440d0941c6034449449061422022003001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 654281690 1250 654280440 654280469
    0x2d06030c030c0f020703060b041808030f100303090b0307031b030605270103021c0507080f0714010c0f110d0303140c030106090314011803020a060608030313060b0d050106 75
    0x840307525124800c000a01030500d0300200c10300c9074000c4d40c0c0f44250b200041819480c1c070380365903007070301c1340c0d040000d480341c03090142c0318521360625040e01c2a400032901e1100c40000035000504d800c0440b00d2910449030161200d01200d420025090000e0340014500350615858907400c0030400c04118103008442d20300e0b98005031841c03c0c40b04000403035500702038000d20902100c5082d002004e0010000d030440754100c82140324100c41c1d1800400f101001030014155010b030010000d0580b0300030803001c00c1083c24000f42c6519a0310b03504a00c10015031134400382d00140f0b8014803031000649070b40384051014040c62064280c0016000003030384507000d6003811000261685001c696078144040c1154112401c820010304643c103045004012031102d11000d0000101950305007010002980002005180131140d501c0080795810003039503809503000100c80d414a00000015101d201000b5a0302549404004214448550319008080c051401c0c55642c06a03441e0303401000a082480b60000a0040c1d0380030412 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 654282940 1250 654281690 654281711
    0x3311031605010e0f3405030f070303030608031c0b36090f0c011805040906050609070c0209060105071e060c0212030601050a032c010204081e06012d0603 67
    0x41220804e8080e0560f408591040341103130307401d1203a00410000c1024003ca02030fa9444042080815501054050081e000d9402c2c0700341c0049403038000c1d24080d40701400722030780d83e00510b592031280d5011800b214043e20b500c4980030b9030030b4001c82e180c040000d15003200c0c2c0001c40c0900304050100d40010344580c80000500300c0326480001402e0b070020a250180c0445054040d190b6180c00c2d04071030850422204200d00c2890304c01d003108400281c500a001000508035a2034208003d14083d14030611030b1003071800280c24544500404035950741d01030085801da85820300151400d4001d1903086138600001c0c240e41140001c00010500b103a030181401081c00d02503140042c1c00d140c174041c003824141c0420000c0100c6030b42c00c070080360289102d625002442e0811302040d5881f40c120b07030544107204081d08400c0d0800050540103402620800e409495903002e29444441c2c1422005042800640103a0010050704602900300e911080042907170705031081407411480b12040d2580c001e0400b00e99100c040300c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 654284190 1250 654282940 654282943
    0x1623010c0f180e010b03040804030b150414060307050103020315120610050901030503120709080118030e01030c32130807060f0c06050c0d0c093311031605010e 70
    0xb10ba00d42c044010100d01410240c148004220502a4880031900040410204440001101c0041d600079503402ca407030074500b031036104941202440c0d601c5941805a4100b100303801c241006c2c02203000500034070f9000d14100c015806904010801c000a42d500c8490035025250103928980941070000a41149d01d056026030312224010741000f806240e83c1c030300500012380e00004a985845212403103213400e64642500f12030304023640c0c200d030320f45500703050b0600503000d442029004058441e440300428150034600450460364000d40000010310111000b144500d1003101c4012080d40310f402002d03600410714070342000ca520500b000f00c08590052005c00c9089001e0140c07002030082d5180c0118110041c1c18000c2044c0d02c0d10310017524136039451011588401d455000c0300c080c48444c40c002d004290b5211005071200c1264411100d0a1800d2000c2d80000d080c2c0000c000e455070443d06171401c0c1000c040000710f442040030b40c80c00c241b511042000160301124140380700d002620600011400052400b00903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 654285440 1250 654284190 654284207
    0x5010f02040906210302060f0423060402100e0f06070602130b030115090e06190f060c0b012112020312040609051005071e020a08041d07051623010c0f 66
    0x200382c0c24464107804e40080d038081407003a081605800002026111414601c0034008030417080f544040da440c07400d014155010440300d101c0d41c002c80d05040000940c803415a2509c48c4540841e5002c28114000809440c18030040c2c050580140c0b001818440e0400b50540d418601d500301c0104072501100401c4640c090354910114090f452809000c41403812400340160100a005580314844007130042175040f01e2044504e0042405014060b00a591880d014101e001e5031201520300d1150400003280c1c920320740c450034004c01141840c00c5121651920f0380c0003900b030b66075010411800100080c18107015590310f11401350340034480006507807006150940c0703440150600c549a107410541040200758000c241c80d80902c00300c440001c0c070760365907003402c17030802c0c00c5031f00000c206039004100418040b003642e02d04004031044441714105500c074140c09840501a074030520320b000b003014000d040040d4030041442c100c1859609280310a45569804a080d60144119a000200b442119011766588886e03032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 654286690 1250 654285440 654285479
    0xc060e0615031b0a06050306060c0a06230f01031b080303100608090c1e0a180203070311030408191b140d172a1b150c030a050405010f02040906 63
    0x648044010340c3c04100c44031a1446400140075005c80080d07850b40711001214080c42c00c182c03d0719550100e80c07402100802646244010043c504c81c20100d203800c80680280c06448854030740c540c207a29541c0c4051045102031301d001ca208405500015022400700059070203801070341e03001101c250400d50700400409004152240c25408a40c1780c8400f922103c0c045c402440b4000260200c107a060b6010914015140c0d00600b0048403800c1c8006901c02164065070140d103640c1c3e000d00540010746208a100c2c0810b03a1b000c1c0941d074080010211090301381014900050039402c0c60f222480c0d41c03424010031001d039804280c401801203880544003a0013070010003a83d10040c1807044044010009400881b40c004041d0002e0b4480e18005006010585280b0b92070010400c2c42203544010410078100c0c0380001810314083e070f21500c5001140c070001841e0340d82c0704072441c6100600f950340d109420340c060500078200b0b40d0b055590f00660b4840d900c0c0c43c00288041c09228001249407460401500504444040d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 654287940 1250 654286690 654286723
    0x9151e04061e0207080d030f060b03010317070f1416061d12160815012103030c120623030102090a060c03050903160602060901060509070c060e061503 66
    0x400d01010340c100824100a8074941d4101c24401003400d4103070300d4001c4d00d4200c001d036846040d21002e040e1303a068000000d008501e0300b00f44100c59646a041065000a0200401c09071403080c3c1d90344c0101450001c0e1030036600400c049020041c040d2500882c00300c1c00c1e00c130300d2015080306406041145081c070024008000e1407419a0920320790440d4041050701c0401550b120f00e8003114031a0f004a810003502ca542ca5900c80100c04070307540e80c50032555402c4403025000c8200c903008000a07895182d903a9000c1c0e03044040044820568450350110014a004001e5030180021034815030480b00082c8141e2001d41000d6200c14030180c4030350000c0c0698002142050b100c1d030300404c01c2c0d2180e500c800c0c10100480d126030800c010390324824a810ba419000c0c03c40300301e0305441409080c0058603074160342a4201c40340d680961f8480d4850003201400e0752314134055260406140c8000c144030324401d13282c0150890181c200002c0580c0440c0c6068244030040c0c071603250290280082c42003d15050050b444400300926 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 654289190 1250 654287940 654287947
    0x2090c090a030326270c060a090303110105040803152205010501140301150e030709020703030f0605120c010e04020c011437020901030b120a0b1006120b0609151e 71
    0x489400e009000d0317880b035400f41130302500d07003022a176800c1000404080009102546521070810000c01c1164188002e13030000d181404070200d5080113204043c041d0b50001c05070340c95542c07000b1b91500414010401d280d044005102c985007448112a100032030742d00b01190100321549000001040700188032070381d1440680800c01001040c1c8201c065900400726801c0a445079482e48001030308102556001c29195400090030908043e81980004110601880100a62a100d20501c844032060301040c401c0360303219001c1000c031507004001c1c600001e50014405450910714901305820340d8034000008030000310316000d2105210403825807201a1000d402122403007100c0b80c0840300810201440c18207a1a400600700819911903000301861940207055203158114201c1441d94840f001e09040e0f0300486c8402c081781c05000448802d0044906958035040841001640303a030003041298050b99000404204031165500d031181500540c03414000c2c102e44400f122000f03051005050f407800e034044082003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 654290440 1250 654289190 654289201
    0x1501031202030921070302120a0b15030d12320a0b010804060b030304051807020601060513060302250305120a0c09060c03120623060c0a02090c090a030326 68
    0x6a851213084602d101c50000740c140610500f420420280c00181d0414110132108221910014002e103450340300b13016440300d55540c64882109086c00b6011994590460780311004454400e0310038414001041100203184a40c45400c40703c020382500b0340c0101c0801800c889030b40c4105c80809254800004901880310716000400242481c07802031006000030b60350145690385407020000e131005810080c2c805902444464406200d540c000c07162403005105820000c100c0612810540d001000c2e00312a01c4000341c10000706601039005403541008103030f103100c00341c10188030660354410550702036211603681d00d41e40400500c540d40004c15503000f0030704004020711007581c4852074508071181481c000035190b61320326003101c5041c104582d00000c0c03400c1c4407011800d00e030185040082d0024459900c1c103c003600c941444513901440782401600c0d0042c50314540907040107100c2c5617003c0c070810506403400401e00005010b800c41360704240d0001d80c0309007481d8102d05400d50004200000d100310802c4d9440c02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 654291690 1250 654290440 654290449
    0x120f0621080405090907080a140607020f070b09040b0d140d0c050a0204090303140f010807080a0507120c03080310031e0f0213060f0e040c060f0e01050702011115010312020309 77
    0x45200b094020710014000444c0501c06001b150007a02460054507400c14184c01c1107603103280c1c147d40d600740343e01a1001180c940c81c000140e1a0b41c2d000004043d10300c1ca481d004141d20203070440791802e42c0081d19031000480e180c0d203004400c060f00b440b0b10651050100d610856526201d240e403854414030420300e803e0004642c000400176400380c1d04481c00300d1074904a24084020b00002504840c0a05e50307030050000090070310748454142c40150703049500460b0303100b0300c0a5a888143c0c43c09800c580140343c1c24480491645010b0910a0044034920880c50341c994507103206610840b03e05807240a504010b10801603840746030030a4051030858803081a2080c2c0b41d020f644c4e2214600288101c03228460300c001d220700c80c1c010500074091008105e40d615070f10510703140301c1d2404440442d0322070303c0740300085089070050004c60403000391a6501e01c00408100015607142d400400b0036410312503400f40c54010303038404011284000d030584074206c610394035510b0700716180500040480d0641d0000c3c00f22071030903201c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 654292940 1250 654291690 654291697
    0xc030506010804210e041a040e160e10032a12080a08150a0905090609190305030603072403200904020306040f0204170705041a10120f062108 62
    0xc018051508400704540513651003040717000e15a0043e05042c88407060781148510382040b8081501d0601c64400f800d800c1036219002c0b88030500e02174a01d19424408600620f503080e5009201c01c2808205984a40303035081d100d2903918510046900d00c4110351824800ca4030210010300d103440b158000548a5598034840d0b0241c90488002c000b42d8500040131070482101904101d0741c0038250000307403030319060b00f036014050031a50031341c2c0c91050002240340140000340c002c10002040102c0c001950407070347c0850703032540068001079061080d0880881c0000e003214149001d40b20450505003941c2c0760000290a9680400030641c1200040ea103030b001190307205003281c80040045800503600c0c0e0f80c0c04005002020482c1e40b100011b80302007000f0034841b0f003108607206140c01c185c003107c1d0401d42e10700400044d01d07030a2507100c01c0c8610708941903915090011034003c801d800c90074000e8580c81421064422113050501c40e00500f40c94100403c030104540e981016415030788a9505240d40240d26140f020b4030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 654294190 1250 654292940 654292973
    0x903080f0c010b0a06020109063b01020d021204050f1204060e0414070c1b0501050406030f0212070e040c03020f03010501110313060c020a06050c0c0f12030c010c030506010804 77
    0x8002500707070078040080d40b000010300303001415100d81d2030325001d000b03000741551202140d54a00d032012064072405c00c005101c060440c0c05038114861300001440400e000030958540c401d964090000749144070041c0080d1620741640d00c0114540d18081c18040d24054501c40d50300c083c0d800c6094200c0d031001f00101241e0584080e420212240d241c1a0701040003007003000780004d00c8913120018001c04c29401403d651550b80207071801e42d09000c840c004043c030740200f44551404140100001c202060007034208100d2000d45180060905411a01100c0342030700803900c0c1ca0010300c0d000104181352500d0312452003400c180345011418541e51110422403440103000301070600012908058001038108121142c00c94030460a45441d0307510304016025401011707040713100f84400000803c0151103641134680300041000244240103c010911101c3c5400b050016001091611002c3d03240c041000103201007800c10000007408440010010300f1030714007400c1075040201c0d00d014072011910a0a134840e658 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 654295440 1250 654294190 654294217
    0x60f04141506040b0705071a0415030c11060f07110d0804350307120c02030304111c050a02030c03120406121b1e0305071b080d110d0c090308 62
    0x580100041140c000c50340136560240c000075070402040f102040301012181e144101307002d070540600c184491800341b4064100b070140348004034110316220341c03c50451004c1c907085c0740f00c1c00c10f404040315060034000c03a9a00450a810010310166039409982d0a11040d80800038000441c55130314002c220400117040039000e001198403843c0c0280c01c240e00940340c4c0c8510559103007400340c0103c101e0f15a41003101d192380442c0d444e40091141400034041e9150000c0303503601540c51070b07440340c1e0344004500807814042c0d0850b6200c407002c80954070b03104031001400c1c02a402844036161500c101450f04a5200132103010782c201c00a0100c03080c1644d425141aa030032800d1600c0610544d101d1030f0002c04017034503102e400c0c03400140c0c2a0303000b5400011400c4099907400700c0c1008022000002e40551300140c0720200003840b280e80d11000c15150700358041a562040d401c591415180c1c0c6e011005a03101c0e803410894003000001c042d03225601c58840d8070303101c8106040050060f843d50301d917820240140c480c581d100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 654296690 1250 654295440 654295471
    0x702030c030d0207030506090604031e18080c13181205070203150106030e0607020318030304030b070503190c050306060702030c0d03080133030b01051e03060f0414 72
    0x115901805030001206001e4100c42e1000d80c40e010080d81c880851005031298015680811242e46010403200e20550300354035804408111090580d100c2820030703490170700300401c1c021081800102406043d000b00500c10092607564100320030030450b10501c800c045801d500c3d205030400c010500e07800d80400c0c160000c900e034240206101c4141e81c240700e6000001c3d498021012002048003510040c80e041c3c0e5515a401c2180f03031080700095665110581700800981c0c02800341d000070107405074244011075000342c140c1e030070f01d0350742d945484003100140c80e29404140701008000800048902d4551b105078810000d02c0300340354130080a42039100191015001e40400100e04003036407010424104000c201a181d41d4240405042c0103221040a000340a0360880016403404101c2550375040c480c1081070300c004008107054a8168000c01d180c030a01d40c1802014003500c440d680800c071f2440c201d82c1c07095584079505d1810b4000c002207903102143d050310542c6440080c0c41c0380180c000308194880011302d0400300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 654297940 1250 654296690 654296693
    0x3070b040f0c030b1e0a140c1309052d040c180209280906080303010b18100f080c03010b0d0504022b0209011401052b020a0c0210091a07 60
    0xb0141c1075504040e140405000c20b00481c421070034002c04072401c1019100d50340d9140c00170b42c281030344c0303000d5025000544d07000e002c145006200c40c01007081c6061030007010101642c41660380140c45003110510b00403100782d02d848484103000c50000134800d040080c03d80e0f861501d641c9009a104c5180600013214101110314080800c1e030b641252901d060080100191607011841c0101d403c4002821070b801c21480c45002076107058a000d19030540b082100910306503820038413072056980000d1920b05400c42920080d155a8480626500c7c07410b0050b82d03900c1a982400402520514001c1c081c0100b41c0420001005590310300310a46070002801180807800c0d41303650000608010780c10b031020b4620174040c80c00028180f0b05030070b903031100342c03094649803641da99440005804a03411100c80e404100c0400801100d816020418644030340e100042d4001c4180e14178004040f038106610100100302e803d5462000d600c4c0c0f0030b00d69940140c0a107800c054803030411001000d0803a0a8500c5403160038049200c2d0b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 654299190 1250 654297940 654297953
    0xd0606030626070e0a140109090201170702151f06091e062c0303130503010e030a171008100c030e0705011202070303201e090906150c0f0d02010e03070b040f 69
    0x400700a2500307900303446c550712452604002c0441017400c0b4041401109924a62408801404d100b4000d83d0050b00040b85010102c1c2c0000301e00502c1c0002480b682c0c1c0400708003400708046c00000c0d101ca951808005828400f800284100740c440001c08210440d808102e0a0b5028900c00ba540c156440038541c6241c0441ca04110500c40d1507000b031b03140c000401d8940944203005801001c42d0402c034000d00541e0580820503807a4410415094002070203210150000707107403495000e03081036105100e61078071540c0f20f00c1141400c1080c400d50701b00d503483d40d602c0d203c1598540140724900700507402a0492910748070001c0c0c1810840c10450b1030245c0c0108124040c140294810038412600d0441e842c1414000b0407a28903a070301c100c1806086450368801030011018613029901d07555800b8040c90125120031041040e4081c020b504146d00c0202002840321640b02440100701c00c58104005210000c551074020b400d40301c558642078842c0d4002e10001020035001004540c11541087e01e08040103e18140342 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 654300440 1250 654299190 654299201
    0x12901020a05100b01020d0503060303090405090f0a0f060b030609070e071209050a02042003060910090207050a030305070c03020a081b0f0c0f010503010803031b0d0606030626070e0a 80
    0xd0315600407201601040241c3d9000743c0c140600036070a03902400300803c41541e260100365031664055105200040f0241040d40c001d80e0410040d104803505424a00c0d8454901102500c4c02c50702c4111450a41e010000c1e5801040401c4604074064042460416422a82c1d46158802c0304440c3c009007020444442c050601c00304052410303102130201d50b0702c9081055031076032036040403400341b460614400915003056050241404e18149030328556200d0b1801c11140100240802c907094080c2100020703002050f2004111003071080026002e4441e207800c01a040b10001012003041c01010103a210019901189600209502201980c0c80d000c1108019400022410005803588a070040c2140e04890010380d00d450300f101122a54607002d42d110045a680c0000c0c41858185da0040c03000c14452402001d407942c44280400006040c0071541544409844c00356008001095441b482484401135103a0122480400d41c00c168074004402d0400d00e1b52902c5501c00c9000100142c00810012801038204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 654301690 1250 654300440 654300443
    0x70506070c1b06022b0f030b0105120f0a0b09160c140601080604050d1b03030b030c060d0b090f130b04080d050a0204050f010908062202030d1e02012901020a 69
    0x40b0b10355030701c0381d10180d51050f4560742e60582283e02c40f907000d0b01c0503040f650141020366039555540100785032a01a005481c004201c581400420b1241560000341a01598421120a8051800c60070890482c104444040e5075182c05150203e0406c000b06828913006880b0510b1481d1500e003c40d014148807400e518440c2d010149802150000038101c540000e003503020700d0042054800c0d0b980340810a884140d4a41c002c0c02c805d00102c01101d010038001d0b440070b00000300160a0390664218a800100f140c0c0c802901004241d5a400e001c40301401d105400542c000f0042c00383e00401c0c10110a0b081420703920f01c0d8020280a036000c0081e00300202407041e07a081110110080c031071802c0c002d4518001c1c0d0041c1c0a0a40280583c1c3d0302040b05610a800190031114080c000d89040d41309c50b000383c11140030301c10201000340c01c140c444000580382045018084200c50343c0c1c0c041c440080d00700c000103840d0802940c0c03045a05092619143c07030790f10750038246005c0c1c0c0240220b041090500c0180e0508203030070380 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 654302940 1250 654301690 654301733
    0x60318030503131505090f0f07140103110d0507030638030403090b030c0403120c0b07030e0a05070e060405180c0616050a0506070e0402040303170a060e0a060f050402070506070c 78
    0x1d0040c44000040c407c164222108265442031494039160340c3d03030302c02610504210f06201c08856005500035840504100c4109040c1e614010280644d0307001d60340155080c8001a41d20030f402c10480c0c0c45204d200c40136a1554030076250341d0b4150050000c000c442240100384550b400801b00f41018011120382c0028a180e00c0b8250b00c900d072500e42c54009800034401580d0200170b58a0780000c90784036210981e619136104030060032a07202d500c4110000c0601a1002070a44203d54124001c61400c104142c010082016241d08510b0301e05c00703020170745102424451003071490401c00c40000001081722000a08152103003a1240160141e14400071002b0030b001d0181d004000c42c1605100c0041801441410240c6900c004455090f0610081b8403440c4000b40c006035088a0308410700c24200d00d0660040360665020860948445400603218429a182d402458dc1c883e010440d86001201c0c6c02c2c0140011101182094103a84500d92502c900621100c20080700010740b90402c171610803403141407802032a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 654304190 1250 654302940 654302951
    0xc0c0b0709090501140102031204060b1305090f0303060607060f0b0d08070303110a2003070b070f030506060406120504060905030c01020901022a31060603180305031315 74
    0xc1016000c0019070051a240301c0c1000000301e4181d086543c0c1121070041a0b008528010828010710b142e1100034008079140da48035152048150364140c810000c60300d130350300002401e091000c80c1514203a460310503081c1a4006000f0810f09035110401d4400458000801190040f0588580c01c000d11092529691004d110b4990009000d084009055282d1085d01c0c1000070407488189801036008000c0350700c000400130b000b5581001046070000c111a0424000c82c2c1c10080e150b07807031501444080b5900e50001d400071011020080d0725008054100c14255a81b40c9050300307040000b40341e2041d40d942d400050b030b00ca001090400c59154014400d441d003210680c0d80710004450b00314081d600c0780034240d00512a0000c2a41c8141c10100a450200444001c0d24245600c51003405521000302c04584044da5401150002c1740d003540d0082ca5010b01035410000307071142046805021141220b649601003107510514000094102c01141e42051008a21086900c81c0b440d0410620340b10a40304c050f62130409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 654305440 1250 654304190 654304201
    0x50a06024c0b1816020f0f030a1b0f03030e0f10020406030f050c03161202040f1701050f0712060302060c03031506130501031d0109030e01140c0a060c0c0b 68
    0x11000140403a0804205010a400080c100301d43d204002e050b000c0c00084400103c0c484080c0c4900180f4034040714015a03081c030b02103c2d001420070721040c41c1008207820000c0c84980c0c00d40d11583c80c14010f4846000d85010b0901350310ac41038141400340c001818140d850030400d080c05810040241c0c0100c3c5c050485140b1421000c0c0e0300080d40041c070402c00401c0c00e040320782001003600c1c080c15102d1000415420300390790380d2101080801c01442c24110a05c034900d00c0d920304150140c0004c0005e000042c1070912018540b101e14180f030101c1c16038104999150201380f25080b110b0411998002c007040c5080b4100c02c204000500041c105507000030750010000407202c50030600030014510954041c048514040c0c00b0030b0070b114481c890140070a80501e51007030180b05642c0a03600001800c1c0103d0710f4400144400d9010b00d0844402c20003e4011031050a0040c90b550307030001030034031104901142c041c18050b00758540d030b070354802d030080040c82c1070b4072400000e880922a500103031290b90400c54412090074074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 654306690 1250 654305440 654305563
    0xd0218040c0e07020111090d020612040b040201020d03020c0c0f03070906031b0f21150608010203190614270f1006052109120c1501050a0602 62
    0x45104044021182c034001910050041c4685030100b0311008643d40b6244058081201045040d0740482c1c0c404410702c00204984203917602c0710302c40ca1260800481a04242c000a46060f5526108000300341c01041041c10310140071984031440e0701d05403121440b90410380006400c2c1115600034110052130311400006114840c3c21041c0b0b260507208281000c0c0340c6610503034142c589140624601004040b5401d1600c01140c05100e40540c080c200300e0b40b9200e142d00c403400c1650740c581d004020380d039008800e200079078140040c0040b40e5034072914104030311840c00c3c0d1a08440034040303041c94490745e01010400010102c1440301800b508402941001c0e40c60b0a941ca0a101e130002c0d03940c1401400000c40100795103018208641070404030010000642480344140751072110000e211a6150207040700015041c00c2841c0604a0000450040c150780482d001d105004500140d008901c1103110341001c000c0e0b1500882ca100c000c8040c140040032074841c115451016082c2e01c0145921900b01c00c40c030b81c540440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 654307940 1250 654306690 654306713
    0xa030209041d030307120b0d030c060c030504050c13020c030406080405070603020406021b0f3a0b0621070b1c02120c0c0705030102040905040b01230d021804 69
    0xc0440d0100080181c0c482d201d102a00000a0010640e00070004034041300d004000420407800307905808141040d40343d0106109180d100812070204403510743d41750070400c42d405104aa62128a010080b92406481c0c2c103036124040726000340034005003200118040076a0f0110350100030081d088941e038a55550300204000401c54058900e4000e00c2e8000c00d134503100b4000c540c2100d41136801801c2450480b00600301079611808800d501c560443c162800d540c9600c202d0b06d421040c00d1140c3e4425141003890785030150001004004c101c0c01c00141e0900190702c00411316082107081d56400401030011140c1c44e0340540400c40a9035034803400c4000681c068003c001011004900076245e11200006480c1d038059004044080380c80841c094000383c10281c94074041e02d0203441a0049410941da11000b1030308980c040e03041020041e80f02d00410040c0305000003098018aa21102c81140103040c10541c4442e40d202202d09118101804d41703132095666400070700000921040c02c0d00164105840d100480300d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 654309190 1250 654307940 654307957
    0xf090b0f0c0f0f0309102d030f0b010203030c030a09140a051204060e10020709060b031e0403050d1104030218070f02010606020c0925090603060503060408040902090310020a0302 78
    0x1040b40c000300d40d403110100b500c51000009900039030074a150b020030860480d000d615041c0c100704c0c00300705e41651090f000303200240c4906140c0c001c042d4080210401420f0320011002d40a80c54101040090b203a6400011680e0000c03000c072540d0b0300ca45429842c00c0c003910340e20720302900e001c4116140001589002c12003c920b188100300700e1702c08400b148030000c0140503501c034420220380304c160040283e00300842c540114039a5407041d20042c548440b0b40c142240c1d92034119401c51074002c02000f00d210215448101010140c20204620b80b6150764002c00500c02c00c0c0020392881c2c4c41341c4100090311407000540e000741d54020003a00158811204140c0e081c101113400070b0009180e174111400b140d00600c18603059944641c003a145880c001010b111521801078030842d81910609569208010215950040780402e0355804115916040004007030391400d130040c40c802c1c0c1181052000040711482142c0031140d0a00c0c000d070300c0c0c1d42070100190929232032400d001c2405000140402546505500600640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 654310440 1250 654309190 654309193
    0x608060d021216061701030b04050c09270a1101050c0c09070804060b04060b09060a0903062a030c05070f0206070b0705130f050d0f050a05150a0c050a0e010f090b0f0c 73
    0x2150355000403640302d40040c03040164050170000610100340d02844003a0710071301030002c545400502c10080b40c000c800441d0f026610700405100c03440c0119403803405c4080b00c201030008003450b00a5449100410341810340580c14060006041c011407a801d010302c0001d0301c0010144603140ca4120340241064004540464030035103003c00507035940c58244a014190b03110030300320a080c54109824050507510011070075090103140c8000000050050242c001a07030210402c4441c001038403c0040641100071041c0c5050504080849c010107910000799048203401030400c01e0704070b1003030002c0741036446000310191202940d5010407d885401c4402090000c480c0d65041c0c41881e030702d40e40d5600e003503030a001e0550710080c08124040410311844041c88128050310070344004400c00e9498901d0701d4000f248030700380000140e0411001c10110710444050301d0320390904910341b03000c40500500b042c03034080e1228148040f50310304804542c4282c1490000e0060184000e58851850080700220341240220380902d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 654311690 1250 654310440 654310483
    0xb060f0117010605090d0b090705010f08011212030e0f070f060507050c1203090306071806091805071101020a05070506161202071106030703230c040608060d0212 71
    0x6951141c1030348115040400010312042c0d0904104444980c0310102c115401140b841d211008203002c184403d00410924000f445102c5c0307007000141206034a032081c03005106030070004100101c103d00d212400c056011000901d0034808810030340003001c100100010b2845505221900c007040050190140c842d8a0660100c1c1a44c4900032590340c8100000141309070082c0200100303d04084241002144006050ba41001540d00100c0d00c0c080080300c406001030795040304c107020031600e0042c08000d0096490824906403c0c10f41154000c01c03200401d07045c503a07440b070000e0042c911034249544248011030080d50384000b549402800e03a045454143d46a010f403002151103107450f242d5082542041d41c0301d01c0203603100d4901000094202030010b589040a0400001d040c1d03442c1d13402140700e0b0300a0303200052a0342c0e040d0070940c0840d41000009004c54a814184408405118141c40c1240c00b2483c0c0744000c0d41e00e800204601d05001c4000a4110317500e5412807003010000f1803c42003000d899084281e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 654312940 1250 654311690 654311719
    0x301060e01080a1b08090a141509010c140315041a150c070b0a1403010e040506090d0203030a0902010212070501140f22020301090b010807060e0105091c02010c0f0b06 73
    0x4607070302d050740140a103010780745500e041da0045c0b2030f85038130072091001c0da2501080c0c0d407551305040340340740f2800d12250081c520030f80b00082c6442c42903800c0a00702d00204281303646c15201601003450007034040b81820f400b2001805051005044002c640030140c014030080c0c9140c0350704d6002c3c040249510b0720480d4900c241c07158110f0b121040d65101d1004a0027031a5107850700c040e240306c503401704660108002003000c101c00c940900200850003460204041d402d985071a0401c1030070b000c4081c000701055004241c048001c1d03980002035a401c51511040010b00780c11900c0141d241c21f5a14011556180000c900c40b003c1c4041035001c204a401c007604400455034410440760000c10701100d07162a900800700705840103131100400d80980c1407000d4000108400c1c5600d8400c1d002100b6402a00203502c60318062240715805180b02c00c411600b0b00381a814900c11100041c611451090b0708840b0b80e044007018000c0d60710441c0c101100a4003e81070341841421800c1002004074110741150050740754804218 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 654314190 1250 654312940 654312961
    0xb030430022506050304050709060b030a0c0f080411030c0301050a05040b06090f0a090822030203010b0d020901170307120201050709050f012721020a0e060306070c15020301060e0108 80
    0x52030040248805680e0810400780d509170800f41c0280c031a0701c503211010401040c0b61240c80e0141081394184d946078504030001d18103590004245108015440c0c0a00000a0f0491255500030303510824070395403078a916011914129017501280e41c035608002c06d005101103a40e0081d4002d40c09040c0440306a903580041c440148000e60b101200b044180c0005610401c2c1607020103003503842800c2e0171f840c084d10009055131007252101105190642e2940030800c501d001d101315a140e146c20b0b592035030500c0103074001403c8004140704d03103000390b0032401e41854a40c200307004644400d0351041c6031404500036068024001d0808895200100b5200c2c4804501890b0a6110ba80c0640050750760000d001407030f80441d0145002074544908142d01002c01240b03c101207503501c04100310390400703070904000500410030b5608881e400801480006000e010240d01e0200784154082e00c0c50a001001107218500b1124102105a010864a00c0400003180403580000340680d55142607981d407416442c0d0f01c030790790b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 654315440 1250 654314190 654314233
    0x12011e0f09020d120207030218071805030a02040f0f020307111002031b090a0e0115021e03070813090609020408060f091b0f0d0503040e130308010b03043002 69
    0x20350b02104810010f000103409100c4120104400c0c0706403454260350390b020412452444a242c0915130f0180100180c0b290b100b00140003205641c204001c46501d08004a52aa0180c200107405946c44000c4000e174086a60081c40c01109015011550380c582038034001c0150f44500220755450043c141030003141000c07030003940d0044e9000b035095900c80be001058540075030300866010780c2001081c600080d00c40d802800c0c7c540200070f40b00180302d59100102000341000c40c2c83d80000824411001e407403200b410000207803181c85030702010160382e64864003e01c01c6510320a500c4041c40c4c5d424084041248045030700a44100c030012012590140c44c0d01507a0203600d2000c0b40c00d141c0c980e015581c46a0841e581d03205d210840700d4041c02c1d01181164290114034001c0321120242d403140d0001404000240074030080683c49441d800544015401c13a6400030103a2206206c0c24040030801f00c081000c0c44140c200d550f2b04001607017030502c951071180303051a140d10284c100075400760003090f0400c600c042010400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 654316546 1106 654315440 654315443
    0xd06020c011404050a03081b04080a020f030303070e15040302040e010207050c0121020d06050d0506060f0625140613020a06171512011e0f09 62
    0x9a90035103a000300c002c1a140c1600b4208404104041840003a095061401412035100c00245084c10b0100c603402c0090b85000080005d100c4d080014108001c034401c1c0c48030341ea8040e00c003040684a0008030f806402150484540702c581e40341400118803c40405011b80c0d050540720b40120307088501c0050780c1400b50390300140d26005d00004000b90009208240b906c180344a1490b400c0d810301e0b032040d4410000041c0c0100b000081c1c034030242c12140140c02d005e482c400c132504050510580d5080241c2c1d0550058a0418600d051b82c10308070120f5840e0680121209504106004240001120b44030140c90444080c00320007500f08040c0042c0e4002c0c480d43d50b0680d0905502c0c01004950f0009038003c1c07042c04118081542c039003051642041d407100a0440302500710208201040c40b00c1e42c0da40c0c82e54a25480e05802c4802011b0b0b40c10641c0c021480e0080c200110081e010f02c0000719130140e0f20 = true := by decide +kernel

theorem cover : BRFrame.Cov 654136690 654316546 := by
  have h0 := BRFrame.cov_init 654136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 654136690 ≤ n) (h2 : n < 654316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
