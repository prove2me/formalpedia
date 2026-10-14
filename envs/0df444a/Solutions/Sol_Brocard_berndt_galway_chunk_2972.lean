-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2972
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:17:36.057539+00:00
-- url     : https://prove2.me/submissions/ba6a3b16-c49e-4b88-9ac4-4cd6d690e419

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 534352517 ≤ n < 534532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 534353767 1250 534352517 534352547
    0x80729030105120a0209070f030f0b0d0204091e03030917071106030a06120c09060501020615130b1e102a02060903060708090c1806010806060c0a03120c 67
    0x40c00c60b4200010042440301e6041ca411551050760029409640c401616070300400094030348280e86002034030060181c403003041040146901d0004903030740c1901c1d41d80002d580c01e47d04031400212030040b45000a26440ba15440c80030000d102012541015010340c0460000760003003400e20314213841011200e4a910a42c00003e0890000c0c0c080040c190401c0382c0a0364005154540100b000b5480c0c0d00070400c4d480040b01c082c0c6680018150810004500c0d02c5400064003082c400341c981271608940c2d0746029855403c402d800380c82165002d4425074110307804520306d400001c112080201c11101c1e990012842072204038811010880300039600c500400c8207003481d41c4041883c200c1c8051580d400c0703c10201c021800e9810502c1000003203210740d000d010f918459510b6455502c120708000280518240c51080694010440d03103446144140c150402e2542c420000d28040b500303541c40001080d07641c060802100198403c1405e004101034111440c0d00300400724204c01c11811502c280119a034000c420501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 534355017 1250 534353767 534353849
    0x6050703120504030c0b220605040204050105010908061303120c110d0f0e0618040c0906020c032406120708010c080a140105240409060e06010903030509010f030b06040807 75
    0x105d0000d50590300f00799001c1d100d40070f104200c2e460394410900c000b520841c100c810f10b60b81d908010461a1a2040170702503d42880d010307a881d81820741e00c0340e4500000d000e03094289080c0000c80c08052058401e10b02d08101c0d0382c0284140518650041d0803115000f1080100f4007a000501c15010320912000030380c041036903204501b64801e0350a00c00207a00500185c14240f01820842c400c81c4c0360340c058203021200640d04d010080c2d2412000908001c5045141446500021105091104c802d552112483c2a40e202880540c64000000e0bd9401800c000715040703010703400700041c4001c0306601504103200782d91900021a5550b800a800301c40c600801901980340030f400511481c2085440ca03c01c000c0408a50900c02a0385440107800790400d0340407801c2241c071150288071000300945d44c2030b048642801c0c8901c0d801e085550141c003500640445030304110031000824455440f80d00300c00b80400d40a01642e0340d560b20f8808080e2580742d10b00441d8a506400310f2200040000c000f00c84654010040c85 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 534356267 1250 534355017 534355037
    0x60507140d0f0905011409070f03080d0c0c14070f0618090c170f0a180302100b030304050901090501050f100905010c0222091e0506010506030c070b010605070312050403 74
    0x1000003024120303008800d0b6643c44482a00240c400d129080c044040003079140ca09107050b42480c0d1400b84e42e9040340c0c40b004008801000010250010340350354214240000c134145000704c40403034504400810141c00040341e0802c00b03c5080011504100f5039220107103400d8003a494110640d401c1c0d159082e8503180300800f40041003100266846609030344080d00e051a10003442184603d002e410645442c1d44c0641e01c0018040c00300f440780b01c3d095070b0020740ca603100103920103a00c0107512108105110140240c44012200044d6418403c0701c01034180100142c02c156152800500101424040c00340030354482e0300700f048180750010303e0078a0041607a41d1140200e040074011030b0700380360801c0c0132600400800b041082828001c1403001d00240c807940002040101400d00140c0c40e90010007050050403140442004070f03001254070750540d507065074156500d449801050f032084c440c0080107003a031200080003040c1654000028404c1500954542c40740000d0181000119070301520000c002c2000c2d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 534357517 1250 534356267 534356287
    0xf0e060a09020108040f050712030e0901120b0f28051e0c1e090a03031e0503010f050d080c010c02210a1b060b091906080105060306130c051008010306050714 69
    0xb403580c6c00c05216034140c03490103585041d00c13541440c81d2142100800e43d220712100403410030700c1007075004003803156408251410035225a920810060036140001320302c02d001500b56080344511804c118030300714190100b1002d4180410017880141c8400f85000604121008117110ba030712810302039038680d07840d20b00d088085a102c000c0122304080d0700c00c8030f50051201640700d035103408102c00294001d4803007070340b820010704040300641014002841840700610042c004003c40b03543d0b02054940c2518501c02c203204074180464240501040300c107040d800c0c504001080f6901141c4035802d0f624034903c6480f90b40c0408503200e078a02a25070110005000681d022034010716140340460341d01d01810001811031550400b0401810084440109140b010104182010145d00c51b80f0010310045008004a05101c0d00080d111180500b80c480100b564442900074094954403840084c8002001001148413400000d80b614400344001d50303440f40750800060070140076141000b103d1851013911860701d00c50320 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 534358767 1250 534357517 534357533
    0x61c11090906060313020d03110c0301151a0d09050114090d020307061107050f01020901120b09012c0103050601061407020117072001050402270a050a020c010f0e060a0902010804 78
    0xc0081300ba071024172050700d015885054000c9917843c0640e0700e401c00724000c414081e25208203442554041d0780352010040e5901d80715907082050b1060310720403825103034280081192500501c0c070304010701c0b4500360700c80081110550292510300c0c0d81c882c0c003150b60355510941c40d890780b0080003000c0158104002050000d100d80c0c2c4407021904c10200b0890600303981c0d84030b50b0715004004102110070fa40c0085c80c1002c640e048102e01d59003190742c28091103c0c10511010038511034040c0f2520018401c0c10640c3c0c5205038030004a2040c02a0109950080f50307500c3c1002ca544410030721822003c1124040b086c000c0c0d0a1300c108544040e6010386802c012021a0300498039514000ac01001c00c11a0029070303120a49c103200a10800610407070004150750400d0300411466040340400210311403004030003428844481e880c0b907030780203681c02000150743d40c824400c2c070041c2c4a4031741c02c00f52a510307000580d200d88003a40c2c09a09000700d01c40442c1c0003591111494400c40b07400040c0640441ea5510011f00044d1403a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 534360017 1250 534358767 534358771
    0x10516170106140703050f0d050901050612100f061a030f06010302070206071115040305010b03060f09070b09040b0603041a06030f0705040b0609090705121005130c0e061c110909060603 81
    0x92900310b14100300e40d01c1106490b044004000f03182925000ad001c2007050034000d094010000325110010907a0002c240703076540500081c40c0a031a520781881c00d0490384564000d100901c2622136050700c007400e041d4000416402180c000c0040c80e1084007141c0030354481d2094544c06940603268130301c1c081c50b50b158030418440003030340503620070103a8103c0b00e03d142007280900b00642c4904000300fa041004405c140c1000d400034201171410350b082c8100030120030300181001c21181c0111149582d03004942c04500074201c10000260445000000d010400c201821101901e07000e20f01c1d0301000e9210007080680361b03100030703034034502a074096102404585400d500c0314043d484010305040c600880b84011801c0890112140800300e80003140880e6091030f83c03c0680d90101801b1309040f0180e050400081c1e44840d03086a00307000903904c042c00600140546824602c06074002c228948030010f1084940c840c00100214031f295609280da280ca00000000c1503074030341407005041195580c0c500090050355040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 534361267 1250 534360017 534360023
    0x8070215010f0303121d030409061e1e0509180f01060e071b290f0919151d0c030309091f1a0a0801050906030c12030c0105161701061407 60
    0x1546c00fa502540c4042d000600301e5152000203141c803117151601311801c481d4240e0005446600527050361808080d80240001640d428401642c0899003130502a019608503422154106408030180910900c009000c2d401e10515102198180170310414081d003600c00500c03c0b802d4002031040410580d0780500d03206000b100122178003d2444443e80c54940f2002d8a1031003018001c00081d403000d1800012a04090348005c08944d0f04c0b020303007030447c545940c2c0c0074201a50f02c645410204240c01b00300120b4843c0d028900d2075841403005840c00603400e500888a0f40040550f032003081c900c2442414007000b558140b0070001c10319501c680d81c3c28a0452038032080d552101d040164980e02040c07801c0a069840090514851541e840f00100b41010b000d9107010381107148641909020007010b43e42c0006c249441c000281e54180b4800c0f907040b4003514501031800c2a400c254246003c10140c04080c1c000180d12415658402c1782d601640038040d00682420702844c1c001500daa5a40341c0610480740080003903900c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 534362517 1250 534361267 534361271
    0x806060c070b040503061e0105060d0b030105160909290303090d03020d080a02180d03090819020310110f0702031c0804110301181b0e010608070215010f030312 70
    0x14a40392558201100c80e0041000640042410701c110305080200c0d5620101d55844004c206805d1780c01030043c00814810984103500004a050810072030b508141743c1400090020702c00c0c0c2c108180e442e00802250100400052030b02e01c40001c10122500032100001c201d0b0301140110000d0075220f40700b982508900a4061104200044907911100080351680d40250f005e030080c920192802000d0351400341c450088940107220440c0841041e14080706800e0084403034048a00722840d0580350460303554070500c454001c6640c41c0c20986460000d601400f482201610b1241c00344140d8801118a2a402e0000e40071050150071a5102410014012240020200c8284040815070312119641600707081c0001071502088c0403c114002c0881c00780310301c00300c000740803402d91240e510070044001007000d443c803402038402020454841140e100034000301c41007078a081d1313180c40c0040d00000060340e0040040c403034401481181504407070f40b24181d071140391020b080507107951422500c0e0f1901880545101d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 534363767 1250 534362517 534362527
    0x6061706091b01081f0f3f0f060f020703021905070521013e03060f04061205151b0307110102090909010605030c010e06030126010f0f0506010c12080606 67
    0x9400c1e801084001c282d00a12120001d0602205602d100a092000c7c00502100c00b60300d089500003079014050103040366160000041c942c20b001e80c82c0041d000014151307a1500c2c9042c40781c0691500100304880c00f07502281c402a0440210307210802d80302c50040c1c003d41101c6402c1c4103a2600400c4034a607040004991407268488400a9085810724004104420031107000c1880704901c621524000a0141d5060030040c0c040074038003102840014146d40c070914955900c40351a0781c995000c54054428800101024055842c007683c0d10b6140c03214030715002003c00e00180306034400a48140302c082a04110b94107540311148140e1320104802400ba10310354080c04a100720362118910648104110000810124a0700c420316080c5800d80d1030040c1003050201a404054031100116070440382d13040124a41400d00441103040c0300e29074050929654200002d080c8449825003002030810480030040116482d03480042d605030b41407820081110000301102036181e40103c004a500c04406403540f442e01c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 534365017 1250 534363767 534363811
    0x11e05030601110304150e100906030e030f0403050303101208090402030a02270a06020705010e06070f0506040b06030610210201090b0a050318010c09091806061706091b0108 76
    0x5030010b80010a414402c6c00901903019400380204c00e958105075111a200550701c6001411848503000348000d054545403401e41c680005c1040b5091070f18004040c82e1942d0301c3e49030082d02c07540190385e03c00711100d403520045406564000f4034411150f01440c668500740310001480042d410003040700a1107582032009500c090800b46449807501041c000800c0d40303c1c0110100003460380e054024400b150301110040c00a41d0700000ca64048100c11200d9985601c1240360002c0c1036010158000d010303014590900040007400345001307009190850903502ca45d61044d0440c1080000f52240c0138480450600300191b441605400751442401850201c0b0065117070903020880e503002c1ca00c080001040001049420b070f000b08248070141000b10000e0080040c0307400300614046c0240179880c1c6c007a40c2d80805000c030050580708e400305594018002c0c00a180d440c1e0316031f010560f022003010100e015040000d034001802082d110300b01001104000886c0d0a40e000455030104010021004400ca07001e0505e08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 534366267 1250 534365017 534365023
    0x5090109140703050a110a0f080705130e0a020c0f0d030b09060d0308090a050d12050a050103080304080c030c071202100201060b0f070302101802120a0507170115090b030705011e0503060111 83
    0x1d000d0b10f07a1520010045100c400030001c2d0802002a0704010302444010940cc4d0b00011807400c840c410089404142c90341200306009102d9000c0071280741c4207404652085450100d00c07907503080c0302c5860404c09611460248182500300315041980504040c4044000038001c0010a030040e42e0101211002c1d0800e5031203a190555940541e004120004800e16a00d032407401410b51103c85400107110395455555a00514040030700000e180c048042884200d54400700165000302c0d10b4a0219501c0c1552006419100c1c16402d8041c0e000d15800c94010303071800e005019500441c0c66000380686400c542d00501441e90308441412021401303409106030200f00d0fa4000c1d50340f051f14801200341c10030201c0c410007004100024446007a9041382c3e4001001c5100071074444110361480f0a00d525002d00501c0c0140107006101280c00c42c448580c07408240481030354480324001e5020340031210001d03201d1006407120350081c50524034080d5241c00e02d403181c902c288080e40c0c00000c18101340b035480b0808014582 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 534367517 1250 534366267 534366277
    0x1209030c0e092a0a05030106080d200106030c0e1f06050a0e03030d150f060804110a0b1303030807140414010513091401050906010c14070b0c060105090109140703050a11 74
    0x102e00b9400d418141240c500072034184010817040b4020058549080740e41a01c4180c0030780310109008031640c000b041e100484119003140042040200082c07a00ca1418149a0b091400365403083c03460400002e0165803254041046014441d4801080c10310b400300c11203040c2d0041c406802000b80ca200c600d2402d8174100085c201910825a0121b40c1000002c10703401c007401c907035004401101030700908110154100d140d40350800e4000203140540d8a0321401f00d0345540d05644900c0c900100001c1c1c4007021220368000f242540d100c0d54075070b081030300c2d01d030710840f640b10413202c1301362460100300420043c03601c13003009514500710181040d60600c8000906075807203104030761102645545805019201080102000303000d088200c0d1102e4581c240000000e106181400c0c5c02014035002030070b02d59a142003000000c00a001112503140c0c0c070019a0046e81c0c81e042e007841118054a8010008200002c980c000c09007901c174041c0c119242d13035841041c11809014080c0521986903076603d4210b02a440340e100801d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 534368767 1250 534367517 534367573
    0x81b04020f0a0c140307080304080310030b01030302060414011b0c0c08031c060e130b09120f0a17040b1609080d0509031e060c07080c1005041209030c0e09 68
    0x3c000c0b101c07410700e0700140001400c402c00f55002000648000740c1a001540e03001504002440e80300e5644d40c0c0028907903c641c1d000a41030008540c00081010303030014215200310310a03d20203140d41c9450382040e0980304403180107140107500300700e54035203144618421800a07002c0e024155105642e00c0e56541103920241c00040c086803001200b106801c160302034140101405545941c562420710340b0303081c2d21000401d0003400100c0e0100400cac0000c1c002c010b600301d2800b9003050b147c0d81c0c0305020300356201a4012110000031506026484178914103a0441030f01c260f4000030314007003503038460344440340d0300404811520501480c41004103407207100300081c0341c1041c8280c441c242c0c6c40044a04051030400b00c107403c0c04203204e41665044030410042240398000507081c50702c40d01c84920303282000c0907004109000e00c1d07030b10130a050600740c0d0445403c410b0249018440701004140800400c440c3c1c070985010160041001c138104002461034059600e07800700c2d03500c041d00d603081540c400103080c81c09108005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 534370017 1250 534368767 534368777
    0x40315270218040f0b010e100306020c0c19090c020303160e15040e0a06080c0f043c050609040b13020607061a030601150e091f1d0709081b04020f0a 65
    0x11500300103402a181b4098401c07a0700441041c0341038250303050152128007004107072a40106003d52401c4c3c0030072203001c2c2c888000f4031007810120225004250004684184902e003030070041c3c800c101a001001f181d0044425540c0044c2c0461400001d03500d049880700301d10382140942210311042103403400900041c00da1403108004a00f000443c45c3e0a45406400032007054000303500c030780203541d1011101c00488105590205201b0a40c681000200c0528030210301e00b03240314200d2141c12940560024203c00c00c81030100015251441403080e0701d102218010000c000c00000f14a82e20246880c003021203200500e864601545907944c00255101131070350078500f1040f0385400e102032070144541809001094800040701c005c00e48002c01c114070300c511440c0110103500c08103032070b205401c0c0c8141d0072180c5a06c1d860030701992491344150456280da02c04d945991918040342d40c03984100e103040c003250b40e02c0300185490560381c0c9400e41000c2854002d9a8040d60812201d1120103116001d40bd070800c5a440d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 534371267 1250 534370017 534370043
    0x70519050916090e16030c0504050301240b0703080a09260730050d1506050c19080901110f1014060d05031608040801020f04031527021804 61
    0x540000b00b01d8000c40b9a00a1103410041c003200170300f090507810031440c074020540b0940100e09a0390b0348916081150154200244044008250030741101000c8401c101e0f207100c69591001c61042d4000d9010060000c0c401d00c0106501d01c01940000e83d6031402103038003d0200480c203440804080561a070520000000b25501c814416400c04550418000b502184220000b200c0e4080942e1841403901d42400301c045603400800541d6409a040743c1201444000c1890b2610400b500341e030442d400d4519181706140107011502120f00c02c1c0c1403e40c1c0d0041d41c2500340185003005640c04810b84040f04141e20501d0501c90341d050003044485a800c400110010351101032400806421130000c0c070030381c01000042104400140d0000c00c85012624441c00d482c0c0c1d042c401d24141e00c80e441980c0c0050541e60001c80d003841c501510400801c2102d2040c2a01140c0c1c00c891000300007a1295240d50a004504541d03000c20740000c1d4170341c021282880148a4242c1491519000600da00c042e03809442060040310703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 534372517 1250 534371267 534371311
    0x7090902030d0201110d020705010b1008091204080307080a12060e010609060201090203071202011404081c030c0815040b04050a1b020a0b01060f0c051b031b01020705190509 76
    0x7601400403080d1000340001170356010581014450450806000c5500044010605c40203502a00c03000d034000300903501c0640300490041034001c0a8400e40d505008910b0310315145210310080741d084402803405141400441c3d1103601c2550441e5007036005104a81c40301c2c080010b40c5120302000b419180c6400d032065410710400600d03e501d03a03045202507a141106043c05640c1c0019a00200c0d0460000c107200d00cc500c0c4012180120030001018480a022501060900001c43d5082c030300489140b5503c101c0b05800800c400351030070f042c040c001041081011941035900c0e50f01d541c03c40d02001d800800c0c4d1401010204003140c07411a0f201c2c0182e40c0c1c420b1903000004c0c0c0f143e142440d900403440140f548006c50344407201000b03018483e00041c01214920994940d0055402c51090340e0000250750384145440e80350b222070403003075010510901610b242c90310804d041d90307246181d40c481a801060001d05120500640e5400180c41c0880c20031101c0000640d076840c480d030a8403030070305800d1140100240300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 534373767 1250 534372517 534372523
    0x20106080d09230a0b0a0903060c080402090f1b0d0209040c0302030c0f07020415060305040219080c040f020c06040c0e10050f01180503011107140f19140709090203 72
    0x9480401000b854030003c1094442c0203a419420501d120b00c0ca0342d245100300c00242d80c13040700768005080c2d900b0116600e00c0300b0b500810b800049078040c0c641400200991242128448000c0b50000e50160041001c10451060350400e03070784c01400510114482200e4000c442c17501c2e080790b421041c00c90340000d05210a410603024000c0c0400300e609056085080c11174280e6001d00501030010351209001c0b600300259651034000c5007161800742000307000c00c0e85492008018040886041e800345281441880f202c061820914080b20f1254002d010001160b104000280600041040246030284041140d00c0000c2c001140038a204000201041c0d1900d502c9c0040b4030317401041c9a040d450380c4103081026881d41d05034038a41890074640315031468610110310b580242c0075000160551b1a20b0300c2c2c1c010103440307a00201400b500900444860450204401d40c0d1400011034143c1d10390407440c800b8100a40903800301c000310f8429060b04c3c0903500304c901101d29003ca25400511060f880d80c0321b60701582414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 534375017 1250 534373767 534373783
    0x809040e100c02150601020c0607080d020d02092701050111070e0106080609070e0d02040c2102030106140403021005070203120309030415020a240b031510061701030305072102010608 80
    0xd020b1000c40b45c60b2400010303456503081c084803030003950000f609078100100c1c0300c11a40715000114046445400d50310b90100290030a003282401100b042c0e803d01c410098000c3d02e807690300c2c0c0750350045489a00b00340044a5a10504204041d1441000c1c0007103030180c2c0c4140000d010307050907902c8084c0c500d4180c0421030b000c100038000400384030000c0d2082d081c64945e6811007240e40d0301030b00c0109503540d0004044a1456118049051001080905422091240e0000e504844240d502d0190754440580c500000c2e00ca240710007503004181981d45020a03000d0740113070a81600003402d83d0440030414007801c285500460703aa000e5500001401e02c20101f00100da0456071300144001c2c6901c0041da0f1720309c100403030002000d20b031640c0050b808418980301da07048000d60034009000d4a484500f0174003045c594030300a5490b40001003503401c011400034031500c10f42038000c04107a1509056440c5403800e031102d0f4000c480640b000610040820007000800c000448034003099400060a503243c82c580c2400c01140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 534376267 1250 534375017 534375043
    0x9060905060f0c1204060209061b1011040b0405120102090604090b0925030b1f0815031f090c03020d050c03011a060d0e0715050309010f05130809040e100c02 69
    0x4d000e40129442c16440307030796005034480710050351a041030001800c00d000d2502802000b200d02e8208103000c0e58045070880e601ca1886e1014041c8404214140c25140550701902d61000f6040c40708000c02e2400c1400786e00c80d80c568100051810528001141140e8070541000c28182c0c2c46110b11001403c0215126a102c040d000605409002203e5086510f0001c020a40704040d260516546203580311900004074001078201c1e0123038128030703207009024114102d512141151054041c50102c1c2004280424450b0b81c40403448005250100c040300242180d03002514002051500440182c403808142004940a6030050810039110ba0070035082d9084000100003107071240050000720344880c01a1400039070100c10106110756089141ca252001e103521882d40d45010750307a941c0410f41c2000c010740c02400244020b120308040c2c8003258094071740c01c2d22608a01c03440300da058400310f400000a0220404000c2001c03406158181c2c036140742c08104a40c02c0052551410030310207058040280c0449520 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 534377517 1250 534376267 534376291
    0x506180a020d021b0f0a02211606030f0b0a0806010605220303080114010e03070b090303211e040512030a18150606021506060309030c03030703061a030f01140409060905060f 76
    0x1855020524003425600a0580c023002180c1036640f84000f408681c2e030046440c050f401800381e450328000e0140000d081594000c0c0d01c0c2001012903410551038010603101d83e4802050740383d180c0b40040b02c0c2c0390304c40444414285ca00d0108044604202c01410000b1400380c0d0b6440c40d01e504020030070b40035514424640d4140020040c032414603880200c1c00c00215418190483c3e00c9013020000f1905512604500218442014201450700c0454804d40d60060a203400d2096240780c014a003ca4208810340700501194400da0003062145002c00013590701c00444400460700100c0c0c003e420b1259460100e0480c0e0000c0c2c0e9110504641c030300e9124500c02800c45200402c9004182a40700e295503001904550013000004009070a5090800465041401a4040b60740d60710340500014014450f501402440b200030f01c0880c054640c007502528043d00311600c034070415910f0000c00518954120402580090725040c03104046003140c41048900b0740904080c0440c0c0c90300d400020002103000b054120021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 534378767 1250 534377517 534377533
    0x1e0f0306041d331303170106170402220501030212070302012c0306040c06030c0906080a0b030f15041e05060703150510031508010506180a020d021b0f 66
    0x1d540001d05240d450343c405035000c10b01004a59200e0b4103498500c0c3e403982250700100341300988051124141d80309019076108420054038401002003050207104810001b4401c4000425506204500d00e40182c8020407443c2c0203039420031300e91040600c42400f042c040b607446004005600304001c1d45910340a0382c4000d040c0003400c3d0750001c2c000404880c00605001011550800d01e205c412103143c5040e21300400b01d41c0d0f01e203440d141140d0042c805008140c00641004e1649910034003a41d02070302907501503201c015055940480d03000080c40031210b00ca0b0325103e458a02c400603181030000ca04d80e007141c2c04604203070f03190a0070704484020000d12803214601d800480c0780c0200310089402d5410208074074000c114498092a4102400003542200c0d520130341d207002c200b8a10390181c2c40008002c0300340084480c01d90340c840300c0b142221001c68030b0540025100c0311500c0d00ca10007805255000070481d50042c140307800c131500b1001300d80280981c0a0800329080040c024048208940e51149801200401c040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 534380017 1250 534378767 534378821
    0x3050912070b071511042301051306260c040515120711030d1d0c0f0102070b0f0d0905031b010908070f0204180639051e0f030604 57
    0xc0e120300b2030050498440740c64000e0344040660095950315005d003d885464607140e00c5e9140706203101c14820074641242c02c0c60f4110341d500980c00d4500404010581c0640c80340303003000030b41e00101100f8201a107681000301d01c010713100e175603ca0507000340034080d20741d62150702304410301c2071070300204441c0640b9a0041c040292010711026045600c10101c3c5009000d001004600c07500e136005ea00b803d9041a4181821103507109100396026542c0301151044491244601c4180985018503040e0640160095441805124581c0e0001d00c2d840c4142500c103403420081d500050200c1e0100c0104032066000004c0c004007540c0e01e107481511110000008110003486070307440229502c03400000804c05410010344009641c0d13a6804299211801c15503c5030903080e620b060030007029000a0b00c4c005001c0d40c600803240c2000d513000d5807649140c11f499034103001e48580d4161150b40100120316698084031070041403111082026000440b5030812031900e03410400100320a442c0e844082c20741d002820410340c280 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 534381267 1250 534380017 534380039
    0x90839060c16020102071701051009091a090f01060f031b2405070209070809060123040228050301240507030815041112010e161b0b040305091207 64
    0x306900b241d1030b0502c1c18403031005030b040010390307403241008070076040e00c4009140064004070b1144844141444a07a074403152514116801118080c0c03a031100009151144503c881c0c40b1508240b007407003100c07008003d06078494255080da41105190107000d900400400004c036000e8800c0002c040c000c0c1e9812410140140016003900400c20031100060240408203402a0120744982d50040c041e4501d5107407050740508800c40a80380e6000d2441413030000202d03d40c200050070aa00240346441e1908000b000411019400c002c160440c0104804009039146d03443c43c845401ca0303030940d1103060b00c079031500c071880311000ca400c503c550940030410340e411040e661100844084542c981800031254481e00014681d5215100510390420301e40b220643c40c0caa240705c040c000180710346008100742e80e00da60004481040c156604020a140c86505070107080c0141c510346040e260a170030b5080e02040e00d40350100e03401801d071401d4012450029040c4402d007028002e07088449018002454494980b40b09000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 534382517 1250 534381267 534381277
    0xe0111010e0a0b0c25020103110a050903120f1209010f02070f050105090604020105030126011a0a08071a07051207200102070b0d0b030709152313090839060c 69
    0x2171050180d000c1c8001c41e8040d80c40180901d02c081840b80c0c0310070003200e01810395448950f03128400c3c440e01344220103890a0808680c02c1d400c0024100d400d103000c03640000494a80502601080d548917000d082c0e00c1001da1003d08850780c0220711000080519040c9642100c0007d0a642200d810480810000d44d07000030480c0e04403100c4001003c02c008500360b000e461400c8040c41c0e100f955003801c0c0164030b00f90380408401c150300c03070407070708085555503914150303544221074814030100b503044d03800c050680c010fa07030007404501c3c1c01602a41d0440d100c05207080f1445d40051000c803615802d140300451940b241e141c255850358000e00043c40c4071410308400c0c024502034251404031480e121407840d895510180003840040ca4034001c148000703400c0c171401810842c1640a0300d90ac0c01030030800304941940c0ca0448082c40c1a000d00700350400c03401c01c0b03440809494400410b0b12441c0c0e00f00100010894442c85c2d50385c0c81801a0740142c1c01158249041605500884401186a00c01c40501203408840400c42d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 534383767 1250 534382517 534382567
    0xa062301081504060209030706050301050111011b0c0305070515150402070302061501110f0a050c1e0108100b070f0b092a181006230a0e0111010e0a0b0c 67
    0x50b02a81d40c91401c00702a00c242c80325141c040c019610001491900a4040c6041c0d807030980b5480c0c2c0c401c003070000c0503003210a1281c030001c90300c5800790407c08041c020003001125074040c1c03400d01e2030001e0946076035240441c00d0540000e8002c40c03c0410110411206901d01e0b02c05003140c080d0714010583d03c1c02981d508000d4007245030310307101700d2107440c0d983e0080f449030002c0707100720f0260349a0104d854240e03529241c41e03210580310340c000d8a06104145c9171400c00c03003070b040081589104141c000440115441d44008040000000d003003200401d00d07050b43d0000e030040c584200c2603038402144510303080b0702010f0053300e1030003070782e201c00d020400c0c40307048aa076400c001e100401421000340804000030402380c002c007007051018610805100b007036803180c00ca55040c1c42c2a0748503c41c1203c0421104031a4078200f400701c01c01700358140704010290b4410030110002c1a0140b5140f1101c0710003042da107084a101e1500d9140303e901a240c000300b0044800e9040d0b40c48102c0c5c5884a04001e0700480c508000301c40c01d00d0803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 534385017 1250 534383767 534383803
    0x7120305071d06191e0207050303030f280c03110301050f150f0c030705010c05090604031103070305030d0c0e040e06060d032a020108060a030c050f030304080a06230108 74
    0x103801a1541000d42c0c4c00900d054104480b01c80e00f08002030700d4403100320309001480200c0307208503056600005500c1300b21080600214603650700c5d03510041030680007901052401c9403680b44401c0b8a4643c8009070104002242e0010f0000f5117010082d085415080c00100040002c0c401081107940c0c881c0c8104924805903100003c2c41003601884000c0c0c0b040c0201120b401b1004514292000000009070590b04d03c04e00007048450a100740030349890183c2050507134050801c02080c8001400348442ca0b01251000d4112004251659551402e40d00425658240c19540d5108019515070240b01c061501c034080e101000000031180e4090745a100c01000310b0300a10b074540784041003620880c12558804000080126142560700c450340002d0103240c0207034005800300d40454414075101e481d01c1d04880c2e022500d034140500c0c102c148500103030755009050741800140030010303034214207010b40c1d902c40d40709035070000380e11540c1c1070318031110300c03c080c1e08110b07440340d890061140c0000000c0d24a404a512512 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 534386267 1250 534385017 534385067
    0x60301060e030106030b0a02130b0702030309100c0f06050a180c0501050a180e040b01060e0a031e020a08030c07060c0519060b0d0f17072001110708030712030507 71
    0x2c2800b525041d0300007002032584e0801c10074009000e50280000300d00310b0803d1044103a580e1790701600d0340074074030300a5403503001002901d03a00e19100319542e4941401d4281107000201d10389846a40c56403d8000362085c58480f0204400d8260754400c0c1680039040081c6589885c07599161000c24907001e0141c5814041c0000b2580c8100d0700440841c03903042040040d40701e2603030325618200d920381001d0700c0c00c50b0b00c0440c270700011818a014803440381100101404004055203141c854030208281e01c03548000c403524040300440940ca031000e1202c084c2c4406002559580b071803103280c910b020026481034003041742019800b8005070000c10a903842420a59014150509904002005000410aa40d0700c080d07045103850820114035003403103280340100207001c580d4044e0b80100e54540b1036504014240741030b4107650f42100080c1c07074000c1c0c0c0354201894070160320002e041020346002807a8120032802c3c3c1c0701103061000c01c0b03840401c80300114110f240c180b00e1400d1681d80a482e07241070181503140d006007029 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 534387517 1250 534386267 534386269
    0x705150d02030916080109020a0b16020d0204110f070507080a08030115050f0414010801090509030706050408090a08060405120a0f080a15060302270108040b0c04150e03060f06060301060e 82
    0x300008030120712061602c804c81d0340e00300250090041c110300b01c0c010301201c0c0c4001000550031095420314804080511303d01d40240c2d0800508030303044501241e1003591517200001071040d44019244400d2003410180c5d03211421b0410b2072400d00294400f421541c03040102000083c0fa6500742c904591901c0200e508040745140e054416000305c0700361400101c0041400159020f00200d1845000c00a07212580d850b40c031000404192030742251503182e19441007111074002210b55021076405802121a0303401e02c1d10240011703c00121640c00b0f5500356004206100610400b401402e2034011141c0c842403a0411481c0054036000b0308901c01024401400c00040790081181c000714946038185400b12071103600d400f4041e000b50000440041f4503200824881d14860720010b4510603020140c6614a031036880f941c40e0007003074600402103085090b080c00000f90341007460501d8080384050f6214000d03401c01d0141414a821001016020311080700c0342400030580358501203034103448851411802d4001000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 534388767 1250 534387517 534387523
    0x307030603021c06051f061112030a020403050d18030209061305040506010f0b071e02011701180b01180315021308100b030a110405040606090f0506030705150d020309 73
    0x360020f50040311164a040c0100b000071030b0280703000d2240104125a484960800131101314079510043c1d01c4ca4000b000303211243c001d05002003a1100a0100c0b032207a6290440e03d4038640042d0382e4009030a801080230700400c00e0600c9001d001d50b40c40c1c0791038035000d41c5001400510644510000c0e00520300d40000c91015102d03101d031641c103002c00030014041d0303081501d001b56581000b4459064401000d00c008108002000110382400d41c000501452284a800760411400c40e040000c0341401984401d802c01a0440d036a000c0c002c08039050407803540c09201025500340c0300259400390400000304205454100f40000c8407081d690824184c0c151481c0c10f0302c6800c02407103200545140ca00e0340300c100042c2c4030310014034541c42a5208505000c100e01e500203041d51340d1505c0780002c1c04280010070850050a20340c0c010b66001c0d0096501184d4251b5448040c812501c644d000c0699140e00e039810004282010407005000b07207011303107000d41c0c0320448410483c0301e402172041e0030801c04d0700080404d02206c020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 534390017 1250 534388767 534388769
    0x40b04081507051c2c07060e0d030503011502030c1005010807050906030316050321090724110106150c0201030b09010b0403110a0801140a1103060112020a090305010c0e1503011a03070306 82
    0x41800b403149900303038441d5146d480009105910004400c2c84201c9401e04142d01c540125546c59140c00d401c50b424071040030b2078881052054000c510050101e110030000810448030100aa088001000d5060841d100e0900300107401c1035001d02d242c58103010f100c0d10000100c480c0e0328a0011010410ac00c0361038030500350b11540d186004036000c07401498501d44030000380039015038030074000c6800c001d40e1501910010b4072400c0442c081000e860b208002042e004501d403480c5610400c00003c1c1d482d446221b0300c003661161014100020f4280c9003058219600b502c941501c1850480d01d080d1950715190480400e07100b41d00004001c10502c84031030041c0c0e02c51201560103483c8240003413025a00460701c4804150048941e14034082c1000e8603041c0952210044a000d210182e407280705034144045201e02a500c440c00000402454560010124000b032264070428040c507924141c5041458080011454a64401003081c200410040228600e608500784401d40940081d60301c3e9a1001000e800404403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 534391267 1250 534390017 534390071
    0x50a030605040f0b03010506040903050a211109120a021f0c0609140616171f0b0c10020414040b190305030714010504020306011802040b04081507051c 66
    0xb0803d608243d000d05070840c6090100940c0204402c2d55000e0810059920454014021900c01c2001440d003510401e01c14842e034112451810614001090b1300c01182c1820301f0051001601180d1a8007074074240d8028440104560014640009641c000030054160305100d10010004250001d900707a00440380c2c10100c2e0703002001041100a035042202031000420181c0303000e8010500000d01c9486100c0c4810b40302111566907031012040d07507401d240819005081c0201300c0c04140d4140042c8000d100c0c0c104054a006290940c480910042e082d20f004043c20414103414018041030154080c42d12200300000c5c7c0441c1c0106e04000c05502040c41c260110100603503003418410007009110002000f092442d02c40c500524041c2c540c88c840500f2030300c007034900942c150800c2004003d00000941c0625000710030302c0e0018070b0103951744260602c50380f0550148070700b600004400f20251404500e100c2d842503007410005d103441903070100800310b0680d620100c0852550360050103120000386081c5500342c0c3c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 534392517 1250 534391267 534391271
    0x10f121a090a080c0c040b060309030d020306010309060e0703030e0a030308130f05030c071a0408370302061008160605130509010308070c0801020412110d1a07080a1a01050a03060504 80
    0x541d44801300c1d22040c1c044082406507003004c6003d400c0707051403012248546040d0024504000b090140c420283d44003500d075034101600c850555021a200e8443c1c130700c081d007034031004000f190b00d14540500305180b030305265031040da5840c004201080d0440000d80d03200b0340700b203a100901c0a2910740210701c1c0104032005441844045034408903c1c0002a034502030703c800c0e400501d0008040e4500001503c02c2c1e006020340c581200c08803030303045e004004a030f44000d005040e021004407413075224220400c4201c8401e900584c003400c144401d103d2024400d2019121240142103190301c40c1c4a9a6080445489441c040020000e80d20750b0071b150070000300002d00801403201c0100e5075282000348140c0c10a90050b200002c4040001814080c148229001c403842300c1d41002c1c080b0903a44401582041590700940c0150007801a40000b4101107800f400109180103580c1180c140741e4401041c00e08000c0003070340b08629040c005030700291442d1910041c5a001d2821941e150700004049000c0c001650106801034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 534393767 1250 534392517 534392527
    0x102031606180b0f070311040b04380405120a050604020105030406021317010b010809060105010e030102070204020a260402150c010e0106090b040f020f0d0504020d050f06010f121a090a08 82
    0x10800d013600c1c0c0c0101e07440d5a060142d015410481482172244d881081c3e65194104020094003110440703003148840c41a01d0198003809880c1c1c3d03820160b4107d0388890322104006000c0c003a07494115103140d800b00c6070748010064403141c0d9944070383c2c941010304082e042c1700d004000202040090307011180494111b10718050007503541c180005045e00259404409542005244d0055510503c4018070070303031001d00208911f03460500199800f20010f007165070995020802c11000d41c0781ca000412203051240e9501480c00b448a03140c80305031800d05040c03006c07040001d041c4405642c0d00c0c0b40d80c0d140d0512121440d943c5480d803184141c01000a810b03480301035402c0200001d0170800980c054600c0a100f03980a000c007404002c800800c0b485520503262039a10280706032443e107426a806550b00c18806000300b841c42c08551201f51070103845020841d1594080700050160038503c8110100800d641a440b840c1e03c4116642c0c0741e40443c20b0006549031564000014502c0360003000141c400c0c1c0c0d0424586a88d42d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 534395017 1250 534393767 534393781
    0x190b1f02010c110f1b01050403020a0b07030306050a080c0405150306070e03060915010b09030a08130f090903120906110a0c0b06010903030507060b010e150702040b0102031606180b 79
    0x41d01c0b41c00502000b01c0c100851104058002140b18980240380c0c0001d402000d41e109291440c0038500c040d440c3c10402c0512000c40142c6511f040000544000380c00e1640ba240b40b1f140040a03100c80f50007a038011110310504109c0c2ca040003610418500003242c000c20a691101c001904100700d806545915104440500c940350707030440e50400d1020800d0303059135915600c1c1b00b0040d176284503030400c2058800500c40100840140400603018040c002001e641c200c010546400c071440e000807007009038a01c01c1131020070503195180c002d4002003200b40f02c14040108181c6010780b5126412221074409900c801007a010024280c0c0312005138180d03949955203500c00b0700c00003048440c2030401142c03030341c0404010900d00c1d030103a070280e01100c0d4196035440c90aa2246d036843c0240c000400e0840c10301180c02c40b25102036030b840d8136901c061600c800106403521210300401c4291100c200b0124150b4004015008060515220100c3d40340c0d0880004200102c0c0e0000c1030b802c540d200380b406030620b4400c4080c0450 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 534396267 1250 534395017 534395021
    0x7061506030b3d2f070501110304080d050a03140705030a021b1002090126040f0501020f0d090b0721090305070b0705040821030117100e010204091103190b1f0201 71
    0x40c9000310454403150000028010720120001030344680c5590009100b0041503100b00c8d000804c941189003680d043c01e980d1282c2500d80421182c0020125001290540000ea49071241c0481502e1651a11f40307141048a40a4580d110150804204a40000341c0580c0009026104a41e06200d0001c840c2100d0940113000000c1d00b1828440d03000a8043c08a0440700e002450303003102c1c60082e01000603040d110703030761003035411800010120b901d0754007070000c100c148141c032015012500c200000401c02c500740c2c0c13811302c08416009054805128518500340a810b02041541207004911080080c80e0615420b00340d9950040141c003c150742181802c00c42c020b68807101400c21500340744116910f8203441c241c00319843c0102810a48001014030040105104200111946404140c05d032180c003e40812a0804c0c5c0d583c0c0140c1c0c041c980c0d00050104100c0e410b502c01e00320200b040110450444c03c2400c6c503a810700351041c0100d00f255844441981c05c40e50381c0c841c403030789000119030925140d186100303010780 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 534397517 1250 534396267 534396287
    0x1e030307030b15090f0d0b0103120f020d0903170d060b0403050d08090c0f0414040506011a1e030402030106240311090d0f03110307061506030b3d 64
    0x2820103010803414142200e0303c010380f601940f551414289010300740040100c220308801c0e0302c440c000c11000c0101e42441c04080c0a1401074441c1c44130303494076103806090a40f428840384c0c210b5101c10f014900c03c95005a203030054903403001c0045002104c00c42e08440d82e004000070401480d181240004140d588040100101c07072003242500c24102541205542701070040b5400c4059070098003080d00b90f484d0039814a1a0024020300002c0e028210201d1b5000d8054221401c8842e503000f00d006000403180080d2440381c0d01c01402481d483c029030038205420b0602201d2503a80020804404a000c45d60290052070213010f880c002888901011901083d03400c456090420200740b0b017460610440c0c400b081290f8010b0009000026041c80036034402c070183c80c0901c030507001c01a10b20644c40800300300340000c180450140001241c40c1d00781001c80c0143c000240e110030141403420072111310b284c545800c060b201501105075507001607110510401e2210040703024522040c040302d1403003450740e0401a190 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 534398767 1250 534397517 534397531
    0x1090b04080f0c12060a050408270117060a050111011404081b01060b09091b1303031106060a0e0a180305220506040b070303020705030406020c01020609120904020c1e0303 75
    0x15042400742c414880d403200e908408420540200b0001611b41d109030f00100c1d0450720400380c2502c0c00d0b603042c0106c00d41c440307490300050059140c43c0c48100c140d80d1112118042c9101811500c900c2d01342040013410903000b0b841898180051040c02c91800e140030b500c80f20203403813018401c1c482450945410907655000e40e01442110100007081c2810910501c10742c4107640e050343c11302d407130036011108100c0300100041090078101c280c3c140009251041c40003420002241080300e0342c4c002e0a40c41d01a00c07042c040a41a0030ba43e108808000d80b556400070000f007298640480e11900c5d071100c403403440240465492040180c1c9441d01e0071802c0641c8100100320807901d103d22540c0301d62800c0d4285070310344801d2107000c0d8860700a00060111402c60401030400c40e2190400625024240da00c0c141180c110394800030150308680c2424215580500110703a000c6010f4002c1c000303100e01d40c150a40c85001d030b4401e5034041d83d400700f100e07034101070200070007180345110300c50400d11424402e88076513596108071540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 534400017 1250 534398767 534398773
    0x3030c02010206161b1410020d180b06010f0c0b010f18020a020d0810090501080d0905061617120a1e0b0102030412031b0302060619032001090b04080f 66
    0x14a941491008060080b8055441c00b007540c40d0301014500c042d117150001d07203508a0000d02c152091004110041c440010000c0250700c6061140b001402c5404612807894522054040308000805d005640303a4095001d08052031429602281140c21100742c00c0000c040303041c9440007191080c0c03090800003c54424000040801000d00c80e40c60070390250404090159000c210b040f44072602484030968000c3c582c40102c0c0e000c03580d441080b4281d8500382e01682064000d007a5910125500c244448054001902c070241f4100501c1e185070038404014001504100409160808280380b2004440c0103800501001c55517041c4004913400070504030700c01d20383d000890481051240b089009900225005801441c1020b10388502e68440d1050b03540204c00308544580c1481d0111194108105d4482c0a0f0380146014034000041c00594890143d042c540e84041690800004400351460716158400c408101480c1c0340c3d110041e01e0321019900030340c014240c0804e002c02d010500050950107050300b1021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 534401267 1250 534400017 534400021
    0x50d06020331021e150c0d0302040b0f0f0909180c0a080d12060902070308010312140307030b01030908221d13030e04050c031e0601050301060c061503030c02010206 72
    0x110424a0041c07020350846118807882c01c40540b508209807004003640c02c0101e103480c0200300008402d0380f0003400c080488400419034984048003008021070070141814118581800d01410342d03086e00907102d0b40b201c2c94600140c00d800c660f110340b00f0380d210030303c000d4620916800e091002c00500c00d03030400d400d6201c4c86034404001d401e2626811746c404a8040401030813554031549000c0b00c0c5407091120791480320741c480c140098090706900c01003000034001e44c1d41500650440c98904003c9602d41c50040070817a03144004135040f000481101d410a18908000481400c0364005801911150380d01401d8a000450403810112546921082c1022084501c41c06151510700c01540c40002d00c0540d03c030302940c400041c0c05c020526142c550b15500a06140d2229580000010141d420031503100e50428404001e0000700d040100301043c40c1800240303240102d140030b000081c02c038041489210100180d15030001c06001c51a4054a1442c00e04101070481c1a12420043e000c0348006000300d005210b0381c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 534402517 1250 534401267 534401311
    0x302040e2d0609060103020a031e0c080a0203070203041404090b012301030509030a0c15060b0a08070e01021213050a080303041106040f05012102031302011d150310050d060203 77
    0x11010b4401c841c010300d06035054480700300440080d04005910000d15540b00011a207030750002d407841640d4055040701081d11040040010818140602002c141c940180284402e6540110a5406541045051040100b00f100008014200412000c0c4c01c3c61000800407800c88030314003a404941c05012a4031104001d80d40046084940c1244d1502640c0c00501400c05104d00c1694100d28941c0600424109281413030a030b001211029446000c980000040c0804181e0b00b00d5006c61780103840e802c1c11041207880380d001079103500d152041c0c8001148001200b41c1c45422014550029110241c04100410b450351080307907407a801680c00380c03070300d44c0741d40e00840d2149030080488050b0780c16208141c400c14a401e00640b603034094080742a43c22060066500365540c1144099445010300022840850105000151512051140104492040007840007060301c81141e200c0401207100c008960340d0380c4103036125060102541210354000400f100003006e1261540107180591098890b802c40100e03c0c1c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 534403767 1250 534402517 534402601
    0xc090c1206091005130c02010c0906050327030706060317070c15020312070c0b0105120316020a080102120403120204211401061d180309100302040e 65
    0x52a2140c10a080d20009031060408050454003d054822403110098641c3c00254100580384580d110030382e41d8101d850140c1e50709000b074204605080c148a911141040d42c01441848010102102c1200581d80102c81d00143d00601941c5e079201400d40b610b45280345032a0020b4407403440182c0c0d603886200e01a0109501c1d07401280c3d079040d840568032600920701504402e0314101e440140c82940000d0046007200c0e880328450910542d9142c1c1da40d06400328620b414081403606030002405030074030000c510200d400000480d50799014061141c10b44000610010b882005a500b01c8111940085030f011600340c0300308495401184a61a031910307880140c0c584100b24000d5100e03840020040c0c6070f201d8080700c2e20415201603280903910322517007140080710640c203441080e800540c3c800380250300c88602c0003002d500e8079004540203402e0701980d08c0c080c510035900d00460000c83c0c4103400a80701701c1100d42c040d6044400405914101c103030603103000401071042100c080d840003c2c8911405031203c0da88540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 534405017 1250 534403767 534403777
    0xa080109050c0f060a082d06010206090f070915030f03030227060f09060d0911040b0f0a0e060a0e070c0312090302060114310c0c0b06060d110c0c090c 66
    0x1c0c101c81e040c100d0580b0101ca00c485c001d0455030390507000b0705003100e0b0380001160f80003407105003800200142c28031000081c50090020500107332900065142130030300c9400f02ea14021a600f90783c01007407885c2c6030b4206801103010303648002d00c0c0d940c215800c2e004154254010706448034142c006080048a40302c1c1441d40c80150705105d6a1111040040403010b02d9141e014255502c40580803500744001450088120340065400750313000b050011f03202102c1d18090182c2211050103560807100c241c000c8000c10031003a02d80c0104c0c2164140c41e40080e001e61642203a1000411002561092034101f000c00502040381c4a8800c0d00040d84039140c14001d681c290185d48011340d8503a00910b20740e840e10300c200000740c203041c99090b413000d03030240710360003248101070304a03100b01d604607a1000108100f1480c00841d40106004803c1c820201625008a074101051561082c41a606150b4074003080b4080001000c004000000c43c500224407148000720000c0c48810004082d914a4403079150200300950354059 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 534406267 1250 534405017 534405019
    0x9010c17010303020a1b0510020f0c04090b0a1d060103111017070f030617071805040c03030c06090611070506180d120b100c060501050a151d0a080109050c0f 69
    0x10517403942c07000904051b240c009051b0b0801c1d04180c6aa2a02c0c00102d4104d0043e2070000140e0011400e1181c602c0203100b912500c000880301040901d1007030b680c61ba04414010035501c0a82e40c0c03402c00d1100c214002c0006c064184114090346c186607103d10b41012142c2c603072508140140d54003421185914000d07421a1501101da00700581d203a5226402210719030b80c2d0302220340404d901c80d503000503601d882c0144000c1281c0c000c4041d10400d414101c159901e124800d01d034420550401c1c040c800858510411041170304d81515240b50301a84506114000d0b1282d00f40050945151038142140c6c03c07075110181c884544035106a0301030340c070f0b0104612890b80711940c90034125045484c0d0f0f445c2c4079000d0070700d4107000c040700e98022030394290361800144680341d15030380701000c83c440000305420084180300d000e002d41000c8641440c01420800000558483c0b80c5004061200b80c005407502c0f0351040c0d0141040e13000042040003c82c0c1c580e031105028000640301220b030b51140c00507100c6285408052901da0440c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 534407517 1250 534406267 534406273
    0x3030f071a070f0503180708010f0f0f0204380304060902030d02011a06070c0b0412050f01020304030206010512100e030a020d030b06030a0c110a120f0f141b0609010c1701030302 78
    0x40320003c480c0700d06c180f02078844503445a948001010311081c040d50a40d000384500014142c1e9440b0300d50410f903140c1540490440744104010300c030181481c040004075800b8101c1903079080101440450b0318000180c4811136105c0044200f00c200189a0002c0480314400d40035a07145c5004030710701ba801d0354000c0ca4100c407028051401d00c41d09003410300240038041c0c010250229040e594040c4590150303c207400101e2008500102c0c2c10a00c18204220b44500c0d8013800210f1541c90705c2c0e24000c1d140c640600a0501c2003041184103406000c0812020040404081041181c07441b01c081c92507a80d803100710788001602607aa40303610351038040c0c4501143c9013005405280f40d5900c00e40210010280b40b819201800600c0140d2140e940d800c01c810300d007040c843d80d86120b465410540240c8a60b800c503040d8010014240130006029510800c84400349560a042c2600d070304002c10580300030404d498108146100300c1003000b203d203005402081c2400d0707081d101c1e68524020346550b4400d811007404085d025078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 534408767 1250 534407517 534407521
    0x1b122c010f051b0a0507050312160204060302030f0105060a081f0b032508010f1b0e0a09090807060c0c020303031620060709050102190f0203030f071a070f0503 70
    0xd401020740c012601982d190481c54607903d0110b10422030214508125668450a4903600b0071808101d140b020b40022802800355007960318145005105140b107060022013180e511000315220750700004040c680c002c00b41d80300c60140c1c0540a0003014110340282c402c10303400800145644011900c801044901c9040c00c1005c003202d0344410190400070f281940620070010347d42c107000740e20b0030b44140400048000ac002140350500650940d00d40451891182d8541850705d40302c60403410041d9210303491410314860b02288040021101a41c83c1d22583c40c203418001e05108000c030710001442110b101e02c4c0f041002410641049a440c1d8004d00c00079090b42c0104040b4000c000400200154240c00d03141501801000d001040030301000354010503c0707540804180180750740c0202c00e400240500b071000f8507510494000800c0c407040c515001406d01060390303451800b0341d2028411603083e081aa404207660310365074508501d640c800c840d0340200120144010601e40c3e44902c038500312400c280e0751164116 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 534410017 1250 534408767 534408769
    0x17030a03090f02030f0304091406010c031206080d05090109080c0f120f01110720060a050c0c0901031b06050f03010308090102010212070e0a0e251b122c 67
    0x30450a4000d6460360418540c210051360f040003104601c42a1a0145031100d01d050404002c1d03810110302d51812109560803c0310350b9034400104900d40d0b0701450840207690803007140d4401003d2a4020f074034035005511b121012184c200c3c008101100080e601c881086959802039600c5001291000e41c1c0549014203140c900d281098a0281c40041401610030303820146000b0390031110301c00e10001342c100001c00c1001c28040028080ca4800b01500c8100b100d880114000030381d10f2040a455009210001c140c14034031300c1c420801484a02c2014100318403d5071a42442c0d100108500350040400340752003408510790b88903000796002c0325000c1c0302c01815a4210ba03a0b84420b0307085949282c1c110740d404d04c00c80900c024070340041c1c1d001c1e462a445100c2200d8001040c840748030250b4020414042403c800d10070188480c0d0490075100302004d14112030030000c0b0400301c0301000541c8401100501e403030481024890864014901640280ca4040d030038203076200c1403e051700506402038984440507a001c030031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 534411267 1250 534410017 534410021
    0x1205010b0a031d101401090207020d1b0504240b04120305180402030f090d090b030a0f060302101101140103081b16030b010e01080303090d0c1106040312030617030a03 73
    0x2820903d4000a0840d140200c20a441d103401d803015140015203c40d6540d19503850400c003e405000d29140552808825402081c0c202402101c0141400c030300045603582c405520100030003510006005000000708912400e0038524079480060000301d03030390310029047c500c0408480895403078200014850440b61816111904010030b60f0490728032442204606a441e48015880b071203259a140345c26080c810000c81c90b12030036480840a1150000080c002d01c4020f0095035400f0044100100f40241c501034900042c1c080d650001707420241d410075403150300c1d410110340502c40c40d01c0002004600d02002103114955000c0c4400380c1000420030000104005900038020a500308100f12480000140092100d0031802c1c0d005846068207400148078094040d600140103103c03039401981142000000d040d222a0310f2010401485400421401000554055105070070b070010f04240e01c640d81e17800c10020105004a5510029107401404649018a4202a040005404000c5040040170713102900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 534412517 1250 534411267 534411281
    0x30c080901051b0a170a0c020904020d02060f0a030b041a040c140a090302030f03031e1312080f060102060709060e030a020406060f0909060b0d0b0111010c0306061205010b0a03 77
    0x410000100142044000c2c00f40c40c0281d1164036000402d26000c490030f00c00d20403003440103d000500c2040281c20340c100d600c84000e51a1a030100c880302c2980c2c550340700040142d150700cd002900706002148030074200543d400a032550510f507460901100800e1000c00040744c040080d07061605032800e54180c418189940943c19120803400c2240c0f2014003890303208015000202541e0014811003010310441c01c0c00e021600040040100071801d50030301c00300c075000380d043e0101d40021080c21302c3c002501c1e00d80b40c0162142d15075040001c0b00040c000107440180401001c40707034849495008800302d4410f51001800c140300d034880e42e540200d0113060100c2180d280c0780c41506141d040c81102e01c510090b82d11031040400501c0e07282c80e0b415820681c00c2003c2d01244c0c01d5400202403a00c3d2030010404060300300215402c010a004000810400043c010b80700004001180e2095600c0e00c4010202175402d6070080e400c1e551545c54005000e50308000326000c1c0e038400d0007034004500d014841c60000320f000381c00c882c1d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 534413767 1250 534412517 534412519
    0x50d030804030314160f03110403020f0a1805010914060906120705180a05010f0b070f02040f0e010906050109020a09090509070510020606090c160b0c0f040906090e0604030c0809 78
    0x3040c0600136181c10003e000064806061090b8040c140a01d16078114151681348082801c0600000320329160064840c06184000713401642110400c2d507050f1345480743c800c040c01c102c01c000701c4040314207104140144400d00441c0c3c0440e02c0d0481f100012580c600c11680b040a00074140321241d80c90905001d0816950040d01ca50bd120b07400d008180c81c0d0391040c0c41291580e52540300d1074140380204413101074504c182c0c4052600340300040280149480301c0d04a5417140d40003440258a0005480071070000c1c01c11090b03400c0501d1400c04031144c400c00640000d02014000d40c41440a640c0f91ba807590308a114002c000f0022510100040258080d25008103901c00360110030780e081c040e503c00204220142682e0920b0050f0006410800b0718984050180c1e0082c04024003941010000101030b00b0f82d440140003e80030001d8140010030841c6224121040c001c2c00d89009502c480e61241c1c040080e00b414083d00b4402410000b5200020200103605846a5003540d2148070500c0e281d29112816440b4000c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 534415017 1250 534413767 534413771
    0xc03020c0d0e0a0b0d240518040309180b030610050609040b0604030210020d0f020601050108040312090c14030c1219110603040c1d07120f0b03060f061504050d0308040303 75
    0x103010302c1c910043c0c0055040007001140721039142411980510003201d800e0700d000700e520003d0010341c42304040c01c050040c41021300f0343c40381c80c0c40c2029120030060b580320000070007100440003030100064116030b031011416000c48426448610125040b45a9401101c0e0000c5042c040d210680c6410703000f03031030040303000341082e4901031b00c2e070b00860880000d2008000241c1e00410303820a015510031000c4040c010648080d00c1c1e95410140002c1c80c0e050007902c041d00304045407580030380114040e0300822081364031000e0f55040360303a41d90020b410710138901c202da4880d000d0030008550900745060988540313144080541141511112481801e246040b420b485034030107020421900e85401004600850140c14034100e064501240c1d214402e02001e084d00300d03008103c01380140f10343c02240008201c1c2c03032040007088d00603014107060000c00c3c00d80c1c10349505104400602520328944040790740101015910b180459582400d200b01e14417551290503003180c05146030202080c0f103030b1085600644640b0700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 534416267 1250 534415017 534415019
    0x1c050a090504090807150912030207031b0b160806030c0d03140f1e07150c0c06021902070f0f0b0304110d0c26060c0705120a0201020903010c03020c0d0e0a 68
    0x100b82240c0c840c80c2c085820100000e81d68050003110b01e0100980d220842d803c1c04003003810b41c0e80d0b00100303803105918400d0503008200c140030540540713041101c0c0302e16180c0c03040800816060522040c001601c0d0035440c40c2a440d5010502d0344144c801b240300306405801041882281001d1104040c2014001d8040111150000d154001190010b003407110b0581402515200840d001c2d03419108140500302041001f0028900010010705011549140500340003508001c10b49060310030116455008108500c00942c2c004c0940407021140d10008060713003154500341d11b5007060004060700780128800300d0000c400810291240400a42c0e0041c070443c1c40750302d42c00000001c14440c0712600c3e000c5400303220142c418070810707501c0030310816003a1040e050480c09082034401d113600d54901414561100b80001080342c2480020801000b840c20300c980256030b500c0400303800034001d4021042e410b100394280480307038000500c28000c0d14103036031001020b80079460b1841c20980b4084603254403644c01c11002a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 534417517 1250 534416267 534416269
    0x1f020114010f0f060903030e0f1c0506040c060206040b04120e060a081b0412060f1404140609120d020c010e0102030c0d200a1d030703030c03030c021c050a0905 70
    0x10805000342510b410b4201d01900f0f100594403844940d4102c9810014440e10400c0400e510242e042c100d5801582e24105500c200c2010504a0480c440c2035540b5203002d1048400300940055400d1080c0c0c001c0915172a040d03190501240c80310340a40d4054880c03109540400d000c40c1821105815104c40c8d414001100d40c031100215060340c1001c01e444c00070980980800104100e02b00709825400c0e00050350a2500741003c3c403e090006004401a0240e6070398441c0f52240302469100380811142c4944044403403400d480d04c402034070611013000c100d5002e520701041c2079580002c0d40e020b1007958006158248002140060000c2d041800c9403200c3d50f48036038036032441110030f20045025208802d48181d0760241e520802d01130300e5070a400f0f020301090011800c21a106410160390b025506803802e100c002041511102c00b402c025005164940280b4070300001b010340207921407030f4092190b02d090180c0c19107298140c1e214001081802c61a010024081080341d200700028506000182450f1020381d40f150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 534418767 1250 534417517 534417551
    0x1513031803021f0813150f0612060504051903050301150e10020f070b0403051b0d0b07050904050f040f150e01050c070618320f160609051f0201 63
    0xf15180c000d011441c00c0c07444203a500071042540200c0e40841807904602660b1340503003403030707002222001d540da44000000d803441351038102c0002003081d150300c400c1c45615814004010501620102c2d200e1146030100c807030180800ca1201600c64040d118142140c0c070341004840055004507481041106c0a50780c26540c0d0f40d0507043c02c425040b150b000b0004058099030013858144a07401403907034060248020400280f0004d00000300703d0540790540c0300040c2c00404a2080b500b04030f0000e00303c0d48000208024258402c02909c0b0000c412141400a603d940c02d440100d80410345001c0c02550b42c83c4051000300703603c050710503241100301d4070000700d000c842000e20342120700540d45c3c0641c0d5000000c13850103101d15805038945640c402c400d0464944620703a12018000044680d01418544917403000c11480200a8010305001014095908010540c54016210040b0829892a2880d001004111148129002030070340d1009000741d465034440c42200b080c901050b4001c40c04540d20351102903411607611f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 534420017 1250 534418767 534418789
    0x60e0303040c0503010b060c07030809031c0810090501120201140903160e01080f06010603200703050304022b0f020f12100c18150c170408151303180302 67
    0x701d01c5812143e04050405082d1200b0701800ba210b9003007803051728448600428801c00300e9620889003680c592032540031130709189a50304165200d10428030303058030303180c0c00c20b0503107101d04034586e61507401540711940034040355020b00a540a0310512031450b030065001c0c070b610031180c00250004034104110703030001914050401c1c0d42109441005001005041a03490342c943c0500046405400721980d40f141041e41c1e414144900000c254031026540c6d04c0d0a009519a002c1c0c2e91919a901d94403092820040c0c025030050300c0880c01180e621050a0311240c038800c414149969001d6455107403000c90300c4808051808403800c0e640200f12541842c426612603154021220390200075128240320901c0020446200002060078080031b040b150190110901003c1c080d40e041c454510b410054144084072480384070303440200740b4860b203030500c680300540c4000740080304e0030f01d000c445405030b1140c2610254031040d5521642c040840d00c00301c0002e802442071501415101b80980170381666a0001040a821 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 534421267 1250 534420017 534420023
    0x7060b15040801020d0b090f0f07090302030a0b01050910030201050a12020c0708070510020c1027061e021603020405090316030503150f18070212222907060e030304 72
    0x200013030204240d102c03405011807403070040b47d00e00700030302d41580350030441c4100500640800300b100c400600342038050002d6a01450300a011a80760181c40d281a10010500b8000d80d40b04403c02c00000381c110f000c5400013000e40e0381c107030345003814040c1407801038922a0180c0700840110f50240a8003000580030030081005000c0304005010071031070901030210b001410724002045410048044105840300303503441c0d84c0500c1603d04101a503030710040044a48400d041010b0340b84080c80340c0028130390750214103103c01703420101e514001c01030251401d0341e483c0c0b0f0121103140e5001d000c00c020000351a1990001ea41700e140c0320b080c2ca20388155251600c529100000045011035004002d0000695208052800051050b40c0302d0030440f110100007022103403050a415074140e03402d000541602d10034415401842d811111541e2078603122400d07505c03401d5840d41640566101e4250002e040ca4080c12030143c042d0741d80b05569801050500b54060381e80c00290240c1e40d40391500c00f58206a2001c000031031080740 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 534422517 1250 534421267 534421271
    0xe0c070f29010b0f0d09021f020708031c0e01140109020421020f28080a0611040f090207050109020603010306020903010c05250c0807121505070507060b15040801 71
    0x141e1103140041005415204060403400e00040c07082014400840f0b482910482e40f6a44a0182e44100c2c0040c082a1a0007900000c5018181c84800c0750085007004a24080d025112a80d0b02c07034541c0c0d99030f4041c2e00e002441c0c0000c03000649241500c03a50100309902a20000030403a1819420140710304c0c4000e1348445080c550024041001c400f40310100342260505000e1042d040c00c05400041041c0e080520103441a14800c10f40070610700c0300c00c90000300b0303040d84c89079103040740d03440308080d8881030034204c02c2e18040d04080c5046032030346c4031800703c1c0c1c01d55400440920b1800d05001c00d040c004c1d0000f0f10120b419660324115500580d8030390028500851140c5c80140e9a070100c0d106260941c0c00d40361454050120502100c907000b18459004544080c400500c0101104e40d420300c03802225003070340303d01003074001d944011603521113080d00d004030203004940151251104e24840412640c08503000c0340040d0040c8402030008000d50042d40b000e079001400d5a40b10603c082e00460a54800d03884400d0981d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 534423767 1250 534422517 534422543
    0xa09080705060a1403070e100e030c0609090c160b010b0d0f0e070506131212110609060103080315090a06050103061d010b0306031e0307030e06130e0c070f 68
    0x520100644809024299051414401d954901502d01c1c02c208a80340c5403c100800001d41c41c51190324000e145110080c40b40c1c0c1d9100110320054403624401c1c40346402402264810009400c140013107807031220740548540c2d0940c2e0382c0420400b0a2b0010700c141c04524104180d9640404c83d12103540c1d029250203031a07103540d40b484170000d0003100c04100c0c0d000c01ea00d00303210242d60005004242d03101114003c0c2c400680d600c9404005d40340b100341e507400034551000c2d450310b040c041c0720b83d42001c01105480ea0315940c0c040c07440e540344141d0b21001101c059480b0b40c840e10040c40040c0d225009141c020300d40d5916280e91141c0071000588115080760310b034030410390302c80040201d5a032500800340205200715682d0b0f40d40400e40300b8074807502014021688080b40000228159450421180c2d103280041d01c0b000c155003401c10b131659103d45c00b51009400064202110860b00d10b0a4412580f0508149100c907000d02d01d0046400509540100146002a81484804086241e2800e00718900d44105110402c1c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 534425017 1250 534423767 534423779
    0x11070806060f010804150b0109050612010303170f06101b0f061d0c10180909061d030306011d1201020301031b050102030409090f06090b040b0903130e0c07080a09 71
    0x80342c0500d1155040203015001c0c00003040c0c060b800c4404000402d6008200202d40b10010b80da601020f41c0300c035402c880002211049000000c899905881c443c1c0e488201c04120102031010b544016501405011329481c04240c0718a0440c41440300d90849040900901098440607540700c410003405852007650a13403010100407541c46980d10f80c00c007004183d11504c1608940365502d2220140d202d008421815000712100e003d0015a6009458101002c4a65403108000b002420702c01104645450501202d01c1c01c1b1117070301c2c441d02e5405a00750021402c540d50784004451b400c1210780e20074420f940580d01c0c0f030308589400341007004c854444c50000d82d980d459880c1883c241c9a42e1484c2003081e0b02d111405202c260303408000c4400700e802051001c40e00421504281e103a030108a903004191601c3c02200d4003c1052400b60280b2072405091401099030b00c1e494a079869120b07084013000e504c7e15920050103244051103d407a00001c20002c1c503401c283c20350343c8501e026030200e0108804180d00d10020420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 534426267 1250 534425017 534425029
    0x9091a090606160f02060c060106210501030f020108040614011d1303020715110709090b090703170a02070801020c01060e0115050a030c02010f0914070608040b0105101107080606 78
    0x41c0151602c520b0b10a482400c11000303040f0000c001c0a0b20800e1945030150f50318181944c06501b21881582c3c4296503c003005014181030300c0070030100441a190342030402800e48510b41c100c0380c00441d0320744030054036401101e0800c002042160350b42d41d201004202d04a000034424040c02001d180f600c4e15582091080d00340300c0c4018070010035000f60b03403004000030703501140d100221358454150b40314003859490309840030000740c2042042881101743c001119030580c0c0100c0748050040001d800980c40305001c031525440640000303401651a1010103000a04c0390700207110140061050790511a11030448609980c0310516095260b91517110a0054142c800040b43c0101011011035a21120818000d403c50050b004400141903490500401c1c050003900518401c00d802101001810300d00d1400c1e41c1031203071440200307945102c0c40c030001c20507038081d0185134000c0d0f0304281c0400c5180c0ca84001c001c0448111407042e020043d500b049071859010400010021f0803018000c0e00003071a00f2000c1c0a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 534427517 1250 534426267 534426271
    0x70f0b01170f100c091205030d1407140c0114040b06040b090702100902010c02060307210c0914010e060408010515100e0409020f0d0506060405060316060e0109091a09 73
    0x140320b40060b900d885841c500060b002944040c80800440d024601d450b0540b0b410095510030600d40500420070410800040700505070f80e01c0015041185444803030300048804011108480031036082c22441005000040c080c041420207640003082241ca803007507130030b01400e0076501115085411018000070f0319050003031101e404016221042c940c0303007020000750b0703c0d400c0c6c00440b540c00790b49007480415640b02d16021000b06401402090340c030300303203800001c003100d80c0c0e84080380c0101054802580005942e015003050090160ba6210150f0b0070100102c0c000c020304141c49041c4004c0d80b0f4036003000e8940c040a0300c01482013200019681c50801081c000c40c4024100300c03442016031051504105401c01e501c40c105540984000400311124400729680b920240c401c030764840e04c46814103042100010301c6611841c0241c605200540b642c6041c541c0d54a40b034014510581001c00061010610505240c10b4010051401c0c00d01c050b0348008010071030700c039400202441a2801c00005484c2032035010f0755 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 534428767 1250 534427517 534427559
    0x10f061d0402030a0803100306090b04060b0909030405091504061211030102030f0a0203040317160e090c1c02070c0b0d0b0a0803030c09010513080f12070b13020105070f0b01 76
    0x240480c40e169002075111300d00c210004041d2400440407030140c1904049080166520280400c03401903a07050091028404840495489003481e8040303031a400e003091424044d4086030000c41c01c00b0305160401800b02340040035800c1a10940700203600c250364500560707004100032201d2005891a50400b06660401094654040d03070040003800100c000080510740d102e6000c00005880ea00c40745401c50343c40c1d4021503000603c0070400b007440b44801d150303080b00396070030f44036142c1810b0516048284050b440e4222540d65000d4000e0005101c5285400c0800121301c24265005103082c40994508a182e1440e4001c656100030100d064240030700301e4407480ba0020340854401003511324091007582d0740e01c401080d03460003503008900c5070301c20f902400c103a44401d0812903011511649030429113566140e425203540062244041c90b040210b40d40c0300321030f4481c0e0403402480c65507540e80d8105444c20480c2d0400c0741080380030000d58002c900030309080d0b52a50f100b00841046549865007402c0051400b80240c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 534430017 1250 534428767 534428819
    0xd0c081203011401030c03020705011a0a05040522050a05060112030305070507120e0301060315020d0605010f020607080c070b090d08010807120b0604020702060c0f010c0f1d030f010f06 81
    0x14003103030082c0c00b4002500f050919001c100ca00441c0d030110083e00400038010190740c2003049801c1c04070b141003207003c009142a111040216034039010801501c900ba641965000d800015039040d140450500c40d156034000d1007240d03400d0450382d58040c03403d2001d074003d450203040d841882003015814010341c0c5e0020614a0418100401c07521050b03240074500340c1c2c59050146044d0a0001a1000c3d040100110f4000c010a0203903400341e03003050080d51100c400e41003854608a40840c2c00d6002d4540b16015245030307801444160350b10002075410440241100c050b075803050160388005143c41c20300520825801d03014240800b503261010317081c813406810929103a040700400f030102840d008038050030365400951350006a00e501011034000d02ca0329002a41114001a8503031031329a000800e02c1080d130918000700021401d000048030114034444440c800030790315641044410000c808000707000d417802400c1d140c6090340d600c0c00da400c48407a00501c140964a410f41001440030f00007443d14017607035903824 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 534431267 1250 534430017 534430019
    0x206040e091005151207080a050a0c060513090506210a030801210813080a050706090902121503011e140603060c040506030a140403170619050d110d0c08120301 70
    0x141c0c0a82d40603013221a0700075050300010300405030080000d50000d00c80c2c0001d440700340c4014105503481d0041020140d40d00381d9012000510039105404660b881c0b0a55030300005220b080001100c05001c0241006500c90000180b40c041c8031030103140c0c8044654840010071601c00c2914010703100d888140d0141880e1a5400034506029540c520250b6807154802d8005035107c0181c5480c400d40c00340307504045224800d20311030a041000c0003170750300c0551303185843c1c0e100e0349641c1c1c03a501ca0980c443e0140d074640400c0904007240050b49000c42030281942d004001040a20002445841c0005228146100c640c1c40d000c080d454041480c401e103410607c10390240c030302c2d480e00d00c802000ca445640329607400380c480000004d291020075400610394402900b0149901c1c1014100204103039048840e90015046a0002c82c10302e28204510051000c44101c01c203540c3c910302000c0140f12181d569041d41d40300160040d00286651702006d0307403803440c0300d01000040c1c9400c0c036910924103a03501c40a0000034001f080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 534432517 1250 534431267 534431281
    0xc070506070801030312020714061f14010504060c0f060905010b010e0607020913080415050d0c0e030c1012110a030c022a0109090212061203070209220206040e091005 73
    0x20514400c1c0703c1c160248e561401854256078a03862940310501500580c0140484100f21146400c881120040c1d081021511546d5056403070680440160100340304100804c00140100c9402041e14000c800940031b021070354031440150b40103944115050f07592050380d11015030f04101e60290100041d40c400d8100b4895070702180762010064000d9000201c428800000c008088040b00d010f80140348509510300407191b0064001c1d08100b01c8600c0031800d1500f00341d0628410323102051846030040080048294200c00d0029002032251807108122620407081c90a1900740140780c521004644095525444904010200c42070304080c141150026903500c1c1140d0b002820010025410400d000d024a0804e401a22604815808482d013a800031880c0901000d050500a10821054510200b580c81c5006042d46038407480800035400111003000c140701c0bc1d41c00c2000003ca55107410041c146105540001392150070661005d07400c01c01100c02c0011921091180580c180501c0d0020b000345c1c100a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 534433767 1250 534432517 534432527
    0x916060c11060f0f1804230f07050f040b030a051b030c0a050d0903080f0601085b0f0501091517091e07060206010b0d0f050c0705060708010303 63
    0x1001c1144a0500400c0c55452040980c00f100c2c60405550300c002c4da1045441d80300010413003244001031189260103d880c60010b9040032421203c09103c5002c1d8040c0d4400310a400e040c00040c11038810000c040c01001d107201e00711070080000d800c11581664607460039000c10741c1940c50090140741710440214100c1401660401565000760f51400708580baa844a4001c4801e400741c40c0002c02500c6c280500441031542040d111802030704095440741c62030380e81d140103444850080d40c1c4100454084039a00d0f12312041580e010003903040600340c0c0d00d1032403054503a00f20004010240c20410b2648003880c00c192200200e41c000c0289496a07001b54840d18000020700856014400c606058880590400701c40d40702d492820308c0407084810300e5001e42010200d241c0d0722101c000307020007200c1c011100030840e141d00240c40822605551b0003480503030309110007050aa040300030310218843d16460325002074200c0d070065601c120031450409072102d02c81d00b8800c0c90810080c00031000d0000500060001c40c0e482 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 534435017 1250 534433767 534433793
    0x423060a140d051008010f0c020309040b01120504140d0c020a1a09150c160f0b0a050f04060e0109140a09021b030313021f121d060916060c 61
    0x54100700d0103424407080e2040c194030480c035450882600d880300f08221601c3c01c03030000096500000c002c1080d102000c91070000c81e10407964003401340c0d1050068034060300d0107801118030040180340c2074503076404080c05030b4180c58055608a450010460325100200410050150440741a240c21004000315401294640300c0c5402035000c02002014441c403400c0e00141241c200301c0018003403100d8207620780740039850b68220114032409070150400d010008034828501e403098803060000c580340d15181005610751540319419001c00d1041c14801d42010340b0086000c1d000410381516180708240b034010004001c0039080d080408015003800007802d0301d03200c1d04146002c0c0c0715a88001070380d4030b0407056040104408204000b480f448000100100b000f8203e84201c0014070a45518508a00d071100c642d100306800886240001c664801c003d180300c0c1c4940114000c0d0360030300c09040b40c0e540200441810700b00102c4803141d01d130380613000440e50080480103c400400301440d1a40e0300ea815691414644195 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 534436267 1250 534435017 534435037
    0x6030c150f03070903051902040b0604080714010216080d08130302061603290a05031504110604030c0b090a1719080f071401050a02040e0a0903090812042306 69
    0x20100001d94804d0041894201035a0020300b101c0441204207259100e0030302c1018128003e506029860481e801c00d00240c03015110035202401c1a141480c41403842941c184070107a04502c25403e07244140c450f2466500d000e40030782000f0f0524568500c0780a0099040070717004e031951250409018002c2a408140c003a0000491031240c40f550742052000c401a02c0e09050710003180540a4190380900103140380365a2008050300c0107800350b44e0b90400c042e219000c411518aa8218010004001440340c0440c041a0000184118103264036619000c160940315001810183c9000803402c3d40c51520304030160050640b0a10950003803040707800309031140581c891552131403900f01864001c01c0b40071019116034115107019180c4801003400c00811345111485035040079481c20011481c010024006c481c19910748602548140d1901c1042400a0140580c00e40411031840d1021071240820b000310405078101016094a0340d05004c200c204200f1401c03020b200e40541041600c42d682c40e0300e01a2228011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 534437517 1250 534436267 534436297
    0x10c0203090d0201200303090d080603070806220605100618060e0f122506030c1715040e010c0e090f06150d0c021b030c0a090209030708060405030306030c15 69
    0x101ca45c4c1c1e44400d50116902810305001c00310810482c03140008614040020503902d0403200e846400078503403103141c82e0081c540541c0114000a20b801001c85aa00440b40741c00c0c0900c4008030103803103e00403200c0658410401c101c0b62441040b003680e01452000300042c007410b035084c80903d0080301030070702a0b45003400c034019252940910055a03425501a0345030311024141c0350020102d080200501449080700c040b001d0000c400490018480d218038126801c1c25201e0001401e84001d5140328407074020180c0c800e149900d04075181070303144c9028036261007000100101c1e8030a40c1c0080502907a14201055004204400402422543d2003948a40100e07055400103084414420f030200315100302c02c4015942802c054407080d41d1070740000d0008000e44122900b070741c44000e8000b0107803600440080d8686c02401400d043c4032031080fa900030604c0590050843e0540c580c0c80d92442c2c188402102c00b945c5507000401004a82e082c2404504100301c0110b80c081c5180030f400a041c0f0725070084c1c00968078641 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 534438767 1250 534437517 534437537
    0xa14180f0301020f03010e0f0c0f04050409020a08010c0201140c07020a120809121f0b280f030305040e0a020f0a080411060325030b130e0102090d14010c0203090d0201 73
    0x28a0a41c1201c07500030130406841d58940e142c8454520ba400c0a6030318000c06100c482c0080c9440d500c0d8425200b240682c884514a403170314050030032001d0994004213a03800740c00c200000030540b40c01d104907680165183c0001c00c810150081c1c84400d65070041c0518a0100304000580040e03903080d103100d0507240043d000711002111820983d07058003d010b40703030380c00007411540340101110004055641d030b80c098846a01c0000704016450564034034404640c0c10210b4644400680d2402c0c0c0e02064400352103102c00031311581c0c1e4680e805100c2080e980280d000c540000350a001c003645840420358000380e01141076103880114150303805617105004120301000f0012011070b04008400a07083d2899038010460340d101e0502c040c0d90390000440c2c0307111002c1d036200c0d03807854880d080c06401201398070440188413140c0541010b0b401c034046e01d0000c0a5451a5601b001800308a950703411047c2600c0e0b004500180300000d9640344282120210381c0000203540c424841c400c000c2ea42d1100001640e45d080c41e00340010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 534440017 1250 534438767 534438769
    0xa0602030c130b071104140103080307022d0c060903151f06050316030b01050f07170d02070b0a15051e040c020d091205030406031d030f0a14180f 64
    0x42c00b8a800c550364052190300005a1909040043d120940c02488010481503000d004c00003114014516411483c500e01c2c0104045460b11024540c44913203801614134070500101400c0b0a030880b01c85058054140000301550050b0800440c2254a401d94480e4a050541c0700065611101c98180c2c4130120100000a90701d90200f0051085010080102d1409251138241c0a000b6030021100d02d03082515003d41070500a101740075035040d44070182c40d44c61828030380600000540d407090405607000e100c00360501da1410a600010105400790650050315900b603894031040014001e06184021801c2400d503d442c80604000c640c110358040301c81002850034040b2103030100d08460b45442d8070901c4c2c00d500c1d02585402040500785a4881d1796406034030364480300400b140300203c607c050583d03130040c042030200360f000cbd6105910100c2980c03084503030301e1000c600313240c55503220410041c5914804914407a10300d421130a40d80101d4072481109080018400a0541101000d06c1540c890905003c0e400c0c0301e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 534441267 1250 534440017 534440041
    0xa0b0a0312030b1203070c03030e01020c030f060103050106270b121506030f03070b0f040519080d0b010c051024081c050306091810020307080901110c0a060203 70
    0x11540040380803074840540c0ca01500810102000c98000c0c00b0f00c451903500c03e503022040721070040d0301007031054019040d030310111380001403252454107520900100444540d010803050460004c01002400e030344d811450050300b9030f81c00f98030001d400c891038480c0d80d01241080708818050b8041140010f0054455000954458a030042039040381c02002c1c00b601c418002c0d050a64401e0a06a04591f407000244141a50300e2080d444043c001c55040004101000f29903c0615006030245089941c0244050381000300d01c4988681120704110000d544140c403c0c1a000304401e9031024244490b001c0e610f5140d03aa1506400e807182d030740c40d940d01c0000c44030000c8402021003619110001013421148c0350002d01d80d4038203805184c1842c94858010310381c603503403247c01124441e2102518850311500d81050458080943d6444000c042c0140203492029180600c00741d0711442403642d45103070508020000608499486005580c1150100b00c0342a45080000b05140501d500030001a6281d03514501203c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 534442517 1250 534441267 534441269
    0x18061a031207030c20031c12020d110c031b0a0f030507060626060903040f1a070210091403120a110331210f140f061e0f0a0b0a 56
    0x101207a85503045c03c0c13041040f0b02c0e4100c00009070221904892000747c102c0307248910610010004200110642e1a5045500500081003800c600442d200940030004000d43e00a41c094060503400401c40b2f13800e8201c1031076a12640c0036404090540c080e0f8a0f1a404041d154081000c0c1c28480005000d908100c402e92020009002c0c1240b141c0042111a081034035201c0c000032010540c2c450200401c1d405500803003198222040322054600c010b2421030380504450764190b4100d91104140000009601d94a9202d60b40c900b20f40c0e200c1300001c1c2802c03190303500c900305d0079402c5000c0d50000c00300c0b0200c02c441c00b0894840b40141d047c030350100c6601e210305519501c6041c1d070b00c044ca80100b61440d03c85a00c51500f03142d4600d2101d52480c9402e450b01c0c18a540e446045402c02c1a120b000000040860058a0042d8585020313a4021540c20101e00807940750601c5034001500560110007041103068074100c80c10a04000001c80d207066040071144c0d562044c2e00a00b58030b258981e14400002541d440784101d070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 534443767 1250 534442517 534442523
    0x170901081803130602070603060801061202102303041208090a061a060403061a060f04032409050f060c0a0c0b1017030a03180b0f0a020c0118061a031207030c 69
    0x1103c0d40c2c3c0b1080003d444032010b22035035010a04242c1e0205400b20103010303160030b4901d00384a1070818500743e0200301d10b072008651010103000041c1c0c04001610500043d4880002c80401ea0030350342d05141c40c0894404190106410804c200202400110704001c101500041c1d0000710114101c5c0c0401d0074040075140380c40c0000d5102b20005000010086560440004000c900600c2d0600c0301201041c01024800c801601c0ca0b035850801c800d0000641c1d40c0321302c00303120251030001d4002c8072101440008580c0225800d07206d80d840f0f024180030701e800812010b5800a0306d1081d0606100d12a078015101d0001140020408030642000442d18508102c2607070040c031107080314002401014020342d0f140d07032040c035074040001d00b002c044620b6400c00c03034510410396030f015404e10780f50395500003040c88001e0b0240078000129020850480c0203182401644425695540c40f411301d60b00c0307031078541c0c100ca12101015020382c03010300800c2502c0e0b078041030300c1c10340030403820101d41c1c0e44400c0d2408580c0840c95640017 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 534445017 1250 534443767 534443797
    0x30f0405070b041d01141008100b07030c02030607050a09050d080d050705040e06030d14090d0203030c0d020115050a0302241b06070c11010f0c0b0403020604170901081803 75
    0x44802c0302c031403048104203003480e25802d1641c860f00b080001042007014913400c2034114001c2d80b0300a1041130382c0d92744010041800b00100391511002c07175503a4000c0c50b0580020354948820300c01e6240c140040358000d60203080c41490000040c43c05001d0007190301c1454441c0300498514001e00c00607404450917095812820400ca103480b21010b0115001401601e50407685000000d0361400d0000380e4100411054071107002c0c0c003007560700c2c5110550005980c243c2010101d4200d00050f201000035040c040312400241202d0900c1c848002d0031503015070380e0034290102c0c00c4020400c075126078403050241d9070107a03103070f0302404064958080201c2400304038100c1842e00298106c2075031020550300c80d1501d1000e007500c0e2141c44100f002c40d0b12100101c4003030481c0110f5038001e01590301031550181d0300c01c00346c03d00f9114222140c070f4040249004440540150700444d080000b004080e03460312101c00368a403152070402e10200002404d1400041184054040d01809580180400c00613200041c00003401c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 534446267 1250 534445017 534445019
    0x904060902220602060c0c0c10110c040209060d0c021f0204090f091121062e080601050d0c08191223070303090b01090e0c01080c030f0405070b04 64
    0x100001d5101000c071500510314001102c1034040c0ca41c4810049498550003044103481707062040100c0da1141d401d82c0558031440742d0310302168940405007800c0e001e1726120b1000c040700113100241042c44440505102e54410040d506282d520310307068507480210720400094110f080c5100341d01c4e000b00309001c0c90341d4039012181010310000a800400c1070b035040c000300340242c40012780c450301034841d0003000901105007149140e40c141891030a160141c49000400c42a51280f042c02906014043c1c502c4c43c1c078007442448421550031145c008200800e0300e0b5114007003041c980b0011603142e440c1801802c1c404d4102c2640102448130b0100b002002d810b070741e802e03035103811078010741400d072101d07d06001c540c0f50700c2c1c11003491600f40c003500c2601701c2c0781000d04100c0c140206540b09800e82e0760004a0441c01d060b6124030034004590303030710845800b81140c44c400084060b0201ca80e6440d01c402c1035511410000d0407000c0025404209007075907081100c1000700c480d2502c503480c20340e051248a41000f0061500490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 534447517 1250 534446267 534446279
    0xb041a191a39010f1112100506071b0b040b19050f0f130e2809060501030507241e0e09160801090204050f0607050c0405180f060106081b090406 63
    0x3001c0b04504803614002c000c0f480d41d000c164010385400856403480140e0900040408069414030075900070785c040d001007030258494000641580008106a80003102606c90b58414016000000058840c0e11036107800d16251244200c1daa00c1031050166402200a1b5409251030107002951640c02004054684441c0e01580300c0c141500300020740a4501100d0340d002a8090728020300740d02920321280103280f075401025170140415840025100103580c1c031140c0c000440c065200d43c0b800707076200340041d2283e2480c20103080c8400041d14400c0480061401001741401c1d001403049010030320540a0003000f41002000b6259407040307804803604110780104001d1040103040c0b002c1c103c0364a684850120ba600c0d001c40301c04a0003540a285e42281545107000301c07a05c0c0c5100906551440380045543ca030300c2000c089800c1d60710a071528100c00c000c581c0d029151101c24085100310851120080a1541c9032400041c030652014004034140003d075185c101d404520782c01202d8651354058424031056035180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 534448767 1250 534447517 534447607
    0x51c0c0c061d15040b13210b070206070f0f02100c030f0c030204180b0a091103070311030f01140117160905150301180b041a191a 57
    0x8882d0714000c6030758142e1140c1c0c0d1030714140103000c8508098440c1d0030b01c0d05018480d200d07544401d0940401708a14640055080103401c01088203407013400a4000000e0700d450100040c4901401c01e20564103e80c0070404a00d80c0120340211144017441d0800345a044040140d0519070844908402c8508000140b2a01a010b070403004d61031401c4941080000720ba403800310124001c0d0f020303005410b200c0084042401c5039640107440040001090080b682d030b510580c250455583c9100b5103510b80021040113035154040c0308803440d80310001011440d40c9003048036000e9603801405041e940c03104d41d41c2015220b900c9040406850300c4010080c1179982414800d4540325411086154001554004041050b00703100c240700b08900c0c0403081c42070a5900306410842c0d80244250380028199075000844050b86d29030188401021551030081e041d02110420300800d8094941409860100c4900800c00350043c4990458400314000e010358440030740019824000c40708624006240c0544406400150710301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 534450017 1250 534448767 534448787
    0x3300513030f02070803120619030f1a01030203150c2104170f0a0309110603151813290108071e0608010302010e220b0a12051c0c0c06 59
    0x2d84502c80b00c40c82c0041d04a981c1c1056001d4031201e5041400641350b500f0b00380c00e04c80c0d00b190004050384d20801030101c07450400c00d002d84c0244c42100748251004180884e040548080d20f003003020b0f1005944c115004a42e43e0340d5045001080c0070120700000d440c044506040d520079412500d00c4600364001c880001e08510010340b01680c0190544200c10410543c840c100c4101040c00004035060102003441076004146075030041d26002240b181040c2e00782e841d800214483c42c2e1102185034203130142c0050000841d10446910b9a26113204280700d80c4000040403410741c1607000c482914905011900302150500d082800a0b401e0f2aa100101e400c40d8040750009c252080e03068003204140c441160103071905c0c2c0506c194800b21b2051401800594401d40c0d042544240142100821010020b4020801c41a1078112908107035160b2981c00146412104007004068260b05680c4c500d1040d140c0940b255a401c10b04004c141481e880c241149005400390000c09410001e4101c49580e2000080c00090310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 534451267 1250 534450017 534450023
    0x1c0e0f120a0b011203020d0c030207080703032a05100f02070204021303030210020a0f080c13080f0c0102010b10050c0f0604061a090403080402120f010e070515030403300513 76
    0x820000032840103901c4d4000da03119030b0554018100c10710941000c0d6039170742500c40e0503811406140c1c0041140d40c0c04100010040d413290b52580794207020714600204403041c00c1201c030101e2041101c0c0b90017044000800030200d0101c40c01c0000e0050800b0020700c000d11030150300079001400441d0b0075001800001658084074020f800399252006601742c0b40d02244580c0307500c1c002054001c5150003013103108400140e0320242c592029841d05081040031000c52210340e01c800401d0f44041c2d820880390b401804a41040c01083c002846490701600029100001c248030740c10801c18042210a400d07201040b0780402401c884050340c40310b0501c0c2c02c0030b8028010001c40c62214034200100c1800c0d50524400740c901c10303a00f582da10388054a59608006c040c10072052042c0c6c0d1b0b03120308040646500002e100c2c585813842c40c8401488000d00d04400d2000e111520090b10441000070300801c404250800020b0300152642c041c804000c5400c0641d414010520500c1850b9142c540001c10111100d0016141c0e00140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 534452517 1250 534451267 534451283
    0x9050105011a0415030207020402090409060b010210060b030a020721031a06030403050702090c040f0e1b0c0a0f020102011506170f01080a0201121b0507030e031c0e0f120a 75
    0x11004914054401c1d44110059484c4140d2040c0350f49110b680500045440148003515000c1c404000400340c03803401d40c080c0c0e1180c0c0e42d120510f10644e0100300004d212204c216080c810a440c060765103655000050201891a8000814070100880c86041c200710705800d405950300200d4418000b002410f098011071441052a6455503c9103044415a44071b01c1e0305a95582c94504d16a00b070100f03402c0f01825100d620700c1c040c0030100b04920580035140292107416039074440c03442c040b1101d0b445080701400c1e00d080f4a030100b06c629200c20307010803100e031b403540c0040ca20160314885200403401002101210302d4046c1c20441d01107086a8445c2c1a9071200c5140da1016103176031140c801d401007100703007841521a250310050030000107500900b0030761a00b54881c3c9000511204403c0d03a000c0400142c2c680c0c05c0080c0001a00b42e04250308101003105200d0103400070440d1400410000010801c0c210043e0140000081c010001c1d40c1c07261085e400c04040034001565019041d410660f8408020b04c040300c100c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 534453767 1250 534452517 534452549
    0xa080417011a06160c09090201020c090906011e030503180102010b040509030a120603020d11011206080d05030a0f0e010f2919150207060f05280207030203010905010501 74
    0x1005020300401d404940550040640790b074810094181d118a03101d00605045070701000125100071000c40040c83c8003400070450001c50f1000a0605080c180324034070990705002802110100001e200b41903e2111030440b8410172404100c1c0155041507100806030311000800360608101c0b005e03038138076401080c0c00910105191134104000d0701d07000c44442c1c01c198000d0104900c240d120b911b00d60803100000e44c0c00900c850720798021038450036481700103881805107040c00c81da495900003098600403802440801c0300906241e045a00c9010440c1402c040220100206680321410b034810400108081e00801c0410418044140a03203900d43c15191400d19010703440e41400210510454600c8450100748100c03402001044499007889005e48440c091444c030100e60080f010020344488846034005219203880c05600611440240740b02c60300700038043c000c2c4084030b0030070201c0801011210400300c04d65143c0340412850a0720700e502c003a50660a0210702e0051041c10761026042e101c50122800701d0f5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 534455017 1250 534453767 534453809
    0x503030711040507050d09060917070f0201051c1803020d09140427140129091f06050c07062102030405031c1b030e071403030c0a0804 59
    0x2402a080003500803075185150700e50324a0654042a800481c5050081c20882c20848a20460f0b00103001141c01c980e80d0080401404010201c0324480c02c5001700c89850024150340d00c00380c003890110000d051080108004450300c5043e10020100c001c40039041191000703840d034001040358690410703805401a00301005501d80b0a04520b400c1e1080800c089810071082000d01c0010208400c40c182c40c40e680f01c01442101c045805e5085030603009201c080e180085140c1050300315a02707403100313105985255605a9003c0c40b0f031b11005a2525085074120103581d00c0c070403050b42600e046044055000c41810020400c0f030307003000c081c00703810a11a044500c803644403181a02c14901180894507031000e401d0780c0090f00313900d60f002140e02510a0050b6410000c06001480c0750550080240c402e9544a0940d035450f81c085d4981400014103a02c0d0138040e044034034064640b81e166502480300601132001d400b01c42c54034104112074164900204484a40505080c69107894120b4001e0001410b0404210989 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 534456267 1250 534455017 534455023
    0xe100f0218010806121911010302090901090b0406030c0b0a2003030f10051f0809010b1c050118060902120a0c090b0111250b121305030d0f06030c0503 66
    0x120058540c071041903040c49006442c1c1c41c00c0113014030360020102248200050301488070161002450081d1180716400e4504070240301c0c021a6940d04140c41401158003954400c0c001ca030443e072881e0700000c2c101d444640071074050312542d04041c00a025241e0009420b10400c00201603401c403960300d40c41d594020b501004e501c106807080802c01a40207001248035007214800f01900043e80309040c403201503558020a805c0740761022240c0c404031141000c0700c01c0940044040d688840329a008001182c00781c0e00140240c041400500700000c00b00b4804010407030254010440030a0200840f500780300300c2d01c0d0100203400030031070490041c0d682400409403100c002a040225551041018103010706040c04140180321858107581003000380420300c504250203100450032a440300348460580c40428a4040480d80d03241d01c000b02000c0e040001a02a051015003180c10003e03103c03002c0400400c0b42400f1385180241d01a40d842145040340f105403601d115030280c07046900c81c2c140080c503650f03200c0070952 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 534457517 1250 534456267 534456277
    0x9041404020321041509050111191401060b0f0306100801060507111807120b0a050609040507051317060a020307020c0d15060e151009060309060f0e100f02 68
    0x24050b0b0000c0602c3c10400c81e8190190368081101c0082400c1680d111100c406140c2c40c440c00780c2c04035100c00c400b44002d590001d0125040c03420880200403c00d55503460b47d4545040740e402504060028507121507a41c000e400003001406c1074000d03680c42d001030f100c0c0d82c000355005440c0700d44140318010621140c28065600305040710750645a00c0e0400d030b0951100c03d0100d881e1248544d01c540310601d22241d0728400020140607103220b039900c1c906450400c0b00741c012035400161030340c45801c8101c0100165a03c1320222090312000b0b890100e2581c881c0e20b402e41d564011290300762240040400d0200c1d402d0020011000d000c40500211f50441d00e030070304000120f10042d5283e02c0160482801c00c1c0450910000b60414184503070849412034140b50862022203200303400034000c80303003904180903030303850350902c001c80c0081c04840c005501c0ca940040640f840da4a40305072014180c88511103428400154061403092401d800b007031020b511031490303054803984801c2c0841c4405180c10044110320800307100f03584d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 534458767 1250 534457517 534457519
    0x231f08100e030918060123042d03081306090f0308030601090314010902030c030f0d081b07080a0305131115070f0b160206160311070c0303050904140402 67
    0xd4408004140e1006003046080418540c4070030000041c0a850381c0303a0741c46154800c801002c50034102100010480640a02542c0c8000354034000301d003c00030710008640846425849030166607101d89180e80302004212140c000340151b0701400410b00001c02d0082c000781c03034014140d14550762541020368055209014200008424250510005200500441d00302c10141090f58503240d81e60303592a210002c43d00701c181c05944a150b1981142010416011882401c5000d0301185441d85055603444a0240516080000d0ba10100d0111038507101241c0700c0210141b071031541d4815038104102c5503846070517002c0010f8500400645002028005050b4551340300d802010b040d2212010000844502454600819401c12160307001403c0c20020640035441800801b001d450204c8100054001d00c400d0300c0d0541d0404410001034400f1810380030440070050600290303c0e540b440302c601c0d4074007540d000104080c81e070031804000c0c950860f014020003102101c05110801c41c5d0f00c620380c80440295402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 534460017 1250 534458767 534458773
    0x40513150c080a0c021024050a03050307110a032f031f0e070e01031203050115050403062307030501050a1203050301030f110603190b04020901020a0213231f08 70
    0x42802040140c000a113413a0080c41103030300c40749440b040380c011101c85d00d080d09509218030b0120105020030208440c01440215050009145981c07551900d80c401d44000038980c524500341c815450361032030a00d002840d0010312409060a03034460308040074003a01584501d0b81501d4003241e03c3d038500001d480000d103541e0105140b0340b0f0034400220001d041512500c071428000c051001c21107030f4000c14014021f50180103291104038603000c018040304d506800403107440b07200130b60050040d0781180c00c0f941103d6110000281780d10f11954001d2140c1c032140e140d0b2142d0844801030001090f1b05800c1941a501c0071111100003035940c0042ea503030004084801004240180010408900800b64a071480390051007070b6a1491403030310001e2102e510440364a40000c010250568404d412846480d880809c19242145011603080001c0c0d500d440410700207109810060400d035000180380c0150380000342c40619613403181e088070078000301440c04540f014215a181c036040030000000340501421282c900d000703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 534461267 1250 534460017 534460021
    0xb120f0103150c050415051e040e010b070203011e0b1e101808011d0111070b0114010e0301060f170d14030405011512031205070f0509030a02040513150c08 68
    0x2c01c2029000280c07010050050902c8000380d025800c1c440005143d40b0b42c2d50301e640c1c030410024070440340c02da29508000726000500c01441a61514500103041d100004d0303580d41c44090500c0082d0151035150807a60b2010035001d0002d0b10300c2003d80250496580c1258089a00c0402c6050210406802c940b4039a101980f0f2000104d003d009401c544008802c608000202d20b0312014038500f940c9512410810b1000e00c030044461841d005c0c4109044007003401902d41c502003c0c2d40700c40514030018083c06942e0401c051144100380c3c041d180480b0203040c040e00a004c40703a543c00300c404e0382e08032911480841030b030340191a211120001c5100c00380f00d160380d1100700c00a009040c90801e50f0b08010001c4500d50b6903440880001c502d581c9100004011040030b820600c4610f2038002c03c0b00403000d860961007410003080c0072000360403150701d4911101c24034105407900c2040c1c1c000381c0303007827280d403c040d4009241c5402c2c000008014035140b6085d81c003800d02140c800b8880034460080780d00030008980001c404c080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 534462517 1250 534461267 534461303
    0x2010e10030b03150906071b080313060920040b0d030e12030c0d12020a1211160c0302090c0a08041b0b0a0c030e010c020a0e060a03050303010b120f0103 67
    0x142001011194039000842d1841c520200c0d14001084250000c0007a00f601048180442007201684c4940a80381c551640101000000081d0390003102c020302c447d4006c800540c082d5104881122407076081002801407640d1130401c8803421808100044500440e0001201e0900300307401055000340c0d01510126011a840e10121075851040c0704180d407046000800702c11144c020405015003121b5180941001c40600601800120f6548229100c01d030040c003501c14295004000f04103031070300800c0e000c82d83c40028165004140708641e2018101c0003140902420321003401010300540340b0941d030000c0540c88980d02a40180288440d48c1c00042c100320000d00040d000448015107000c140989180700f6481c0c0c0c041403213a401c03070103c1000007102c05013240e081c1580711111506640c2c0a0a000005585580100e010501c150240820070001440487d0791a1035100040000719000402d8070f869503154180b407a0254030025014124030300020120300b8140c200040241200d40c0310512240800c10170b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 534463767 1250 534462517 534462529
    0x190b100c0b0603030906070605010e0f13060b01051306030e01060501030902030307140a0209040609260414120a05030a03050105040212190e190501290d14010f05010e06010c02010e 79
    0x2d0070150580824860004a500d4201c00b41160034400e0102045640c10850031200d031440060044280301ca0788410b2043c0140c2d0b40c9101080c3c690030a0b00404c1d075006000044c0c92501c603905c2d14103d4141c680784c001800d168140d21800c0b444100d000240b102d99601e400441c1900c8003140040d506401c104040340020b44200110445a49201c060320f450305480d40010b2841602241d00391881e64460072000200709021150400040ea1400d4a840100320b4038041c0940340101d00800641d16002880078403541d44100d803100e511f103004001c440c0210b06600d003140d229080b114008021030305110010a41d0300e424005c2e6510b0954411100780903540e1146407003020040384110620003a52040c400d0154042409100600d0301d84042a4020803054540182166011480307011004081c15001c08601c40d800c000b10300040044800340b0700080c0e02d050803116800c1c02c1e103001c5010740c80e2000207204218140c001070704130784070300201255a968a500540720320b806003074004c0c0000c4d00d00344d9013242440c1c01c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 534465017 1250 534463767 534463771
    0xc0a0506010f06020c090907031b030203060732040519080d0323040212060a0c021e0a03200d080a0b04020a0e091819060b0109030305090d1a190b100c0b 67
    0x456000355527a031034103100c01d003c088019441c1c03040707801e040c0f040d07003020403a141c1c00c440d181c60458000024601d0001e522801080000c4a80e05c280003d54102c912200646016100c010858090094424580c03c0070702e06510078103136580100ba40d42400b040c0070f80300701c1424649003804100d038103480d01088421000000c1c4100d9000d8000c10071509841010422248519403c408c0000c0400c0d02c50350191500c1c81e1400f222100f0744406607144045000460998440c503850304202440c2c07040307100a1040464585001c2c030a034480c40c01d10001040d40102610701407201100104619003000e0107100591041c0315801c00403c0d600c081410140c14100d9407158401c2c0180e2424580300da603031480d242400000c000c822003a417468204403042c400d1600c034020095a090030310741c210f149156005090750044103051482158912011024403040315150481c0809464040965142103039071130b0401c00c5900c0c600f8904a140c640d0303800c0c2034103041d03200580703002060300c40d10094230722955542103040ac0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 534466267 1250 534465017 534465031
    0x33f0706021b010f060816080a140309120106050901051f080403120e03070b060315010603020a03150b030a0f1806020c0a0b070c050c0306040201050304060504020301110c0a0506010f06020c09 84
    0x240b120000308000302071080388403821440501040040c0f030b12007000d18200842591071144401d44d40104490200000c0800d81550b0003070741c24007514070f0a80c0c200c0c01d5005843c60540c1009441038011906441940b051094400071030300c140080c0d0321034040c0304108582d2402c4540c020250004024024080c40000e98480c5c400d03e0204000d02000031a02c060b15001f81042d847c680c804541d60381040356038a1500e40c005003d500808181806c0c54208540600621034001410380c00202ea10f480c40c03290f00f085900d0000100b215954a0366907840c10b45507030040f0f07500c0e1045440c04c046071508000d0390040d407141000e0801c1c041d10b20800c0e9102d03a0f0080d4401c4d50744105d18400e4035215000610b980f00c03e01d10502641d1641c10307038540241020782c01d000c40d00030342a2207608401d0030000188e03040409e0300d8001e5007124000079203640c0d61000c68010310700030080006900010805007840c00002840090240c0b080080c0c98460743d8402558008000030f00400e4090f0300000702510860425040f240e030f00c090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 534467517 1250 534466267 534466297
    0x31b0b120601181e050109080a08070b041b0e0402120105010f0501110708100203070f031104030b0a090f050105181203070305192c1518010209033f070602 68
    0x9a544c44000040c2c2100848402001c944082040300b903800a4124006051290140c03450901035503d040007449040d4000b03003c40040d00200b0b0501155198510304080c3c280c000d281d40b241c5580c62242e042c1e40c111002c038401c074543c50144100d40010f010b241d0480d11080d29614041e8102001510031004250803640240b0030b00d0710014011000b08a41c020440509200595900348000c00030400418007001a060500f0002c82800a400d0703c011281100e0f0440c0c0c801140351540c210500280013458030183c0b05e02c4c1c180e9442c509000e0103612413401080404e00344607608c044480140c2c0c6954203c400181c0c40c100078000596600d020381c001c60b070f210a207081550174060303030106200100d410102610001942203030000c50441c1800415a481044043c0100f0b17080b03001c3c03400d2587c0404014504515640110650003400d9003d40566541c103e008055070004803540c05440c0700740301c0045c8051416204c1001141540c60310240501156056081e014908242600d585000c1d521000c6c00d40220b003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 534468767 1250 534467517 534467519
    0x30c0616080d0902030d09032114070b0f011e0302040504020a030b040b0901110c1c1e210605060f032203020303070e030c060702220204031b0b12060118 67
    0x9030550000b00907032520903000040d122014014580b401190740101d100380050b0400500100300958180040038500142c0b55480000052080302c2c0c0104000a01c4a020030100703410081184080401b8420440300780c2c59030b003a0f030742c900302d43e002c09030440e18030707059110300040a00250030250041584075002808941241e9525a00d03003294007403c403015604030440b41d00b48220540280600c07620b08002e60380305820801180c03555070b00ca00c01c0c03100c3c1d120106240d901c6040d665000d441d442800c03060006408200c0d24040101030040304040e01ca40324071008540560541054600c01c04040d0340700070745414102040c030706480c00d40d54409005101850405103111143c6201c803011004c60758402da01450316030070030040180007204a402080c2c4241c124445501071030722071206480c9020b0b0101c0365410748820990060f1626100c84516402490000502105005a2101103003a01c05c41103410049241c0d01d030b0800205000740003441500d40f14a10100396291710541900320041010010341c0115 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 534470017 1250 534468767 534468773
    0x100b04030b040f050f100c0203131809061121070e12011103040305071407140d080c0d0c03091a03370e0c0612072d0905040f0b030c0616 60
    0x19012810705d0502d0b07008421180380c44081d4041c0c01b00411080c0010340c00c0c54100c0901208810207405070303c0240d84d000322500300e207504541040c210b0b10b41282e000c112081c08241502e441d603121081c110010049401c2455070300c2000d00c0c806201c0e01703480d035a41180c00c1c2d0b2502046600c82c0e000021030a10740d280d5409800d148007010040d40194481d0b21401d070748010916202003c0301c2d0358600900d103500100c0f4200a0030341d588240c0c1c0a032540031100900703040c003e4900b00e1060b000340501c10041e8426003070565003490300020800042ca000342c507040c6026039035681d80d101000c10082101410b2700c0c10300c0810301c2842403001041e8541c040071900b520441525074140442c2c40c1c2e44840e4545a512120b02c100300700b205110008a503100ad940c01441e198a01180720100c01014040c0410814910340c5d81000c48141d0041c403640e90024080904040b035591401019a40ca6018a5202e0707481c02c400c1c0018500940308a038804030028014151540d401c0080050f10780184034624210382d416000c031000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 534471267 1250 534470017 534470023
    0xc0912030409050a0b060309060622090f02090c16081b06040f0605010602030702031e16081f060501020d030b0a1205060f06010503040b0f06010905040c0314100b04030b040f05 77
    0x81c1003520b500041c24035000d0119000d880c16a01e056004000c00c00910800060200300298410000e13215420015003c961040b110b096030a40718004900c0d0a03901010401d06625448443c0c0c02158214200c0d01c80000f40380c00c44c841e0100454040f6409001c07200001c0101010340780f00000c554840c04201e02c200030341070a2800450b8129140c3c0400040314040090034070419003d00210b01c011400c10240b64003080d6141d029510ba00101a0a240160005a020064600c0c800100701c040b41000c5e6a4071006980e821012075403a0180400e524a03489580380b41c0724400456805074014a405400c07180240c00602c00c6c00c400640107110752401184082600d000b61000c688180d004149500c0c002441284a00001e00031504128081003031001098910fa800b50304040c41da03000415a4444200680f0f1071a8540c1c0000c0d005400e00880c0003019030181e201c800103140036032080c0408e580b40b581110b80411240254172144405003c1440403c41201c40558060f00c10280982d04c000541c480e145 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 534472517 1250 534471267 534471269
    0x3021618110406051611120a031d01170901060e090f15040b1b04031a2a03010b09130603052d0606061c0911010f090e0c09120304 57
    0x2518084564503212000340351241c4039000d860103014508090034144018500d101c0c0501c030503002407901c1c4030181800180620060101c800070b01010030b404040f54a9615100c803210305401040b41c9081c00130004220544841ca00c48052b96040f4040c00c104010401c03c04001c0c1c8000b00d150758641000c00c86c0340c0c03801c02e0039004800000c010040c400d1085080b42c41c10f074030381055203121000641800000341900c400c00350008000c00d280b0140303d01c00e10104085005070703031000c0d107040820064141070300c4042c42d0300d50259042103c4551f40c0a010316502c083d40e06030400c0300d4a03003c0104010001c40f140080580140e2000034245041c00b480da03000c1800ba0346090b0402c0e103182c0c000b809450030b0008409141108609016000c115141248100540b1408000c0017075002d108000394100840a04105050903100e00100400c41913041e41000c0004604141d40c0f60702055000c503030145801e010f032503c84101c540d44e0b601c18400340c1c2d8542c0610603a03049082c00f180c00550710780201c6030088083c0041c2c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 534473767 1250 534472517 534472529
    0x702010e06070e1002070e01090e3c011b080603120f0a02010b010f050d02181c120c21020c0d0503031506040506070b19020d0905010b0303120f04030216 67
    0x20100604820013443c51544003240d0300b59070000c0020000c0c041b41004150444a1100001400c104c00c51455800c0403085165900041d001071403402e102c034015581c103070b4580d801c07203071044503280c1d204040c50889158488c590a42c2a07a101c03241807140c4100100d0750311200c040c0681d02c010506a0f0188100c0c0c0121001c0c003240900411800702040c0d09100b082d201c81001d2801307500c40892624040c00364412400a0a4086d400251524a0b020240c54170540d40380c0180c11114850b104007020030b000002c0c020200c4028a0340127107c0000d82c81400e0744200d1903005000c106031090440380c0b0b001200c80178942a002c0d80104114003445507a0322810b80c200d07a0003a4040d640e24540b1900e85142080742c41e41c143e100711802c1c0301c10b01c4143c5401c0300740c404042d1320641e1240311b0703101c002c03051001c1d80c458203405c000c4500005002c074402d200c07600001c2d00f040c07003040240310311140e10702010789138011803034003413520034030743d00000c6010704044449a080743c041d00690303084182219160384011940d0f0010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 534475017 1250 534473767 534473777
    0x210e07090b090601082e0509010305030702040c0201021e032a0a080721020310090e03070c090603170a111501030524060118231809070501080702010e0607 68
    0x707a101410003464095100782d00f441c0c005072518015000540d1900100300307003424000084229642d81c8203401c0303a080600001040300c1940c2d0303500d10f401c80e6254001281213001380c8c1003041262035140140265041544c01c2070244004c0403048040401c0c070307000200810b4000005013902c0e290701e691071301c0b5505060034001c14103544241201029003100c10103040e01c410000c101d80c0040740d144000c4810010560300402c00741e80c94440c0454902d1102e460b80154900c42d0cd041d86074480301c0400802404130034403514940c42c41603600e038044811180300e484068003a50b500d00002d514280c214005006a24680c240301079100010369000d0700d85a8108001e5081c10002e00c010f0040c00000c1210404004424280c94900144900362a1207070f1405070009041c4081000150742c0b5521101c000009003400789039037203600e9110b140345000043c88820403800750084030b2000321194240516207114459106c01000310514000044a04000080580c0e0440d56214038900d030303914091003003d005000559403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 534476267 1250 534475017 534475031
    0xf0c021305180d080402090601230414010e0604030f1502030114010e0f01020c0906010c0f061407020a0b07080c0405030d08010e0a020c150c040806090d02070b0406210e0709 76
    0x180d12500000ea8841c000381e48014411403c20f5484800d42e6030003641500c10f90040d45407000181c03180102552406117032800d070040482c2a154080240c01112180d014001001461100660300c1d0800c0c000a2a08100e04100c140b01141100950610480c4a00100c080303000324070750107004a820a07041012003000e0220300000c01d45e0f10129820804108940400c2d0203013001c3d0001c0c1d99143e852000501900f00c2a001801585c001c078124031107180c01200c1400070b00003501c0d00d04014400020011002c6002c04045045184006a42d24107542d020100c0505511008815204074200501c0c81c01c1281c0100004100c0703803014440c2190b1b4140580b151450355050550041c0841801080588a24418080e40c504c0714400900840e548641d1204c1928585a00030401c0a0344515085a55241b103603006102d0408070000c1c0381c0164200d607500340c0e0304594444110700d002e44203921030807000a0749108030714403e0a9441010321150b074460350000d080754034010b0741400c101d015800b02200c6135517984 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 534477517 1250 534476267 534476281
    0x6030c02030d0911191422090804090c0e030d0905090408090402040f080c030c040e070b1810090e0906010312030c0908010c0e09060f1c031205010e040302010e0c09070f0c021305 78
    0x849091220011a42a44041201f01d80d224111807404000410207031602042818040304600b11b80103801941070a00101d54480300c040c0241320040e0340c81d03002c0d00c16400c01c0c1c410184592030300c2094590003091104242c417252607102094120085d4558069420000020f06c925407990400c000c1c00110040d01e00d030f90400e010142048140300040e4021030801c2c1c0d4079120058040740304070903100c0401c4400c0e20307031046401e40c0ba000000d600074545c001d110099a940321f1600090020200c0d9030035428840242c0e1132459598840301c0070b2100408218022051540706c0303010b038101c14514a91481e04000880c0e840c8045d03401d550310043740201154081000c6a458103104402903801203040d03c01c1106141c0d4440450b25101003950b8014400c40394409210030141303d030920240c000d02c4c980091100703503160342d602e61007000d054408601540c40c11003a5201c824010401c0115503000510321103581d56480c50542d1944100c1b008807040201c0c07050104010fa550082e0004019a60100019039184c0305d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 534478767 1250 534477517 534477539
    0x70c05090a1b02010504080a0f020106030b090105270705040b12062e21032003041d130305161502040302041103010f03110414070f0906030c02030d091119 68
    0x103806046904100401c0b0107d40f000c0200c4039188054034101029580402040b40145a1508011303ca640e0040510284003015088907001e21003a840e650303540c00490081e83e012600626401e0229042210104201d1400d0352010005a01c050701041010414030711060400d40c0032603070f090649100d500e0740029155140014100403d540100722030540c246030440e04445100c1300b1401c80201000c00300010148510700c80c1d0b003000d041032000d40c18006103a4000c0e0301e94001d07000381e41400c10700ca60484062810301000501840f03d00402001852040d2030071070311540850b101d50b000c0e09081c8240c4000940b010b0240c0c00081d0000001a00c40381140f04010030340700c41c0100b029006009000500c1354a81d9a10644200c903440202195840c01c2240814080d103114440d0900210030380f4200407417590440a280707180c00d480d07907551076140d071188004e404840d00701c41c0000041e442171040380c00e00340e1503030f103c07141842c002c1c10f610502c08180000645000303910a400c24a5250380082000255002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 534480017 1250 534478767 534478811
    0x2010b0a050a1502030705030f04150305010b070212030c0a1a0a0e0d050705070e0103030c02010e0a060212092404082404030302090a230f060306090c070c05090a 71
    0x464218103960716103030000e0704880c1d090040c0c2070155404050420b031a402041114103181e440303000e5035150840714103211066009071060350b50b20388460042c3d2030200e00c60311555040e03440c00880281030143d99001d020340000401ca402c500b9210401600d0b4190000704442c0c0c1840e441494072018002c0c074442e0340000c0003405402c00d80c030241001d10416113810007140c01d2200d034526243c000e44035403050804c1840c281e4545c0c800b003070b25425280080141640311038801c109500030b8a402c0d074152001400c0c45400e0040340f14174030041c3c010041d0410000c81c00001800d1503030b8009c160b22804d5601c1c80300207000d494441e03590200301400040400c06e5030421300040c104103990341c2601c807400b1a52440600201c000400040805500240c4510550343d00410800a000861510b402c003420b441300e140d960205510545104400100c4050340901c0e04004807440b03484003a1940c08640c40f084c0e1407209640015001700e400703414000300495a038443e00d1100e80300d0b5510300c101213006280850490b015800c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 534481267 1250 534480017 534480019
    0xc0705040f060602010e0c01080609070e10050408010c02120a05090d0c080a0b070216030803060301091a06010e0603060a031b031502030f06090417030907090219030b090f0a0203060d060f0c02010b 86
    0x1005c00c03803152380e810000d1151f1001c41990503590540e109070040301d40c9270841500d140d2040201240401030346d4008050010398821000803c0007840410003640c1d102a440c00303076004400c0030040e5041941c42a4050036507039002134503091501e862551042e004800342d8100140c01c1c0e0000c1604000e0007640c280042d041003040c0080c0c2560894403a15480c40d40272400040c02554001000c0744050b1001d6014204d05c54011110010504540f4070b85110801c0507500140050801c40d84100d06181500841c0d020b40c2004251700340316450342e40c1d00b4000844ca000420003a80d80780c0000404240b181d5481400107001c40d800680da89007410340314030000c0c0003500d554041c810358810003000600d01c8002c80e5501400c120180d4032a500c8485603440c6c01c0032500b003030b61050300106a03000c00162000001c241700c54a1b8800348000b4500c5002d11030103100498a80d40ca01b6a150080741030180d5aa000f1504014068480450f00c002c640b1070f80c007540d087c03181030081d403035a603c8280c4c4125821710401c00c140348 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 534482517 1250 534481267 534481273
    0x13021e0f0a0305041103010c03050f092d0703080a0e0112180219081204150503070930081209070506070303050a14041b05030102030103020a0303050c0705040f060602010e 75
    0x400414803921030040180c68401d040d07860012406200308030500b40c0b04441d0003002030000304c5182000801902054410f000d01702901400704d08280d20101e403d4141c039441030400c00340c05181004c2c0d80c40c02e4815441802c100d019201010004c038034804010a54400e503031b12102040307110300000510480743c490450000d14035040d0f8034864604007001031a407060301183c000b82c2612a214010305158859805406240309000c0123000c0c030421400a03104440c102d015180c0300c8824203d0995503840119520000a00386000512402d540c0c0c0d50740c10010501c41240700490703140b088176525412840e94081d2000400071038403104100401c0c0300d8662004184015211030f0b450480410007600884100406054440780050350312082c6620803101000c00c0c0300600500d040901381041085902c9491003070701e6101d140045890308050003100c1c100d9030301400340c88849103180c80442d295003080310400f405009a0a00041c5613966011307030702046901e4500050040d02c1d00601a017159000d8440b005c80b90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 534483767 1250 534482517 534482527
    0x3040608060409020103240519060801051903060614041b0503071110090303090302100e120f130605310902130305010507020a0209090c0d08130513021e 67
    0x194480d00080d0000800da5012818050610058018207440d00c21a61202d4501d580703241d290800b40c103448211001950003c142d003090341606180b00f9000c0c005d240c00b151130000101320703a00b442008501610074001e00c0313a1003103450b561090300b80c544036030081180381d00000c24074040d403034940b045203400c1346e500c1100e240e0b02c401040d003d4814040140040144050b0700e1901c03141100902c403a04010050080400c50b030442c40c44c01030018509010260014402c000003195101c00510500c01c80300700346c40081099104000f60580640c0c4401c0c800d0014803800d1007444085070b40c41c0303a40005001e0b5500c1d240d459802c030541ca86182c102040d803849100c1000785141214010840307081c0141c51501c0405656005a520b60840c45031850380000c00c07943c41c103401c00000644c00304400340500c0c403c0700c0c2182207840c0c107800d01340e5620001890350792068aa01c050b4000440c504010903205007031342c0b007200441c0d80ea0340000743d05004040c03011319101e40000b60140c1111601d01c01000028038880036034140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 534485017 1250 534483767 534483779
    0xc0b0a020d0f021002031f0806040f0204050a0e0f0601150314060f28090b090124030b030f06040c050301020a02030708180405040807061b021504020a080703080c0f0304 74
    0x141c0c12480c800c00034015805901c0810520902210400d1000004150360301d06001218014030003070840d030303c1121151440003081c641c0c0080358031030050703802492004580e490b607001c1200810b40681445085640c43c1300c1111303e03503020302105170140c1c20440a08015031420304000a102074222940013014604008900701040310010541c1002054541a020810b4040465880f40d40c240046590b44503010103101c603050b840c01c01c28281c0e40c00f1071080c003100a011060040c4c030102802550301140684200202c688503100030004d440809140200e0521100c0c40407a00748113181c3e0508642d608010104004c0c09030b000302c2c00c00107080a500840c90000200b800035141d004059004000c4140010b5003010007000d40d0707510740c141d04c0c01002041142801d280645e91584003420407601e0500b0301000d0892945118814410849a80c002c0c16660f50001011040100b0041007282d21682046010440c16010040c20340079500c2605c40c02da5411281802c1482d14000406450347d942c0b00300000c4c00b80d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 534486267 1250 534485017 534485023
    0xc0102060105100c050a0501060807030c050405010e061201090605070302091e100804141014071403062e030501030318050a0e090c1f090f1d040f0803090601030c0b0a02 74
    0x3046507900d0100020015031902030f0070b046c5a4074010300150f0030b14001040705040031030310b001240d01c164150302c2001c1c1d07039506210682d03209100d040e00d1000342800240e02070404400561190128900004a498240c0d491030b003141d005441d07582c0040d40c007098600440c100860024040071394141d491280c001c08600040ca6000c8904040e410086000d0100d8100f180010521a510901c4010348031400b40c141107030401481201c000c0c042c10140300c00443e01c01d034050540305001e490400e07a468038581d41d14050002008a6210080310300400c4080718000422412480184001c2540c022455500d1403c0090080c4011b0380c00e0030030111551001c100030343c2c030104414100d801000304940e555a407081110705121502d080541c1081419010640d40100c0b5001c803080c0c10001d840d5000126180d42001442c00d07014040d1400b4140001400fa80b03003480d00240a40c0140300b00851840f00d0015030324244541c1050b03440c1d81840d44504018020040440e159102404a820003a820203c00b140d000355 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 534487517 1250 534486267 534486289
    0x6080a1514040207021f120c181a091306140919270b07031b020a0206070f020a031101080c0c1e10020f120108010e3304060e0c0102060105 61
    0x3100703ea00141007402c546070b00c800e01c850754280450180c1e0b0070f904220082d04001c49019100511464038290b141b20704e0042c1009044002c1340341c1c2540c4130031309040b5011000800624442c200c91400c1c4000c1240f87d03034a42080705452054800404c129203070a021500001011201d144a994901c080155240000c44054403860003004080b41c102260201103681d41c81e0004552180c58030100090b003031125800d1481e00070700841c3e030300308803008408007084c0911224000031401a000351012101606d0184060075003d8003d20103259004001d81c00100001c4580d40200c1b8400301ca9a0800020b60b00400c2666000c02901d421900d000281d001140e1a0180c103004010b010780288134041d0b01482c100328403000200401c40031075448440405940c0e291304105c0d450b044451085001007070450060081c41035145020340109840f49500311724980d904490901c0080b10307030420300003440341810441c065010b01c0c02070b0000240e940351405c2c0c40d802d0101d4030038150f0556124200411442d102d0180d125 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 534488767 1250 534487517 534487519
    0xb070f11060d0218010e01030605010906030221070906090f0f03060c090905240303090a06051e0a0c02010f2d11030315090a09031d01031506080a1514 66
    0x101480000e40040c005028000c40c40300c415101003500c4026080d0401a050b9058003600d4486085511000440540c2e0160140030700280602008100980c042d4005d0700d054412400b1105045200001040c504070044912000142041c030041112a4100500001a001c444c410544075420018a04a4800c01c1e10005004a0b078540440c620079200300720007006000c9041c41488181000d080d0b1510f81842c50035500050b441011a40c2c0c99441c00204542d05500c4c0600307070580f06441c0034402d541c1d03130b00040c2c00741400140e600b00e40c041c2c907000c40c0c00415a145154a0b2014645c1c0796000040801d0704402e04101800300c548411841510320380c1076070304643d00701d0414201040c3d418008440d82c5880842d010b07030500c00402484444d000965a011103100260b420203001e0341ea40100c00d05603018600c014002c2444a03400c4d030a9044d1090f02c0c4c07030094a0605003c0750032181206440d244003000e41c80f03400025110014882209030394043e50009620b400049488a800d050b101c0303c10071680000b407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 534490017 1250 534488767 534488783
    0x601240518130507050405210a0f0203120c03270102120a0212030f090d1701031e08190809013e0a02011a060a30020a0c0c0b070f 57
    0x201c0c20303526041c12841d04001d0b42030030b00c41420074a01c050466041806014800c07580840e44103880448003d030235082c1000388000340300042c55500c840001c1c1200d51070583c3c05001d901100100c038040440108800141a00110b641d00145101090810240401182c0207641c0c01c010283e140c1c5e000900420540800500d5951400d0140e0107914003003102c1d420044007500402045400f1403805012813043c00c180041e618811100c0400703d91003100301d9988a514074030000140081811f00410028480ca59030040071046159103418050750044003849407000f8081d03000c074014a9009484640140c6007000a2100c03821600507512031019441d0303d02c4260085502801001801d0b1041d022041c0703100b010142c0e102c07181d400080c081c24041c1c2d50a450002c44c0090025a42052030440d54250241d0381d60502c80515420b0f401a4486400300f80d076107141d02c200082e0407448080c4000c1003400c07095260b40224888618204203920780960220740106000d00c05440070940d15186004821f03803003200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 534491267 1250 534490017 534490057
    0x1e030d050910061202040b06070312021305120303040203070e07230d021b151303120e0712150c0203090105070f120f2705060f12040506012405 63
    0x40c1d01c1c0c01000c6400b801e05505044000540e060b002e8040007210303000303031000d00030000c01406208040c844c4110080024414041c11103401c04558040d056882901002c0a043e60380c490001d122003180c401b001546400002c188400c603d410031030344000b452010034038038452400c1030000c0c04640e45034000920380910386480c0c2c000344415104031070060400c0001103441d6144281c8500f81401c0c0889040442d1207080000c418950062210510540c2d09110301840e1561694040b541c6400d01000b058501d40c07101d00380940988140030001c043c00d03c3c20200d0492144604008071841d80301c0140d0010740c2d00d03101c40700b00c00380d50100c02c44168a4080c02e083d40d5400344d900d070048580e03c0895020313209000f507084c0e0148596200c605001c0b50f41c11581c61004042948124444031100700440c900030360b0442008001c14140300001d8003010b1580303d960f034101a0010100303000554115000c54140d00000010f02c012403207480c4205030800d03514592240604079070340240c4903124020442c0143c0c400000307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 534492517 1250 534491267 534491281
    0x30306040f090b0709030c12080d0c0203120910061e050111071701140105180103150207061b080c0c070b030604060b0a09050102070503150a020711100804051e030d05 73
    0x200e03001166110444441504d81008002c0c90041c075401b0440762a00b00c85c01c001140c803402c580c01101143c218100510b0410710041090003085250200e01c01d41c04103001000503075031102c508501c14002d038005811385064900540302202e0498024a009488445042440420f10b00904055403820700b8201080d441044040b0700e0040c80380c6c041c4440040b10b030700342e480003d4190000e2181c010900d00c64210399032520b0030800c20707284501005200740300480040001c503034070402240700000c0c0c0e400010310f007000580b03654056465440c504890b91208100d240c0031198480f90141d0300c620801e94040c1055100100c003074441042e44281c010050021020844666480c1d000d00020000300340d82c65960300003103002030050a40c510505026020304000018203003400b2074400040d00720f182043c2640c0c2c0d10318070440c000b0f40107040191040b8907490301448080e1100070a8800d1488162513030701d40c91810749002c82c03500c0c28840510000700e01c98820b8400c0b54030700100752502c41c06454000300d85070b40c0314a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 534493767 1250 534492517 534492521
    0xb03060405040822090501050109080a1b36050103050712030e090108060402031c050a0518060408031309180f060f380a032a0303030515010c020102030306040f 70
    0x30420b10290002c0000440e00c003240135000700210340d1800001e2045030380c0c031001918040024410031245800c110300c0700700020180d40030280c6081440c2440c1c0003450f1617116030629032840f51003c20043da80152441d0300e4400d07000c1d401d048514505824803907981159590743d11600d1a100f03002a81c0c0000040c170040600402a5015030711001e00034104a40c0c0d5142015a01e5100ba10306038020300a031031103e210501010394080d880c0040792240c41c0343c803051804c11500c0340e000140c1011a401d0701903043e640755446200400092003210002d544802413107040128100d00c5500c0114003602e44103c0155500b881503242c2a4030b82c000100c3c854070161410980040c0000070b18260119141c007102c02c901a840c0c0103514448154120702958803c451054040303c0706512a4055000541071020030000d008070041d05d46d01d400781c26480d00080345030004a42e00030b829400c02c0f0042611036080040440e40703004100810102460100741c0a403090300040c3d140c1c0b0010b8400d50042d0b88072041007804002c69 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 534495017 1250 534493767 534493777
    0x8090309030d1d1327030e0d0807080301030b01080610030f020105180a090f0c020a38070309060f14070305090f03190f0f052205030109210201060b030604050408 71
    0x2a080d440110b9a20400303c00a08000050451345c81c209441c20403007500380034096600c2075042d1208060180b10b44200000c040c00c50700e04503211501042400001032174103020b14021032160010700100c0d4105900c40d0300b0b001000f801001c0701811441c0c00c03c0481c0c03158107000d820940a092951f079a007480081d0046110401a509030045020300000a803040d6035403141c0b907480c50305641044401800e081c2240c8038040100c000e40b54840542803200c0402120700040080c21141400440040d80382d42d40d20450074086034550003107599030041d00c090001c1c5001d8600d506285980402c0800014108480e0740000a80030706c007016500d00001e145200b040200001c1c0c83c2c4198101c4c1c9d100e8409800d00b0170704207110809607000480030000c2c090f00b0b6004882094550159445450a004041c4014410030f070340d449903400f0020304404d0001c0e06480a2081040581c0580140c50200c1c1c3d01c0100042900100660b10085a140540c100311200c28841581e03000002120045003d48450070211900c0c001c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 534496267 1250 534495017 534495019
    0x180209030d0c020f04060506040905070e18010e0a060e0a05222406080a0618140d080108060702190206070602160501050703050c0703180b0408010204030308090309030d1d 75
    0x181d824a1a1099009a0003a0106100715640c40c41c8507004820703c42543d1140c1306041e0000c00502c03050000c00680d41140d03074450058500132700c02d064800d00040180e6045010603c000440000600c0741213075038031103260300c110305410901c801454941c101d421000000c0810694030b0f541c4021410307840011380001005c810703860100348249030030b04101580005103104250300101045611003c00c1d528020308086330344c0503002d0400745940707403510400350a29026840104042054880c0010008501071610801d0040104406240040054030384081a0041103081d401001042406c40d400961120302c02c94020620fa1003460900c080b0b00c0501840c0300041a00e0b00115045080101403072444030980e0141009004030b03103036503009400f11401900e4007080c15401304021f81c082030082503031288a1799411103240c0110350395010609941c02c1500b210119940000c0d0802c00d26505c0700000c0c0c0c0051404016500e010510300009544482c2d110a0b0820300012065040300e05c0700380d950b08402014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 534497517 1250 534496267 534496273
    0x120c090c05040e1f08010e1608070608150a09020c06100305061501090e01090231170f0706020303161d010f0512040606090509010c2c210105090307080418020903 71
    0x30f254242c4502038048000000540d01c1109402e0b0102d230007000c0c1100440340c582000d064820708080c0304644240d4018071040041d01044425200b5407212a5080020b01136440300507141c103402082e89040181c0608000004d0111807028400309202280298010501a2030005e211050f200142c030401829070040f09021034074000060b00346010b0300103001c00d00714074035401580c0080681911201c80300981c0501412030105040c082d0141f81d07161842104c1030102201d03600c07441d4189184c1382500365008a00160008003e005202039180d4010313100c038a16040010440c1c1010200c0c0d80380d003103c0c40045041180356501031200302d002d4000c40303208500d0403144207280e1429041c030201400c040c4c0b007a440c1c2c162070304000812400d8107205548140c400c40d5250303051001c1000e429100c00310680d101448081d41d420b11881966034104911072030064001d42c0305080c1c120b10300c606003121001030003e0041c0c1c10812407080002c0480c0f080394107588101c910321000b0074bc030801120090081e51416a00342c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 534498767 1250 534497517 534497519
    0x120c110103050a0f0f0c1107150503101215110f0313030306150c15110d090203011104030c0806090d140c21070606080d050702041a0a120c090c05040e1f 67
    0x1c843c46d009200504155203540360b0024000700350030340c0c0349030f00d120b400301c00d11081c044264142e1240d0000e5403c00c40d08030b0000384450300c1c2c2d1840848108400401c6443c150080c8409e089030245014141d00c484035803039801d007000d50f403990702a2b032444001e01d20001000b40c021b19804142c0240d028002614204401e0b83c0703100c0c0c0248001e01381e030b190200309440d0b81740c90340702510b008a9035008000c5105030f80780a00d0309012901c0240c2c00074140c0006d0807a815500c443c1e810070008441d5028100641c09103001c40c0c141407501021500308803018107201c000380c116420540281c1e800c41414100b06102001c12a40c03441d403280f020781072142c0740804242c11166030f0350301c141041c3c6900280014a00524040010f55542c02c4003d40da211450064008140140a41c0c005403806512403a1241844045c0042c40d51201c2d0024001c560a0380201000401c00600f01003400f20403028000a4484808200201001040d0151440c052442000745035005040001d40640c596001d0414850101c2c840342d20321 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 534500017 1250 534498767 534498791
    0x140f030711070b041e17061906030c14010c080f09011403040201090b070609020619030c0903050607110c151905090603150f1504060e030703120f050f0703080103120c110103050a0f 79
    0x603070041e1611400c803244000e5004c9109623600c100002c50340d001140b01c61042c81d04940d80c040c03001c0d00c1202414012180d40040119651000401a07030340304c041c05550b41c02e043d4002400b04540349440c0c5039001001e204100c0140d07084201102074a035800011501d403c010b2a08074003421030340100035000440071581c88903003121880c041c038800001c0e8400b80202d07002c0c4401201c80141c640710150090f4440004540c0b490300079442c0c0f02d03060740d0032000d84400b03040303c0000c038101d403031004c0740c0d602034040005060b9803007020161412110b2281d49086480c16040b0000a02e840c0400381221410f0100c41d4111251581d078601e21a20754035025000c4620001c0521030419690428445c02010440c28040d034001490301040d00003c1c0d0341d0040c80b20761222a40001110481c003501c6542080c00005c02668480404240c040c12501c0c1c071aa5803004558114900340c54140040c0a0080074400c2d12950000001d040140d0426105000c1ca0002000c1d5262100c5c00f000e0250380074404105460030480d10b5403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 534501267 1250 534500017 534500023
    0x5030c070f0e04030c06021614030702100504060e060d0204030b07030902030c0406080a080a020a051006140909150703110c0102040e070e09070807140f030711070b041e17 75
    0x222001e10785144102561424001d040c00c00444004000404811141000440a601071f2840b11126914800d03019a195141405070f41c1011034041958030101d81002146000c01d07901041229500c1c101c0d0901c2e1504030060244c9284080084c4242c1e40400c840c107640c0c0503941510011908184542e850341000d64010703004080220080c0d000e4028016404000e04060155a041301c441c0c10007450300b90341945071140d503600a444210218000c1c4031245011440410000300e1804150f400094441d1503da9001240f80e00d075000c60b8040c4184004112091901103201c456012448085403039694079040103c00426110000d400c0c010000720325506070410550180090300c44840c036008045e1101d00c01518040410070070281d11094110004814920600080c3c2e0080c11a003407589600b041414482c40d242c100256010058501000300036949070300c18403140c00800f11401034400d060801400c100d8600c1f6a000e06403541c119000c407075480088070301d90032000302149413015044102811025071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 534502517 1250 534501267 534501269
    0x1401021c0903031104050f04051302091806090c060706021b0319120203060a03020d05030c0102070f03030c0804020a090e2515051201060f0e0a06090512120f1605030c07 74
    0x40001e26103420003004d1249603040b54180d80004045c540b902c0031850800000d8540188003004910100d01100d00680300c04200500440308008001e2040c0b90764090645081302c01050301c0d20580c040407401c8019150b5008a55000b5080a805a5242c080b4580c031080503220310504103c1d031200092510b10492540740c01038030700c1c241d40d89001301c000380010088144d00044d40d00c01d82c0030710f08100030001441c0420b851311950344030f501078070b060551034090142207070032466003a01d00740d41c00b01c24541019450310600d2240655800e080807107062680102d0700403c80d500558a8141d65002e040d541e035101080b40342420a21304d80e07440100a4420b0201c08140218411403021840030481841e40074080c4050383c0400700c14003c1d1140c3c40e0b2a266007101c00c0354500380d1040501c29004002061911a010302d0b034081e02048d141c00d501030386418144031904014007000c40494000790641d800601c2c00000722815440d403245860389419044110302e20107044000c004240344030003e0b86034900030b00801d0500c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 534503767 1250 534502517 534502523
    0x120212010e06030f06090726030f0d050a090b220b01090905150108210f0c0705030c030307050c040903111f06061d040c27030506130f1401021c09 64
    0x1502e102da100030010f40e910300079031b9080815003106c5010310600034030300d103d110003219100c1050000040b05102a05540c020340081250302c0000a40042d81e5140e4002c0326000500c803d401c220100190300c03440709112016080c6008c0c1c0702c450f011051140020f0041d00708440d0880d00455031943d684940c4030003041584000c842034000d500702c1c1d410055816800d141242c5803000030b400f444182254165520140040340d810110061000c05e48001c0000301410040403480e0091041c2c1d42031408051602008481b028801e034420420000002e01c0450702e826008419900440c008000d0300c0c0545102e880300c5c0b814422445040d222100d06580071040030040f040b00e4104006180d00d80d1012903100146190b801500004204500752a003890b80c01082c2c030f849186042c0605040141c07102c80d62402004030040352020281d006d0041c010f09202c0c05410200000c03078000400c0c810b030340d501ca40600591000d4034000b02e040c801d8402c80c40030b40445d90000c14001450a40e20711110500300140301c103002c16 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 534505017 1250 534503767 534503773
    0x301023a050c0f13150302130504020a0c0212101b0f020c0130020a170c070c060f050c07060807180605041806120524010302010f120212010e0603 64
    0x8000100d201c1d0500038010301e506107141c110b10b10740082c042d502c8414030820701c00d4180350004c0c80502030304184c285140e45640140c1d0304c0740f141c00a41d90540c10f64101c14895441003001c403a40e507030400701c08050302e07070306940101c54030105091003820f100803841c0c2c4414503070070301d101c100e5801d10104003000b403400207442d9000c02111461049135610102c120b01030104140020100080c01c011100c1c01120700340c20880c251004100204406a80040c00c0d420007281016400c2085104026030f4590f1005640800c24140000394807184c0c0d60703110034450b4074184104001e241e420305221b40210346843e40818111004541e40e200000c00e8010100d9002002800483c0e4250790040d2221000f02101e04540d01c15040a0030303c0c075000000d841c90600d00c0368403070360f07240000340840b007401e01c2002d180d0040000d03003650380842000341d4058107105800d1045508060060005030b030006003a004002c501d1414090380f112503c080350091148200302111b1100c1e08000151007030160800900c03565040c1c050f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 534506267 1250 534505017 534505117
    0x32319020106060f030e0124062304060e18010305030d0c0e18060303070c031505090a080f13050d150c050705120a02031308060907060e090f06030102 66
    0x100d080b1401800b64800244040705074680c05403190304901003040c0d2000c0000b900d4100300c5842400c100da01d48090100007401c01c410000039400c00408403d8000b140d86400300a1580d160000f40e0b0b01c9103000310400c2c00302040000c40c09450b1032039001c04032076400740032865551f120b050840d030305d8021a800d07110003030900031780700700907031040c0304070f0b04401005040c41548024941e8080c04528008040f250075200910604000c603c000802c0c0300103501a20101c80044206d8002e1010340380300401401407a440303a42c3e00030005640c0da0407641c03a130b0034130303101d0a403514291090b20f0002225940304544c010b2080d201e52050114511510f6040c0481041c10400000160406e650500900c0c030060310a4004000003001b154828000b8015a42203106807890310704a0030138440c6100c0c00340c004083d10b5000004000c0407100c204a1a0090000d0b820000b8503c280b0800040f50300c07030010b05111901c4400000324605480c00d40607210b0a04045400440841511703071031001222004100d008000e0304074403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 534507517 1250 534506267 534506317
    0x3040b0c0f19020d060f0f0c03021914030103030e0307030206042706051327050a0302070b0f030a1a100e01390f06060f092a0c0323 58
    0x59070100b00c03a80542254189240d41d15034100810a103800c10030b65a40f955112850001c0c0303481264482c0c8103e8400680381c1c010325442c50501e15103280d800040c042c81a903501d41c600c8800c42038030b046981c0b52420441d9203c005000c0f82c104641c03648001d412006c04140801e80d0a1003002c120103c0070300354103050800090142034019240c0030300c90240c210501c40140903d403c425004006070b030681d05040d112110041d5542c02640a111601b55059008580f84404159052015400402100500d90700f03103840545100326500c0068200e10246a03200c40d0340e54043e1004803a94486400107040c107101c000c04031400b40014121240260002d80c00b00d0b103c0320340b101500b03020350340d03107500703400d55543c811842c03611030109841c000301a5a9140920011000182107008410140000342d034030a01542c508000e81081e1001c400c401400c142c07908201e12841466008101a04100c03450006c201e02803a081c15100c072007024240021450480301e0201c4001100350003081c40030750705000d18800c200050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 534508767 1250 534507517 534507553
    0xf16030b280e0102160501050f0c030c03072001090b070e030f06011511010c050a030b120c0609150c0303090d05120c030a1112040b0105040606050304120203040b0c0f 73
    0x340040600c100e000c1e05032034403200d07540700800c2081000c00051070007140a060f09075500c107021046680d40e441d203007000004081d559205401c01c030f40524003420360628a00e0f040003808020400000c101d50a126000445101c202403844c003044040200103808240c140103501f524107c86010100e958600503c41d01c0c1070000d800788103103036208041d201c96402c200d040010600d040d0b01c0c0c6400c2104070340d02c6801c007800078826150121300f43c2d190555603400d03004002d026101910040c034480c44400700d407000298000b007141e0022034011a200f594601c180000100c40d030080068410550002044100d440040000110b008090f0b070030465942081c50b40d0222150701c11500c000d041840c2400209910742d6986002d15013200c1101400700f08440182a5107007107403c40002900807200721070071701c010320401040450240ca0180c900b448180c0c1001000b0700a4072000d44002c0103c0c03295100910510310034419a00500a0464426071301d1211000081c2d036400c5003c0050001d01800c1a2010716070945 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 534510017 1250 534508767 534508801
    0x201020a14030f0c070f050105160308061201020703030501140a08100207060b090c0717030c220512070306060918020d032307061103040f02120f16030b 67
    0x168000d003800491952030300c407640754560040c0c006100070b0040030040b0201d0b0b005801401ea200004007040c03442c0c600c00714042c0003103600c018140704040007065004080784c0c440c2c0d070b1030b0764140c20030030141d40b641c8022480782508d04800001c1944046030407003c069151304a5412515051504419a0b5603842001319032017052098044680c49003e04040010094018200d10381c0100d0000403011582004100750400448941080d000300060650070442e0941004648669128000781140b03020101848a4483c4117202c50501342c1030040240d00d00030551083c0c014010150402c000916644a16592103200b8001110410b04043c00802c49414500c01c504607200c0511a4050344c40c415024000000103031002a42004681601d940002540002480013046280b05682e40c41040381412005c0b95000580040e00c014100103000100f034503d4500d071440c40e01124800380081404410502d8007810380d400d802c003030040e000c5d80c4803100c0e40b40d400354041764002d00d000030556031a466020f65401c2da07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 534511267 1250 534510017 534510019
    0x1303022401060c1505010e1f0302030714040209040213180203040218180714040e0307081806130308090a060c020108072007172404020603060a051309170702 69
    0xc80c0c401003007180d00c110520306400d4000c440007240700f194504980280c4800760444108088804288550000407141050002c02e01148035171180c0c0c11580000e44507011845554155140303a06450700c035680340d6041f030304c907901c00070000c650303e40c075a01070b81200c01c0310f40c0b1070240725464086480550003020b000312485554020000c0f1000c0c2e282c00020b00318482c0107440d000798026a03002122021b4000c10150000c2c2c001007070400d42d2485c03031408010030740304220348810b83d540061000c40e00154282e010f075032041d02c0100c018200c2c03020341800f05419004031070860720581c0d0046000014000144d0040c03005c5a803d855001e101c0340c5480c810f8031451640e400080c00581c465000803000da00c00c680c601031303131a10090803107420308180a07030a14000254118080c0c114078403615040c20300c410441103202ca001e402c10000452314043c3c440041e404001c00c06401540008005040b82c0e403007458001c041c2000401810382c2c00d000c1e03c9030f200140440e00c1c080741c660301c03a42d00d81e000f040e00c44070540e040158 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 534512517 1250 534511267 534511333
    0x30506150403061e0e0f0c2b020d15020301060306090c051c200301090c0306120f330c4b0503190209010e0f0315130302 53
    0xb14690311000200001c0312895003400da0203c0541c50039100d4081d000000100e03500a01c2071a40703150b50b15040012051030307240b182503214a007204001c0c181003202c1c01000c1050008414150600104100b02d034003440003443c440a4020485004030300d980076505031082a070f410451a030701e40c0c20000441d0f9400300c501c004a0b0041c4540d003000914007100700302d0813446c1000401d03c0d8500451424444d803200c20418040d400200040c00b0070040340c410540c0c10b40c01c40c40c0070f11070f0b1403030700c1038424800744211700107810003408121306400e020b103200514480c400311b05010100c0d446d100d941da5101a14400c440007001d07003465541c50311188102d40c00c0c1c2c142e502d05e030502808114503c0c400d815018408000f03241c10004c0c00458039503072814210f40f6050701d0307072512030690b80d16082034100400c8100684280d40f55106010030544d07641e2140012510020680d4484068005203000a14050102010380c900418050030813111000030443d030500248283c08070384003405400e9034203c060a03200303020403c1c44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 534513767 1250 534512517 534512519
    0x5040504050c041d07062a03030908041202010314040b0106050f0f03070306090f1103180f19020a0602070e0609070e09100602010e0102160f080c0a030c021c05100506061c05010302010305061504 85
    0xe4a84804d000281d40b20303041c001b0303003a032b0566602c01081d041580300c021070742480e5040358107658040c007035032110000c070720780c5042285466682d0313005111060042900304480821030303842141a100440304510100d8200989a04d407120340100608514001c091010382008501c220200245c0141860380804040b0a07007147d1f2849000480d2039190800e04c40b5501c580c0b1002e04800c1018000411f48184c60a1109022244c17030040c4041c942842e8410000c6610104041154000140240d90040d104440340c0d059a220341c0b0b4112014442c0b0324020768842100c000b0f01810b008100c48000031501a80c000344001c4540d4150207080780200c082e18410652098014000a21101c01a00c1070a10881205060200c00101c0c07d141c521051012404621800e11000642ca454a401d80c0a0400d002c0b2407490700e81039507110394603003008243d030702a0182c81e030340440d103643d96420035185014268214080b40b881c8654005010f0b00d030030700c410b901103407909011803410309004040d400c5001d1913180c180d1a203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 534515017 1250 534513767 534513827
    0x5120705040b13020316110604030206010302090c070203010c11060a0606080103060902012606090a02070203190302010b0d0b0a0612081804060e09030319020c0705040504050c041d0706 81
    0x2030500d011020794081d81e02902003c11100b98030165000c1d1a410303080541c0c90301c0a0f0009404910070304c41c0c1d0b440d581d2003c020400003d50015269040d41d034199000d002ca80c0b1342040521090040c4d8a00035419420300030340180f00b940c40050060701403407810444446803600394002e812101c150240380e0025107408014000f05140d40c002540107841890071314a00c0b50700c40c004030a003c5141c08046613082c2ca020030300c0203d207040ca1002d40c1140140904503d403c100f540040d0342c5101510034410482c0084d00b5880901d4000c9d80050000309024062065050707080c0f4180f282c03588101c0e0303680001e40ca0190042810107028130140b2400750b00115440c580300b0003500305d440d27003208003002a40c0320762a04000305952015000e00350248900b440151345a0810628500780c106c900c1007603030070003407051168000d56003001a6420403074506032070006607034a42d400c095040a5510f1502a00b042c1030001c1c880099200c401e402d2443d8410006403011a51508011180c00c0070f06540800700b202d100141c490b01c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 534516267 1250 534515017 534515021
    0x4050d0f0f1407080f0301120606060503060d0615081b090f0115111618180c150c02030d05040e0702030c060c0f13090b031011040306111c0b0a0512070504 68
    0x80e4134010b1061900304803d141c1c8020707059009070801110880c8101c2d1101c1045560700900000c1e0940d414243c0c114a040004680042c2001d00d002e000d180c5c07104400c200c0905070300c1000001d00320660503562640030b1449400b90601c0d801c3c0c07240d0301074001e0200007020303542c40c0c4909078141c0303500320060b601c503089101d8220348440c1b242ea00882c05000300d041002c9004c0107128010010000003410406141490184100322142c000403100440c0c1c0c0c540c800400034070011100c00946010300380c8141103000d9080119644c080500000750144128076a0480103500f18020340202c455800310007607150f407100c000302e80b40e000f000a08001c81e48105c010408070300c42d800242202102c400c007118202030401c0c1c3314443e225803581c0100c2c1516500d4060000a08050041c5003521407090300c1030042c00d88801015840d0300c998407000d400d040d03450f80080820b54244c8211516180700181502243c0048040c50300105440c41c0c0c400e1044180c04000203450401300d800b1004900710f0000340c03a00d02d10b01001c0c400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 534517517 1250 534516267 534516277
    0x501020a090515040515041502070f0b16140c04060b0d05070c030212072d05060a020f091003060302061b010b0409150519020403060b03010c140301061209080304050d0f0f14 76
    0x903e102c180000305407041220480308d11440f90717a0041582516081468002040c560403200394040100040500c281c503440c80c1d4405590b110641000c000d54003d005420700f1080c41c00301d58441e041800010340070f004c503030192030f400076072080411840d156100156902540041d008015130444042c01800d01c0035400a01462400741005450403600e0072048a03c0c0d420683c81c4402202d240724841051007800c11426502040d0a002141b038410103152141c2c06016401c01c4510506402105244040c407035082640210341c05040c980e2a400100399a180001040b0603201440d0300e4043c04180c0c51410b40129840d331134020090061071178a80c240d03078028003c02000300e4000024980c0d945c2d1450030900c02480294020380c00000c0c1101030004042c25140500d00944c200400c2405814514241c03030101c90443e6403609242400c0081303800e04070040c0200490141c03000e007004c42003209028006c200315589805680d11500359040070790b07041d41d20340d540280c9000064481f41300010504201d800a00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 534518767 1250 534517517 534517549
    0x90f0a031d1c0305120a0c050d02030a020d02040b0a0e0102011a0415080d0e192402071206240f05130f061203090602010e0303150d0605040501020a0905150405 70
    0x400d005070b2581514507078034901c500310005403000800c108102440301407107801c80d0000d402401201810301c40140580542c8460000607030740040895000c0c240b070790403103540070b080342d009544a90344d545004400c0e40020540d01c001c2200e580c0d89070074645c418860300c0743d144241c0d80ea8030505a81c0302c051100500001200c1c109490140f4000704020004220824410300030740e4840744020031440511100d0341134a040f402594410181c144030712040c003480174103445142c1d9948214a90030340c004a00c0c10303020707510850b120700c014003400003448501d030041e0a90500035040e000e00c002c2100103a08440081e031080700c045440200050241d403500e02400030428600c207801050340046e0103845001c840c001d41c00302110440c001c145004054110000c4d90003001c3c0c60000304001c0c0888960680c030383c8401444840040b4440845c0700c01666401c4010442d543c00a83c10080c61416191441c000d501c08500d1101180c0c25034400035092800c44180c4455460070f101c80c81c207251520b024030080b911014006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 534520017 1250 534518767 534518779
    0x13080601061d03152a030606090105070c12081206220c090f1701050c0304031b0f12030510050406031a06120f0a0318230a081203090f0a031d 62
    0xd400ca041818080c59607190f017070b01c90510b500c018014007010410416207552083c41000740b241c0c1c4000613030742121028240796690301c1301498881e0341a003958015905410310421031006000d6000b0280000008000c486000d03074441c40d0400c0603280260801c51134010304c03941201c03d070340b01a03000403d02c1929410081403561325140c158001181c3c0d03170001e000000807c40808040380c001d018071038018400c0104540341d41419140106049021490403003403402ca0114641002609020720030a1a040001002c0c45120060b000f400f030b00080e02d1103104417101d62008a9245402d1040c20700310303944508501c40c03140c0d2520051002c820001c0c6102d45c03000c19a1680780c00210301b44a41074020031039001501c40d04000d4a400b8110820540c0000007000720170100303124410724038140320000c1d6015140c540943c8544000602c0242c6950445040360248004035242c501161010354000d80030b01c416039558100a6101c1551100712180c0500000da046030481e8a11640c0c0c0d84a075103501010b062 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 534521267 1250 534520017 534520033
    0x221060402150903072705010321141b0d02030309032505070b0d05011a0703050d1104091a040507021f20040e060f090105011b050607020313080601061d03 68
    0x80c2030001c5ea80c4101c041040b40350700e074034000360401c0d0100d2402480b01c4c810031065055403164180107916171001070084c0072400083c141140142030701038031031009010880e83c41c0802110ba070245980c07441004420b01c0740c1d001c10940c40740080281c0c0e00c50140200111700b008500c9120200c1085511401c5905111111100000c00c03000d001e04000f900c154500c6990b5103a00c142c0d60000c94205071311907030059154508944100b03c4100c02c0b50100c580604d040381e11001031481c1e88000f0300d1507460150306030360700281c000340200301038206201c1034205800b4512484a0001808140c0314112124001a003010b442007212102c4404a5140215100000501116000310348145a00e10744898241000c0c08102049405403404d505e030750204007078903490030100c5c941d40494800081809117134140001010400300d07035240901e0300c2144a4018048a0003400c0140001c1c0d01d9502c004508000e0140c0900089450680021814102c40c4113a40d01003007411114ac1600501101c511030071343c07500518031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 534522517 1250 534521267 534521269
    0xf0a030203060c0304050f03040302061b03091f0212071104110d020c03090a051806220f0f180507120201140c061f083304050a02210604021509 63
    0x45511030f050001c0c00ca640c2c0d060038209145080050010682ca0f60f00401040c401a1120700030340310140710344d08005000307080700c680c00d9085004039840184c12103400d920008240260780c120442d000926001d881070541001d070540c0181c07083c5200500710fa2804900080d8504003644420058086404040d0810f00081c0e41d10f401c1e0303805443e1550340e55001269111803807801c80c01e8140205000c8804603680d01c0201c80c05a14028014210352051001d00e8050040c1c902c1400403000080354002e0400000c2d00e03001c40040240020345c00004003900d4050035034200d0132410101c06503250440c0061684501e054803061107140c0b100402c0b81000800c8000c040385000000180030203022944c0a4841b5191494220300c030190b080820350864007020f1000c1002070380104200d202d002401540701c10460000c1d000e41d9108215607800920101d5450403c02444404194032070382e284210b4148120028000c0140100c080840300f0307040d51b4002d080420b005140c10100c5816165407890030384c0c2800c040714 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 534523767 1250 534522517 534522523
    0x9060f03010608060711060f07080a1d240601030506030715020a0210080601080a02130902090a0b070f03030506090402010909021b1b1f0e010c0609080a0e10020105150f0a030203 78
    0x69000300211b41e00b200d02d8070501c0380c103025090b84424142c6025100d0700d00301400074040f110280c030082c00c842d5516000d4190070141324a02031703010102001c1314510649801c0c100120034420300d030014190ba101010410715882405110b0066a000f801400c5d50b904215144a4a811350200c1509502c5900c48010060f1642d0074200c802c040a83c980400529201c070000d800c80b4001410035511034410021880000e9420210300d0545003424070040c1c85400780713408103101e001140c002108480010031800c1c200170b900c404d401c1c0024400e41e014886501c0d80310501100301d000365002030120340b0050041c0006007213540078242882c0040140291019504412410100209520b81840500042118460400b52124500c0c84541c03c100030152086079001424202c03508a03c2e81000504d01c2d881052000a8200000d030325044110031f0b64448901078003400481c0381d200c00c14000d070320010b540f40a190042c4101c52049004030300000d48100d040081110040001781c1c4a40e205242070f0011000d81c87c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 534525017 1250 534523767 534523771
    0xc0d0801150c2a1502100509062d0a0b19080c010f03020702210c1e0904080d1125030f030f0e03040e04060e1902040f060b0c0c0406050604030209060f0301060806 71
    0xc01080c842e124141341009003040b000c98280a8514189418491402d10001e09141e02c000100320001c000302d402210315403921180c410406411240700c050015100107503000c251b03644000c99281581070140d481107071b1980505e100307402207034000c1b06418149500844e9651110000d9140c0185405031b50344c001502c205944030181186404110190207411040140503a542421114980201c648007003940032100b00d000c1c681d01402c44000441c0c00c21003a030050342d805440c1c05d00300b4844030304650b024003070540040038842c2c04c1203a4682000e6148050300e0702c103540950585d41d1140310465806007500a460801e1180e40003503603a240c4549440403c1c000350000e0104110803510900703150800b0015540180039035403440d00450781990342c00741e10400003601c543d81503502142c90b450034210f1030300a00203a8015003190b140000c05180d0342c000030030005014001181c040089035210010300419014500000750014184400b244462502c1082c401d064070004002041040d29180500d09110003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 534526267 1250 534525017 534525029
    0xe0727060305010c1d01090308031b0c0a11030c040903050a0c021306060315080f030d05092a120f10090c0807031a0615090918030c0d0801150c2a 64
    0x29817005880c0240f0400e10948240b400d1a01901d6681151034000003480040c00c0a146160344048001030844448141c903050001070381a00d00e051716508140f0b205a000050313151080c0940c0a01c1c1e0070901c2e15204242104c0d4050351880e04041d02c201081c1c1d00450b42d040309030b83c080d902c4020a0f210761080c0c003c240c05840140e8010480700d1a07028069890803094001440e40d810151000988000000c1940c24000140002040325240c001c40b5505219141c035a9884c0e028080761044040d2102c4402000e5110060b1001c000c1030524100e05c81d00c924090380d444645800c100a40e0810141c103030442c4941c28081d0b41100004d81e9103984580c40d0000c0c80d402220718003120700c0d0a81408510036041c80c0d110000b582c0c200d40d21110b540e43e075501317071068070442442002d522020600000351051414906098602203d139501440b043c00366507001d250089000041842001081290140d60980010390321511003074462043c0e03642e50a41d0500c5103c00c010090015000d60300c5c1401c10709140402080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 534527517 1250 534526267 534526277
    0x60d060e03040905010f120f08040b0409020a020d0807021b12030301120510090b04020622060806030c1203070206030c120106050a08010e06150904090f0501020d0e0727060305010c 79
    0x80740039400380031385505038031554200046040804c000d5850302e024580441e030102e080011030301709140840310350085800c2102e090101050105039440d50750300030210f501d0305030201d030000b680134007007141e060404442d0a0300517042002c0c0d50262001500101086000003040d203200d05404002d141d1441d0026481040000342c2981540300f031040600100c01c0c1030000d0402030282a0f801d4480c0f42082e10302400c0240a842e001844d00c41103600620040312050445282881c622380d2060000d08828007525661301c64007500c107000c0714914104441c10f0384010300c50091424040190200042904001e00ca0a80e444042100c05054608a258240600303001c1c0c41d01c03519403104404c010120743c0c0507001052003079410b10600c0060341d14040c0b030f100c0119a500806580c2c00a6002181c09000510002000201c2442000382006410b40160070b95442d000820014004000e15043c1d1317a00c240d106001041c281d48a8881c07140d01c0c001115040b030020032038040342d441d40d250b40d1a0701b101e901c070900000040b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 534528767 1250 534527517 534527519
    0x130f0207051c0206041a07140a02011d0a02090613020705390105030a0e070f06050d0c05030c030718052d0103050106050a230c07080d0203030705040e060d060e0304 72
    0x4041000112540b02031008102c24609a540c40080701c0845646048841e02c6100140800c0e104e104503030541000420803a49800340120b0185c0a0030407030f40b400002d607051401c100600d4200140d081c80068005150107102c1d100c18050250000c0d1482c148140d541d020030062000c52010002c80700c1e070701084144200400900301c03040d035102d0444501c50038a00c0c103040d203440c0180e0313000c0e09682d0440003d800005180315803000d41c0b840c0840543c09445496811000091010340110140500704030090b070912a00030744e10b0080b50a40b000300e4030184052420300214808a2052014001c60030b2102c441000306038881c0c00046032041c1000c0000061140c2202d102d40d1800202901804d029084c2001e010745e506015001d0b11038028110503804114a001c2203d40903403107402030102d00480340011580d210345141b10b0503241c08841c040d0030780f18810780745124400d510020450381300f21555500d0700d0034a0f041400721000200060500c9034404851072038503001c41d9003072140c05007400ca2800156611 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 534530017 1250 534528767 534528793
    0x140907140603060f01050c0f070801020408010b030102030705030414030d050c0912010903080a0908090910051e130c02010e12040824040b100b0c0610120f02130f020705 74
    0x1048103030440c021035091051082c01d48400c40720340e5003a80309090850729042040c580503d043c1f0f52820b989a1441801000984140198000c1069a80c190700922030f4688a405250a030f200075142400091400c000040c00302d84052900c02581140d8401c1d40d14265810300b035002512410b441e1410584000980c4a0580c60543c2168583c11651802804010403d0b1000f6107500c5005004c0d510564850380c000301000b03822811551280720080501c842410801420701080840f4090107010307030300844d040356440c00548180102064010500440c0754502c0b124540908850240b545c1599200c8040101040050025450303100004010b180c8480c41c1c480400e261402d03c131085a0320b04454511803548040c0e150140d6401500101c2000c00f030b131501c40405030900f20f1944680340c205c4012661400040d400b103403460050f01c080412290390364660003403011003141000d00602d101c00c0003914a00500707151009100303c0e010030b400041c07046403060114007641d009000844003a00301441300621 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 534531267 1250 534530017 534530039
    0x409050603012a17130b010e15060d0216140706030b060d020711090103030c031e0c060b0301061805060307060c1e020f100513081906020d140907 64
    0x84010101c0090105004204080c004095600c0d00d101001694580d1580441c0c02403080ba0f45803441414948814981200d55901c9007121002c11151510b4113000041c0316001003040c030b40100692a42851000c0700e880c1000380c1035120702d01e20f240803a000c2c04101d260720380c5100d040907601e000781115001c030300d58444e200342820700580103d800c0c54988400c110654545500f55050070384140401071f550540e90520b01001e0003050115030388001d60900210030194072003520280c2601c2a16460686c45003140900c05440c4691040d4000a1002006034080307011078012014200015000240064850401c90139141e005007600c5405529802448401d04041000070000c0c40f03180341045002d03040303694400f9209030031816090035200804584096580303841018002e40300090a040a07403545e041c0142054102031f229140c00b450a4800003098003000c1803441d81101100001842800c0303541d0350000940042c02c5840f045640d820300c0001c10b00e80c04540300d02030010303803004100580c506141c0400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 534532374 1107 534531267 534531271
    0x12030414040b030138060703051c0501060c051606080f041505070e042f0c070b0703080f07030902090606180d061506360317040905 58
    0x5c4039100d45070b101c2c442c0360f68038031000740d03c0703403080c2462441d01c80640000e50f0304084200030410000f807190004105000244905081a1440701804000ca4001360040c0780031411300030903074090241c1009000801040003040c43c40c803600f40040240311130800381c0880c1d1412805004141008050000b030400340d503840ca020042c03842d110b00b000740504009207000d03016510704a46035588911a09448803500ca4000c0084145108002d0481303da0344035041c520402d0040c80000f00301e00b00c058004041c0c3c140070350340d0040b1a0610f203510721042070700600300c441032500d01290030303005071200f003100e65000c0c8080301e4442d100c115840c2002404107540d12890b0303118050000c0d19081001c50350003404a8124000110800ca03282c2d0019129070a00c281c4403034050000208940d02260b02c4610480c500b1040113070f050245070b03203035165101841c188194402d080d001107014080d680e51846059 = true := by decide +kernel

theorem cover : BRFrame.Cov 534352517 534532374 := by
  have h0 := BRFrame.cov_init 534352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 534352517 ≤ n) (h2 : n < 534532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
