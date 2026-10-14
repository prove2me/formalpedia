-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1583
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:41:54.118452+00:00
-- url     : https://prove2.me/submissions/4d41cc53-1941-47c4-ae2e-72d60a3523df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 284532374 ≤ n < 284712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 284533624 1250 284532374 284532421
    0x31303030b0303031003020118051e0907110303040204090318060201020d1b050702010c020402040b0705010f1d070e130b091b04060501050901080a09020307030318050103050f0402121005 82
    0x707058503501c2c01d01006980c8204103210040428a01e940c00640b00c408101c856840c1d400d5921070b011039140e5503041d61030804414900d40d040e000c0d80d03030018000801006031812050180d59036900114401c008200d03030340140d0664020903001e040740380070382c0c0100b80c0090703008140c500d00c84c0101e441035055014050700401c0c540b040c015241d1403000400703507500404d0346100080042006c4000741d401100314600081c4040d00041c6029501c1a8032001074010541c00c44070750f5140c0d41454102d00581c01644000178880c940582d254512180c0c1c0d0381e07190101e205d0380340390045503030000d212000240d094600c1290484600c00c91440c100c0c007040d84441044511480c0d484658080d42d8a03420188035210990300306031645440d01c2e00d10401511150340041100f500300b0f07250b00c1658010385040c002c2e4002188a5116000c81114118003280b00504580119041610f80400c1200c0c002c4503940c0250002d0301624954101c03032180c00c0b024100340545440200c82410b0000340400d01c0141d0321340c0b10b1102401f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 284534874 1250 284533624 284533631
    0x909030a020111090108150d120c062003010302010f0c02131e060806071b05070e100801140103060b0f0409030f09080318060901020709141b09010c03030b0f030303130303 75
    0x807100e03018040d0060001160000700103800140307240207050341c416031280000348001c4e4518111360ba1000c0409c00d81402038009044040184208101d600910004ca01c0764200800c0843c00707170071401541c2c001440064100911070084828003802118603c010275000f81c40980c43c19078000380328001d03201e26102c2c150040e51030f1042e049551040e00c40e08040c1d40500c070180c445901d403038008552611207a0b1510040c2030000c00300780d0004004000300f2005107000780044070a071400310b01006440c0c0c1d1591040c01d40703074182000041009034540b0100e0542c0c1d40a08005245000c144c0401c180c05c0c0841802a04a482c0221500c145900300c1030361030031524a030782c83c0440651079105194690140e1503940d07020084030005018a45440c001600038500b0620403194150350710b41d542015140902c44803240d0000ca403050102c03038990b000e02e090440700c103024080e14107428a400208590701040000e4109075a42c0c1168007155120341c1c42c0445d0280007012030351a400d0481c804d03140f4100041d4210086842c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 284536124 1250 284534874 284534891
    0x2040c0516110906090601090e07020c2701061704030c030c080a120506120c0904060207150209010f080108150c090a1d070c050307060f062114031303080c0c0909030a0201 75
    0x1385801c005d4130642c0180c2d501c250041c501503003d50510380103030084055000f418103801d4103880340c412490b0440b410103140a65401d1882c40c804003400103800490070080851420b4070300075013210149401541c54a44800b034a011401c003200e4100524100502d009400250030a40c01c0e840a801076150703101d0802003060342c0301d050070070480d0908500382d00d18642104581c0c6500d4503200301d07083e60083c051032025241801c15990310b60000c0c1800d1407c01042c0d40815211441d5901c401c403954104003609049089504100070b1680e030342352031910005a511140c0003e0401c1040c08255200f00368054078081485440e0058600c1c0280006c40c1c042c07a10707000400007100076110340030221610b900700024518000c0c1d40e440d03010280a200d11501c0c1c4807602c603040041c0d601e60a1500e019400320f1614170b800c21984500d0541c80e403100249016071540d105006008001c80090f61440460350b201e0009699040e9640750303203003401144102c0a600240e180100141a1800f00c01080d082c1c0301540208031504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 284537374 1250 284536124 284536129
    0x1104090b092409190c0207080f0303010e060405090705030304091d010c051e040f1502011406060d020c15070c0b10030312020d18141006050d02040c0516110906 70
    0x100401071240d161085801c2d40c580b504051904907048407080b0019108a02c240c078050043c0c0700c1400120005034815002084150400e00032968010800c1c07020710700d59458220340c030000b001c002c0e007c0d51003a0703540c101042060000b000b010000340000750070307a5121503a40c604100200081021a10540c4000f005410900e81c103224000e54001207844850030f05002c540c0481c00b1203030300b050349440c82008200204007403204800f0f080040c841162210703180c80c1e04040007401d45480400458080f2074982c01c1c40038a548030340559000201d0000300503102c03614401000d14000144070300380e11092181e03017441100707503018250009040c0604d01c0c5445035201d0b0520013244000034400940065030700c500c0107200008580043c42000050300011618400c5034081130303041426030204a9601072440322840640c402401201c00c50300c041042042001d20300400b02f04c1003400e20500900c541d0340d5405000c5158040c034142e0f105e140042c1d0b03500002101e01c0c50320240001004c4040d41c8a40d1050000440c1031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 284538624 1250 284537374 284537401
    0x80106050a0f05030601030602372c330703020c030303040807060f020d020a17061014031803070c0302041404200a0510080117121c1104090b09 63
    0xf1480500248041d07880d5443e6034001b9040f541940341382d2103003044030744440c500b41c81c11405003807400c410301c45e65028010409001907501c00d2003442410300f0034120368860845040000c0309014107491041c03031810900c00c07240c803041501d0000c1c40c500e008480300012000049002d000c24034440c0e02261542079058003099961702040314000c1002e0420000c02c00040d8031134100300c1e580442c1000c0982030054605401003039800c5028643c00048507017003040c11031f0750140746e075603000401611072030341c81040318034014001c21a08841020403a00007002c600e0b00c06030007091b00e40341d04055041d40d4a8a40c1440e260030810030710700c4160700c00d504182d90345a40d60300301141c15000b5644040d0980d840c0e050320600282c0c0f02540d03000c913944050014400560750700c94052410a0a180307036640117132581402031a0320440309140315100c580c0c0c4200c1110301e007254804c0c103d80041603120418104075005400ca04043d0929442005408401040016000b80c29801100319a08220380b02d000c20758803800a12400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 284539874 1250 284538624 284538629
    0x20708030d02090a0509011d0109050717060307090608160609120f0215160b0c090f0613030f140c01031116060212010b1b0303090d0305071206080106050a0f 69
    0x1140c20401c10280918038903401000c840c100036080e81101a0396900041040b1801d902019408104d1103921844200302c03200b09001d084000e074108034a09060710f0003800342401c03a102d030711168240c1d00030079a0faaa0400131000203005002090100c00d4076030004680f80ca54100f0214058180d0400100c3c01e2400346a000c019541c49500485243c40f0944401c10140c00500050b80c0040c4103000b4100a040141c000701655071a142c1292110503032480c1000300c080c4010052481072400b80b0000c00140e503220b90140d1a0141110740c640c4070550020881c05948640d0f000414801007624440204117640904441d80d1100c2026034a2000b9014015001c2c0c0362207c3c083c8103e41d10400c54801c024404840d4800801d0090000500b0254000c07503050240c0e0007070b00884e4141d1004142c03298405058021000181d40317110103982182881c40f803207580d6101014081c001d142c4c88a001550152003044143c82c58801620103210040e650444c903030003407141c2c0c09201c3c002da61002c000b243d1001441d221008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 284541124 1250 284539874 284539889
    0x501020d020604110607081b0706021b0907210501030506150f0906011103040504020403060e06100308070f1a0411090711100e0a0c06050a08100b09150c1b0306070207 73
    0x4180b0100000c201761035116220858007000244819010300e1000c8285150108610009003119414040301030702e00b00e2844c02d56286109585050030060b243c03041c409070020154104001801d0802c4100030180180501c0c41c1032880c83c0c90000414400005103881c05040c50410718070311f2070f0300c7c44140450f81421405054001040d2400304945511900c004a09280c00c42c0559042503140d5000070b05a03809584143c608a882d101350407104e48007403001a030896110042115994519900c516040c0103e107009440400741620790001e00428903010f00703d4520001c1140c0d600d00d4685003401180e02202190b50103400b5440020740140d02a000400385003500d18018810403003203e114002074000c414845005000d6000068001000c4145002c050300484e1209601c0f42031100b401440450001c000a01a41d0940002c0003121301c00c0741142e01d024402c0c0e5240e070703030f98a50800b548100d02c203c49074098240314602032095000519218040100d0044003560641e80700c08034126591700b2a40501c91 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 284542374 1250 284541124 284541143
    0x3031e0c1c0e0109080403060507181205031c020c06070f0c0227040803150f0a09051b030a060305010b1203041203020f030a080601030506191202010c0506070302040501020d020604 79
    0x2007803208005041d108004a004000c03038194041496582961411407044034100004a0705000300569070184a91002c0549002903000f428040803c052654610500d10302010520060042c040b003441103d818481581000c07558100e100100c0000751300c500165441400f440010400e22840391889903803081460f9556696480e5640030010000c81301030041d15403042d0340c0e900c0227249600018203886039004e1940c040c1c6038034002e184044003002984503244070b101c1c4608141d5495860104000a81e140ca00b80040cac250b40302845102030703500705c100f10130f0040d00100c2000606c0d00140c01442c1902d11410003884284050000c3c0a610502c482490410b0b41050009100001030003000c800064001d104544c10341a00d00c0d881d034110341c002c8900e031000508441c100411f42d601070103a01e030030a03800c2d100f8950700010514503900c100c4690084603c100c151234245020740e0300c00c1b1041700010703030054140d40310750a12040c090020742c014450a40036010380580701d0280b03400070039054806c903041410301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 284543624 1250 284542374 284542387
    0x20c03010917220e061003060305120a0302091905030d0306030c0920030a0f0e03070302070e06030a0213020a08010b120103020906010c0501240b181306080f03031e0c 73
    0x5400d141c10001030490300020042c54407000c043d0f891141c400a20004088000e0f508020b018031100c0c1300040140003d15052060410015a001078002c039008142c9405035101e03003001d030048006c0d00c116010b00341c2c0112600c1e441c0790341441020f1000100c40003207084440c2c125101409a09031201444045c040001d03540c010030504400c0c0e04550195202d070b105501c81c00800b409800d0f180c1d0001c0e41c00414070342d030750840440307900a81c0c0704074039400100b500218104801c41e42c1c002d540d2586401904801894500440c0242d10100f0446960b10750083c4004a0404508814002504520070020009494000010302031411900b00c881450070f003000b8243e02d0b820b607002e00c240500050041c504008040c1c01c0c900100340b0a02c00e4134944225820340002d1440d142e038811b400b40d10341b1740120f200d444003002240740362200b0302000d401e81d100c15101200c3c1c101d5407441040003400f19500480c40c030b005016203100c00c01c0000c40214400c40c0e00395906540c40e400840381e88940802150007130b1402c001080311 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 284544874 1250 284543624 284543663
    0x5030f0c01121a03100b040506040603110d030e0310022812111e070201022118150a081807030b0406020313120306030221060c0f2206020c030109 64
    0x9a01c56010500703070703003c1250300030001c24544400c4000d10000e403030340c03103460b04d100380b4050003101d4004a040b2010b010640c1580c6841c1c5440d00c07030700400c501c9000c0c034072005410140514134403201c3c05002070a4984003400c024070340d400b81d44146050200d0b64820245c43d0200002d038024500140c80940d5418004a40004454003e01ba20403ca81150405210301804600c1c20803031001541c140322a0b5603160703041c9100191505d84174180341204c0542c2d00503001100508401a2030410030021100c01c4888104000700721540c0900414070301c107180008919907038030380280b9010700a034007c903640c541c40d4110541300740e110402c0e404020001e0780b000c00401e0100714550040c5400003010902420003105580d80c4102050038840d560001c652140810410741c42c02a01e034682c40e40800c5512841c810711580090740340c80f0003c180c441188008a01c1c03100b005540780c150b80002c416070801d02c46c80214030b842401c1c0c0ca41e032481000014401d801c41c40c42c0fa030806000d080620f65000600c41039904102c1c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 284546124 1250 284544874 284544881
    0x61f09200c03041a190804021e0a0911070b1305060414032a010b1203030610120e0c15070506060906040e03040f0f08070b0708030606041d0105030f0c0112 68
    0x10546202c107020104240404503c00c1059000b01560b4070358428400301d42c510413551001c20700b400c0c050818104005070301d40c1000c02d1074018205410090340c0a440000516110090700901212441c09400380001d1079108001c00c102c0d4041d490704801c640d5075814004101410040c014025000f00c004100011000980488107800010517281003000c81d41420070090700c42441c101030b04424114640504070203205125100c1000c0d10b140c011219a4490640d8070312014248a0107208643e040084041c803a00d2902c1d000001190140000100205501e55480003a402c4030300c601d45c5091500300001411080390405a0301c100505456601d40d410080103420061000b82c0003a2208001c4204800500c000e0000c0d107210005510002c1c1440d107002c6840045410486060744000010302c12480d680d410744084680c082901540d82c0c0e901c0c404500680a181d2024586020f0881155400b1000230f0340300d0f0603502c054048038800101c05015603922110048100c3c0841c0e103030050000340340c0d0304c4e41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 284547374 1250 284546124 284546137
    0x31b160206090a171e0304050a030b07200a03080f070c020d15020a0314060105090d110a030803010306021c051302120a051f06060e0609091008061f0920 67
    0x106600120b0b9aa0415134450040c1c506070351280d07400011007071102e05110307815014806041c00095003442e0404021482482ca036003c003404501c02d1000003130009104401a90440c020304640f10000004c4504484d581d85100c80300301d012900c0007000408a40e50540003034411006980c804000c01daa81d0280065190050000c2d00d21042c03550442568082a00040c02540c0701560002035900e41c100c110010003030060a440e0410808101c0300f102c0781d481010200c5540e400405045c42c051900d400101040800d900003026050040300000c140308541d4044c200c2c0d00005000c4094903007071014840e04580741290854400c4209084c41800b5080c0801000340b000207500449400c0c06142d10f40c01d1034800203110b01c0d802e8020000861810b02c0060084c84001c242504101c503288102400069407409150320281c00783c0300340c20001d0755a2122101c040010000c150030348940b03013003504100c0741c50010440c2e20000d180c400d2600090140f42c7d0b20980f201d8207401c41e005880048481c0c0a02420391006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 284548624 1250 284547374 284547379
    0xc09011d0307261b210a0204090f02010305070801050604060f03020904021201031e0b0703050903070f2006210402060705010e07030201030c030c02060703020a020307060f02031b16020609 82
    0x2040007182c0d403071980c0c00ca251041d035038401c160f802a01016240f450100360b05091211102480d0b0302c0302c10b903214003040e20340e00741d4410042d82100d0048a641468003a20b010040c0d4014109074501061000040c50403007858003e0707074180103039030b150042034810000038841c180c1c004004200c1080000d104410641400085140151901031282c000074103a800000d211596810214010001c000e541509441e080c0c0541d1944250b03052591618180c80c14020603c030181a115030000f096070100313008a03003180c0c0d405244940c0e04401030400c880380c403810460070450900302040060442c6002d0b001e4a4148803151028004c10948a12561201c0c101800c1260000c10902203840091820300803641e4000d8054020704010b0b10350300005082d00c0c2c611041c01700b4513107440041c1c0c800ba83d0200c0d00980c403040307034100981e940441010407840c1d803007450340151071240b40c03144040207000160001c41c00392400101c4c9603040015203981c00c0191045242c0e508400e0402c0100d1401824001c01a11190200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 284549874 1250 284548624 284548633
    0x20a050f0403060b040b18160c02091e0907120807030e06040b0d11070f03141e070507140303031308070609050102130f050a05010302031015170c09011d03 68
    0x1408039101107a003003030700300303d03006a2200c1d410400c0e0705145c4900c0702410400c07102c51440303403003003a88649002d034003804100c0c034500f0180d11108514000c6129449195010b80544002d20300540129100300109801140010300c00c00482e22100002660a0507101540c0b28802142e145a80c0c081c4c0c01c0d03000040881c00e00c41003440291080e076881011f84010001c41035150741c2e41c2c1803000498100e401c0043c03180e035000e000b48a03000200720106880018154942001440b0100c00c41460301c0314045c41101c02c7e58000c001c0e0511a980300303840043c008940c03045044481c0c03146c031b5046143d0b8507040807800136010350080c4001a422030108201c4040d441c0595045403400115868403001d980c805441501ca40e034000500c01462414400e020008261203000140201d00345400111681000d04c5001d04154001c0007040040c032a50441000400a50b1001c2e8990307880d014001c3c14003130504401c0311401142600159030404414116006903405942e20804040c204e01c0ba05403060040100310b4041c0718 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 284551124 1250 284549874 284549887
    0xc0301150518040c09030b0c030f010e250c0302061821130905010501180509060f040b0d1b0902031006030903112b0201020f030f040201110a2003061504020a05 70
    0x840e48606803101003107641c5c6510301429400e010300c00342405480e00040003070400803c9040318050405505490920a00840913280d15616000f10440107213085507400c405d8140320b41840e04002d440003490310940903501141d42d0844002c2030050000b950000940210b000e41803000c0c40c4240d6031800d01c803501c000509000341d9101d00c9115180c02d80200c5c8803290754200510556800008001c2c0444412016020389400c0c0400310780c8010010b4401d40c052031503801344030780b50f035200d4002c0048141c015100198441807414a031001940310603040d6800700c5442c0300864044014022a03200312200d1500901047c580030048009100382c010690400541c1490741d08032140900c407002408141d030a490b4800e14507514102da00d003042403000c030196841045448008030b881000d4a81c040312810352021903580781d0006035401d41c00e0556000017406036650a0042017810050090a490700c0040071811006e44024140d81c0c040590350104071030701043c0210755916080d0001c103100711240c07a083c1d05048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 284552374 1250 284551124 284551129
    0x90a05030a03020a11010c120b01030b0306040609030f02031201030803180607080103020f120a062d020705010b0a240e0a0303090e0c160f05120c0c04050c0301150518 73
    0x10815000301d000a6000190000500d51020103040f488040c04001c00c40b001c070690015080800042c0c00814540e2112002e10880e8042da200c800c68201c040c00342c46980c982441e10000800c001a41200403881040d000c5000f40e100100b9140d4003541400c82c24100d9080d5150008240c000034072440740254044110456000140989800703100c039a290380400354190701c10080640a08110b0501440c11810401050303500056180803540d0041800a00c8201e00c3d00300d5401ca40d1507049607010101c020140c0480010700780d0007001d9450140d03000304a403401e00c604010114805107c2d050100202c40b2115080164450150080c603905040a5280c1e00400020985030743e00d0358029404965130400400006903602d035510703030281c00c6581c0e80f864a100101e9041c40c00801e42d102405018182c041c48040003000c01c040d0b40d50980a02e0229108c82030b9004441d524581c50400d070380124240004501c9440d03001084e603040c0c40d004034200320b05100e00481124a03801c05140c22407501030780f00700e050654 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 284553624 1250 284552374 284552377
    0x50a0e06031236180c0d02090609190303090b03060f01030f0e060c040305060c0415180e0f040615060e010f0e09070c0308010614070213090b0901150504020c06060108090a0503 77
    0x9903407401035024911044820000901c00e40903603040c05104613020055414007020072550440d0f0300410050719032143d600802ea80340503811641c1c4e00034001d89001c010a6031800440800c4a100355109030100703845484100107400b06403441d0b60000c440300a8811a503001ba04400d40d400c02141c400182c4a180405661030103400741c40c0d03643c0344200003500f842800b100f4001e6550050301001514a400e14010303d235070300c80c610a2170b43c00070407078140300012002881c52085030080ca20141c41400780c2c2002040880d6030303041500c0071103501785400301e94140b82520112410440e4050b441c1c040421001a0056a030460f0118104040013000f15001d00603a6509001c1409040c8990f15502c01a5040c0717406401030394180c0200060142010f4503103814111a4102c03400c155060315601e90385150410350b2409014011801484440c81008101542d2015405100400d040c0042040782c2aa2a01032100301d00c1144410f030f0080d0424000a062075003d00303100c9070400b14180850f5030300c50b00f0303445107403e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 284554874 1250 284553624 284553697
    0x10509030709020c1e0a0803070504031506230102070303050c120d0e0c0d0809060a111c1b0305030f07091e1d0601020d031e0213050a0e060312 63
    0x90742c2d0f0105402d0f6100e0002c000706a024141e001e01c600301640c00d40041640c60420040043c4050360000004451034031a0042d10003c40d40900284944070308009458013401060107200b441024013240660910050400b070007803070b0010b030040c00f000c0f803c45c3ca0446081d4400301000c5403a216900d02051694850b50007820800d641201c0018201d0f2843e41480c01e00f403034000303d184141e514120b00740100c1c0380c4002715103c41408603195075480d400c800050320f15000d030b621081c040e4000c0016180d622040c0030310b549100325155480c0c4a4922084507181030b0f01d00d88403c0980025002d0000031686c601031654190080510b08200e99025919004010b15442c2c043d001032042c020040200580019011102900503c6580700100381c9401d80000390b8800d910171030341e0201034a410000480f220081c83c0d42802082c000350640d40c0d610581001100d2070f07210b03c00e2a02500440748002114185082034901860006002d0700420110b40b208180300d4025500007084081c00c1d00c00c0000c40d0b500c0600c070340361 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 284556124 1250 284554874 284554889
    0x50403031e15171213120f020312310b1309050105031b061e030a02040e090115050d06020904060e0402040c1e1103130303020106051302040302090103060207020105090307 75
    0x8049440101410549030107a0126042d40d1003075950040e0a40c011400302a43c01c0111022034a62405541150036005c041e400740360105d00b0b240b600000c0c404007074091040c980c020b8080755a4072408054294481c401d10100920680b082d25001c071200c42000c40e001c443c00c02c1d01001d00390381a202c40e0b04243c142e00680c02c140815441c100c007000810082d0258030300600c821005000300c0010f0b81e00406441000c070505900c036410008510700c03101184010441d81c82e9600d01d40316100e150850300a0000d610034050554501c130117100042283c1c005000d41c0940c4255080e4401580340f82800b0f100e01c0020301c2c1c004881c181c1d001d108408541c0c5031807046000a01c0c440714207201e5404c0500600c0110750140030a8010420119011041401460302c078030301c00c004604e44040d60602c80680c171400e601403940c1c02d00121100300400001d05605400500540701e048402c508043c19280c8400224803813440025080000100108007203003a5502600a1a0043c14132902c1c003100800002d06090250f0421107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 284557374 1250 284556124 284556131
    0x1d0303090f01020a02060c0912010f0f14060307030b04030516061b020309090115030b0301180b060102070e07050f0903030705062d0118090203031902060f070f03050403031e 76
    0x403114400c0080022a2010314003c40c940550014001d4076003000038002ca280c418006520200c1d5110300342107801c4000980000c10001c070005880c2c002034882420400c0b1949e04154100743d2001030081031034052000140104065071966890010844008106406221091241c46101e001041400c12486c1c800c9000044800324012082260440155800215442031003024010745543c0e403101e064510590f0402034900c031203941180940fa0a9101503015420b060040d40b40340240210b115000d840b03045248503d55520004a986003424842e5520003000b082c0800c1070139024000912040341c441c0310541c0b0b08500200443e1850380225422550340d0b02100c100454007400100301110005201074030600d070f0a000150514a11060049003054004135440081c20002030780036114695000d016a030700c2c0d0071b198031640b01c0714003628100350160240074009000c0f640d50009091003240d01c0d46070040041c0714160114010032004004406055440011815102c908102008400b50008010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 284558624 1250 284557374 284557381
    0x90f050f030418020921010b040f060f060305040b040605071808030d050c0903030409240305030d06050303072001021006090e07050d0201171b0304110405060a0302010e1002011d0303 80
    0x451880460f034450b20145403040c840c0c007003155100c1c0100301903030f0001c0100c9014a043e40c0c9455005140c0030b60100d5101d45040350400d200c0b082030700080215503811581841c00345d5200019001e8400450703005261102800004000800e5540099001041454450b15602c04042c0c80103000d1000d401c0200e040d071001c141000e084c0418040c080e4082444540e590600d02e142e0f01082c2d9034001e0340140d5285907200c100c41e0048440004900c010001c442800f910030396500e0400307a450360310050b811140380e410540086298140007045590310f6901c280702d5096900d2480681d91018907811000d41140110500c60909031080d000f801d010340152080056070b8022421914601412a4421802095202c90103000351703811145103040e10714040741c9041e403965007031600300c1601d03003c407050b000c03c3d0804401c0c0401d10004902d0340c0050401980c040082d40c4483d003c02000d400783d440000e000800e2032540708681d04200208510140880c000400d60360704100540c050040056a982281e0340f022042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 284559874 1250 284558624 284558639
    0x70615060327020906040e0c04020f0702100c02090a02090609090c09010f17010303050a18060207030c06052a0a1505150114090108060616061d030c0a06090f050f0304 73
    0x101c2460904218641c041c0e100680c0413608446005181610843e03030741c29226000340040c0121441000002c108555504150301000c1164008220680c0900703520070502184a001d40640c03040541c00410009007669407480f090085c0d44102c1c080c980000090000000c5610f800300c0c158000c3c15500004d503100c0d02c10200040c0098450f00648042001c0c614540c458a00760034800f03070540e030b010f182a030382c0e400d40d8040549481004155081421b80c0034807002030402d80c08035080c4282c0748540091400250745050444560040d1603140c03a40c0090354104d504000c01000211000906d400c080e6804058103440d007501c001c07500f407080c034000d42c0c454080003c100614461200c2c0c04001f420300b1030050000302c1d20700c440e5000c1d600c07a090601c0b04040210300c1340d075202400e989948800e4010207090781414034144001c1c11804114111500c081819000b00102c080261807818a00200505481d880380d141c0d04094245000241c3e150070841c072065020500c11b022880002407820010341c0c2d00c80c5092032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 284561124 1250 284559874 284559911
    0x224241e1c0213050601021204090608010507030c17270c030705180a090206040306020301080d0e031209090c0d1503110109060e010c050f03030907050f0f01140706150603 75
    0x404004111440750401c0107a03076a0001c40c2c3c0c00a42103100107600e41d10b5038010703864000d031510343c01c50818000c0340000350320380c0382e402c45030941d227406001380041d03120320b007081c0d0940b00c140d410074010070100311001c4207010300200b078264482c2140c45110703003544074028130034a80342d00240742d0300d9190020401e4800f20b0804000000c010042620300b00d08041311425440700c1c800b0040c09886034152a529000159661201903c000d59086030046641c0c1d41d40340506552000005030307050102d00f0500f40811145000300e8030101c0c6880c21404585031108140411200010040407944040c10a000c1d0000c601c0c814031070204400f8865486203038050542c100041c0d2060b005402c2030401408071421b0015642c0504400a42c101c03e0030000280c5241785080e42c204154103400340e4003803201004005039440001040400c4603000d0f10019007143c240c4040c444104032001415000c40c051580a02c0c0e1207145000405001d80620000215000102000500bd0285a1002d00040d48511031469914035900e03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 284562374 1250 284561124 284561149
    0xc02012405032a06070311061303020f060606031603090f0b0910020301030c030b06031c03050717010e010e0c0403060c03020a090801020702010903030e0103020409090b04030224241e 80
    0x10100403040c02c0104102030f1600c0d5480198003076a00412450b003090b020b12007440c98070014009442e0b05281c514803001c9610303c9520180d0040c454038428203807030b0328041405405001c0142200f0f2131580c48002d240d072042ca0340c805007810507640b1124640411800900e5008091240403070300507a00700940740e28500140e003054104c0a0784100300400008848803689001c590340b101c1d03848002c2e0783d4880040d04140080030f5201802e00c00d403040c10b25241c2d056200900c0b4ad00551034100e1440080119001e03034040900404070404118801880002c424004040c0e204491811240c501520303645c2c2d660540360600d0303602c00404e8012a11440e00303508448007201404d8103000031424410180c000031304503089444003a0038841e0300204c40b81d10f43d00c06e030121070261040513000c9c007090021f40f50403010142c04580640c0180100081b010401c11684c4510714501c84030b050310001511281d1031910142c1e0005118000809024429481601d0304440d1665044e180d81400c0707040c910030814440c941030407030f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 284563624 1250 284562374 284562403
    0x90a0b0f1e090c0d06090b090a0524040b040206040803120a0b0d1a0c090d050f060705031b0d02040e1611030c12090613030b07020106080d0f030c0201240503 69
    0x1000142c480004520b00000f2040b038040203c0b64403400c00400810700620042c02c46031112003004803404c0001441400c144c8140100d48210740306140f928500020280386880d0b8400d80d00101d801700c0c030050309007900300d80002c0c011460590344000c1e0701d20315403001021503c1e5030307400c10800c184c80200e441607203400b640980c1c2c03070f60300e040ea25070310141807140c0089030009a465000205007185448002d54000f54005004ca214048007820310a50320f88240da0102c038079100e004001126603118000780ea005c2c0010380300740401d0810a4128814030b03040b90064101c00c5601703000018100d00c9224205000300210901e011030300c001000020040c084c078000b018a50340c810810008151000104004880e801007205600c031024140082d4041c41242c500c40003001d0b60b08801b00900040000b41030050203250000c206181c0c0c1c0b01250394485940944440201f81d0b0102c0407940c0a019070070100d11611188000a01184d14001985442c642c2d01103808103a05885000d20684c01c00b00074002004411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 284564874 1250 284563624 284563681
    0x80105130c1505030f07030906240b0f1614060411010210090b0112060b03010e01022110030f2102030316080903042d062f15090a0b0f 59
    0x11202d02810a00c4042e210b0000305042100051003a4400c0c1d00409165a11030300c24049070260451400d05160300b143c201c280c1c030f06410000100318194400b110104e1440e61030403070400c0910360000c40e0000b031405e401c0d22015400c051600501c0f00c2849007610440c814010314401070288800289425101e40c0a4840142b902880c0004550030b1820b0710b044600c102c2200c0c610302194541100078100344450719030190b00f82140641c403110107401a0910311040860040d0a480101c01d03490254030a440300325414104440c1803021440c040e42c42030311103016442e0111403138094944014240c13200341024005800100c103001c0364a54506607001c51a506240c08890380c10302400d071a4683c4218412100751400ca2945c00b00980941c4c0f1146508030314031040d6241890392204080d0010001840030306159440b422010410706085201c0350b000030813040200004021441d07080711484000c5c01da02000d2040704208130009452060b410702c10581070149041c1814003400b590a40e0a80c3c0d450b1080007a01e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 284566124 1250 284564874 284564909
    0x120e01020c041a030a080a0807050a08070507141506030c03010213260706210603030e01181a0702040c0e03030a18050a060234090b040204080105130c 66
    0x3800100840070103000c890001d0440703034000303100c0320100340300540d203825003c1c902e020b400384416a005001e116a07103480e000f00a54600c1c4048605106900525001c940302c000468510791040f400360121910403940c00700809080380b017291520131240c00c3c2c40440a01d1702c007000130340d041c1441581e410842c01d83c000c0d420a5451885e03015804400d01a100019503035028028210244140b02c810b04028842a107100c0b82d22024024542d504012840355490300310324101164403a94490101100d8043d96201c1e100c2000300011542c605485070f02d9143d00b8034100001c03906002c20440b407180300040c031400ca551000d40d44184001ea801828200044c04000c0c090342c4100d440120440c3c00c100500e01c0c00d00c54100160700e01e01c00f81a2640c01c083d8000126031000f040250300080c0050f4004031841540301d1949000d680340e0620200c030419406841d5448908100b841d81c940c0090780d9507000100050b050607114402c0074211a4100d82c0c40e00f41603c40000f1100344448000c805010301400b140d1346a003c907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 284567374 1250 284566124 284566127
    0x31501032903030708042c010f05040b01090e010f0303031104050105160302031e040e150f04090c080d030603210507030c0f0b04030206070912050a0308040309030b010b0304120e01 79
    0x8079180507407809010031003038101541d4051003111501d99110750300b16165034444100e0104070f100315580359120800610241a003c0707250a64a040b900844281c3d01c09908000a100c0038003003a01c41706050000444000c19149020501c0902820845403181042451414000e05030340c0c80c2c0e142c0c5c045841081109105c1d0741d911100311a031400400e06120501d220301e203000c915500c50742255882c200442001034800607040002003080f606622030351491034852101070a070402c14041800d41c41401c841d4035002608154100150755401056510446d540c0c500985003401420512000000d6030b0702010700400a178400f440d00d02c1400c24810340c040358008503025000c1d120351070024050100901420040110302c60405242d1a032140c0c404860781040d140203580c40c074096619401041c80c9480215800300c0162094201079004801801e43c1c01c0a40c80c00d8503030080c0a80700b40c04001450f203011000c144c8001d0818020030001a00a58034505401c0403500c2d000d56012040c204411800c1000241e03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 284568624 1250 284567374 284567411
    0x10c030b190e1315061805090d081009020f0408150c0306010c1509060b0916051605150103030e041802090f070905122503020105030708090a02060f03150103 69
    0xc1d058200910000e45580520500f079082a500050030000c0c1003a2000309002d503500904121801828080d1010305201100801e64404548000d5603503c4254101c401c0f0703106038000c7c0c4e0402d064000c2401141d48803040309080c0e9024100f01d044042d0002001c1204500801118442c2c0c480f5070303052005401c001d0700f0140b4510001d04041d0400c800711703107034006000402d200c200c2c0c04903800e601041080d840d0725040000c3d1a50310080e91103003231750000144103400e42d900c40c0d079440c860903500c3c103161000d03440810301c0850780b0b0141600e60b032280300107511040c4120300399240658000c0e00d50420400190080000b074901500485070540e2a0a414a0050700c4000f00c0c1d6811058880380e01c0003940e1042c400315001c11043e07002a0b800701520300c0001c0d0111020503d13514100c105811a40319900240c4904011412480b000b40001c40400020344030a1186880680000e81381e400c1e554111460780004039a034110306c004e0060403400100b44a40110b0100c0c084140000a09007841448001d0000c050785 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 284569874 1250 284568624 284568629
    0x901020c10020304051603060911030c18191509050108070e04021011010612050601050306070c080d11070821090706110a020d0b010513020c060601031e0608010c030b19 74
    0x142d00440410204542884440341e11001c0d800c4018850b0394a04003140649102c100a581800140341014528200800e59415100c0054400c3c3c021464548c040304040c03034010000181000c407680c8410b2403452078040c50a041980004001102e401c0084500868406900864256001c5281000200b2036445075941c02074046031814040c41c005001a81d0344150445c4180c044d510b800004580050041000c2504a000307904440c0c440e80c0380c40902d03540b48425558140400d00b40e500c5040003444401c0105401d4581c8000800c03000004240d10340950005001201c1c1d0120124030f2289808604401300382d41060800f501403241014004142c61701c0076030080a04229541c001a900941e040040182c0d881c0c3c00341801e00c03104014101003020300c00c280103c030b2140c2e00d082d100c4982d402160003038900c03044a4002500c42c07034647c0c0c1c0054006080f2a00042c011502c2900074506488143c4645801081600c0010810841400c00202262003e501062048c2028001d840e031640355001c204c030a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 284571124 1250 284569874 284569903
    0x20a0e01140705010c0f0e06030405190515010909060e0a020d1502130f080705010f080109050612030705010506091e010e06120a030e0a09020306060d1d03040801140901020c 76
    0x40069480308075480c60720400d5005056036091801740400940c0c00f5000c0c10102d08503640d051424032181040158600c002e4a010300140c2c00528004c01780340020015013035844c441c2c021185501003402000d1040c0f4000da0166103015511b120000910803036008942e261002200980070550150b400103800b1704940e41c01804100c2c50181015409150b941102c001143e10912554a20b0780d034220b00c0c141000a000b5800709003d0114006560350150754259140101a110826170760b017803401910060034024500d40e4030400c6070710501034214042c401070100c54081c4c1c0c00410a0710309001804280170001d4042c0004150f03c001040410740b280052a056403500c5946404c152a076a0001e1024000082c0c5d0720040d028001140c3d081540010700c3c070039000c2003070b20903600b81940c41900d00100c0c0001c962284d08040d08008141220f4016448402d01480343d10010000840c030354107051840d0425001412145c4d515452100b0b802000c0d618aa44511288001d61074002811101c989410001c6d000f0700e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 284572374 1250 284571124 284571137
    0xa1b02100e0f0a0305071701110301030303110715021207090b0a0804050a1704030507051e12070906151706030d0c150507080f0a0603200604092a03020a0e01 69
    0x54007039580c0520401840b00003003901c0030705a200c0c04c0c800d0301e440080c811044040700c00d400550b00003030180203029400040001c010308681c41c5031030940152840000c2d02c40340ca48100000310005109644040e400314980d0001030315545c02d203042c00d85008000d071140d801d0000c0e100040181c00c145030211350407811940f4202589071524944140307082070903600140103040f101d40b41007492927000c01401c212401103048a100e00d0741d820a109500c605001c181e0750180380801c514859040403400e1400c08050003086070361031a614864441201d01c0d5820086446030002408545681c1c4070160f05e000d440712035a422128245040000d030388a81c01040c400510503045c0300001031000c0c2850081c4480c02040f024400744ca0a110020903a88013203036582d0000c1480340c0804d6244070386101c0c2000b9298091803000b51041c915030490440b2400039030700d60b0b00c031000f0030000c40c0b004904e003d01d2403000d00781d4044034a2840c8a401d50ba1085081d55100c01c1058070612030414020750091411100b20020700340300c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 284573624 1250 284572374 284572397
    0x909030a030902120303070e0102102708090d061505030105130204050601090e0705040306060b130b0906160503070b010b180103020313140604020108090307080f0a0e0d080a1b0210 79
    0x1500311011381c8194031180000700c00c00140039001801114001b00c240d00b507440c1d03007249440c040d04681d2030002c2c000c0c0440214000c54102c445c0e2003c0d200120340503180f44c43c02c1c001d17040c00164669400e0348048400300e0f150165059400c0b01017080001811048009000342c7c0742885004140c40310000020344900d03291004035a059008000b00f0028200507010b462036864108000f5029500ca44011615145400c80010341d5100c1803041d81c94201c004801011103524000b443c4000340c000840041d0f0101081102c2002100e0f0800310340c248521801c00345480344a0f40c01c0900c28250141d000c850090010441044503802c00c0c207404608801c00d08005880340c0b10b13204106410240c158000389200442c40406240d50000910b04c1d104034403d0380c0b510030ba641c0c3c0425090b180d008880004113002002c2c40080c000b12030703c40141c0b105128519001c1c00680380f141c00240e890b030300c00c1416507565100290b031052040d84000645182080d0000000c2104c1c40c030390100380e008400f101d4120030445100d1a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 284574874 1250 284573624 284573629
    0x90b03040821240604030b0a0e0f07170d03050c0712120504050a0c051504170a082205010e0d12140a03020408060f060913030c0b15010e0909030a030902 67
    0x1507070b4a100d605190103182e10b0502207201c1d20081c00f00000005460190125000c1d00d03086040b1825240d202c10703400710381d440c0e6100c40c80107400500790041d070500458007000310110081100d0340042c4502010b800c803051004100a0602000701001010941080c08110002410303004136080c195020704030004070310b0703d0602100c00754900080d0a4802c0d082000340018031400007205101d450044a000d1a5a69210b0410800200d80320740d4034600e40c2e061004100d001d4040c8984540c0d0700c01c803426554400440e9450703848541c0210365519100360b50102100328008403034409000381c0300a0a0070103580340483c0005014102842c0024004a07021201c1031000341309201d5540340c0c03440c9451054803401d6140000d0042e40160140310818420840019205100c14042d82d000b80700c040d1002c000c0b601c0350010007400110074031082c0c0a0000c0e401c0e5480000304002c0e0620b04c280703098407641402d02122800140706858400e201d5110700c1c9807409001c00003078040f08641054100d8140050290b00c40d201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 284576124 1250 284574874 284574907
    0x635160e0c0c0706030b040b0d020109052412040c080309060f09010201021b0105191a040207020d0c060c0b07050a0e2103030a0624020d120f0507020a0302010c090b030408 75
    0x2d859071140202e040000c3d0442c2c050b0407036070707401c40115001e101c010310304024000c41c403415200c003030b00054440c1010015402d284100f2166003481c2d401942c0ba12101d082c506000b58808000c00150708001c0c41004180190300340b5020181c10031002461501d0304500001c0c85074000c04a5000c448803001a030310a641c3e000354100c1c8c000c1c1074108014540c048940480f0303402000d007200c0c000440c0c940b24400c04412400c0340702d9041c4c5c200c0054070f11f5a10405003c03e100082d00403034000c982102003040c0c0040410519455007000340560394942000c80483e1901c00400d00e0301810460900c1001d00a14006a4201d02c0d031450b8800160b40c0748101e120020100100e00d0000c0051282601001040c0401c940316604031034140d80c0b000280d24084c11818406488614103100b131340f001070304007607460480e8904c10103280d02e80184010300816071441c100340c8030301250f20030b44d40c0c0d002690011405804064082c01020b2443c0c1c01800c113140450700d4004403a4083c40001e100030010b040006003400c0420350300c813 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 284577374 1250 284576124 284576137
    0xe070f110a050d020c03030a0909051b12070207090209012705060f0306040c020f0714040b040606020c0111060709060804021207120c080a02010e010806040635160e0c 73
    0x103040710032469071070070515211110005828010300076903c825003141000401c4511806607a034582c0c168618040310140102005480c0b2258640c0c040640d41e803042c81d100c094001d18041c080c00d0710075410200c40191620806500c82072900e801800384410507a00000a20040782841c90300d03580e40300300c0045085824802d9046554003003004284042e007172030700740b018600c031b1102500d0422100f040d0b00c2090340c1d01c0f1400c802d040b03201e07840414240140d20900490030388a03040504082241d07401000050180c81d010307040800140e000891181656070b0107944031607000142c1011f00010f0500b004002c007001e4440c0651024440340328081011900c8a1142015101c800000c0d5841107480704202040a0751101c0c0a0710020884440420504008126400c100b64141c4820b25480c1d01c1e2030056034590001030906a000f0343d100130004810401a40c03a035104403041c0182140e54160080110581103182c9800500740d10072440c0744000803960341d40c082929046c04420340b0b1a528a9030b050740034491076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 284578624 1250 284577374 284577407
    0xf020a08031902070512060412030e0a08090f040501030c26061608070302030c030604050a0b0310050a060e090a0602070807171b060f04031b05060f060a0e010e070f 72
    0x10001d2900920501c2e48101d540c1603429501090b0b030b034108101d0001000c1c061205150071200c0400c000851516590b56036000c1c509022030500f4002c61040e040000307019060303402c43c00004000b0054544880c1c030304a0003804480802065040d922100d840c2159401456036000d500f03d08204410440ba0801c0244404801103403494504614a0692440c0d540803140202c0c1c500d2001c9811140a0300035244620071010005003181d403000204400303820040c04c0c8003070440d0f96034007481040e01e060007015084a200d000102e118189032145104030343c40c5612141140035840244800c03104c01040310740e01a9009003000d0317110849410b2003415449403e00080008594124030709694100001406a030305c0c0d0340105981e421040c003501c3e40c0b601011151042403400305070001300040d02400022021145031a1040c02800940d50b51900e4400181d070f4038030000a89208120f42460090f1640d000f501c070500c2d070070545514085002c601d04c0700140c514001d0100b07240c000502c5512030b0f0304100340103504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 284579874 1250 284578624 284578627
    0xd02090a030507090606020f060703091401050901141b0d11160c060e06070f0201081b0f03060f040603151112070305090d030b130207080d06030302030a030c02060c070f020a0803 78
    0x5074034090b9a80c0515104940340755003080c5e030005009001013000b074030601485c0094403040c1d6810384110014072000000f2a04403840030841d245008091103907502ca01c1256000107410f925450303640040d208003c0561070310303130054002d40c46e011103400300f9604c1151380c2c0e400108041980b981940c445008088480d01120303420025031003072040944c0719000312059619652000c07150786007403000701e100c3e1031405044d00000f52041d00065201d01000303039014408210ba040c04444600780c00d81540e01ca541110030201000c8140542480e0440c0440d24403882154100300c214615921103681d21941c461540100d5036036000b4848030840c0c17504407120790401070f900c0303265450319442c050024001514820001c7c841c0742c900c0c070790207030007032041501c0b625004040310941c15007110f031000a5400b0750ba045404050910081203c0d80b01070050101461103038000c2d54a0300c080a02c02030448507040050401c6500c000140078a80c140b42049507401e580002c000c0c0700742d441c1750010600b100d101c0c0e030010055100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 284581124 1250 284579874 284579879
    0x60403060c0504031205130b0a1106130201020f0d080c07050307050601180b030c011202071509030c0515060604170f06010303030615020f0c091e091b0301021602060d02090a 76
    0x2c0c800300600c1501e105001c5d45500141c1a6402c503020b014084080c10000d0402c001800400c3c01d04010b05403558042c50044291605000183d01740541500c401c0300c046096080e080c210743c1c040c00448816100d84d8001c061480503400000d1040d40301070315240b403590002078540107000040c02140e40140c0c1040c1254001d5a5407044ca4140042520086400798a4110350303105078034000c84c402840b14030507940d090b0680400d2042e50000d60003150225070290030241e0140004809002d040d1078680203495003102c1071520300f0010f040c00402007103840c40100400800031907550340c0c4140c0d820394100e907010119014203841d00524100d6801701d068018820600000308041e8981c2100094400600d11300c000380c66840003da0b61201c1c83c58021099030400206440076081540c03c003030344030010840d82c41d4810351300030394450404020740b00b495542d0004494448801d001122029200c4010f5000b1890300c1c4000500301e00c40015094020302c80e034030008410640050580550300182002041d24003400d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 284582374 1250 284581124 284581127
    0xb071b080301050a15090303050a0933020609060c070204091a09010605030c010e091308041205060609010b160c05061314063f360307030806060403060c 67
    0x800074454603100384450350b4049540700b980c5d204007842c400c09840e5520002c2c20f60f64191101c1e0401402d0a04206051000040b4a06400044641002008401c54444a01d491a002c50804c83d4500c002994403540c140080d100d0002042c40d400700c45446480d446422501c009000b400d09a50080c00ba41081040c0404003139092640ca07000d1412240200001a515814103072100c04440200c1c0c0496911227072040103080c4901d0035544114910581464052241d03160116900300c0d8015254103003a104024082120400a09070400401c850001e807961603d62200701c544550716410b0415000984900200f2030b04d10008406098028100780c0c584240510020b00204036114a80c00c0100940c8520704604000040724030108074040d40740c036442d4240d1481540d01420714001c080c0000b021101011181d090348407680125121009810b910b15156041454907110f075442066804850050902c503e0380013003250281c80d41407c000110b076851500148582c05076501c064030290800000708480d6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 284583624 1250 284582374 284582377
    0xc020409020402210a05011401030b060405040c0206102909030705031b130204300804061e031406010318080d0e1504080703050306030a060e030301080123040b071b08 73
    0x200380d00e41341495588843c5002920802c0c801c004aa601d400e8902410b5407282d005803001d008080e00d000d10707007591440414211141000b160300140c2000050000d024038103200b44004004607080c0005500d22200d000c002c450504004202891000860700060388003401070800802c00201a19101c85450100c46407454031180e0b101d110707611131101c1c0c4e8501041c9100751000c1c2c0391800300d071400b48040810301c00c03844007c411842000c192411864400202d03040700a00207402d55940c0d60360400c41d00e02800b004210320514040a040c10310915844800d60740b482154080740903e0040381c040500c0003610388403242d05002900725200000c4a0b03d048070f00d07400c0400e050031000106c902600380c0c88400c090340442900e0007030031682c1c1084150042841240a16041000101518081849503036030500f21440c448501c103541d0000b00040107810401e00c22248410301082d40f42e41c402640c00c06901c078100e4012300c01031079000a08080766019224070000760751603519090000380c04a0f03504018545 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 284584874 1250 284583624 284583667
    0x9130e0f010204141941010e181504090c03081b07080304031506080307050109020301060501030c08010905041106130e152d03030d050a060506040807060c020409020402 74
    0x7800c200000f1384d00b445c10001d80703000040e5070f0540d03624641400c0c40c80c0c0181c103081010b602c201d0380c10001c42e00300e40c90440303040440c11028400726000585a1403000900440000d503c5148107010000c2c4041003141f580d5001c81c0d208007070306036606c0c913800c1882c0050b0042c04070340d002502c88030f06428084204504000146840c00800c40300d5903c00a06c01d8103580c0e2600c540c016059213820030b00c0100700080c131503c83c5110b2042c41480c080342081c0ca44000a103142c1010000766140e0391a004200d0a6090a2003924091718082c80c041c01014520500540b0500c0c0c1032241100607566100000d003400041034148912600043c9895030301c3c4c850886545191102e40100740500c1c11400224509400500d139080e1116806440c0204040c42c260380a080819070000890b89200c0e141301048030769030140014103468840c0c0311700058908100441c1c60403540140c1001d401210100030501c00341a000485108036404c0e494038141c20092440444d000c1e10725528000d41050000c1000b580d0b101407802240e44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 284586124 1250 284584874 284584889
    0x42004050f15120c0415050307121a061309050408030405011107021309140f030a090503030406020712050c040203010e0402040509060f1f1a0a08070906020309130e0f010204 76
    0x6030400780314200030790440c01c0742c2d80500561040000019058400c120281d00c01c0d00c071041d15040550340c0503407031010400e01403144001500001003000b400e030046040a8442d03d00c4a007007000c03581e041d600030b40544260100b9403182e800070800b0840002032070092005000342090038445402c040c5005480c68005450403552035003440708040c219203a101c16103c0030340c0c0007865030002005440c482c1000300b207064010b42d1440450100d141c1c00300c008012041d00f0b00c0fa10380045036500d0003070304028424842900700d94440d400400c03040020b1540054200165890001070140b8182d8918000d440e040700011104d801600100002802640740041d50b8400c07070080d07074107000c265916006552034600489800c0d0b002d1007035402048410705004d00031307407503c3c40c140354419030307191580102d41c0c3c4c003c60130308009403400d00010060080c6901c00c8005402c030f03a050405140c40c40c1040341c065102c0c060300714035134062148824a405001204c0e081080040e422205503210100e55800d0b079800307584503024044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 284587374 1250 284586124 284586139
    0x609021905030906010b070f0c0611150112031812030f082802090f030a12020d0908150a09020402070c0f170c0f011e020c03071517040204200405 64
    0x10301150240301102c0c032400540010300030580c201118a800d9030489a8151594081c40d03400c10700248520385880041e00c01c5484540401c103508a11529107600d01e4002442c1c01c2c0c94200402071034842c5e40f401c0d001c103940b50a018182c2c495003024042c050a4552142980020907185082496080f00200801c07841da40da5022a696030b00002c108c4c1700b561004448040c988038003000c3d0502c001503020304082d82c0002c1c02204030341182c00009281864440094400441c40d2851f04e2217030342c0401009400d1200d90038031803500b914044505450740407403c2c0d08071201c00d2120000300c41c00c6295004c104070b66030017442191204000d05150159010502820801010480005c1030700503410302c580000c0d003201402011408040f400303110040c0f440455280c103104841e051084801203011940c802e4404541c01821a802e40000f09031074041950f12080c1100c41c80911400c07110f90100901825000681a0700c62589481c40442c0040101d0100800c44c1500d00680d218003003604401031044940444250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 284588624 1250 284587374 284587417
    0x100314120904020c013c050f0a0902010302090a0603021801020a03081906050d030320030c0d091518030e0f0a170a0c090b03010b1e10030905061017060601021b040f060902 75
    0x5400307c0c2c0c0141d07841d00c1c0d0b85c20800300240000c50035401c99400c0c00e20602d0054180340c5031001145000d003d87e00400c000c03075004221445a05039001c01007006500c2440281000b00c00782c1c6000d02904009843c80030200c41071014036031009480c0e00420020312000d03040c05001c80d61414000c008080080e1300f40b01c1000c210446034060140402aa80035012040c500d515040401a0060080c01005012610810030008180c40c1c0d0640340700f20b03000e04414107840e81c0601e5a0b031070010f00c1030110301689032060802154445054842040000644407040e0307510701145451404185012040c00000301a1407164a012840d20240c0c0c101c8070130b60304180d0003807100006100070006101c40c40c1103208182c0c0c441c5e0380545a030f03141c0803034a02501451414005142544c6444640c14144121001c140e11a03030524104003206031940d840400500340c0d0040c0403541007401c0000d4854a0a55038200210b48035903103400140c0c0c0b83d03449509032601030340e401c000596489910318040e4001502038003128004130140c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 284589874 1250 284588624 284588741
    0x901060501091e0503010204031a0c120112080712180e040b04081308010612151e0b010509060d05060a0807031a0406090b100314120904020c01 63
    0x858054600c1612400703042030a050071255446100518041400c020b0140011107031401c1c80208082c40c09940c041e4541c84258149103040180500082a6800104000b48140d004d42011905440401030781400060340350a01401500030b10001501c0541881219080709800242d080c4080241c170380c000154581e00d44103130200100443d0050240341034080010b000404c000b0040c1002c01481104040d07a6031211305840c211902504008040b0444071050000e01500c56200307070000a80340380604c00076004d908a10030101c5507507101604c450302c4010f125043ea025405540744102d02410341030b00c407000c4d000310708042d060076240e0320b000d0f003483d030004030b80810082211029240c211030244051100004140464040140141c0d041559800c1a00000f8000c0001500500c025462078074241d0540c100524402d0012200480707941c000c20b00d039030704000c080301a620b40c06012500142c48409001c8102d024003c9410790f00074040051003200c0e40e2420320f0f03002d481c02c142c90800042c000035550782c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 284591124 1250 284589874 284589881
    0x40b0310030203070902090609060a02010e0d02070603051302010c14010f090804031103060403090303081506040b03371a090c030103050105060d02011d031006180e0c0607080d0e0d030b01080901 85
    0x4448d0444410818150207091542c018074a03600148000a50150101e40240c20881d44440c000e0050700190010420903505006041c0c0040ea03140e04e10000741e000e540081c000b907041d801c000f0b01c000420303510520b08406c03c2d80118178141d0990014032440c0d10340e00e40704034164410b00044402c0c030f0840503941c8480c2000270f240351195a25440e400d07105030461314107580865009245030303801501042440c5660f2500c0010300002d0034010701c0707030f074481c00d040e1009040340d8400300b0704064422004206484c0c1e00c045940360300d048940c41c2c000003400044800c010400000c1c0085080d0422854810300008003144002181240e0007940200019100c950400042d8000d101020b40050000e110300c65810501118540c1d0080004048540c804c2d01c03002d0103400d03560180d04c040c1a805021030032a1040b8018010f1900028080c3d020f01088090400040c0780c81c051080041e10201c030201c0e241611004c954071662802aa44040b03503d03a20701044014060075800c012940000c0c864408034030070321014003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 284592374 1250 284591124 284591137
    0xe090106200a1e050712060903031406030303160e0402121009050609010510020f0a0302010b030f01021201060302070c0803030a090c0e0f040305030c040f030c0501080c0a0206060607020105040b0310030203070902 93
    0x503015007407100864150b68203000f0240ca1900802030009040010120503240607842641f002c04c070000c07182006001c80d40220742000101000404000766990f010048170350000000c040c01140700455201141c02038000c0c0400c45d00240b0000c0c80345c0d4140a8a042a48500c01500c1405002070311041035000707907001a80e0f01030300b010100005206a15120a05d10909000c2c0d104803200c1c0d0001881651801e495000150050f0359621040851030500f40000c40418407050020761501c0e101460742203140c5014480d1b601010b44c013140364005c0241080c8540010583d180c1225281c0c109007070040000c0001010441d905841080700192a0038014060340c802d58140c95132500c1640c0702d8030305990b241e000030400a60118104404134071180d0201080c030140d03004900400140303080c04005001c2c880e026041c4007041348144001002d040c1e0024500b58000701c16911507881e01c8a17480140c4140c06507400031502c031400442041300c0c0501c44c03d03448088070f00032411940c005603244100b40c03c03849801c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 284593624 1250 284592374 284592383
    0x10e0708070b0a0c0605040606080c04090c050409020307050910090b04110d050a11120a0f020306030a0807020d060203181605010e060711090414071508160e090106200a 74
    0x4030810400b60901101803d441041e60820704003004099403080201c8001f220100c407401d982c3e06080c801810100200c0142a600b41c41c1004241c2c902e85401d1035008852080380e20560f202c81d001b03c11034a060121030020034026048580303504203038415806029060103108860b0b46031480701500d9107403031300030070703400c0e02c0076054a6280c012190701813406072000400f083e0200d034440e42c81c3c40700c410003040103204903007031241450101e003026032101c42524101484c45a0450040c4140002982d0200d001030a16a100101580d1a0324600c0480c0c0320300d80c20000503020078030120401907175682402c03280e402210110150752101181e030598121a01582c0122400140512403000203801c040700200702890160441c0d02e80740a0010000300036013001c503411503040c0c072501010900e0103803c000520262580c281c4030f003031907141310368004c1603a40002c080600c141660721040f40500d02403402c640c18400050b0000703a641da114403014042680c2c4038256801ea4080c00f00d14552102e02050b42441c0c140d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 284594874 1250 284593624 284593633
    0x2a010b030312041415070e0f061605011505102102030403080403020d020f06060409170d090201090e010303051206010c1b05010225031b1203081801020c060c0c01060e010b0c010e0708 80
    0xb015811207c848410325116000510b04041e91956a14003024190070715200c5004210740c521868000c0c207441202d401c401d1000f03034481043c8140c1da1400042d461420305803038940302050440e001032140072201040f00900b18800401e220916501019040c852802030b001c48500e810015400c03a41d80594540e182d885811442c04031b18149407030341001c0c58403401b82441204911780d5403041c1000340e12282603000c81507604c50a00045580100c405c1c0000d0030408180c50b541c1d0300d1504c01a009229128500361021b11000c0003400b10385c01465482c6401d40c02078501540c8a00002501c60103a0b80c078019280035100f0002001108051008081101c03c00f41405015003855a40d90030005141a40e03010b042c010400e0b0f000c200381d89107a641023001c0f402580c0d601850f007441d0005280764070b0300381e9000b1010303401007040c05021030300011016081410720900136510003040c004280109495082004059040e400019104000001501c521603503100200503182c00d0490ba181e5500e1a0b03ca141e01c03d400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 284596124 1250 284594874 284594881
    0xf260616020307140601050406050109030b060103110f160b0c0c0a1b031407090b0108060303071518060911092703040b07031805062a010b030312041415 67
    0x14400121014110074012241081516a074a41c182000c2148041803030303004030b004003c989024051500100b03828201f4203922400c1d61a40031544000911003414140c42d603c0114000c2c0b40d0b542200d00c0081d140f44841e407508080c0008864200100406681400d5150b0100d20781d070540d40100c0d5a04c84000000f00003070750495507034a111700b204800040082c2d50301040000424880980c1482781005070026043c0e030381c204802d9000302c40c00480801e042000200402c921a20008101c0d8030031a00804003a006840c042c012401501c0e0840400130041c41d034440050030800c0c1d0380c0080007441e115045c0c58000481a009208000108480c468000040034829140980000d0a030b1002c01608a06803803419403945e50080356680109411000101440b601d41803410324884044007400f01264010310307104010a00c4800031903000d800e020407000100d003c0118060035440000e0201c0040d040c1c03034541d201301c41c0034548020304171016202020031000140d1202c2c0045035410704c404040d0809440e544 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 284597374 1250 284596124 284596141
    0x406050c090a050d171204120201150e10170705010809121e0d140405010507030c020d0e0301020903062a160b0919050d0207060503040804050f06040306060f2606 71
    0x110500b002c0e00c0c05400b40c3c0c1d401000e00c81ca003008000d501c1c0a165146e4003810249820450300052130395100459140ca034402d0300c0f03a034030682510215840b0501650480e01c8000482000303002644c800c030100c8507600070071204088081424002caa500f601c5000b4140e440450098440090120314203515a04124110040701071507400210508245051410602440301010031210300031110302d903009a503020402004000d0190740d40c031140610301030041c00c6130600c02070344d2202480d0150041c040d480804299a0310254155112480000c041b1841d50030050902c00c0b000d00c0c0c400c031040d107041d02c8511101c02100100e0454035000b080360303200b8403003884c0c81e00c48104a181c094418071450207220204000c09012100d1204224000c0d40904140001158064075003a070315031004003030020a00030030001c94180b0050702c00301d0700c05442007071100313a529000a50a01c00c40d000106014600b0201040c0452854000c000b40e03000b40800c48100d4000c84000d68462001441041e11907000350002501003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 284598624 1250 284597374 284597389
    0x15081501030807080415030501260a0b06031f050402031603050304030f150903020c09070e0d150b0a08010b0f0a14120102040801091a060904030c060b0619080406050c090a05 76
    0x3130203003081506103074a460030b140c41c00d00d001e00001d00090301d42c00180540c0c1d101c800c020035914100b001108141a441103e2919004010800303008920768400090658038140a844403c1d50a1000c202600000c800d08000601007134500360300a110b00908544220114540082030329001001103040c01d14603074480303401003c084c400b140c3e00c034620303c4904000403007401a400b10301e10a40151490400407424807504a000038111801c03c002d11030040300f103841f44100b041103075420628440d80441d02020341d0002d400740303007030850300300510410002d140f11040d40306000c040821140c0c050910314050400c40e4001d2a80110823001d4218000020249010072104d02c1d1031f81ca04001506103640d0340c08007403c4881d821416106413085e04101012031814810300c3d944207404480060140c2400d44004021807036400c0c005021998a0410311b0701565a8400d507245d4280f1200a22880a080800101102d1098070110790130b0741000003181981c4110000d440300501c0280c01c40113054501010403070398 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 284599874 1250 284598624 284598637
    0x62a031b17040801020d0b041a0607050a02120d030c08060f060918190b090c07080a0e3a031d01030605060d0e120306030312090f10150815010308 64
    0x30414805072064541203880d000d0070051598500040c0c03240032031810a41a9682e02e0b031254842c92030700e100c401507003003090001d44490005541058590f0032510b040c5160150b02c040280d0f00040d00080c03070b5072410000500e034180c03c8940c0e80c14131104004550540d0380f281d00380c8407180e002030103602c510090304150018000c1a280101541820140310420320058030041c0c560200384030501a02c0308600c0c02900030102ca400d000c0c1d4281442c1d1030301e0f5490041900542a0050030f1040c0044c529140f10300c00d2540540e4840010801c214050b0f051400103400d80d400941058682503500502c00d0351440c5400b050710207905a11040003030001d61108501c0c0c200c07a80310080c1459030300c2c4030108079612240050000004106400030f0000018140c0714544882c120f441c9550000c101b003007003001d40300441604c85008002c0c26002540d02d4051080f810300b05003026002540c03055285039019801c564201d036099000c0c00d02c01c002880c0d15140301e2500c4010b00740311803080c250300c10010000a50075030014030302c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 284601124 1250 284599874 284599883
    0x11120313060c150525020703080a050f0715020720090604020d060f03051e161401050903240c12010b090301060b0c0709050c0909270304062a031b 64
    0x6507031000c083d01d60841d4001d8820480150071540d00381055842ca9480c00800a081c4c00102110b13490350b5a1044603100c0c543ca00e02c00c001020030f2060146400400ba11313a0550300007250940005c80035204002900181001c3c0c5000301e80a810b19041e0050302404500c4010140056100e5911402400042d5010400030002039a03120400146844a48480030146128002400c1c03980d00ca1640300e03030a41100618001c46400180400d03c18a0070a0107110803604013598005c00c0da0b031407400607a854043c0380b010980502506484030f42d080300003001c012039000003400303207011911009241111070040780300148241001c0300060104007502070280c080408000c00204105444000010b482d400c0298040c03141e6002d00c0c03042c4648501c502030310341c0c010100c1c0b4000d0b0a00840c2c00004070080b2018001e000c03040c40d507a0607800383c100303207000c404880700111040b070741d030766558080003047c0c0c4060030025800e0484c25040440303130000aa01280d503558050742ca45000001c1525500840c0244603804ca0307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 284602374 1250 284601124 284601143
    0x6010804030e031b150c0303070309060908030f1608130605040c0f031a0601050702010903060917040b04030311030309070e0702160e06091605161e11120313060c 71
    0xe10369808011000058621031840c01041400ca418002000104002001713a42c0050040f03541569001003039a601030100c0c50003080b04092410700f40014108500060003100d400410000c0500940c00c05902a070404c00100c40300841c200800c4850400c10744825000d0b140c40b480513004182607401042d045801a42c4140019589080580c01d010301c582c011100f0031203d10303030b0044511b098400154884d03000e017002450070805600007000e901c0f882c003008013003aa40b0320142e414000c420243c03200c24505512007940c0c1c0c0740c1301d404420b5150000c1c4001c8002a00046118015040120a890094030340c14000c194450802032005025100209400214850075000d90b02a10100f81154001c04036104a030469040400c14406980c000421082103c8030401d50201c400f6405001c98103030286140c054030703082c1d44502c3c15010050203444007440541c24450700030705004545000307102a80d4111440810040c646010a03100d0061500f0707030081c082c80e03490400038140034542e206241c41c8100d2046 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 284603624 1250 284602374 284602397
    0x42d0506130b031302030706020f0c090403050d0e011b0201060f1208120705040e07020604021503060f0a1503050f041e110310090b01171e0703020306130201030f05010b030601080403 80
    0x1009600b00300c40c035900384c429424401c815814203002c0b1401820151000d000810800c3c03d0b441e075612000d0301c1e40c50203400c01d0310025050500c00c42c1903400c1d030440c0314814003015040b000b003903000e00400c0d20440400301d8800c04200d1914014441e5000703c41445036007118181c0703440701c54501401d9800342641d45003400c0000581d44030814407054418280c6466241d152800d203400c101000c04010004000d44d0b0082060102580d80d2440a50000c08201e18a5035650344810101e8401989070610b580c10112654020800c0c13150404010408540c5580820003650f80b4602d8010ba418140d074042c004103203010025544405e8803811148841c0681c0e45040c0000d00040803034544126403d10381c1004d44d607004041c080042446000d0300400c0f00150b601407043c00006483c0d10313041e400c400c940d09600c041c6c0828540c00010700226000f9500101900d8061500c803d40c1c101580145070100d00082c036101804000400e00d2043e14107840500c4921030440d6111001504c55600191007035050020407900c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 284604874 1250 284603624 284603639
    0x2120d08010b1219061e1401030606020327120604170403030f050304060603020a080f07050609060d0e15040309060207090c08010e13021e130e06040b0717070302042d050613 76
    0x4546e02050b4045e43e0005c070703038070b803501f840b82c3d03058117050315810141003410800c00c8950000c280c813200c446200b40c50010301250304d055003440350092102604101c034290114080800820524481c0d406072011540ca18500b000da00b00070710075404000c01054491014070021071180c805164862301c60700d4005003080c4c582e00010301c2c00b03581da4811020381d4006008812452000d00003800100000e03120503081241520018100c0c0c095503c841c4d03815503071854020022401004000f082040c1103000c007075207003080c0c107000f8107009103401440094440c034100000c0300b02c100c0c45003c42880b41c40e5281105642040c40c80e45440201525542c035594031510b010700544c0d80c00b000b0030314540e2542492501d0607018001d202d00700e2072904600321280c2c40c00d421855201400b0819580c0306074059102021950341c04000d44003419110700c00c3c0d00301c0c0708840030400c040750168000e00503039020300840c00c406c40c1c0c00c89004600755242c1a1012015035105c00401141c14940043c0c80c11000503c02ca008513601e8110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 284606124 1250 284604874 284604899
    0x1202012007050c010801030b0a0c02030910030605011701050a06030506040207021e1c1a070203070b0112110405040c27020c21030424020702120d08010b121906 70
    0x1030110140000003200410010308000da807016100038244403c85603d03644a00b00c110b80000c0480c803101e40c9a01c411107a5034402e0044901241000b404000e210080142c010000c04550045901080d620607040400480c148015812034100803d94010942010f600304c3c0545000b41a00e504260288604801a5981420310300030b007241c41003410424011804000e0155081c03011824030f40d80103000744c070109000b2512000c0000d20290b40d034100b034944000882c5144a602d81c0609001800b4001140c3d41804a80040b0b9650240900780e0100e09105c0422013142d0066400418035403d0007000c0001005224101c8600e6208001e043c54000c4000310100c11b0364000c00205402d500610702401740724405100e1607101c020f0140b000c074194642a5225211428801560324030081d000d5440302d03e080140d011035130365940c050211900c20480d650000c0d910b025525004000c22800800800c3d0004c41e00305490011542c42030303d08498503180f480c508020220303518000b0060304d44034081149240080c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 284607374 1250 284606124 284606171
    0x204090f120809060c0a0203041202010c0c0305010e0d03020a0e090711071404110901052b06060809013b070906080a0c150507110a08010c2601080604120201 69
    0x101c2d507800758a408203260b81800710080c00503030000810310451200690000c00d0b035090301e0051581c0c60b161402400140c580072150700c002401529200c8002c4200441034004103040480c09085a04a085020080d001ea00500c920480001c20706446105189014a03c8681000d52410403400030408581420300780f46403504446805180d800e000001401c0c203210301c40100e400b81920901344804000000e0140c0709001c021310703c015144950300070082c9450b640d592450f035400820407a9035a1101c0180a59030220340c620340c15481c014ad5120702c0640d1480508c003004951091502c41c0a11f61002c0c00240031041c0c075903900b0301c903e20f0040341c007008510803140540801d000134a0b40c0d802ca032901e458614140d403c1081007114a07004240d03456045400d54103050383c441d00000004500d603001c84d060b0f03070702640070611542c284000d00c001c11360400b0300b0b403114054000342d42d68507400c01c0e00d40c0c0c015402d0038424240c05902400002d4003255103d01030f20008001c1c1d100208208444040c44181d000c2050b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 284608624 1250 284607374 284607377
    0x307020f130e0d02012004051018050613080c010305090c06070f0b070e1923030312150f04090209010b0309030c0f0601060801170c060d060305070b0c01061208070204090f12 76
    0x49114050200c040030390b1b183c01a451001a0745418140f001081203000700c04088000e00c5200d00f14004841c00042110000d02800741c0f059813642040740001101a101e40b140400501a08100c008554880d001d0507102d040204024070341c14982c4024000a0750090100b5913079845602c0344100000c14078401e860184000307a036000c0004103040200003070306c68110303140400030301070580802403010346001781c9481d02d6907003482048400c804800f181c150320420103035000d103100850800c801b07241403400a0000c0c00e800d4900440d50030b41c041c2480100c41d41031002030750129004004000810f6034400640e80305542409032410315002441c0f02d4a051110290051b0326048240180540ba910085039401071070325903000d01000e682544c4ca25243d400044010b030242d0340c00990040841c0c2aa00540002d41d801400c4a84940da60b541201464211816000300e035420410000f60700ca94014024980503081041540703002c0c01c5500300b2000f0400c0030000c68017112890300c600082004415824024002c0307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 284609874 1250 284608624 284608631
    0x106031b09050601020307050c09041104051e070905031b060c100c17071d030102040807180b0607030f0c02130207031806030e03070201030f0624030e0307020f130e0d0201 75
    0x70050088259800103000e2411984184000c601150002811800f9104251000d070215119401c000c0c92042c101c3e40b5040c0c01504000502103800c0e14000c00c80d2503907079851003000c840e80354048122000180c1d403044940c50f600121450b14a0600c042c40ea444580d80142140e00d8070100c13032a401d0604601ca8141000155646084d40304281c0003000868040b580c6003a1160616190101a00c1503e21301010002c0701d8020480c80082e0700c09604640c0600100e0044544040c2e5443c0c0070051500449a181c42041c2030024501075401c1c80ba0a0398640d5a05846800016510300412903100e00c001078144c3c0c0c405240c3d400c1d602c44075080c0c8000c002580c040d543e4a464900f41031028440305203160310810406240070300d07110328214080301303581c41c442d424030300851155800d02603500a020140c01c801023220f0018000340010303482c49000c8075180300302e071002d11407c4001c0012a03101d020b0300c40c01079008000301005266615210381c048074020200f0000007181401c50700c5440c9443c802c0685500580e54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 284611124 1250 284609874 284609879
    0x906051305040c050d050c0712080a09080d2304030f050c010b040504030c140604030e060d0212010b040303020f011a011b05160f0e13060902010c0f0b042d02120106031b 74
    0x107a401b030294402c0700c9403480ba140003640d603218041071034440400307000c20540c540401d0005d071030b90b00402107441d0402d01c4251200f400344411001494914202c0e00102598800142c141181008142c802c5070942c41d10a030702c0c4422242a10030350700c03024245020755039808607110180e80301d202d030f24040c90007642c0760380c172403d11450600c10b04200113041c8001903202c0c808100005e070b40301704428108101503401a89603072003043c207240031303019014090022150301e20011444010f484054401c03a8042e50803074040c050745000081c02c82d04a00f00280a20805d2440512a94040e07098841c0c220020000b148222540d501e4503410705890320a034800802c0490410002d0564440d42000642100c20210b142030030311090140d0007001581008080d151220007070000d41e03002d1004040740d030740c101c8941e1446080920702400240c10440b001c4946111241e28007041d180000304004042110807842011181c1c15020405c048941d8402c1c04015034a41e1f07004000900402000a024620f000e41b4480c031a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 284612374 1250 284611124 284611147
    0x20703021506031f020d200d0b060703080105300703210806090411090c09040f11030403110718020403020405130201080f07050d1112160906051305040c05 68
    0x148090800740c4680d000d2000400c11130066500b4000105404000580e541c2100306408042c00070340080b0f100e8084004c1c4c2c1c0a404100c10001049040000c480810207041c00d0300030040346015049010300000c11100050244d030900884800305144000360107018040c2041c4440303400e031285030b40d04146410080042040001c100c07403607080c5c03182d041000c5810300c00300200100100001800544a02000008a003d1120400401c5441080500360400300c0c6050310468041c1d52060380402d000728900125201c0e002028480c0406604034850454070b151201d45044900201182c0344005502841e80d00203005011040b59400d594403200001d40c94134030750b004101c03c0329001440008240d40996030340700103170b0f03214007000e500038240e1507810303d552a545400c40ea0343c02007001e03803800903240201c028a51250a0060182600c03200c49030501c13680c440210051240380c50b9414008100140024444d06000e80301400400500e09004142d1682d03840003c2d00b0b41d032a0113081030100304006082d01824 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 284613624 1250 284612374 284612413
    0x12090504050106300219080108032502030708250b090a2102032d1203070c0212151008010b13020904092406060e0609190902070302 58
    0x415049404100542c5000c60141a0114002540400c2c901070100e20409803410015110070005400085445002c3c00c1c800d03000128004003c54042007c190000031041c3c07000046661003e201e5440c09007804884602104000202d18120380c14000c101c3d000c145204108945d141001000800f0424584081032810b01550590052007022400f00441c80b07498407a150442c1c11290003016503d1a000041c001c50100118101c00944c5401542031700c2820514a9416805811070f1028440d08036104660441e0303692000c04081c00c0b006018400101940d02401180c01d101d030016109031039151400f404107003050761900c0c0b1100d118003640203002c1112800070340240036240a4001300602c1003101e000410602030381e0710814143d43c000640d1445504c0315040180d00c42da110451700c03554000704240301c00c51000070401c022001e240040c0010b61074031a5086000070b41d00a0714052800b100402444446210110030350254490b03964006101145c1d40700505003607000e50f01030446a04d0002500221 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 284614874 1250 284613624 284613629
    0x21b060105120f060106110307050f07090605100e1302040902040305030c0d0f05160312050702010e01050a14150604030b1305070e0103050312090f03070305030a0b0a0305060a020a02030706091209 86
    0x99200d860020012040015013506646881c10492211500c800010740386200307108000f00745000c5d41464895885000800c58140c800c40403041c810036484100f8840f40a21510300d100000c2d201454200907403c1460b02c01342c4841c030001c805450103031100409420703a0302c245c0c0211940d500001c2c207106144010700c998040400503107004030920400c04c2000f4031074003601c1c0d40b48009440300a100340c10540643d1258030244107122090003940340501c0301074000c0611455890144d4280b000043c004455480364480240700e01c00000c2a0b91901d0842c40c01c40105c0701909600000200000301c04100c092410703e20031903540600b11044900ea18126041c41c4055200c49898541c0030018000240040305803950b902441c40010340b5076440856443c03400c3d00040900060703020010300300d024503034450000d40c45120030080c28020000800144034072404c5d144806841a085580031454201c0e498005180600075481242d088c03e066440d14011910401c6084401e828401c00f14000039400c440030030f00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 284616124 1250 284614874 284614909
    0xf1d0301110708132705091c0e12030301061b171201090f1a04090c03120f02160605070f03020c04060b0403060e01050705160206040e0f180d020c06030a021b060105 72
    0x1d8129840d402100c0c0441002c40a00301643c480c1b0000d40608030030028900240010000c481403106007604c050603580829800038052415011100c110302e0000040b24101c13029656452441061001d00354008101c4100456824041c043d109880c1c02d03950001d003410f170310f98214240e10381d45030500d032800301c2d00e200710240641d1341048890076104640080b0200f55120558011900803020301c0d10382100072164000404005519501c41103003507020400101c01e240c03580841e0440e807140111090407280c94882c07040068000c100070000508403248913104a4802c0c01140d400c1c4226100050640700d103500400c600c01004241001444814003074440031341c0142000304541d04000000a007548541c0c46210000e81e00c10407840e08540301d03482160010901e2080102d92820038101248400c00181c0c2c01000200740071450304e91100c0081200319104005030000e20038082e0788020310070250001886481e00755800d0000c9031402d4050300140d00c2001801029140301c0d8180703c1004410503d0703e000c0038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 284617374 1250 284616124 284616149
    0xb03010501020f210f0d09050c130e0303040305071a0705130e0402011e021005040605010504050612030414012c010f0314040b040503191701060f1d030111070813 71
    0x1380c40440002030303c600303400d000c03040d20781e186030039003680380d403441901d0500d03c049140c22407041c180031011952010060302202c000140c2a240c10485080d030714682a444100c1d0410000b081c0041c0c020001001514407400518040241654400700708060485040c0b0105200081e600c040321005180c0c4d0020748004c100152032801c09400007400b00020105a010000d002609216010300030440010300110b200fa00344038500c0c0529041001d0442032050724062402d20000c81d00a141404083e60402c288000850a20345030140d009031f88102c01c0d90480c14403542c0c4082c410307000c0510100200c8640508842c0b100c0b803040400051211214810f103404240c80c020340c803444407075100300a03600030340c024050b01c01030f454074201107003140b140c0017100c0682948800041d20396904140001e0000d044038101c05956a0784180640700c941401c0d4031302d0002013104820701912450407503012030150000c0d0001503c0c2c0440102c0c0c1c951544180001d4505100220b050310281c03588082c0400500307807a00240c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 284618624 1250 284617374 284617393
    0x12020d081b03040210120609240e0a0207021f03140a02030121050124150f05070228061d030a03090e0c070203060a0204080c09070f050a1101060b03010501020f 70
    0x1107064000940001e2150172420000302d6070b02c0c850038501c0364240303c00c0001c0090b1540d0300701041c010000700b0f1200d101d20507050b0b001d010030320031501c802e412a44180821f084a0b03403603894020082d802010f040382e0008140841d0340203071520182000314034100d0b132130000ea00311086500e80105240103140a09550040006001c1440c12002d107a09c820210030550740745490928041d0302400c404508090340c5103031040d005164079090f1075220220750400710940d4480c0c0700310004440000c40c911014021860800040006007043d019a403003010742003804c02e030505404505040e00301c3d003603800440016942102199101e904485800c1001c000714001c0046212595014103c030455200c6ea402c1451410001142403003040c003103554055004068407014603020040038000d41141c003888800c0d100b41c054041c29130916801b002e000701342507100c40c0441c42c107141c000c9030150f0002d03070b5000030080311142038100720500b4001c3e500a8103080c248951650b052000081c41d001da01058514640c0c407086a9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 284619874 1250 284618624 284618671
    0xa15141503070504020c010e03030a0b01140301030f1401020910020304050a06320d0606020105070905091003080307050c16051f0f032a0c1502130b070f12020d08 71
    0x9031040f98010ba801603100e80080100d2401003240c112031610500001007003040c401c4442d803200c00000d4003601d4034185003040310a81c5006000c00d000041071540d100141401091807040b0b20001d131001034001515000301800400c89202c3d2002c00f600150b0700c040f0b800c0c80f0614010600078060540f40c03511f0380318038061310744850007a504203215203401c600808588001030901030468405002c2d0120034403126544110081c0203245c100c600070000350100c040800c0500e80080c0071401800c9002401168a055031940800c690004d012002480341c00c02070240d4800c2c044c4011034688200f0707a440c600300d61400c01440f40c2c500d4036511150815520021103d43c40ea0071a000090100d054580040e10310110300c40d681d9408410300858034100f010703104242c190307503100310a400c8003446403a0001a10390b00006e480260701480f072840d0b07a4240c4040307080c04240c6250000c0c0124500801d64100340c118a62520040c0044005186006030010324181e540940c0110401e81c00800c4842c00d5162285030441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 284621124 1250 284619874 284619883
    0x2030106080c0f041808040807031e05030a14160803040204232404110c0c0402090a09090c050603040807030806010216121b0602100b09060a06110a15141503 69
    0x403030391255039174255019500c1560724200c044c9503400089140d039151640c2c2c2d403542e00e104038030003106e900d600284000141290747d15001074803a8080025410944280c000383d80c404019010f07032120740c4c4140300041384410104180c0006c91300682c4103642d41e04150042c48107a070100d1080102c0824101c0004881c00c001ca81101d502c1115007643c0100710301c1c40030001c800e24940b40c18180c1d0150401520402140c201c000034411042d0b550b085681c4500345d802808280d0142900c80c82e4811840c1c91704000d24540d540000e0700c03a0748242e0042195580340c00001340650000d4078191035040c00451614209604580344036003182d0240002c01203c6440c05402c9602d50043c000d443c0080601c0c01c0d0b8a04114030b910039044040c108601007202d8603101d00e0001d588050f0380058108a5080140000050030720a9050340141c07405054030b490340c1d042580c15141c0c0c00392580348000d00e10a0020034000320301d41170b00d89000d140201c080412141c8981d0f0088038110000381840350745110f580007409e2613030760004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 284622374 1250 284621124 284621149
    0x4050603040213110706021819090b06210103021305101202010203090301141609140f0111030708030105010305010b090108070f0905120604020301051605090f0609030a0c0302030106080c 82
    0x1504850030701c3c4440403141c06044139030380030040c115000ca1501d0401280d80c0103094410001c9a500c00181d07107040400100034540071019010301c0c10243d0a010214403038200c09007100000d45600d1501c400c1100c00c000c00c821081c8800416098080140308500e4840708108803007104d02d20034405810401c0d050006001c0d81d00c2182e420410080001e0708590091081e1070781800001d00030018400c0c40c0702e4040040c40121405d0f981240c0303240c5540009800345c0601c43c1602c0126260500407040304007840141c03080c0d1442281072000074440740f4a81101080180125449034105035160b5151200140c142c80042e00803114580c018007080b207160340d1017900b00c0d5205205103084039421286a00c2581c003032401d134005a8005140700c000598031280081c606004078030940081140f613840d0001c0240034a42451300b100025401c01048032545013024109070f010780000c01903881c0c04c40741400280350400402c802ca4641c010030b0800c005520782032240e100284442c1d0068054482c00c04000342138031400b00b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 284623624 1250 284622374 284622379
    0x31b030f0d090c031506291b03040b07030302040906050607050a030f03020c460b0c0f161709010f1b080a020a06060f0e04031d0901090917040506030402 67
    0x10b80c1401c0a001641002c2c500550b04018144804455032061801420740c1d030207038035646046d01d940203c4010307454201d001542a100155801d02103034614841d111000354148207100e02c41400013090050300d1800a0507181e110740c0b8010f0381c50340351140d14400d0300c840d60f00c8144546ca06101c440080b49011515041041d81850801c2d050006120250f00a01034440061003502c45c410115040200008541e03125070b0f04c540b640800851110741d00005844d9180b0013032100721840c501c50000402d11095550050100528142007071101c02d010b0389142c21008054102100c507560300030501c80c003a02c40039060703c0003050a1b480c2c08028800a402d400783c11013984208414241102c0d801c1c0d184451903100030768030000c1d1550300d10b0641e0009503111040705080d91001e24041c070015400c1690003a10046402c0300000d0b24081d606c6071419070301000504481d21500c040780000d41c03482e0342d032000001c0c060006400005002100303403e01c80ca604d00508000c100452041000303020559a01040c1e07036006a04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 284624874 1250 284623624 284623631
    0x30213020307090308040801020405030c0d08090607060b032407080c0a0507020a080a0602030f0c030108210c122106090112020d050d120f18120207030b09031b030f0d 73
    0x261601202e0f203a070302ea400030340300030804503000c036040e04190000d0040b250b007101280e409106007410007842ea10756030f900a00c0034408203d601c9460903c14080c01000b03015100004418514101082c2040c00024212256001c40c0c6d0b43c00f40d1400c1403041c001d0304080c60785851025440c100201c3d012912482d103040041c0407000c140c1c4800c44d6a25403000000d0f00502090714090038451400c540650403d49410007806200c400082442d200142175038126403185008060440c101150b4900d68502c0b00442c4101550400c400302c0b13802d80c02c200d49207041d004800015541c042c00361040414418004c00901c01210500c07d10005903592082c190540c6d55003908044000198800160500390220004040e070003003801d10580c0f00c0d040501940c034001d031000b0a10411160301c0b11b042c1103903640406600c028648200344400320300308001419150b0f000d801124000ba8581c0c480c02c2211004a0b0341d000b044c3d000082e10001f00300d85110308002401058029402c11190442401d880d00030700203040341a655 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 284626124 1250 284624874 284624881
    0x120a0c08040c210c0b0a11031224061b010f0603020906090c070b0106030506100903050d0804050c03070e0402270406020f0d050c0901110d0903110a0e0c030717010302130203 76
    0x1003c009840480d5405201c9005032659041000401e401000800e40403ca007602d88014030600441200c007820b070000c04e240003943c0d03441d0030f4441104079540301d109940c941403612400f545030070b4003d00d00c00c540880d007541c526070020712950a46d05148003003500f0a04101c000c100680312003420581000c2c8c122410788090355181c10007003150082d01009030600d4802c1c00001034440e050f030301c518041c0e002034682c0c1000454142081d6129406131100030402e5000480d000b1034148030360090f90700a1b110348295400c000e031680000349071000d15000800c44034081d006100840c5400407040003003131085840f500e8007201081c21340300c1c44a4010f0018040c03580000e01810040045c100700c419990880c00200035604040389200516040075002c1800320328890a403843c040000102900844913540c0d54240742e9042da40e81284021080f003803250459800c0c00d000c1010810003988a00c180803500010317480340380400c001400088442070100b02036003070394018805601e510400644105010001581d01c0d02e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 284627374 1250 284626124 284626169
    0x30606090406060903030f1713050a080409060e06030c0312030c13030f050f1204050d0303060e040620030603060402040228050a020c030615010809070b120a0c08040c 73
    0x224400d1850340c854034144021600c40d402c016210180c3e40256225801403809810940c0c1442c0f01400e8031100407803520005030740c16040107014030360070700c51401ea038082d182c84c1d9529021500b154005806243d1901c0342441850b06004816501c08007c0300100010305c072030710109844801002d808000f1090001c0000c05603881c5004903415161803500f5a84403d030342e810075030b07094440400200c4680c05103185800091b01d001a0b007107905a14291030514291808041003090f98010000303d00341034441e0703400a09441c60300c2d01d1a115500602011a030100c4a803640c00c1303910400e0001c070381a00010301c02e1202540f00000c8060b0302a034141c0780184da4050312400243e0341c0d050080b14001410300003420300b00c401d9002024240318a80d54003140c11502e4801c0806889001c05c0310000300626444210038915840b5612035078001d44810152801d964490f4020702999010b0303404403519020920504c0750901c046c0c480c4441c103501524004000d41000c0d81c820300180c00383e02ca040000c6075800000c0d80d000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 284628624 1250 284627374 284627377
    0xf03090b012607060f1106060a050f0a031509020102160f09020d02090d05160f12060c051213030f050304020603061009081e0f06010e1b0403150203040209180a0602030606 75
    0x3184400c4403030040d51031100511103039a080e80b5800103025200701091b40600060014060722004045107040d43c01d04c014800d5414032682078030780c0301c0080071002010030403640383e05034108a502c0c4046109216070001900c1c0016148409111483c450420401c01305003140100948844010140e81c9003100e881307401c0a8040d106103a076218000360842410071200091031888455400130a1440c1540c80764491042d000d503200d01d800a0104074200380020f00d195001d1662080d460814034200b0481207e010150101202d81c0400b0782d4002541605040e040250300e0000d20383c500d0840d1440c03602d0750104401e40005419140204190754801e42120b0080202602504c261340450307100800b032401540e1081c1b080d01000105004854403020729000201e90380303041e5040300001d200b20b5102d44941d0341580b5a49a0000710803032080c44084001b99001400e0811204003038405600ea042c00d00400038081c0000e4500b1604040c0e4070201d428645010401c0c203505900b0503001a00c3e941c40a0115070070313 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 284629874 1250 284628624 284628689
    0x30c1e090c02070f0b12010b0a0221070f030503041406060a1e030803190b03011b3218040b010905010302090402070c03060509100209010207140d06050907060f03090b01 74
    0x1c00140810208101c448403010b00241b2100400342c1c159640d0343c004542c418424820300c1070045c0c10528090910070106103203110100d03c80d5411a103021410340b2801400607005604030000b800010502c07041c0054010303c05803015407540504200d04140300040c1001081c6d1156480030b102c0000d520807084900100d00d0000e64000940550f2480c2052080301c0ca0f41da400c100b1000d607440d14100b0368a6050510501096405a4429041e2403500803401e45a01d18184c1139080100d905901d14182d040d0016103090203540c06981d50b40d100e4607590034103004032810009140c003a914001290080d82c0c1c0c481041000c46000703080040e41c40a00d600840c4c040d115110010f04145881c24000080001d01d80c0010710900c540016111481582c803082d038143d214039a00c0c2030040e80001014049040304c003420005001c402002c1e84840c2c00d2965840c42540c4c82150035842c1500251810019540c0114021300c2c0303501c0398502045039100c1984c0e0030b20380380418020080000f00e40e50700c3c0d5400c0484200803021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 284631124 1250 284629874 284629889
    0x1a0322140f0606150913050c040f0909060b03011b08100e180d1403010b0d020c0a031d060c0304090b04061a0403061d0d0309030216030c030c1e090c0207 67
    0x603144944805590ba041c058500078002c2c550611005043c0c3e031000283c8030425001080342800c40c40c1150700c40068a000340441d264918100400a9013403c042d00e61001808000c0001c103001e000341c109001140d01880180e4000d034148501c890885603541d14203c51520b50b400c0c1905191280c00c580c22404070701c1c1c0c0290850409441c20700216010900c3c40e404120304074800c5440c2640500c4084450407a844640c1c5400d24043c001400349a90000182016103000000141002c10000750313a4604021400b00742e001c00c000e1041d101107850001c0561512500a035039003403a1a411100300350b520301c00d61181c01c86080d501c00c166099a9900d80007003000b0302c00840c6040381d850513170100ea01140c1c8580b000f143d5403460500c011200b4442c5112591107402c1e8407001e000d4501038101f0a03809040c1c00001242180154104540103041c003c22140c081c60190986d0320080b819460011500781305600904605041c2a03800c800e074410010001c4282c810141c0081101c80490700282c1c48c0481d81d4102c1003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 284632374 1250 284631124 284631133
    0x708100510051309060f06050717030103060905010b01052b0b06040e0a06060f0f03050406090209090714060c030a0f0905090a0b1c15020702010c060609061a032214 72
    0xc840700c0c1c0c06405041c1102180314251421503031240142c0458005210309444403955003410460399000c0d001a003441401100d4070304d90070644144e4512913500980080342e080350744062110070b01c2030034800e41031124001e080c5503141a11001050081d06944416003500711603c14045400724281d80064a03069400b525044c5c0301e0340c0382e84584d10483c0b4100c2e590100e951414800091031441035070720621041c800c0d16203c21203d05107104a01414004100740c1c0c240b5143e4000303100603140c088403a03118060240c081c103034590030700040103603501d800e0b5441d600c0781d00140320b52982c4e034802000315912190a07040c080204a8082802d40e8003503004c1d41711580c000b00410800800141d40e030048010b500c0c0c00c0f1600180c0c00103403002c0050482d07040002800c020320050010010741d015a000701055070050404549081141d40c1b003030b090324141c0e0404040c2c80e44908007000717800b86000070444012040c0340c283d4210b24014214804c004145805907103a84010401c1009000700780f40100341c40094071041e503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 284633624 1250 284632374 284632399
    0xc010e030406050c100b0a03030309080c0a1101091a161a0405011a03061e0c16060b0120060601140d0515030d0309170a021906050a051003020907081005 67
    0x1802607000100010068024440d60102c25a024490080d0411009247e03006032400c54800b100202081001100c2e21001007104401c031140030459206501c0c4204205103081c2c0c03034040018106661a4040015623041100142294920700c1c192810001d1803403902c001d183c0f00b406c1508554145d034a0b2125400c0000060005000b0103411442164a42d00070410b001741e080402c1c1503841c001102d5041e110640b481c2c02d610800b95503ea140c1d0000500207019092072a02c14403c0d9203060140f0040300c40d01c1c0c0d03882480c0c2540d40c10800d0204481c0039856140e64a504613000d01d515200010b01aa0411203529011900d0103d140191200309a00f64030400541c0b0704001111264400183c54174400d100d03c103c01c03207a0b00d00c40c0c01444259607120300182d51010f200d0304070703140d80e4211003041e200b503015603403030550300034190031000c010240125404509801c000040c0303030850708050f010900801d40e0880c2400540c1342c1c403010300d0f00b05003035241011044e540c8070000c191300313182c5811040d0301c00d85042c1c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 284634874 1250 284633624 284633627
    0xf010201092910050303030718180f0509030702180406110d0c0e041b0c020d1b140613050f010c080a0e090a020703020705060a02030c010f050a0c110c060c010e030406 73
    0x4003004802c00b403110804503128240e0030718a08410740b0443e070785540200b0000b001180710710150f403244007801c2888564a03494221160003000340c0407030b207415150340b94404607090302e030750003150780201d04603020b149481c05c0d40c0c002c9020000c03001404841c003c001c2d0b000c40c0821407690b00210940f83d92100598940c400004c90001902e070700d807c1c0a00050142100010070301d040d00c00c0034250046400a410302d01c0811506542002d11618280d03403001c8200851310101701072103d01400f0b141c2c0050500030103030070300401e40700d480f03c0c0228440c02694188030200240d400300c0359500031303501d04441082c41c1240346030048801d802c25060080501e0000b0602141342c0f5000f0f03500b08100c003411100c10aa664803848041d089002c1c001000d00181c0c020701017040300f800c0030070040c041403c0b00d1048d82e241c0001619801c1c20765044e2881a101942d41d0760030030002030558030a40f11228800e1030f140c5603035091a5581c940d00c082c0d41c038100d8490040002d24070380d000000d6010a200e100108240c1e904d5541e900350 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 284636124 1250 284634874 284634923
    0x10507120f110d0903050d0c08061503040534080f0c0409050a06050c0705031219051510091e03210206070509010c0605090616050901020a020f01020109 67
    0x5440224100201d15440056038003a40d000060340102660625000c2408103004e0540400c09406021040000340020004c500404081441075100d80c600c504000007400385a08040d082449204800c3c010300c0b0000700085060380034190380b00c40c3c01d003200701c54604800c09045019441c1180310303121100007950540100d4440035041003d02038074440300800d07050105656107032200030b04135001222074500044040d07005039001120003440d41d050a02555074946154030110400440340000d0040142e01d04805d040320402c00081002480030b42080c0c41c903404135000404a0034419130b812074003d10300714425000300004040c25058500001851401c40304028001d000030344a001d03041c45840500d0422648141c0d0000c100d5009081940d11000704546503002162414100b29038405c89101041c1c050240501462840e0050069810249083c1480b14240070f440c0d01840401d20125003183c2e00420340d00c1c0740540684000310301e03215410040b0b0041414130310040031a60500e42e03443c085001c507131 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284637374 1250 284636124 284636147
    0x30b12030c0a060510030323130f030b0604090201050a0c080f07060e01110712030b0f0d05010209030105090d1403040204060f0611210301140a08070b0c0613050c0d080c010507 77
    0x318100015103030128145d0760f5526030300010f00443c2501c910482d5191000c0111074600d4a8480090700305644074101e44040d1107507600c070580380001e0a8080c401c0c801c9441e10075401070804ca4040142068503070020b04907006015455042c0302007952103005012091003220340740554210300c190f0f0b880403441e140004000c0703040300f1a69980fa02401c401c040b10150220340300e0319000540000b41100790a0224084c1050900c0d460708459111059002034440c0d42400303108900c56000541c07142900c01c141401c4850003443d40503d5840751134144c43c0e003a088200301c4540d24050701da00341c1c0c0b40c1e101d0004c100036040540c040490064000d40001e02c20360b0040200d0309040a10041d030300580844807400c80101055041080110020401000308248110100264100280840460903070f00c5c60340f1810856203a1194541600002d0350564900090010039400101468400031402d51601c0e207595801c04c608040307008503d0081c1940034040d03544140c074132500e52600240f0040ca01807000828909002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 284638624 1250 284637374 284637383
    0x30203060a0c1106010821090604121209140f030c190612090503030a0c03140108071d1b0c0f16090e0c1f030605030604111503070f030b12030c0a 64
    0x10301d01c000b50f40c0803c00340c0c100c0e00200000d00e895039030b40020103580311140110441d04042000f2000d102e0729201d000e800145445240c414002d1542e00b41401c03900c0c20301004500300701ca1050103216026208500149410040c1d51401640070b915010a01d80300950070b059034806020280c03440c8840e50411001c040d1407066a030050b81e008416003100a5030041480184540c00520000306414030642c41150303a142249000f19202402e4030a002c1d03d40d00a0b00404400d0300f00d18421712410a08107041701c41111040f192000e0b92500441c022405584245902c00001c070000c0d803000382550412204012000b14410f82e04050b5240100000b0350609105145080d13040c200380403110880819042c188020250074500c00130012181000400e028440c2081030641e40d14012a95840c01c1184610840c4030740546060040c10307004100401c1102e4044080c90f0104200304040e4a0348070f42c10300d005110b00d0801003441401c0000244009500015204a80c03001050032884280300003507190840e8041e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 284639874 1250 284638624 284638637
    0x90b010c0c03121e090e1509090732040b040b0a0e06010f03140601080709150806240f0f07060203390901180b0c150a140c070309030203060a0c 63
    0x43e0105001010b1001301c008011880c082c108203e803500101c00319074000da0309001414103aa25200051000301d080d24481000d6019a0043c060190030140000300c0d408580c4810131924818514070302c01d018901c0b207441c01241c403030808100d00e40b600d4100d525440d070014444051580c86441403000c6983c1111000c2c0042d8101d0700600055000e44509076950303041210000850f95003800540306281d004c0d00c0181003002d04940025440b203400420540c1e80c200da940e006540c1085c41c100702c04007540d00d418411801c042c500900d9000314200c01c892044441c1d5030300d561501010161340381140070b228400b0300000d000104102c2c139078182d016040d000900e80c1c515850030850072814808845201c140d6000174981c204040c0041d0360080851000f801c2c0720100400c05141c8032050b2070103a030440c0040e01001c3c2e00000f04c0c81c40d5104000f007400d90213101c0e100c1c05c011030080420075070090303076000d0407071500c0c880d00050708800c0c1885200403502030b5402404644450900c0240c620042c5082101200042c42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 284641124 1250 284639874 284639897
    0xe03120a05070e0d02092707050931030c020d0803060418030905060d15030302031b0312040206160506180c0105030603060601030b0a120807060606020115090b010c0c0312 75
    0x15025543c0b1030940135000300011040e50f400d10400e04c8028021241808018040c10b00c10802900d04642d194200c0c0c014251061400d030601660410150003107540894040c4401c20301031540e0840100c00032050041c1231000c1e45418107844040507000041d4000144004c8401800a044001d50040c0000e603410084080382900b0401022040c0e80001d000505202c070070007843c9010340c06405000c0b242c41c800160400442580b04a610850b0300460141e00041440d41e0420850304140c941000844081d42c940388150105420f4140c000744001e1007540003094000810709003072550300b0070a901c0400c440c1c4038144406c3e000340255105101c0240c038441c4071101c034415481481070f04e0244038043c0080c90583c65010055024211080c00c10350480405000012042040b0340504a800d00456030142e0343e4103282015015074600e60007038025681445140304100c00400d200a00311003c2ca80c001804a0b60000101c580b0001110050040160010080140890310010346418a6141c441124170207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 284642374 1250 284641124 284641127
    0x105010e100c061a191508010f03080a050d0c090306060801060807140420031e010e07030e071203260f01141c060e2104060e03010e03120a0507 63
    0x103902020074001000740c480d007000900c403600a6907002441c0b6211080541040010900d00d200d064421800841401030401000300b6540c08008103a030f5900d854400d0b0760401d40a42090045880010107102d0f000a0640d151032050040e6282c181041c1814848003c5c8460003c0a0b400c1a00060b2102407030000300007600c0d81c0c1485540120340d0103c0242040d6450041e039017904105c2c0c20503168105072078121032100c00307189000b43c03000000103901d9a1341300c0c24034810301c84510402008022400b10701d200148900c8252549182d80b06009107000300d00c21a0760007105040c1040c9611078200b1701400604c100c201500120012800c9a43c1200c06104080b41802000e51070000d0701c02c5491301c3c030b1000c018801c0051010300c0020411014012000294480200c1c01d422444030006403540c580d920076040d900d11043c4900d0224685000201c0c8103d140b151384448a44524401d0300c007808155404c080c400e46003134010030b80b400314100c01e1300d44805408001c866441400c9541e118900d20b08000104900d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 284643624 1250 284642374 284642389
    0x11090711070902130612020c011b18050607020402090406050411091513150507050321090c060912010e070305060906090a030914040906152111010f050c0d05030105010e 74
    0xa0b020f501300000040c0740c60415140050710005002e1150f40800c54080402003d02a649203c418000704c54200150382c0c1004040c400071101a440c04c0301c0440003009241d899800303a40e116901140d0059480980100150081c0000d6200359009800c1130285002022040c0c05820100c905440b411030340c030b5907907402402c81c1c81012000200302130341b07220900c02031041d8222002400f01604203a0300e4080c168403000d207590809034103c21468005038520014100d4140030a8101c00094010199031940c0000034840e801140051401003650003501510483d007500301d120040c2908040d1201e068482c1041900c0f43c1003200c00403010301c110030105074080700024021030741c1d03a00350781c4180d1140e080141030b86010000700081580a600c0d01d084601141e058070a0618154614400c2100c003450035003510849600d00410b650190b46148000e030120705811004c2149440900e8020107035100d03c0070903030f424003400c0c2682c2014031604a0f41008103070880001c40c16194240ca031944010b40e500300b00030b0744 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 284644874 1250 284643624 284643637
    0x70e120618011b0e060408120306120d0e1201020d05040503070b0106080106141b0d02011e0b010503011a07080c0a0605100b070303050c190201050402090601080405061311090711070902 81
    0x2030f140c05101c49407a10032030364107015010040c00c09103003681d0303000020f1519161054156081d2000008d0150a1420002480340052200040d1940c0601c040000d005444042100f9000310a540c9020200701c0003136044074800740b81108208070350700b800d081081d503d41003100c0231503002c86804000324000d40035501481c1200c80b550382d0588440664000c0d0079458004035006003000080140500c0060700900002c0c4141e04036500004134041100d20b0546080c00d00008410240d01c0c01ca801d41c81c40e41e2040481e415280d40d411481407d0081e255040c0c03691261000241800002241200380d12102144840205010300c4082c07000d03450740743c641d00030840745125903400c2d940208441d400080c081e4220313a501c01c00d10080700703081892150280c1150200c407070607940180d550314200011031400200d084e070407203000e01c0d00680e546044d5844e160341e42c0c0c028220b20f81c0c0d207069204220070410425202024000d001d46100c416043c8603602801030300382d882100a15024880010548080070b2003903444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 284646124 1250 284644874 284644901
    0x1111917030c030c0a02010f0e101a06090d050a06021215030c1e0a0807060504091401032303160c061b11010c0c0506071202101b08070e12061801 64
    0x5944c80754100c81d640307540100342d008195506d42e00d1040c041035282c8a0400310103000f00c043c0030032040601820003200d41d02c003054888006132442103071322030300d0340011f0710101d500a40f20228400240d0801c41c0c42e041c00008010311107400021030310f05285a01d08040d00440c0341e10540b4402c1800c2c42d0415444a003030315a015004100c1e15682107a54908090140351100d0103000090780c1601c0740f1f000d0307013007180540048001c80c000090400c485031640c890b105400c0001d40f060080c039411590b44142c0c4040070802120850303a05101851240000d004070384118001d2241042e001c2a03c5c6400038a8914610a007400b003a40301030b00c5000502034200a2140075400300030f40040008010054480f0703005940103a64201610750003080c240c40304001401d20601034141210745a07c401c400074074020f007200c0c00b40b07a01c60500c01514070041d9034240705980c0007102e080644041d928020100d0301c005000d01000c6d84040700e60050f1410000105104e80600c55002800c1c1c0781c649141c2910b0300341c03601a4040030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 284647374 1250 284646124 284646127
    0x3060e01062105060a0225030206090c0111060c0a170a0b0a06030b0f09070201020702091302030616021005060103020d0c080f010f08070311030a02060a031a010801060e0d0201111917030c 82
    0xe50705d10803940100a040b0051007a10202d54110091076907403a0440c00890259000b0001c0c06010b40c02000b204c4a200300900c0c04007141e400704003685441e0000a000c0c4200c1c55800b240c410703030403800307100610034516424501e0340076498141c0009001d0256402c450b4061050b901011842d14402d02030243c610700050403422500d0100030034018030a400408076000c40d542401440010b80e40e422a890203001280306480741990140100350402001070300e0310b40004c508070742507039941e50003280c1c89104c0120020006096503419006030041d110300051400500d03d000300c42c03c00c458005400030300032030340000070385040da8070380403031038407070881802007110545c4010000c00000381d041042c100703005c0340038043d1181c40441da8046420354210310003c001181d11000c800480c0300c0110000e41c008202460110880d501d80440505206600c5218074083c5200c15140b0042d640220121424001601d04407502d1038a0b407920454601401d040880f0340c50f5030800c80c0707600f9102c80c4040e47d000302c98031081103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 284648624 1250 284647374 284647381
    0x50907050a021c02160e0412030c0c150b09011e050118090902061210080f0313090b010c0219050f0402281b1211010501080c150403060e0106210506 65
    0xe8030b0022104503d50111700c42e90145001c80c07900340c4e076134030000c20f43d80341112520700341803800c00150104190114209850500c08d110f40030350050050040c2ea822070001d086048040b10f0001c042c0541a80458000b541e9a00024200b0707000c6056100348101c2100f591403481c2c44e0f4004550700c001d42801d00103002c64201c1c050142240035841400000d200505c418500b490f80c28074540b021204950300380d04040f02080c10400b00c2701c14003041655175030800c0958075100103500f015181c0000da005020b41c8540c0c2e44101503880c0d0150040164180e0010302040c2e007080c0c44144e4330705051407800344900036021801c1d40c940f6400d2a00035550000914441c00a8000e944002c02071108000d0000350b00304050403500c8840c1000c0b64158010b241e0040f14008c0c184015228007918400e0308101c0040386a1510004210034000400c9000001d402201c05070107180300ca04588045014a80000d02803900e004caa10346070300015800f103400c861080009000481c1132001d40840c500746903001500766000314000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 284649874 1250 284648624 284648653
    0xc1208040b0a111903020c0f0a0201170405012004080d0207030503031506160803010306140f06012304080604030219050712031709010501030c081209090925050907050a02 75
    0x1904400420f4621182089100c5004a05003540e88103618042603000640442c265014000000381c00c0340c600041c03070106e8941d170000f02540b4604040384c0401c009940442d007089000c0d00001c554100070300590070b4480380e075040e85d0310b298132510078120b2622441c04806515030010841c1c2c02129013080113941542d6412503075005200008014641c4010104859841100c000907141c065a00039444241c4035030441ca40b15085401400c00d4081c069140802c0010301211031080981c400c1081c44d00d08484480c42c449840e81901f0201d00c0a140c5001040100c1c800340e00082e030381d100320f0080e422034034410001544068215000b41c0054901d03007280205000580500440314040c42c03203490084280c82424504c0c6e07421704002d503510340959441d04010000c0c04000c003244005082118098000319550b40071118040c0314a4001b680111407000004000d42c9082c0302e924400381592001000070404c802042c40141402e0203054410703036421000c60a818454003d6401482441d0020a44400d08941 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 284651124 1250 284649874 284649881
    0x20303130201020a0219081908071b0f03110301050a09021e060d0c051201140f04090c050301020307050c160f0e0a09061e0612020306060105070c080604030c1208040b0a 74
    0x8050b8154400e40096400685550409404580a14051200f02820210388505040d07100840503580d011042500380410310f0701c02228040c2e644034003540361041720a4140001400307603034030240942d9110000082400020340d0042e0340d20034110300801a43c0d4488011030f044417205800a50031505c0b1200b4090000d42126856000101c020849824011010a041c1c01d03100c0c006032010010701302054038580040c80358001e501503c00184204000c081e00404282103080d1442000d10464a80c001107040c0711a0341c2044020788000f0b4000c4d0b5980c0b9003890054400d51140510151134424601d0540e90318411420000942e00c00f49600f4220525002c41070903c10400717040f824400d40e41d480103d00007005446084030301c42c0fa00d400b00000123009404541125081d6210400403102d042c103040042e5404601d882d40107009003803594554a584c02c1200003000c2ca41c00840e141d20441040c0f00506410100c60502544541030507980c8108042080764420401d03900200b03001100400305007000700c540c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 284652374 1250 284651124 284651161
    0x605090411060708070501382b290109050c041203051306030605190b0d090516080303010906081506060c0102070209010b030406150b03040206090d1a100510020303 72
    0x20006041401c25200e403421901c90306888c2822003c0c0c14401c808121f030190801d01c401e8151101c00c482403d03428042003040c4003010444891120101e08812040c1e199801c0341c19054021000d5446020070a80100c89400c404079600e00420000c0f000007105041070040c0762041610380b4146003094600155040300e20b0448904805008c42444a2040c3c4000516001c000f0403540da4003290844c03030041444900c03e64005620f01d0121108404d03c20081760804894094a00d031340300080081540c108142499090000c0110701c1c1441000040c4218002010b14160384c8001810020143d50301c20f21a0780d0501e0303e0144032219200070014941d403800c0c40240c00b50150500000d440c0190030360024894480981045510400200034801401058803030312240001d543e001650b45410003000b0409808000d000901c10a07002030045d003282c40f6070075104101c41e400325099403048100e450401116208950042c1070341100c41c8006500e2a01004468540c01942c0242d032844d19a0800090006000f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 284653624 1250 284652374 284652383
    0x80112170d0f050a050402010f0e031b0109081501050411040e1306110c0f010e03031e07031e02070219050f06090625030305010603140105010809071a09010306050904110607 76
    0x10844001c0342020b50207840d04c54050740e9800900c82c50144005400707040b00d050400c2c00c201404d0b03500308880d10006002940c4036410140303400f03e10034080048600c02659081a041ca002d51002103e100303014a01e500c0c1a12002c4500340840b1130991000302c154041c920520520703008140104850b071250b8030002c0d00d030318000c40b80411080344a030440d81090384104c45240ca941d000680441da441c00038403400c1103450a08014528608041105020060038600d4205894020704003040c0801c0c0260300c003440b0310740085240350b80800340d41c81080c020b40100006a0042c0d405008907181d4480c15801c1d1015038000030040124141c111062280c0e6802c00100e4541240781001994040900b940402e02c17000410019a100da000603d0000c0075100d042e03001c80d0030306050040010001000d002018150380c1d0138070304091180d070361802c064a041c40f16400409806c000000c1054400d21200003030080751001c0c3c030207018042d510024060340e03e03001c4801600f40c18010300e800030640751031001490721078042c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 284654874 1250 284653624 284653631
    0x30a050c0a051b0a020a06091805090307330c080601020a0519110d05010606120e03030402060918070504050a170303040206070f0b010f03210210020307140415080112170d 75
    0x5c0d400b0960340c041035013080b0041420396000300420b45900d0f04c1c01f29a11003120043c0240c0c1807094006540e4000c208004000111948000481c101c07004007800440080ca0403a9015619240c0303c1c00060015000100015282200241c110b50000540345005d5602000500f4199495080640d1a4501010464404101042d0945c1030780d41c60100c0d0b280b56001e41c00014030781789407030f00180c60840749800c170141560900000c160000d0b004003d803036000c0d8050318031903582c0e03007040e001030507034240328501040352065030060080090740134000d8025641c0a942c40e015542d140d1200888000c03410b000468a43d204000040c01420990007500d44107100c2c116899040d15140e58036100094241c00004980035484410010300041d140d03503484890300c450000190602c000c6000b502c4600450302840540d0700000894401446001c4c601c000e170750180b20090700c49444210030407514894081d814006410b6500228581c0d4a007075120065503404205c1c0003101c800300c02d0f00c501641000d6101c0851558 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 284656124 1250 284654874 284654893
    0x203090a03080c0405060c0706020609070e0a09080c06270309091b0403200307060507050307141f0902040e0c031f02190c0605090304060c02130b040c0203030a050c0a051b 75
    0x30781b40c02030800c660003200542409820044000c1c50220001e106031015030120381c0402070f4509072007059400480c44803021480c00c07260705100c10a0720401c1c0748101c00d485103101304280342c0d00307815010350319407a52003450005540388100c4070350b1380c0104100b4550281040780401c0f21244014103a540700c03071000e6552820300f079072a21203040f0000c209407158002c040183c242446403a0078040d0740c01070311044c14128145140c42d225541c0d00c1c05500c0001746071003070001c400c042444e400c20141610010100d9029250703500d4059113005099200022409207082805050880c074001c0384606032900701400070900706a40801c511600c2c020040c0c2c0c20302d400e50800c6011143c3d41102404400100580c440300c0658041e80303080c004652005100b01c82c1c80d0000d220500010340c2c450310108450380c0445403614004421080c65000b840b8a07511035a00501e44100c850740141c000c00518442c1d003284204029070341c1e5101a02d80c2520445242c1c45c0012010088547c400c4981202c107003041c1010340450b4940c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 284657374 1250 284656124 284656129
    0x4170a0b011502070e01030b01060c0204141f14030c060a030b040501030b0403021615031113030f0b10060516050a0f060213050102010207080a03020a02030d020310030b0702010203090a03080c0405 86
    0x40e02a00710201d910460580c01c0c0e0066010000440205220400c42c002907242d03848000c0c2140041c05400b08002146119600755500c58000300c41259800345001c442d420b042c403442440c0c08512030b0305c0f101d010300d4440000b0000d10b0504607440c4040064080d0243d601840200074042d441000d40e00103056031171107451084d0b01d0314451640a90b100d03000070103281c2031508000e454080f41c1c00b80da81004018900c10302c50850030703078110042d170038160402040c0794440308040a0f26006210011020f010500000010b1081c40c50141d501c5ea409000c0aa9a071b4440400450000b14140100c1c1d02160040020383c8100f0309014000104a010302c00f42d074110450303076a4038403a408084400341c500540216009044d40c0340c1a00140040009000851800103255070310720307440c000c07012001c2c241607010030328403a00d0703000703204494008140c40390440d5280340603000c6a00641150006944903021400059040f034014070032a13010385010001001d640001d503400b1108680d00618401034101c0c00c0c4000103e54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 284658624 1250 284657374 284657393
    0x1020c0904081b030f040311060306010f050a051e130e010e150d140a0201030b0a0608060904080f030106050c1b0f090601050f0f09191203030f02040302101e0306050604170a 76
    0x4944c4681c0c5c44d82e40e80d24506080e074010340c900d5410341c880d042c10020301400d6a085441e042614005060054032808100000c2c0c840d4010214038511001c0d10012080050185400030701c09003004070011200c241c0c131403104c020780c1d10090050711585000000070034600c0444440501c000c200090114a400e01340d41c0d0340d19003490301c01818a000348c0c86000725900715070f05809148800b91301903442c01d1050f8580348008050b0380025210340c0c0114004400b103002c0c85040c1c022209850482070519a507540e4a64005110382e00802c0c404031640038920260148001c407410301031600381c00528406200b101b03001001000039025045a041c4078040042902c00001400502200300d4046040c0c0c1c0c42e100500c090110100342c14220844c00b0300b260006000b04421341501358510b680620340020b280c80e1900b10b190080c030603900065440340b5020300a20344540e00c40c1c0c80780002080d0040000d0807040600085d400c5d1003850040715440007013444207000e004213104161000194502c2215211841611500b081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 284659874 1250 284658624 284658637
    0x23010e1b060f0f0307030e01020c0d080a020403050d05030103031106060f0118090c0e0901080f0d0c0609020d0b0a0f0509070b1806030103081207020303060d170c010e010509010b01020c0904081b03 86
    0x80c45000c0b003006071721078040c410b424585085030001e500e4445c104403010780700d05a50b010704041c03003604008500000950b505840c0a19441421220024280c00d4040e2694009100480001d0b071640000075121001088240c0035090140180d03075101290401942c2d210740c0345142600c030700700d40384c40025590348074007030502c440305252129078000300924103006000c401600051250750200302d9078015203400060340403d614440c5840a500951454031401810180740b001e50300040780550841888401e92130b10303010b10074610080020610001000080d61004c40703001403190441d0fa03041028811080081100020050301480c01c11344000c000703142c54000380c004ad90f014a010901c59910b9110801c41c2d5001101800150b003140780c04000588400c0081900804189070321148504009492041d94810000315000f80240005142d00754001e160484441190b0340c00c1c9018114554004640c04020f903601410300600d643c0e41d502e910030540d0207030043c480c070036101e160b5a810624043c40079101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 284661124 1250 284659874 284659897
    0x140f1005060a0501170406021614010f05160e010f030b03030c100501120c090f0207050f10110906030115051b070509060105090d170d0923010e1b060f 66
    0x2aa4100380301400480640b0782c2180b030520401c8200142d01d000342c0d50400e9441940b02e1000f50f960a00780b540001586288c8000410ac200680003d000040047d0010031400e04441c004000701d54903a044140c60710000044c200c045144801c00c0c08203035200707400390340000025040214400c1d104101292541d4007056117030b14036402c071546900c1d203e98a4090180100703510300304400188041e88a42a500310300b803240c01001c40c0d9400301c40d01a503010390180c5040d10b400000b5134510329110304000d03440f080c082440824592505010a14845905d000d485115001500c001c0c2140e0801070030744441741d41c9810000a015051004e0b01c662404146210144a0300d140a0b009d66807401c028818212405060103062001c18001d410043d29010407002d410b40e00f20404a800c11400d6210300490301c10b007908171041600f400b502c2d0302030005000e2400240c0301d1140c420190400390002c1c842c01ca4951110036642d0b501700c2c0c5030107a00400d04144107100c250005040900e400017682440480350300c5280c072080d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 284662374 1250 284661124 284661131
    0x607020f01021903020304051203030115030207030c02060a0e03060a0612030e0a0b041d07020303010b0d0b010e0a0f170105090601030b091015091b081b040b0c03070b10050904140f10 80
    0x2310a003440181448025102001142103505001d0403c10170031554442108041d404180041414440e10b8451641c5070041d00e040c1c0c2d22042c884006040c0d5288007482801b030300c0b070480400d0001a09104403012030382034035071200865015079421554180e640c030b20507900031407060021501510102c0148002c11441070302d4511040440070780c05000300000c01410a64100b0f00040001d0f0103440101e880f900d0100c8400541c1303106400c010f071801c06c040510a5041804890082281c540260b89541991071004026000c069811451800e84400321049800c1c0d80102c2c004100003803982a20541008014043c0c8002d030010003888002c450f00f40424440d41caa0103401080300c0c070390754841d858540154100c030440c0c2400b140c10203458088080c18442d000f182c20015110b0880050382030740e014100c0f030480c05545007001c600c51a500d0300499000d40340400c01001152081105502d84412507501400003205603880f0740343c2c04040c0e045034100041c1030040203178a9603071010500c2203000c0d1201208000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 284663624 1250 284662374 284662379
    0x11030c060c0a0908120d2a050408070504290a0b0c010b0a0512070b0d0213090b03062206050a09080a021b01050a1e0203040b030109050103030810050607020f01021903020304 76
    0x41185801394440c0342903030002d0100801207612041100d0760380240203004210103101c1e18004488520f4250032001d41d4a580201ca540280e00c40000c0c4211500c1e08126050103440354100700481e1031489150b4850421001101580e4a161503d501c5203c0010320b640c0125a03600440d1081e940180a40e807601d03555170401c50200d140c1002c80b280600416180302000303800024201d0307074401e2180a015503050000c0b45d1407010803800d8044900000c01540103090307059a403d254009041d410700068407070300441f00050207003415040011030031700248040620030344aa0300c89000a0502400300e520b91034a0301005000711310264014071039103505078014500135078110410801400d0803404103041040411101c15023035403100c0a50110284a000c0494450340280283c0c0b0714815540401c4041e1b00101c0002034034440b0b41d110504890003501c03035981503611039074003a500e44050301802d980b001050002c0d00c058140b0b58042100100180100e900810074002118012403410f4011001a800000c05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 284664874 1250 284663624 284663627
    0x3040605070516060e010806040b1305010f09020a050a0302130e040b06010201050c0f040e060a0e0711060105030d120f061a0c0c0904030f0804031e08060f0102060c03060111030c060c0a 81
    0x100880303c0c028030381d151140f90070310710001d041d00c50f0042007038108000752004c16070b1035441d0781c02501442e0004001c1138003281c03100c410001604003407213031500d115920720000500d034500380210b07174010120740d4030149042511801a00250072000c042c0710100ca0f40c40d004268028100c444e0f501903406650801d4880c0b402100081c20748100400d0041525404c1c84000c08840c01141601c081e204103001d0015542d03142c84c046080389905d07601c461080d807818410711803010b80043e100d15500701c0e00015a003543e030301d51040c55a100168020b520000e07061510190000d101540103401200c585c101c04aa555a1071040392541c0750110580380502030001250040690100881c40e80d040e4151190881440c3c5920041c0543d08038550b08010300c000e0b140001d041500c94400c03440224508110300f0001c0000090041c8419030441d4007038050903015414803180d6000055036881020500c410602e1365403140011100810500020100c0e803109210390740c800c050034040540301d0000b8440c01a02c07412036450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 284666124 1250 284664874 284664883
    0x4030b130c0b07151103010501021b030a080f220603180f0605090f0316030f05120711031b01020a0305130503030a021305100f080a151e08030406050705 67
    0xe120015121100000002905840c0300422110841c0381e10b521240343e07051091445503102d048520b85032501001d00003e424030340186040e20020703801c40e0740240204001204500d070714250030394158041c01050340040c003444014030000340380e8840181045802c0141041c00500303e50aa49150b8810b0b1003401241d034503204011305040401e1217a1140c1a81d83c40313851501403c007202810558542d000127418003820800301c51072203400011290350310711004440307969a0610130124000ba0302408401901842001500c420401e80d2040e0030180c1c460076020b032045111700d6809100390005014843c602201e5034040c5070200203d40000d40e4075a44940010200d03840108a00c3c0c2a10303000303d290b40070580c00010703203034000b0020100598801c030880000c01084016070006a01024003c04020072540c012401d032803500042d1a04030180d01d45402c042c00391594000c1c60000c0004243c01009040429981c01d84003000030b05092464940390403059096030712540042021940000f01c46041200411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 284667374 1250 284666124 284666131
    0x8070e01030623010306030803010906090b060a02030a110c030115090605031c030c09151d04180f062714150118060e09010f1d0705010c240204030b 65
    0x641088042d08069110b200403000d10301c2c5001e403c400b1041522030341d009502200c050368100c103d40703807690307074441d1001c1c0505043d02411901e6414036800e40710728200701080d41c070f000d1503035000385003001039650702155010140448100b0612540009060f961002c0c440c003148000c52503400080d01d030518401d201035a29651016010754062441403810380c21011406590341500d01d40070500c445004405c07180540710b9004040402c401c11444441140c024444050501405c54141c00710943c4400300400c507403441d500721404e030862510030000035502d4849030401c5440342c1c038000348210341c82c81c10b02249029031180c01404044140400240120000200341134209070b0000d00c403044445102065400062283c0c1d4007540580b10062a058090307001a0045c3c1280816000d017864612038142c003921a118144142904d000924040c001940c1d6105c010000000d0090003001c0c500401151a101d0141301981c607010311070301607401c0300400159200c0d4118a0b5a01613169410350800050211b00038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 284668624 1250 284667374 284667377
    0x70b10030b1602070b090303030f0a0f0c0f08060405042d0501090303050f010e010803041403030c0d02160f0b16021c0b100b0c070b130b07060518121c110a08070e01 72
    0x28000b02e000d668001040303032b600084000c4072810310b481e00d0303000380003400701000340c404403d0502ca401001381c0d0b030210b81851400c000c3d642d03200c3c00d0344520f800c2c0011101d050b40d0280a50240030317202501100d132400c0080001035000002c084041858560600311070703c1ca00c1c2100080d403035805100c1c1d212001c280050240c1072007882c1d07120552405010383e80c0c81c42584241400041760b2070200000b5903040c000e641d044889807050700d1000000010084d2640d421240d42041102c54860215215418010820030340f002c40422a2030700d0848601d4241cae601c07a46030101c1e40600c0346102d40c1c1441205d205501c0341d6070300c80d410340c120509140c00030180d074030020382007c0780c40030080c40b09800761000010043e0031110562031590751070b511825441d10001c16504112901140040c0400030000323140e0003e44140e505c0d403159080c0307410007918203407a0011100308410008080c840c0ca20180300f0344030501c82c3e405c84820000b4145000c44100c00c1036422111106000c5644002007001280d0824944516920309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 284669874 1250 284668624 284668627
    0x5060708011707030b060d02030307031710050a03080d0b030706080609060108061804080c0106080a060b030a020604180f0c20010e210409050103080d0c08040206070b10030b1602070b 80
    0xb458196074141920000e01100d500034003148a545035682d82820564010b41660b50755841410054609003a41000d46030246124000a01c04044c140800b415100000c2c00c1200c19403446d12004016008251441e9403140c0d03807041c3d40503660b000c0000200808a80d111400c03d45009000c025656000408041c1030214240c108541550b4113485000e80d1030301801e0030500380d10b542c02c023002a80140160244990301e805d80c0030400031070000c3c80780c04030340c8070328400d01c500030b0320009054440ba009034009410030302c2440700b8802d25408490848446400001c0040c00d503201505000660b11000e4484010801004140c0031011151141c901005481c4000b48030034128400721036500c003a9051a14850010103503484000d41c4004200c800600c25000180000d50716820300807090ba0240e00c2e58041103103020710240210b400303083c6907449160010003035070030000c00c0d8480c881c450000900d02c001604c01d0490200c0020b42e031101c418001c070030118034664104c10061001c1c0c98500c05803c091000c120 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 284671124 1250 284669874 284669909
    0x1b0b1b01201c0f1d0c240a020a020402040e0402090a0506130c090302090c03010806010608061c0501180b061009080a0807030212070303020a1e0207061404120506070801 74
    0x21440c088810100c0500100400a1640d031070110042a8008405220f14240780d00c0c11861081200107068074914070096a030b00c0d603900c104101840000300645d041052052400400c0c1c0103209018082d40d078501d0041d10140c551a0340050100c0c3e00c10f822501d0801800c1e000d00056041444210741d005003041d40030841824013000244d20420b80e44405180702c0e4403003044440c0c281c07003107901400960340540070310414144880300300501d810034011801d441c40345138000292103201e0122355003e6807000d80940c0384010f0701113188100d412900420740b02e40d900d0f40e003110000d95512842c485030500409034000385040941c104070100c00000f1012040041c4100140600780d0007103403441d0081c1d800307000c05a4800040c41d040c0d09000401c5185540020003180080c14180c054006108000c100d43c2c841d60303a080c0301845060100342c41d510103001641b00050030301c5203a000b4041c80c520502640d10207814642d0b102074600d1150b414a0f001c4907250420014840d2890f000b4001030701402c000140ba204202 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 284672374 1250 284671124 284671181
    0xf0813030e0f06070f050303010512150106050904091202011505120601090b2d0a0504090302100c030b1210051302091f051503041a01121b0b1b01 64
    0x200345041040c4a8040b181d0040d51980c0c40008a03040598040800003040516050041c0c45ea0000d00c1007900070340844909902d010004100141034824070141b4101507401c042003160f6540000ca0302e04d070400c0e0381d209082c01085110324070603101000340d40040380042c440d160031108084107510283c000d00308042090000c04022074801d040d2600c482d00020b0120b05080000c540d007030040e980307440c408d00d4190781102c503c5401c148940301060944e00d9000e1540da94040c002201d0f8a9400580140c00007042016040e00b10742088031a05410315022031140000c0002804002d122a030718012580043c0b2581e8050505008445d40045641c3c20858415910780202e200858010040300d101035003030518007810320180c0c40704000b5010180c514140049845100354095200342c4050ba140a2011192002c0d407110001c40c0d07040c0d90f003115250400b1417059aa0407a03011015840420254000b40d01050285c00302014240c1d042880d80c291510130101e0071501d0840342110240201110004050b01e03150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 284673624 1250 284672374 284672387
    0x628020d050322062307080108030702060d150e0c040e01080601080c01140c010501030606090b0d20010e13090b0f0709050904050102070f210c0c06081906060f081303 73
    0x1c1c0400c00c001105110070702d00031001384000b03a0121008041080340c0420240c0c4581414801c03003887d01c5540c0140d80303070500103075a8001d1b100025400981005a11001406508110550f01c118194202c00756180c503d41c200c55070b41140d4002e1030460205007006a100c61480290042500790060809541000602c0307445031404000c041c144214008003d00c816503610032108124241c9001b00080d58403460004003a1106101700240c0c02d0403e1003480c0d44d0325149020450782544200c100746034180c0c8c100c0800a001440e030f155414080718804a00c040d031503907140441e00da240180700240d0700720710f8035240000e4040540040f0300e444411080001c0c454010042400b925011100c00b003082d81e4038a080e80c0644079900d0300501150903044000100011610784150300d1000c0e00f075a80d54000e04910444420000d46009014010800c404202d158015140c00b90030802407801c501c1542e4122900c0d03010f88085610100004504042c001e000b16402800a41c2120b6000d041d149907042946000b03040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 284674874 1250 284673624 284673661
    0x240a0302150c150118020903060f1504020708030901060602150a090c091e0c020d050d0b010215070903050c0109030201050703080a06120503030402090a0510140628020d0503 76
    0xc1d661140302207041050442a1001404800110b45082c144a400c4410352a070a105400c0700080306001307081001c081c1d00965185071070240050480703580321519060b151038003a0034201c1c2c00b0541c034a52005034841d800208407003801004180d40e03e08042018608485407980b2280c115000031030b52040103140c214855803c0b24032420042800c019a0500d0121102070390300c5095120301c1c10504480c560420042c0c06a070540200003007240c80d0660340d09a8540b25074079403040011700100420b08615141c1e500030360200b90f06104849401e501491118901d88050314020085000305804100304242003001554407442072805201a40c613541c0060700501443e04010300303000400b400940c2401c03540d84034400400c945552500702c6005410100d460380d1054409a000b01c641d040000c200c01c160313018450242c071094500d55060351426508054201c1c00040b200e5224408201c15803a88110500441c410210b0a000c52a4004042c50281c90200441e08400c140203007801000380003042c46400e04030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 284676124 1250 284674874 284674879
    0xa080318040c05070305090a0909120f031505120c0d150c0e060306010305090111210f010f06050307170c03060906010f1209110d0302070f060c0b060d0f05060f240a0302 74
    0x210b070701600000448d4541d03140c01078980c042c41c180200c1c1c1801002040f6446440b0303680c82d50002e40e0306021046090b00d07844554038254070600300c01000075080121502c0c181d0381010081e520745007044400030340c100000d40003d60707840314442c0c00c03980f10303104501c1151005401d030b05041d4560f4503400c0204025000c02410141816540c000080910388290404541d00b1030301d60040c1c3d501c10164158140c015109201081d0b030241e02c000181c59581030000e42416601d00c608845070052030140300f210540e000610000420015a9204640c1001d00c1c01041c01081e10740c8805440303162060a20000c0c40303000700390f181000404003601000f00d4016000e0b81035881c1904c00400c405540d814440c100f64001e201c1d00340c00c213240d05250703000d0640c003003000303c250780f0060510442d1650768031040750586c50840f00a0720042d204804110a8541f100640c1d9049208103c0b8008001c01074035003074103052044074007a003520300c8103013080010b2410074001c1c904540a0002610708116180102d0510041404001d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 284677374 1250 284676124 284676127
    0x303110c1507080c0105041202070f0803041a040e04030f0e03030a1403060406030209040b010f080624121501060906052503031d0a0201140a0e040b040b0a080318040c05070305 77
    0x1400e0060040c201d4092131242802840f41c0d092a1410a8945803642c0c91140140241c500116242e41420b0110301100c05210041d410a410400d4400036000d5a8160303c070503040c01c000014aa940c500c080394400c1c0d0003a150200f02c42a00700000c0d04a4120515961181d00f042040b101c890390400c1a8080072482e80c68040c1d125960000407130010007007a00040e60000d4088100810404114800ca050790414982004410781d11004135171354480c1554100c40c50100a41d0110700300020740300c101180100141040688144611079a00708511800d065044012040050102c1368015801e1030042c00d15107440d41c0761030591004003542900a00042100800f984400420304d8881c0e0001c24240c003210544181d0340801e59200c0703a40700300041c03080f4082a10550421219051082507400660564940078a890910703c104001072000e0701c0075a504ca81e8820303010801f51180b80c801405051070300f0040d5598045090313652100090749032003520440c20039481d40303461603002e425a00d95980c1400c1aa = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 284678624 1250 284677374 284677387
    0xa0507120228060b03060106050d02031314010e0705060406050d021804020c0f0709140a050717240301060303091206020d020a030606111513030512070302040303110c15 74
    0x4030308001181c1608100904038401c0c00d407600392250104a61280300f92801c0107040500403d244d1242c45c244200300c0466414051039007100055001194040000d04036011400e6060f50b940d0003400b084c0044c410310740e6444615020b030290400c0711801602003114403600b00b40c03402c04000d003a8400c02016a2072242c0125601d03103200384841d00003916000c000c0081d51a0002d14000e29901c0b840b0343c1d1041458494102c00140d132024503c1a0307200d2245c4003581250782c0d901c0032101c201501014111100300040703491410200c00c5007103059030054000304000362080040c0c0850744440091050740d68803a92505000b007000035000f001c0b003801c80b600710711040903040050a05400900905841c001c01500014041d02c003140d0640c011808d50b212030f2103444208078401003242c3d407142032080d508103000000000c100c0058001d0b0010041510a240031480d01c00d4440254802280590780c4502094021800b80209a00300500348425401880180701c6000c1c0140021486080100c800c14003031000920b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 284679874 1250 284678624 284678627
    0x1050a0603082703070308070b0708100302101e051905040e0a2408010f0518101107081b0c090c03060105030a06030812011a0c0a060b030a050703050706080a020a050712 74
    0x801c0f1441d41e008059036100d543d6401c1491590b40310070301c1212041c0704e02000984d46030090500e140500080810b460781c0505645c24082c0460340400c5080c05d2014840712410b2016400d80c404140c4011682c40c4d6458a10722101c1614144030a500441804000c6c03000f80075001c4507140c410f901c2042d0200210b03030004405591800e102d8100044403025002c100040380c00807054005804c0d242d07142000b001113545075111007244c2c0303070703000e0200e00d00d9001307000d00301140c1d8200d07080041c282070706c0403019103018406d6a80c6d01540d40461001c9910700d0240700c000d0011482408420121201650010b01d245440301c1c41c48a10b100c002c3c01e4506010011004c100c0200c0e2580c8903401640d03102101c86e5481d120036954a8018000b403040c000b400035840c030420040c0754080c083c2c4560b8040000242400380f01a0790704405007041010164151050449610220303100300300c1d0600441c0900701804041e400c1050040548200030942c003462030041011040040e0301808540403660080070401203040d05120 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 284681124 1250 284679874 284679937
    0x90f170a1101270815090312060a05131e0e0a290103061a030c03121803010908190f090e0403030e010204060203090a0510090501080c09030a060b010201050a060308 72
    0x40514003c000355140280000301d9800803801e6030203101c220340c41d890310101d90082d40d100c11180304445420a001c20706a24060361200c94014400601c44007a0700d0311403011440d010030b42400c400c11161560014010441e0b040d0061605004009003840982c11100640344e5844c54040f005003082d50009400070418070400c40c0b00e014010a04204d041540c0d80e007400c5003e8013011403600705140401454071081d00d80000c100003102c0010b40034040303524402c00b090003180c1007051100c030004417074100703403055690031710920710307024030503851a52240c00030303891940200448401c2400b400301d034104d02088507400c508040200d0740104c041450665031480d085016085ca010020f074690300200d0f000c113401e9004006000103010980f9a40403040e03443d03042202122414428001003402e50a080c07005510a462403a072024100854502d00340b44000400d1402480b08004d0320080c0e070310050200d1035a8207005580c0c120990103400d0005074155220407103544108425480803200d244071006034501c0014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 284682374 1250 284681124 284681147
    0x60504180f050a3e0d0b040f02030f0109140f250801170a080306060f04150206010f090903080612150124020d02070b09060d020a090f170a1101 63
    0x8284054180300352110050031052510742001c84500380c0c07000e0814098801c0d03130303820356042c2a06010009660103511442d0700c440c008034210703910b6480310a896141c5004040641910400043e940c0c506a001e40c034402c84180c01a010843c01e203000d903559815065007494010b05005400105502c0c0c2d0640d006020144ea1000c40c550180e6105141c07c03143c1011803103040314060300c0c03940d40740b045d0f04c07042a480b0078114000030440c0d1014400700e040da081210141c00882d08400d0b20354a01f58407203c1c11038540386003122020040c3d10410040c025500c00074442002820100b00a0100301c0a9940162400030300428050040c1400b0b07200641c0d400080290410070620007180d01c1c9103503190260101c1808081001c1c1c0100d02a00005a0744217200250040760a1120b9004e8002c450a05140300d00c03540c0021180d640c000c806004c07a20700403005200400f0119620344507543e460345889503d40e8600026031200145228081543d0039403403001c900200c13060342c856002241c00001300e0040c0c46412141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 284683624 1250 284682374 284682401
    0xb180d060603050f1f090f080409050601020d030e030d09032105040611070b011703130801050a06060516140f0d0f0e04050c04120c091e05060a06050418 67
    0x4559100038040507034000d4040c0c034040d030241d0307001080141c030341c0d5503a00c1040c00390f01000019450784602034007190312601000380304802054240107103445041681d000703908800001c541d00e109201d51981c04000c419001c41d41c1e81014411005420346441d22402901a00803072244c6415004040500c2070310300c88250102d600c0d064804c0c1d1841910900201000c64044581a141c03501c0f20041d00b912805480c801540a25208403507800c060215104c07050102c0c0700d00c003901c000d01c00749400c4c0101c50462409010036000000b4180b402c80101c10541d4ad00c0c1d440901481307001c04c03d503034000581e504664100c0350403045407011010ba1a5056181c5240c1c04222003050144a414a10941c1d001032a0500325003696900820200b140c001c12080342c00a0354801e010f4402000100801c21080521f020110b0140d030404140796503450021055589050101c0c5039120100194070034251184103503500301e0700547d81d1071000344c201080680b140c171441c040c0446d070141501c1109c003010882e07080652100b040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 284684874 1250 284683624 284683639
    0x4090210020106080709062403020c010f0507121a040207080c06010b072a1208090904030f020708030306090601030e0a0813140102010b030a0b15030f070311030601030c0b18 76
    0x4000d00a0081c5003d0040c0c01e55401401e0000038502400d00030f54003640d401d6007241c60030b05d40d070306049140118140004810301d43c00784604000300320284a64001180701c3d9901058502e4000780c01004507107403c0241d0f80c0709160001d6800c2007808140b813240303048811b841c010381d504940e040542c49402000128036080c4207030b00000c129a08400080c4c480c03d841550030030b01750340c403900c4032104200501403421501c0040250811040e64913108603162140039654603072802480c41302084400300c0445055001c00d820814015003d981004610003d00c005c001460460410b0000581c1600340981168105522172001c080742c640140104101c0d00d038000400c1c0c0c0e41d81c0d00038103403a07809441d0388500710f0060030700310382d100e15540180a1681240d0000f000344c20648030079901c40361445005000b079208901c1c11084104d840d00c1c20401c03407981a259400a040762840c519182c0054a00302d040940603810041c01000041c020313099030403e8507040c1d1607094440300101890300b0010844445654000d52 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 284686124 1250 284684874 284684899
    0x40b130f0503040e070903080304030507030504080d020f0f0307110d0203070b0c1f02160b0a0b04020a12060815010e150a060513081f150b120708061f0e040902 70
    0x104101c0c0c0042d62245030550705d4550aa504c03e240b488042d00b009010000603000903c1a4000c20a19120341040c0741410340342c01643c4c0c41d000360303c1e504002584c0640b800f82800007080003003281d042c82c0c50005502e4508030360303034501d40103070340140640c025900c5110110840d03406000102c0601a0042869201e02c07a2042c21641c0d00400c80140c4140441c0500d03000c000401c030b0086922080440840c04064441559000b0008070020860034000f6902c9008014964030360000300780da02e80f55512010300c1e0103825000300840301e1702d5000ca0126400350b549684c85e00403c035680c6044500c94000400345a54428a881032004501c01241e4007418042010031250b0700300014100003100030000d05040790311410250b981c1e52001c88012071400320101568029079054001d0300c0446040102c82100c030740e803405200c400d0740060840c010012680d004020703005a1080700380c0c2d4000c42c12541444a040b0800072000d003500710544030010803091000e101c03400e131101c0e0007124626a0103051100c9482 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 284687374 1250 284686124 284686133
    0xf060f0e0a0c0f1406210702100609020301120f0602070507063f150e151207060f05070f0f05070602010b01051c27060213050117040b130f 61
    0x20124012030b03014a02c0d050204010101c0180002940c00e0070407440106040102001180d030448544101030760039a41c200c2c0084002e0b042414040e800036002003690303e0128288006552540e040200d8070792060004216041000c0001e84200742c11543c0480000d9540c10f03d90701920501c00041d205101d102d0000500395800313000e80341d05420140c511050f003251090943c00f071138810302d00d0312030414251403030b120000007030307800b11412408014041070304543e2401d04916404086440340f02c11130450300100c0050078299820007040108001400489041c00c01c06084100340070440703800c008000c5020380c100100103c442d0581c80e0052a0170000801d035251031541d88007140141d100550030040d0880b20f65004200340d032000b43c00001032070507003030441c007155004054200c01e54406040842c080d69000044c004011415809030348050b0755641d140b5100c00e00b10701039900141c1004690302d0303044550011000d58540042e40441518515100e6060640c4020301014000d030600c03a00a06940401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 284688624 1250 284687374 284687383
    0x60207080307030e0309150a09030b0901050406110406121112160f090e060d0c0f08010c0311031e0603011b030902312a0302070611160f060f0e 63
    0xb082d4a64090000011220030300c0c1e00c030b02803010180d402c52001c0c3c00410355800d0340380207400e442d241b40c5050b03000365980e510341804184050300d031b03411f442c0d40d9030b4140414000e542c00b40007440303440094241d1a0614011001f0800501211032401c01c940c0c41c3e0349403c0d42c2d50080b04131081808604481c21844c02c0c0603071076440786010040144003007a218170f480e02d4021702546100048843c0c00800c41c145584407814400c45207080d40e401c80341641e4490000c2544505a08520040c000ca00000640c2c00030410024040745d045588100501405008108050f40039401154000c00701c1c402c1c09000d5120b400200f4050800808038114241030b6403c1c0032280f542c168041c1104038000c8640412142c01000c00c0c500815251700013040d940e400460b8031128201c41e41080c014029424040d9240c1c1c00013202040c9412408141c180019400140348028041540192034900081c03c4459140c03060280148410901444008001200c0b07019074605004082d4001401303030401c4003090000544a0803c182ca5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 284689874 1250 284688624 284688631
    0xe01031112010b0609060903031603050c0d080f0103060c020705210105010b0a02060f130203060c2d19030f0603080304020a0b090a06030518071e080f060a02160602070803 75
    0x7580c081c00504400d84050041030701010700030300100e2030010403405006465006070b5080307415200c2040310490100b224001000c0050081c0e0f1880c1d2102d480380c440d0b5091920701e5803558200154841030100a41d15415114112036001070001050407c03804140c0c1008100e5000c90740c016182641d0043d58841c3c02e403031580040ca0a0001c101c0d40c1e0b05e0f040908541d0040401901c0180d02503c0010840401d611545810400320b90400c44000341550000e86014800c0710302803529880407680c1d21309448580c1e814150413401e502c00e10703480903d88520f0586405880c00066603401100001c3c801a40254010240d8034400442446a03030784a091003242c1e40d00503602203004071342c9400002003006000041d9946d2480c020485400c1c5403030304800310050170000d080a1007802c10b65803070b1050302c1c10030004c810003031800c3c0c000c01102c000700e48019948408a40c1c85096030360010a483d100c0e0910100f076480d03100d0034218005032100b020421102c501080d0000050807148009081c074244840b002c040c610 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 284691124 1250 284689874 284689879
    0x20a020705030102030c04030b090f0712020a060806220b03010509010e0f0604080910030b03010c02010608060603030c120a02030705070e150402090d060f1116170c030d020a03060e010311 82
    0x1040380c0e41d441407500300c0c803040b035854101040c28007040c4000740710481910380103c0c01e901126102c0d014642910308000a0b0b0f030050580620104032401141414054500248500d040c000110300d007190224006001110880b449852442c0910902d805164000340c49a00054000c01c0303d8988150003034020100001003510300d2040544c0b0155030440020603a10440c0c1c040c00c1a42007481a500f171114110a074000745040c1a11041800d00e07646091255016940043e4004100645000c0c0c40070b0910b80081d00c404e000e60030030802c1c403080d06c07000038290a660f15800129a5520001c0500320300f140947c02d001401e07030283c2100040c3d1140704100b014001e82400100711200c20a2600304000ca208480840360000743c200300038404103d15a000114854203848046107003012a00c21345d03800d41c442c060718500301001e55480d0082c0001d101901520705142e0080600d00030524031166a41c3c001d070071103445080c1e000503a001c1628804c1e00711100030b065008141032030f941c691a004400ca010003c4250 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 284692374 1250 284691124 284691133
    0x10c0503041a1b07020402120a0504140309061c2c01060608010302010903021002010902220b09090c09150907030b0102010b010e090705070c0e0a1e09030813020103090b0a020a02 78
    0x440300000c000d5581e000d038000c46112140360307002d240c2e440f01e65008490207982c02135082c441e202d01c0580300c802245c0304001d02000000e00f803415140000c41090003201c205030301d074400d0007100c0140c0c41c1c1c642210041c0504103600301d103e0000c14507400107849605a030b91030180b00c420b13417082030060791900140c0710f12f8808002e001058950208644511003480080d00140310f88504102509004442007240c0c680e502c00410303600842d030041a4600c140146901c4042c0d40300e04c81c0d480311900c40c4030b170641e90441103400071050304200700425960b00749070450a118884000120724940d0031111f07201c01e05e08005e0b1416116151403000a001000c5c0d0a280601550070010803681661040400c2111a84010400401c40d198110110b03034640046030300310360440061801290641e0a2404548241c56098011501c600c084c00302480c241c01c101c4021020500340902440004e820018441d4850002151003a41001b01d0004030050700304003074080d110070303a14000d0008840e02a00184500f0f40543c0896 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 284693624 1250 284692374 284692403
    0x3030e0d02060912060612011803050a0210090309141c080c070305240606131a090a03080c01061a03040201080a09021002060405071d060f01090503030301080c0109050d12030c11010c050304 83
    0x1401c1e1500080819249090040c0709c1c00000c0c060406409040d0843c4101c440c0011106480411621403210960100d43c001504200701c4041e15035040d11341c002901c0c603c00d103400f2002091b401902408005081c02c00205401d0310386801041500000d540200c1104d0291020380e04603e00c3d4407007051150070341321403507000503124180002283c1601c14100300e03a4403c58a861400c0060300a681c01030140011304101181c16030356580d41c0b607800303140290040e941d1100141101421114139901004c040c1080c2c3c01000c18859080095a41c042c4d02030030003020954400080300e0041a607000d0003503011098800a44560b80d00003400b80c4907030b1040c4206e605483d1244500c03014000c23004d80301159643c440c800902281000000352242c0c21041c1007092069485100190450f0000d07004a100c035032004120440b036607840705100340140001d0b6030070a059a180d80b00e4140d8840304030040402e00d0340329090800007510815403500002c1019001f00807000b0905002841c583c41550240e071195070740c145a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 284694874 1250 284693624 284693659
    0x5010e0411040c0306080a03110c0111031803010605040e0d08151c05030d0519240302011805030f240709171507080115020703030e0d020609120606 65
    0x20540110740103540001d403800ca4804001c041c0c000c0003070312001c2544030000066060303410810040210b00c661105c40120f65040b8500f0f180c94000076086040040c16400030310385400103c2204c0240c0c402000c880171940aa0700800d02500c49644210b42180c43c10048000014000c81d114001c203056a07640c8586403241c940c4210340600b64005980d0069510300805481c42007601944076451280c8141d07803e0203a41405082200c01c11101003076501549502081000c11070b10500040024485040200e2454511440300c04020345c00020705100071014411098200790000340020800141100c0c0f40780318400e03060751240c407107240c030300961240c441c08861964a544152032180c0403a40c0d4006401c2d203400c1c82e02c4018007128500c829a801013840a031404400f10792100e00c90442078503a040c2c00c0d45490034030040300084481c46002c540040c030040c40040d502c52161152203004880884240707940e400040ca1911695000d40d0340300c802c0c0740501c00161004070302181b0410084075000d402c840303801030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 284696124 1250 284694874 284694899
    0x201020c0103090b0a1d0115030c0605030c0703080903070c18110f031b070c091b110d08090f0f010b0405130525090e070503060907060c11030f0307060501030203010501 74
    0x3c0101090b642c40002281080240c1c44003400480c4908442c078100410b110a030b00315040d0303440a00e0598070812007401804207806800d80101543d04e00940307181360a151034501405003807002410004040041003041300f003001a9507882d6048a510380d101d50b030394071107400020070b01c2c40070030001070512800c1c11b00c0d6180c6200740e4103010041c0b840c1600e55581e4081044111580c2d280c200b841d801c05001c5400420640030b40503002c3c1890343c000090580800c0100e01d000358081208000300490b00d089101804001310f491003415a560402c000c43e600c41d080d119003483c04d000036205a42c46000301c0d40c810100150862401c0348030036a420040394503044618041002102c00103081c543c80101150303655045074002d4103012100f0b0890000c2ca580300d44510b82a11082106031000340c1c80700c0400c0c0000d18060010980103a4a00000d01c0440c0c50100040c0c0f144000103c00340c2150406d502031285514144407a402d00c06000c0d003903d584510a02d00840103040a00059020f50b10705070010030140000300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 284697374 1250 284696124 284696141
    0x26010e0604150e060303130e0403020c0f06091002191110021c0807051c0228090b030a090605012615130f0b0c12060a0b0403230303070504030201020c0103 68
    0x302e8005056041048075008110003405580e0584420001000e540010110721400b07000340b480204a03c0c105410002c0c034081c0c045113040c0c802c480c03081d074904142e59840200e8440d11003d880640d1100e000326401d0b41090280c101ea40301d0011490080b80800807403581440d41a441141c54240f41e4040c80f030120782d031b4466103442e4002c0504000c5201a40c0d4051940180c0c4100e0500d8250302d0300c14492014146121440400e255072074004c9200011001d42c8004a002004001c20748411204035103401000b900c080d20031003001440c0040420511403c541041002c15001502880f265960300351a407024060040c60148592031404606040807004c900180c0404822203074004c80c0d05c0d81b861340c101c1ca02d01c6031001c840040c0c1d842e603084006511a8510b610a1401c890790541750000300f191000400d200802d540d20036203100e442840040310203001e540c19680c011040c400c00600004607101010380b413120346044c0d0710010040203c241c0d40f007002031040c1c038802c0e07098841c03400c40301005400f40d89024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 284698624 1250 284697374 284697401
    0x151306090f0f0e1c1112130303020c090402060a0c02010216140109080f03040902090102010e0a1514040c030f020d06110a090b09090103080c01090f060e0708150c090126010e0604 78
    0x45003144e552a00c0381e18038450640304841501c04207144030424220540c0700003049503d42401180810a0540610180c00050015241002280b40c550b00050081c49080034800502010102183c1564805c0000c510001441040c446000e601c4400c9260300408500d820340c0069180c2002107416000816910705c120941c500550500d0304105960b001ba40103500041d04665072280c070b0000c21013041101c8040a40200d540c078010326141c007819000c0d65001244070711001a01410310002a0f2543c0c010710842c0d41028007451030700040e10009154508010010748124208200500c1110031070000b050b0181c0c035a01d446d0101682d07450840014010200c0c842e03032240001c00100046501d1200800058550100000754100a5680c0d04444e140300c04054070300300c1c1c0e02d0071242800e200c1000020040d0800400804d1010041c400000c40940000c0281c03981250101e1440740c0d0340d02031480007842c0a10401500c000001010156402c00024451711100d407074244c01154407420b02c2d124240318007454 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 284699874 1250 284698624 284698663
    0xb0c0f030f0423030102122e090f0204050303070b07080f0906181204121101031404111801080a05010501150c02011d0d0f05060a05151306090f0f0e 65
    0x2010f900d0700c658400c1e82c411114038644201c00c03a40d255001c1c80200500030010a405520782001c03c503200006401d1004040980030a00c0c60540802c010498801206d8102d1008a00000c070300320000003074000c130360000e0740510010410b4800c10018a400c070b8450701c080d54403610315035992118400310350b80540c0d5000ac0741c0c2166020425900c02140002e80724403071503080b21155013409800114651080d404440c0040c28122800d040100500762240600c5007440d0a05c50102240384503103200b00e010300000c1104104103428510f60301d0703031445d019004024070721b207107403c2d07070f444600356102d0002c0d040445d0154a440004520988202010b0100354030558034010180c0e40b5500540e200340c500466402080b245003c031100070b984000010342e404d031143c3c2c0803114101242c50041c0ca088805000029660304100c1082074044072a010072400a04c00c6805043d95512440041c00408140e04458503090a081050320610102c2d040b00080d400700e40810494074991420450325542c00081c0307082c00061 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 284701124 1250 284699874 284699879
    0x30b040204031e0311100b09090a081c0f06030303050105010818030d0c02011503050a052a0f0f1005180103050606030a0203070207180501170c010e090a0b0402040b0c0f030f04 77
    0x10458042c0303000900c681003000c41801074641d05807030a01130380c2e40040e0301c0351107e1400282d4106142c0790307a04034442d240200141505540d5200b001e00503050070602c0e410703420212900b2360b1096005458444a11503040201c43c0c0c89040050140c802401014040342d44180810710012400c035480c42c004951101a5041c40102c0b4018030290500243c600110740d00e1701e8032000d07000902d078040d0004500c070380000c2c0002c203684e1810900307109003105040c1303d40f100c881d58030111780c9800d0203142e01c1d4441201c0c83c1c0003803c200800501c00c00c105030940c030340022000e17442000725134002004190303421150880a030589101801103041d24401c440c442e4201000340080341485070590007454100308180107580106880b0881100c0c00c1c1e040c2c0e001d210540b9105d40040000400b0340700030708518008507000d0310480d6900800038040d04018940d1900035590364002402c4508546d00004004070020010356556942d8110070859401c00c0b50070403254054034800f4110008000212843d1034147c03030006003480e2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 284702374 1250 284701124 284701163
    0x30a050a0b0a0b12012a020d0e04110c0607020118020d020603040c12080d1d030714010b04020708040509100303080a0c03181a10050109030602181002070303030b04020403 75
    0x1c4010b8888054207031150011021a6a41900030b000000d015000082c1380109035425040000c13014a5aa090612085040b100950100741903100030000e0030701801d0882c00e03901040080000b2403900d03480d0300010a40c581501000702d225801046264020700c05086a945144180440d000c0300940c003c080c0e01d22500181001400741d9405800f8082ca000c0c1c5a5071a80003500d6181640c0b003c480c1c00c0000035010001d5001840744007180301083c8605120410a01c15040c0d0364465200041e001c80101144042c00e04001d41203d0708481c4040d10543d1203480310b00d014109030304140140ca21038100580014003400401113800201c0350190707140c600d1a100e80c0f541e80c0040c1000602c040070103860342d9043c560941540c1c100c0404620a011104e108030700201f000400d80750240c840c1d071a444520404100d6a81c1c4510070009481c2c10a00050752240c0e03d484e4000c0601c103011a00d034102d001c800d80802031a4010440c00c0849009880611100c40900100030880c400d502008160190300030b010344129 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 284703624 1250 284702374 284702393
    0x605090d060615080a0609050c040b030a090c06020307141216060209090c0910080114060c0703021818010b0312090105090405092a0303070308060303040e16080105030a050a 76
    0x41c0101e000149054483c0c804062030303088140c40002296001042c40642009446210000d1184030070800c880d090075180403000c0d110700d2161259a1034003001040b01801c842e44495101944400d4001c07409989000203503c0790804c000c140c1c2c1e507042d25181303418140d10108107100103242c0100898a8000b03c1c94145000c40e446400a0750407550a0203a40c0341d640f50203000a00524007a82c9060700d82c452202000b003226040c4d0301840820018400401c4901e0080c144060080c3c0c0407512a900c1d210030a2406203080f04950010350b024103111102c03080c21118403e4103005451010144d00d902c0b102691003800e80702c03030907031282e00369000110f074508403601d4002401d0384010503d4403a24100300c4400040913071b401541c0351105600851200c1c4a02d02c1491f5502040c11103084515000040c04000262240148d40307024080c002001c0001c1c10654050046402421078294161064148640504904a07951039040c2c0413a803441e002003940c0c50002703004840c0590060003003500c0103041c1c1c0d2b0060704 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 284704874 1250 284703624 284703649
    0x50102152a0c0f100c05070323070501060312020c180a02030c090916020105010609030c0b0318150103031706130b0f040e0a0b010f08060708130f03030c09060504060509 74
    0x59a0180b00d5440309020610140c10f010025800403c0920b098840b420101c90000c0c88040a01c84104244000680c11060f0030035a00c07007510307c580d051703031030071030a002a4420f02ca40180f10754a8040c000c0100420032504170312840c40381e801c6515500c04c400c1489080c3c410f025002404106c2c040010341c68003265002140d1140340341d6005410400c46001260100005880305114070b03503c1d407061003180750709104170b078014602c1e03160152a04c1d2450701e03010070b58101d5000b4010800c40000004075459038500d048614002007504a4280194008001400400a000071800250450b0102d00300d02402c001c0d541c01000002e000703c40f100201c1034120300420983d81040c0e00b03c200660200d1a61391244102c860a19502004e01107220842c9813010036000142c100c5504110070b0081800400000518640e0200060819924607100c503451400b1318016250003c14540400000b001015403540010001043c2038840240054a682041e42c05000f640524000504c05200c1c1552510307100003920074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 284706124 1250 284704874 284704951
    0x25030e0d03020d0e010e1929090615060d0e07030c060c0501230c07020d080a0f110f0c0d08040918050105060d02010f0c1a0a060806180604060c05121005010215 70
    0xf12116094003c0448e2200c2844190640940d001045031078081031000300c1d4005e04011612410030001400244640642084c54040c103540d18070a1505100401c062405142c00015501840b56124401400c40d511080212032030750030000310003641e90314039496083e660b445004250880ea035560300307440d40da01300c1c40301641d01403080759014002c41c2403040103100c0060381d03030348024102c0200c16000e80610f00c590b862040b940d01c010345c25a2100404a02c201007403c0c03c03610b800b01111306003410343c4240100d421030004103103852448241c01101070000d10003d0700c41c00090106075107050420041010114010340882c001c0c1c46800415440340c4c0248801c548240c4a0340c81541c44241190070380341040b00c00f844583e41c1c2e0102440f03001c3e41000f005a000d90380e1848000341f401d02201c03903512628054401001d060301c1c0d24140a0540c0a441911810b42540034014007525150360691040711181c40307034501600034100101d030280b000400b5144103128000d061a1100d80030325291010014460a215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 284707374 1250 284706124 284706143
    0x14040306020c1c030c030606080402030c010513090f020d0e03030f150105040306090c2d0902031305030a08070f050f18010c02120d08070825030e0d03020d0e010e19 72
    0x50030010710304802d0443d441c0c2e800200280440302c06001c80321160000800d2000c0c007030800c00103a40000e1100c0d6141d80c20320300151214800417201d02d00c101260091944030b424003ca03080d040c2601c0d40074013112100c0c000b041c0b0500c00005401c07603c9201c19502d141d5007900d03890010341e0500d402c1284100004040c035007280341542c2d9488800403105a4002125100781c051020015480540e00510680308220003000300b548580b00c600d0b404482500c98040e10f55000300024440e07120140508010320340200540740e540510f01001021248100c403618082408124031034410b612134010350f01090f0301140c00c0752400602c0d020081541d0300c0e00c0081030421124540220040e255501040b1b45400759200400f07103042100300c0501034031002401c1d141000341d40c2040001c550105104c81201240301d681942410445802c101c010b050081c62070750381c908c11108003009075603055001f04814200100304019509540141500740c1c1d1440b07107074030313690750150084da00e402d044644020002c511410111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 284708624 1250 284707374 284707393
    0x21b060c03040306020d0609060e070e031f091401020a05070204050903070606080d0e0402030705031f1502150c0403050606100c06050c0301051002010b0102061308130e100614040306020c 82
    0xd1a541c05504100c135815000720f85402c050101e80600d00180c10f2500051002505002001d031010750010412810007490752203052103030b00c0900c01d20154001c41c1c40c00c081d403407801c04040005000c1450703085988641014030119802da06100fa1500c21110742d5800c1e02d440e00e15000c120141801504408090204100f100c0c0002c6041c400c402c02810315601520341e0701001c40d0041c218008600c3d01d680a00c1c010020000c89992002c1244d0384006a0a51060703036243c82c002165100c1aa5040351900d9100726000800440c0c0000d85000c0c2c1e4021401400303002d94a40161003811300641c4001400c951086010444600d080421011402d0480c901004000b10989501301501c1d0160345400020342c00000500c5a82042c030888018843e050001f07101d000a0400000d541e1180140803001303030300d05500c02000b0000030038110380303451100300210a28192203407a040c1e541c50042d40d0314000307407020f8032000655130b015020945401c030242c0140781c10546540c503030728042d42c0050101c1d0814003914142 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 284709874 1250 284708624 284708647
    0x1b01060801051006080907140d030516051e0316030305190c0306090c050c100c0512180c0915010c0218041a060d17070615030515010b0406021b06 64
    0x120ba21075003074a00031850003868104040c0945201808044a681200506100b0791485440410700d0000565071130524407070b1030401b140c40307020b0012045903440c070490309102031090000364900380e4141a42046000121036010b40ea032031041d031059034807001d040344989001c43d00a500c2142c2c007901c2000c20080c0107140701c440301d0071a81c540f20108003184c0d5401d0140855141c40c452032100c44047d043c1285022a81c03000955111141c1d16038610f030035194682c4e80b542c54410015614800400c81481807a82041003c6c825260b5501040d400540b00d40d0421034030910305045094000c145074201b40310b20191040046410664015050307801c54505885111500842d103003480c410f602400392040da070480316402c0c0002d0100034050368820380300d00300c0341408110340c0301d05400039074009062543e0301c580d60720b0b080c0e0141a01c441690b58032095400000240900404e616030340c07100c030801900c440d0b0380314210719205c0e00690255200580c000419543c00c42c0201c40320031000c040c010f01030b40c10b081d8031101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 284711124 1250 284709874 284709881
    0x6030901060509090f1009081b01061e09050c0304080703180b04090506031b131d070b040626010501080405120a0c030e040b010203032703070b070f080c1b01060801 72
    0x18039146680c07100e01c4801465505100f089015161b200c010f2164400f81c0d1550240c0d801240c0d201c0504205c03280b05032150781340c00d42c4503400500d1000d561600040282100710b0a900040c802c008089080c0b01c0003490340540101100d12640d0311a4020f07041c03440948085a84040301d0307a030035801c80c03c2c14801042031140c10700900011321000d640072402d460000e09040c05d01c1c6404a1400007400e500c0100341c200c0d594481d031728403261040b01c40000d0903221581c403848400601c41c0c030841c2d1030013031040104815030301d00c00900c1966160b440b10040201c00a80ca0103500f1141c5c8505c1c401c8079203203001030066601c070314812600079000d4422559841d01c55a0b10312a5644400d1702040450410303c4100c0030150400f160143c4841d04540c108141e001080010307449210044c04060034a020008401a418100259140e032204e120112900c1303207491700d0282e401e0b600c156070120101d04a22451443c052041c00c3c043d118811000001d805c00141041c680f41c041c0309440724401a54941c00c0204081000340b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 284712230 1106 284711124 284711131
    0xc05092d060a06231303030914060a050f0903010e07060f031506111f0504061406030c040e010605090408092407021005070501140916050f06030901060509 68
    0x76060701c0070000f0085078a80300040400c91014400f411740884c2c0c10b5030711030744540c020b0540360303d6541c4004d80e1840c5080d900040411a003c0300501c03071005010321107040c0300300504200b00400002e0a4170070031451042c0703d0303101803010020b13140d01c10381600105250341000c02c440100c13542c60140343c0c200d5001e40810300081e491050207090041007524407114034180004010400049c4103005090b06032001d0324250b003001c41c01080020394210880c024a0020b0081c194222488140809003400a113030b54101e55035043c000901c2e40310001c90707903c030310b1060750415522402c810800c0801c0300714040e112070700480309850300207035041c0404440c0603580440340000c0c2c01088000403240b0380314600005016508002c11400281818030410707000707000840641c0c0024542c20b46040c0741c240584900c6601290001c0c01460500b400001560030051a00020403a981c5800c003140315650b095 = true := by decide +kernel

theorem cover : BRFrame.Cov 284532374 284712230 := by
  have h0 := BRFrame.cov_init 284532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 284532374 ≤ n) (h2 : n < 284712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
