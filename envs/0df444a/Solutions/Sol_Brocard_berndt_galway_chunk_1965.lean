-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1965
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:19:36.161078+00:00
-- url     : https://prove2.me/submissions/d89bf790-2843-4db1-842e-7c49f688919f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 353237410 ≤ n < 353417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 353238660 1250 353237410 353237461
    0x13080a050d15030507180e03160201030e07060f0c140d050c16061b02040f0e06060f010206010f1707120b1b0715050901020706060909020a080f062a030f 67
    0x1d081c40040c10105151046e5001c08040280c451650501c1c0400b0b00108034002490f0b00000524040282a290b001c100c1c0c1030003038a0030301c8003001001c4226076824141c400c0d440000c0703420381603022442c03042c0310904045005015541006413582d04540c2082d1021107003001203a40042c01d640000010311070300c0c205100882d88445941e24111002c1c04140d107030040c55109503c540c8081046640740d41c4003c811310002d00c0c2c1003003034100740d080c2140e840707000352055446070309091002101503100080a5050300e440040701c0e0a0700e8034220740607000381d00001c044401402404800314804000403803510403a40140c40c041460f081140b480703515200b0304941c01e410078070200f010b440031900100e0805d400110030400000e00c0d58442c803009009000300030008011505115000590100350740020803403600031190b800500b9036401e0270541d501241c0401c1c00c00e640020000412944025001503170f00e00c1c42e000040082d4400d113400a82552084802c4442210507109003c402c0b2a21206504401e41010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 353239910 1250 353238660 353238701
    0x120c03160603050c282a0b0105041808070f0b0a230105031902030c0d060519140411031009060f0c030b03070b0306040605030d0801090e010504031713080a050d 70
    0x40d001401a07410078240500c9280c0345d01103c918072074015041010103454005001d440c55000004410f0821601660903042600002c02c01d80f42c103101d0804016800711903420600290750720035071070307400c07040e01a115901216000d2011540510080340b061021800000c2c0300301c00c50768100c402c5486c074140840900030703a800520042c1c03400920030340aa100c550341803005041ca4070010b03141014240303090742c0118051003010204007031604154001c055006485141000104000e41100e03d140d442c1c0002040c150041408181450840040c80002a081e030b080000009e440e04262520302008403074890792500044a03020711481040800c00c2c00b0300e010f01c10411343c1e000207075490102d401610540710b00000820004d0b0350302c1d4001c4004200140a0310039035074221001410158091146000c80740c140f102462207000184603192040313615403510341036803800c0180250078450040c040c010340900c3c0d04494000c41c0d00c220150210010640d075884d83d5403c90344806099071081034006204040c1c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 353241160 1250 353239910 353239927
    0xb0a02010e0c0a05130e0d020703020102100c05070f0c03050307080d051608070f030f060303050c06150a0b090d020406091a0301060e0606090a09110d060506030601020c120c03160603050c 82
    0x624240e044130412904c40701198402062807004040c0342041c560b55110300f110f1074200d80d401003144000c0707900076002d44050b500c3d01c03281103003234841c0c611030500003410420140700000c4901c80c0740c21000e40500103544440d5280c0e55464615803041c24103a5001001103501142c4542501a156000403044074544400c0d0784000e0160203a003010740ba5070240041c400c09000300e02e109500c00008000c2c909000d101450f52403d015140b50b1080f08680c039107003d8000060928910309030000500c040c003074101d840075480c0c407410302c0726a001841e03169809640c0c21198400342e90b07a4014000500f8143c031000950410100c80a02d00300f8800c5140c034040d0b410702a080101e400700c4220740354408816940c096075076824000007030405002d40c012002182c0750441000c080e007558005400840c100c08001c0201c03e80303450410140b8082221032031f005031b01c40d01c1c0080d81420700d00d075609410441201140c491014010011f4200740c0038400c80c00e003d41001100700040d9601d400b60542198484041e82c1c64035056 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 353242410 1250 353241160 353241169
    0x2031201032303120c0c01090816120503040f020118090e06070806012105061f020102030702010f090b060f040605060a0e0f0a12030c0203150702010218090c0409090c0509010b0a02010e0c 82
    0x2017026007138950100303100701c5141080d000074520660202141c1d60700c5d030b00c0a04042044440d24000d407412003020035407560f528001d0084a000e590000c0310008031030099401198081c04450740035600c00304d50500001e0000c80707401003102041c40700000d4111483e00030070082c01008000c04160401c8005100e00c0c140541030460024059044030340414555510303c0491080c030340032500f0111405e90a4024001c1e00c3d419805540560056802400b00c6500782c40f00350b054172131842014003d080a2800f145031032500701c100c1c2d011100003801c0072812a6686001500313640010060794045228122011682e01d005004408101c1e02114201416424003140c5005031030205c1008040c0426407410409550301045404042800c0c00c0c40a412840c12180080c040d407c101983c0045401d0807030405080c0c03030566555445511608511410285400e0142010386009142500c1203800c00310003103100c3d114041403034040c052502c0880ea490140d05070007821940d94980600d41c47d0882184120790345d59 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 353243660 1250 353242410 353242447
    0x1503061e0b0a09050a060515041e151b0c08030d0f05010b09060d020702090a090b091f201318110406080702101b171009090302031201032303 62
    0xb03d00050555492000000421464011680c4504103046640c070700c0600c44d00030800d88041880e000304523410028800c1e04604940541030001c1c20340d8449031801403140441c5944000401010095065a074641098220b207682015650390000110040d160005e8044c103078400b0120b40e8100159854030701c0000035070282e03210b020b209000000303100e00303d42e0041d01660318103600103045140780c1c14132180090082604120031034400924034000380300600d012410344241e01e14030210902d01341c001a0f1070341c000c05403401d6254007502c4048035400c2504483c0043d1680d418204c0748249201e05000864039450359803802010410300f032900007141190803d003074804403801800c14080580701d5400582c02d12000da50341c513100502d05105c010b0002c0c0c0002060075110301c952a82545024103500d40c00d000d11044030014030105a6a41c108850051548200072290280c81038a042c00c1042248040e0090300307070700580b07480d4061000450075403920346400d901185844000d5103040400a0000140c12 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 353244910 1250 353243660 353243669
    0x20f0a02030c22020c0303060f040e150702100527070b0706050c0f030f06130b18040c23040f020301030515090c180f01050109030b010b07061503061e0b0a 68
    0x31007000c03c084103149500701e094403d00e1422040d501d600c400340c1460341c0ca40040f00c095210b01034100c24003100341000d02c030b0341c580009080c002c0e000400025403141e408082c0981050214480c01d248074503000c090784200350081c001002074080000d41c0402220440140700c4403002d41d9040103104000d40792442c012584600e51121000c80c540c0c4e90f440413001d035406603001c00003440c1000002c025649244180c1030748610300468a0319040c50308400340100f103818140100b90041c11070000c000a00c085500c3c001e90280c4207020424000340c40d000189000300d03610f9140c1440084280c425801490140130701100c00c1e841400850841d89561900ca03981c08580a600c1110b600400c04549005400d200c0d07401c0e030220160100c0d10050701444040c1980604903644042010030310004511584181c0504088039002410390200380d00b003c000c81417552201400303d4619139510f1107824101400341e40240110301400002070700c02c0e1a694900c60031800b0310a407000d81454152800042da03a000c14100580b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 353246160 1250 353244910 353244919
    0x8010b011704061116140d03021806030a1506170105060a0f0305041703010605040302090105061e0c0f01060e0603010e1507110f01020d02040510030504120518090115020f0a02030c 79
    0x724900400c4420b11585e813041540b8407000401d101445600d11090f59442c1d85607088501241c1410001c03000c0f4041c5003403100609584080c444000e140960107580c11010b14040010451840001ca032801c0c405a8042c4000c0307000c3d640341002601c6655800d500421054942a14010108400070002c0242d000741805050341c0704081402d221002c1e10b1206c041c41c94108056807942c4508000d40182c2007407000b2845980301400100343d60070a5001d64107280c5d0414035880060504200c03100c1650040100100c952184818520340d400c001d015a10041c2011240301c8030a08101045c075080d52000c4c0a058561b510016450441803c20540c06034019580d14020001c84404030407607042070044042c285042d030001c80d200940008503401401154401c03035410000020f0904150140d400c00c643c050060f01c1912a40c4d412a40900d0042c140c2c0300071710080b600c100c42880c000035990602a000942d543d01c55114080382960100002c1511843c884001c00c2581502c1c2d001940d40d44218000c41e015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 353247410 1250 353246160 353246171
    0x2a0c010507020d0317010306150801060b03060904080c0118110904200105040b0c0705010f08070504050f04060306021c0e0a08090d060209030609030d0b181501020f030d0608010b01170406 82
    0x42c54410003144401746070114240a040d40c0d40d04045016011912004084150101c00040e62381c0c0144150002c42c0e103d0b50f801415582e6a80400c0b841c00705c02042030b140d4a104002c2c544401c102841a8081c1d4203940844d404e2504031410000c01c0b1314001c1030020700552072032042c04081070411452030801412401a0b100760525180100c0c1d581c011a44910390451000c034010b0600c5102081010640d02c00380d86400c043d854180c005c85e8442801d40d001c2c00403030001c010070f00042c10008290000c0b10400350001c00e0107a42d0f6a900700813684a01c140d0741c01c3e030700d40310fa01c0c0e0303802d81c400c0c0905158040301c40010020480d203a280c0003524840c0c286494422409000c0660070000248c0554413000402000d540344d03480c01c0d40400d0f489a00c81c0e48a682080e14088034501c2a2510300440c141e40d1414240c480c4803136a408050500d601ca28117409419071142124610610704108014070000000e450b001ca60213251030000f41c2900c060fa08294107101007034000c07414400e2101c90080c0d215410100c0840e2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 353248660 1250 353247410 353247413
    0x1a1c090c1215090213060815060402190305040602070b15090c040602030a050c10051806090106061d010e061621050304030518030a060618090c14010210022a0c010507020d 75
    0xf0b4007051005c03013803640c0741040700008100c4c00106110b05590008028580d490b03031004100022482890210b0010780c0d41c1c0c180b032002c1a48668400303a813040c40342100518086803a107401603002d02c00c072202641503411000c80d0383c007414090302041e00090402080d605007070410300301a49900858106804100c804290132f50000743c100505d402404084d00100300500303008400c200c500c180004000c2541c07092034040303139a0328814070501c0203c41159856414003040e01201c0380c809102d0b1a112410000d1729031030251035940d050002d0012000326940072505811500c3c0240e024810b488081084482d1035101450180d0030500316a400f5034140381407070707403610000300650196504208035505442140d40c481c1c00c2113850351010701a111912119105a9a260031a6090f50244640140380780307640c150400451611200c0d1078400813050058070709034110340785800102c0e00000004160b00c030b1040e54007040700043c1130701c1401200c4950094108845680b00184c5a0303c102c181c001c2c0620300e06000c600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 353249910 1250 353248660 353248669
    0x5161418220c03050106060807050a090608041a070305060f0603191d030703030c111603021306170a0b070215130206090d0f03090803040f1a1c090c12150902 69
    0x60761680c0161403000443c1c076402c20b180207020078041c0102050207440810303001030140058034805203444d5030b5a03492504202d021580302c54090700032240c00000b249816500712103d040b05129694030350b000111868035400300448490075040450040e036042061203810b01c13030082420403211460a01055481556515501500b01e4125094041c0070214445041561517089000c0c2d802c2555110400811a480c034079407190480640e003011140302c03074000c0006081c46080c01c14984982c0800090311036640004c0300d2841c05000c080ca026411544401c070800c0103000c01c0e6071b0004203d1000340384a8038040343c880b207612070140be0b0800f001c1c2c000350500119590307481100c2100c0390240403884600301c44e240c0600e800c82c21103401c41c0411555040480c0ca010004180c0b42115600130050031454600480960080f541401c40b54880384100400846c020280f080100d50340d1844200158410250400c0b90002c2a641c0182c2a03c8442d810581d002c900c411081030380740c2e00070030000503100c50340f0310014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 353251160 1250 353249910 353249971
    0xc06070314070b0a14070e090604020d1a1002061b0d06030f0f120e060901110a1a04031404140609030a02040f061a0c03030103170705161418 62
    0x1c1001100040310410029030701c0c01c45002d118075500910048460045044e02c2c0d01d000c070f4154000406090741841036213082960791f50880e501920062518039003c41200c186da0315080507079181c208028100701c844c140101d42246404891001c1c00250502210411000c80e030007500d8001c4030310200745824028000d5110000850380a103145000392214030300a001001014003c0c1c903030407a00e802024060b0702601840b003407120001c00301c80c584041e0500640c2d0300003070f00585034414172602072084002410300040100503040315a0100c0c40c0c2c90b1500c2c005007134041c408001d4680d55420301007000030290340048030351440800c442103616a216580828a880d020100103075000d41041611188070707e00f688280c09031881480c0701c1c0000f0b000f20300301000c02d1040c19007400c01540b08100400c0851050110300c0340100c2d000100e14a0059180ca585141c090039460301d02010503008130070081050000080c1d011010150348000ca260780788a1800d90140c0f00608186981d0010740b8040b669054001a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 353252410 1250 353251160 353251187
    0x60406030f02101418100305070504270c050c06070f05032806030c0611070e270a0515090f060109110403290f0f06040c0302070b180d050c0c060703 65
    0x5510388080301181c0c8141028601194054503041309141089441380c0240740c271411054a5031850303d031030581c0d105400290515041615580038407421034540f024003a000944560f0344da55074607070200e1712146041c004090003100c180040c1ea8400720800b500901034070b50203803540707000640242c41e48074240708000f5001251104649803c001104011210701d0003400c1d0b510583e80c04100c4001d41c0c1e400c6954010500940341c490450100003010481451050621900d15a581a00c0c400c0131090035403408600042c2103505410041c2c04221030700003100e500750b0250f00407000300713a45c003e0600340347d032100010300030604801d4a80c50303036181403101481187c0003076034071119040345540f01c2c82e4a090000c50009044040b003200d100802c0740454104c9400b4022062940e04142c00d842c3c11040200034001d07039503a002415000e110000100d40b10381002072084401203070303550f01201d05400756401c000d5083c2d00c05051020900c00103807401c2001071820511032044d10b40d2a583c00482c1816680017440510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 353253660 1250 353252410 353252447
    0x70c15090309060801080c150705150114031606050703030b030c06040608010905060607031b02010c082a06090304170708011514010903173609060406030f0210 70
    0x20100701a40041c849048030790941d1050b072143d072516002c544501541da19076611045121101c040519958010242c2070701c50310841d1201100c19008450540c000d0303100703003038900c070004a49005003800c0c4510409480c2007041000c1c03076030401402030064000e250018040554800c5500259102009a451001c0008000f1a112551844010b10289007400b0b4003240e40d0500c804100c040c107040381501d00030340e07040c0c0b58240c52a90803403100c2044641c9001c142d04010304031242e44041000f520041156800d001c803060744598061001c0e061001800e40c5500541d4411f004200b113412000c0165020b603000c1e03002e94060007641a10484c5000b03003d8100b07000651802d01c0c803e0007900481c02440480d0030403018101499103900040d2040111444050103021510300d2044d8507100304001409a4011800c260407603182c901e840700050500c120880c0302000c004c3c503001d0305911f001050b0a034030200494042c8103260644c1c0e40d00300d801c401418000d018200c00102140c070580142c0403004c0c00c811010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 353254910 1250 353253660 353253671
    0x30e07030606090b130506090610031104121a0402090c09010306090219020d140a030c020a0f03020d1b080a050a0c051c090501020a17090f040608160e0f070c15 70
    0x1003e510060034100d0b60a44280f042c0808441c503074038903016091041c0c00040c04208141e507140d0030300120b042005145400c15555500ca8580004801d010380050704402d810348108030410316210030b11000512100300452091802c010050b503444110545c464201e014040d113440100380143c0c05041e1541003820500d002041001180510110780c084c4d0a043d40d080300c84100c0380800a4516900748480407030100c1c0c2c100101010f842c040c0e00101d800c80340a20496080000d23546810703103810424241103006800040040d1800e5074803030180e6090302300c10030f2406001000e030b07641d603c2e4070b01c1100c41e00d0051240110b1102152070162003e00c0705036801c9400d0307542c0209598001101c90704840f401c40046401504046000e520001d083e0b20440e5001c42e41e0300d038500c005141c44400d80c0160414541c4070b01000d521b40c00c6900d4500601000740014001000389043d02d8002c2d0a4001950300300c910b402c1064400c200e41800c5070713200c680c0c00c40c070182450000318a850902c03000050002450300d24550804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 353256160 1250 353254910 353254919
    0x30909090f0c2b1b0e040b06090403141306030c051309180f0c0320061210051011010507110d030203060402120106080601110d0c03050c030403050607180b0910030e07030606 76
    0x9003140c90300c40041a81381c40345652100300d84c1400c12400e65014083c50310079070005e556410007821554020b8000d0a18005c80c200ca80d450000541c030230103181104091280c0304022458060017000e6030312011b41000c5003090701e44584410080c0b214461019006c1c0c584280c010071005103003000ea80c058110440442002c00c034285118000761301d11040300c400d084101d48001c01c044400940c483c2e245d000701002d03c0d00f464100c100f03107902c0d005005200c4001090000245a039a00040320310311030310702c0d04c4a2540e00413070f60249003155001001e51b0240324006d9950344150501040000c001d1a103801c0061b226214440810005d000c2c0b407154188074101940041a12a040060b41d88078400980e01c401c00400b40902e00d5480700c1c43c0400d884007240e1006d04400009000d2005030840b541503504580c140760303a0b0303140e03685412010354409010030380c0d2200c000c6824803408040b101400c1007002d614549140e0303c000c6281c640e0101045020907030744510907100322100b40010002942c12038028030040da242c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 353257410 1250 353256160 353256173
    0xf0b100225051207210818030718090b06030a08120703060312090510030605060f0a050c03070b04171c1d070306020a0e1f03021b01050108030909090f0c2b 68
    0x80380a2000c1c110300b4418540900385c240b203106a000e662103424542084840525490480520300300c0c582d1500403004041a0039605841510308503442c803401086440071030420306400b60014081e81e009421101404000c1581c0408035140e914042007a100c0d00c3d070f02d542d004ca00401060300300508144080a07800e682903440944c42c001c2d11011100e40d6020f181c0d0f03100a504035031051183c00d411050500500003666038030301c05000c00d420181007041c0f9080c9513001c4203085501002d401c0300e100050318144018030101708201c554031509161420300d003d800030a803580042d804c0724031800b5130f51910000e001890600382040c40584014040342d264507180e18049002e900203249040c00078001046128082c0b078411584481800c440c42c00078100740b40342d07078114003a5010040004900b14440303103030900004244201d6009000301405152510f038071204102c88408054190704090b0701c00d10303a50442c00408203c581d00d40c1c07801ca03911f460300340610100e502034080030003403101003104040c04203051088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 353258660 1250 353257410 353257423
    0x60907030605060d03020c0603100b0417120a0c02270a0b09070c0206041202011701120615030b0f04170a020c040b0a060c110f130f0b1002250512 64
    0x1c9560300303010381c1d540c041c14007040c1c0e40f800801900580c0032000f00e11103800c0c030364011504032029841e0103000701d446d4100300080b940316920030805a400a181c0c075814503818010741105803040c0c2a1540303003250400005240e2108008007a11034000c82c2c00c440e0803a2100ea544407024190040c10010314508403410314001c046844295014014100009220707a1180b40540344166006001d04e00349070800700c0100c1c0b10310340070604a042c0300801c0c9624011a40080806000384040f012150b90492503141020950344070760174548a02244440070300c0015921440c0580c098580d84c1c507450141d0b40e41c1461040d0802d11407429000036030002e40d99a0301980400c03442c0400b0415103050204511030b109200c3c40107007510a00001a00f2a00c0c0180002e2030540c180164032002460444041c1d144e0340003400c200b56400c03054100b213075191154251b0000307501501c00410070442d04614003c41d41c402c06034503002c100d500c01021600700460040c80c008000900d00250201034146204005240500d43c0c0d43d12 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 353259910 1250 353258660 353258663
    0x6120a0507090b0306010c0b090c030f0a1e0807020112090204180201020f0d0206070c08040905150916020304060c05070f080708120c0d0e01030906090c21020f060309070806090703 79
    0x820b074020105050b0500c5003124000c03513040e5203082d051b0001d61524000100060000751b07a0303000c5c5070741117180c50780c04020054080444e8000f80810101501c0c03d0500800541005185050041207100108110f10203540300c607502030911030780c4030001c28980c000078011003400951091900d40e00300803843c8007104c0e810b0914801c2e000c80300d00705400c0f8090340e074820705500000010ba102100064036103106031900481a0b01c148040c504064072000b4074001c0e0341c0215114824180000308200c1306d440d02a13003840d0040c2d44038412061036103103200700a440f403085004000c140010490741d042000000c00c4546c004000c65001d09a9140c4c03100303074040e00c81c50304c1e102d03d00f654803502e031003560f80303007800303821200404a44001080540c02e10306050301c105035078000e83e60605540f0060b52011a81038060428144d1050081e0080d0500f044204c40d2a054140a00d615001301606881c00586800040c803400703c000300c80d642e841e65500350b49103103424800c1d00410418041c400500108039000103462058a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 353261160 1250 353259910 353259917
    0xa0b04060e040803220606080d09060315091503021801030210021513020a03240f0b091b090a03050a111203120c0c03070804030c0f0506071106120a0507 67
    0x80d5903505410315a000c00b80c0340544003660400120303244159204c0c81d8103000e20404800202030f01c09484000c112841a8400d403050342100c4800560b090703004903031001400c0e050604010190389900701842d900700344d00070100716907558003001055006500040c0c0003554028038030140a410f00c40780040010b02840100e0040c0d164010301641c10f800426900485c0c91001d640e106183e070b80c02c241c500f041c800004241e07000705c0258000b1012801c9983e90b2103c02078400c1110711046101c500d031404898502ca02044113525202e00c01605545500120341c00520382040702c0300800e015507695006104902110f81d0100207001700004110001c180c2d40043c6005100d0325160702d5a16007400b031601c0c00f2522200c001d4200b041501c0c9100b030a1145503400440003032011b070410080d07441c1540f0f0360f80003041c10740c3d4249003c9010400c020784007040380064030300c48a8103042c035803819000c6400c9011340300000f0309184040142100c84d407942000c2d9440c40e0340b001d000c2991810b024014000800e004d98460703000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 353262410 1250 353261160 353261171
    0x80a110a05040e06162c10090f0b210108071d1005120723090c0406020a021011010903030b040b4204080303071701080c150d050a0b04 59
    0x141c581441500c10712030303642c0c0183c183d982d901d6480e00c01c1e081132400c00f00c0074005401d8030b08207002a010040190429140d00c45410101d44404100d007e21200341450100034100300b05122280b2071114070710440726107400d107903200c040d801110300c21480801030300303a4a649998000110070100140c03a2088858041100403031411903c0f0f21911640100c41d500d882250038401005181041c216602c80c0c089280190303a0401c0d2100740d16884a44030382040da94404c180651a02c41e8030f0007520042e000b60382c401c04c0502d0503142000c00b035250a07580002030f00c205a0b0a01c500c0384a406056808401844400200b224200ca4a4042e005201b1040441e00840c5000304000e01402e040d8a8400c3d01d010810780c0d40040e03403d40000802c0740090340304142141014801120941c1c0040010b0806402124060b5403245050440140640803141600ca1044061001003000f9440801e240b400741c3c1c007e0701e00e03800710031103500407185510442c010501207500e413004001810282d5400782c2a030302c9040707409025 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 353263660 1250 353262410 353262419
    0x90907030b120a1208040201120e010501051e030d05070201120c020105070e030312040809030115090e0d020610060f0e0904051011130b07020a0b0f03040c050612041b080a110a 77
    0x6803001542c0f03005202c0c2102c01580f40d5203600800b4200e51152051400d1202e610300c0b84280c0c0155a002b49101101e69106c0006005628100c154207000000802c440c03062201c0707160020717659124104001060110004582040d0391058603410408bc040200621903a808038000034001c14007154030b4030002c0c04080e1400080d180100844a030004030078205003c075107039070b114076090b030340301180d625819980e802808082c03841c10850380b00144200000000c00201030040241001c920025050454100780304010482c42c6034103004e401d0310aa40b4021021005083e02900e030140088204c0c0d900100795030402c400c21000181d071b0443c0000125061000381e802c6141c0c079069003e0b0000e089881c50000200340845100c40c80603080d050700040101e82c080381da50343c265055911200c41317190290800010041401144c440260041c8010781e01b91740340c4603040580481d0580c0c090b000402e015075032011814039080042811004d060b201041d03461621141c50101c401000104006014050700d100019 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 353264910 1250 353263660 353263663
    0xc0201090b070b06010f09120f06112b0b0a080a170a050702040e0c06030403170105010c2004090b0c040f0801050709031205131428090908090907030b12 67
    0x1103410b40d010f01c40c66250b480d100010768960180101c101c00f00043d4420018000a01c070074030011140c0181825a168540f504016054508802c401003d41008004841200ea81c068140e200840e2085410f9084068180484060900450a180d000290304408a83e0910214641186a1098882040304001d114501c10240151149200821401d10944026003410340111102c04001030a8503698151900001c0882d04207550641c0001c0801e0502d06d0140b40c0300c0d03030040c09400d00f4207100340585030700d5440d1080000103500303181c502c01224001c074402d40c80e0b03a001102c08642c881541034443c0340c0700200f882d040c0c019218442c9025942540090448018414107001d1801c503030307426003e182540ca03241c0e24846581e40b984204081000928110034601031010068010851a503290802a00803c42840062100b0410211200b00e603085075045000f000811500501c001240b400194207018007107000d018904c80d089400d400801444a61541c040f84880e03034111040007100f200600010b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 353266160 1250 353264910 353264917
    0x6020a0905091509160302040305010e070609060804050304050d05032116090e0408030c0f070606060822200301020304110411031915080d030608070504020f090607060e0a030c0201090b 81
    0x3c80c2c200c008200881c1444442c0040400e0401c1503007000351030150360765241c1e400c40306221042c10103600405014003d080e0f008203c10020202c61074080b416041075180c8503268442e61288900c030340c406210504c2003000902c161904059910920711000b60100051480c5510440700c07200e010954583e8081c0b0107020300e1016040c2c41590307012510550311aa1241e02c1a8030240100d14421414071031482518040d000600c40d8a02c5484041103003490488040c1c004207001d0000e003e0549807444c8150000c40d844504456140c0090300c242c00ca141981241000f0843c20700c100b900365000004000038007001e404003900200c010380b000c109079500f00650340340c24042070322504e402902c05002c1c0c2c10b6081064000c2d01e1303280d400141000807196540746031860300074106290340103c3c0e241c0344204220305c0d05100640c01440265000d40c030f03084200d90301c015940310380c240080c8500c00100b001c10601c45580e03c42c0e660510454112500c11809090192003030840392402c03400101ca020003c120500034500350f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 353267410 1250 353266160 353266201
    0x60604050a0911090606070209191d03090d110d0b01030c0b07031e0e12010905061f0501030203040507050409050601031e03090302011110060b04080c0a05090105130906020a090509 79
    0xa89507441c039030130421a010050400d541c0003100340441c10140e80c0f00007160b40917801501440c4210800100d40500780c96034603800e1000503051442030001c0240c04400c4a00c00300c3c7c129101540101c00b4940b141011900040032500104000485d40030021030044031411390b0302030355050302816034520f02140c2e1071082e000c00500040c001e520343c0c003000d131203400094910350302802d14940300801180810743d40c0e80790303c4d0f2008071a0f4554228030113000042c4081c41d0004034000c450144203401c0064888041d156124841c1059070000004052207400d10464000d00300c0280148509a5607082444e0707242000e010030783d11800307031307010200d07446d0360091544404c1035068942c101032501d150010750b004901c400c00d001d42401040e140940404e01e511543d4060249905203580792420210b54524007007002e00d805001d005407610a10495880880c044d0446508030317051102c010340b00085030050705c0820b5005007440e001041c01c1c01403179084017801065503401c3c0c030113180e155030f012940c010100c0000f14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 353268660 1250 353267410 353267423
    0x10b0613061107030209070807080609162304031b0e010e04082a030d06050303040f031103030705030c03030a0c1d06030a0e19050d0924031b02060604050a09 69
    0xd040005900a9005a080c440e6140076100c2440e965004915840303401c0701c01c034000988601c00c001c00541c120701c43c1754000034141c0360090f4603c1e00d01040c04015600e0044482030040c00c1c428504010807042405a140004200060300c82e9524a403d105a1050303071625100d0783c410800110f0400707542214941280c4401c6411291500c0342e840b02103641d03100e80d07102c40d0102884202402800b400c401c1c982d41c10700162005560701c04018465208880c143e401882c0302e9042000100250320180b03819505aa030405a1a1404405a00080c2c42c40c4608240104030b800042440e501951010014502c105800c4006001c04121404d0480301c0e840081016001e000da00d11030f610f02420654080c0d1760161a0710b0000030a00a4070101600d0b10740201882101d00c1718008120081000500140b844032080d41003540f602c604060b2920700c1880f82914002500220400741d8840511030303000301d240c5490404420a5003c1000c2c0020340b59282240ca041c0150308150200d2240e01c418461400150341204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 353269910 1250 353268660 353268697
    0x206011206020706090c05030c0a03051005070c0b0f070e0406030203030a03110409060f081506010801120809090412020106170c01080a0609050115140406090311040608010f02070302010b06 83
    0x10960252508440c00340da1140d82440ba900010f5154403c000d031a90048410260796071810707003054030f48019201494010083c1c400100b0008100107032424a03012005e002182c5e66035291002c64010401003800f030294020807050041480e04030142c43d002d420320f50350304079040540c40144403e0b150a44002074050f40201b00c11a03001e4802e502560008046003011850181d8440241068031015046007a9018080c1c03000c200001003082003444415260541400c0d41c5422000a000f0700c0c014401d070452505404120409c0122641c21103140400c0280111100c0c205400d1401515007040c02020140d03103080d00201d0582c0da044450640044180020441c5490080c011a000d400c080c2400c2507042d120300000c254181e940c01205c1c00313800214a0010b03201e4031032000034540040c007649042120b2007040140040c0b0f13404902c04003502d4021003030580c0c034960710380401c00805480c0d10107003441d440c02400843c060075580007404954000c1c0e00078030803036a01341c0402051b8400d4130404848441c112 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 353271160 1250 353269910 353269919
    0x120f0a1725060b1009060c06110301080f060906071e0909090b010510140a050f0c1207030206010b13050105030903070209041b09050f06040504020d140105010612020c06011a0d1a01031b020601 84
    0x45602c507e005200300702c0420f0f1010884c0000c1500d402c2a001120140c000c882281c2c1603043c10000700c0e50210072000180303414101141d000d80a001039104417040510a5040c0c906958081c210b407100500c02d00314108040784180c1003200f6a40740a000f01c52150280d6800401150310812100140c1e2034001d00407440d0120459059a555100344105c49008405001001e89204180600345144802c4034000d641d0b0300a900c1c00900f0b181c0c05170400c544040c0c081c44490a07440410031400c01342c81c400e0802030365a0311681d0140b403460280c00c0001390701c20003445c00c210400030740e0f0f40e440300c501004a0f0300c554007079103075045031064030b904840b014143e0007460002052071034580c0189d0b410078005001a064090b2076250032000d00c00280350300c407140e03440308010040e03a680a034020080725009442181400700d00c04410382c442c1010302c2004201000f042200b0000d104000c102d6812160006040255049015500000501c0718030a107000c0780c606010442284400080c0c0e038290f40382ca90243c040e41e800c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 353272410 1250 353271160 353271167
    0x20d0b011d0f0f0a0b0304050f06010612090804050603090a05120c06060f0d15020319020405060306040903050408160e15030a0312021902010902120f0a1725060b100906 74
    0x2050000b030b40440780443c000e2054403180300000142100d0b40302c0e030b0360b0303407820b810b206150038140311415286030f2154004104a503442400066a22704000c2c0105144146051140040c015904000c1c0e02013000414007030040000107040704464440c5041c0d8800a0030035132503244500403100380000c06e404c8030300001c2c0700340f41541e00607030b00380002040000807442c10340710007401104c04100021320960000c00d0180903140c0b00d907180c124810400040d4a041d040c10045a80e90001030b04d254001c40d00c804d50142050702802c1a24080c0003a00300b10346030103911486000c5070b54514800c2e083c0c24040354010449060580d032102510320b0000d030003045240003a40d0200c94444144000455030703a4248481032130f0042e04030040d0a4480b040e80085134400582c010880a842d0328a00100c80343d021b5160194000e20102d0050390749030b04054121130403d00c042c2810483d00c0740b0100384050300145030041c00080d41c0003032581d411600032141040707050700075014040b01202c02c00c1094003007a01034038100b000034803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 353273660 1250 353272410 353272429
    0x8010609030813030f080d0b150703230c030711180106050a2106030b180d050f0d0504030201140a0204030f02040207020d0f11190b0a05160510020d0b011d 68
    0x485101da489169598541200000e00005c00700c901410004121448081c64000c03629850743c1141d01c1d400c241009030f0314039810310880e070000b01403100e5211034880100844807078040c0c080035085210307030740c0446081070f545a6100e200c04544541641003d0021401e02d00550351140c0356176511403a03940d09040e0161307500d422540b40f50381002000e070010900d003503128488180d401000d05000c034040e41186021043c401e801040346001100380c0380d500100090000b981e10007010f203414410340e141350350118803601e1700c81c160806541c81d040606200c20140c0c15030281500750756054211801c5c0d16090040c80070b07841540b101801c20840011521301501c1e203540105482807004100840d03d180d15516003406001d491826100b10007410034084850802e0040c144911070b4030404c1c0442d15092030700c040128007035062204108840856210007060056100301d804d1072f0814110b8014950200600c0301960140d4505021142008820f21582d4003a0100c20701803030503403020740302c40103405050241100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 353274910 1250 353273660 353273677
    0x1c02121e040306060311120d0206010e0c07050717070b07110108070e130f0b0102010b0a0b090a0b0c0601080c01050c0615040f02040b1b06061c150606030e01060501080106090308 78
    0x800c000000507007a413160500451040d41d031000c0d00031084081200c0c1c80c000c47c4036040c1981001a40480450380030400c0740c1900e41155000c1e034181c8514209070418010340f0030040c914491003d02007005041440315070040701020040301c5a258440e801c1030300b81e0150002c018041540e480e8510101c2d8041c000c60781d40103155280c0890103444c07038070015070488060000344075401c0d900c0c49040c05031070f014040c2011548084c0003c2c00f220f9843d40105260745080e02ca034a039402c40128110051b80c0e101c0700c11000074812404440d84030303820074100c15110803083c450b21100744180d5001150360750061040d10089052500500032580c0c90720a02c90110032102600d41d8402e039981c421a2115a0360b06c0604013410003408506d840d104ca01000b410610080040e00704198450020800d081c4e032000c11003450582c2031010b081c0d102c45180341400031030301500075052001e8182030011864650660013403a146d03240070000c0c0174040e0f076880103490f004000e00545d00010314449080c80455a080010401c22 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 353276160 1250 353274910 353274967
    0x16020d021f090204091b0b03010503100f020c070e15041a100c080307120e03091507080408060f0a05071707050a0e0a120b0a020301210f050f1c0212 65
    0x1010b03960000342200c0c29907800b00c0d50951040c0141944442c000c1e17540000c0e020070560180746504101c0081d0340d41103019504401c130340e12158080f078511450b406030b40403034150b10210740d03445403101c41c0b0492004023101c50380d81880580302086242e00c1e00703010300c480c41ca1280e1402d0040403071803c02c0c0400030004003800c500b8080c281036000c0000f403501d8000c600c5244140e850104039000b91020704103444a40e48200e80c20390013440b401d25581d40b012414004600c602c40c11540c0c601840c0380c55400d41c013446d44610f4190140c502004411290980950310a03400414204a1541e0740d10b010f03078041c1065803003800c45800d00000201e02e41e000714014151000c0750305000e21202d11400015410124903040031022041800400302045490740e6025000800041c0030340c190740c14a00728140b44404e00d003481103120040349410b000d10030410701c005030750398010007a1051002440e911958681d080c0400480b005449410003400d244080780348500c5100306a045850000b91084880089034250041001c0e03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 353277410 1250 353276160 353276171
    0x30308060f0a080708010b03030c0c042a0507020114030f0103080313061802031216080f0c010203090109030917070e0c131205010501090903080a050a0e120316020d021f 74
    0x55550700c030b241c07009201c614001d0400c107082c40c50640c07c4d2824030700000d000e0343c424401c40300b2038131001c14407007842d84003980c00003080110300150f88001c20720410724003000c03c90317070001c40d000551201c0241800c600030380ba80e00c007204100140c05154401120700041050b81d040044c000502104001d40d04011100700180960307802e41c55039421168115040000d50754504410800c40c00c0a20010000c3c0304501440ca007003000c0520040d0014900d100010b140c00000503441043c24141c0064aa440040b08021512882c010000b14000d02d0500341c01d80100c0c0b5091800200525410905d00c900c0750100060800d25107030200c9246c0002002c1e00000f1008400d020004291481c03d03113420040040c1316810a07510040d04020f800c4400603002015076034100030344100420b421001040c1c00c11019200000ca83d5a070804410090869000c14541d60142402c0482140412000745000e07921480300d0701c01c54a01d90f6410b80e0740c0c0401541000250b080f40031008640e2240c0b806620840820800c00b084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 353278660 1250 353277410 353277439
    0x4060e030a0801030c052e050f0408010b01090e01050312131203091805070f0c140105100314060103030c080307030608031c0507080103032115030c0303021b0a03030806 74
    0x1107821240c00840001c0d21000100140401590100001d2000340c0e802e4030713120001c2c001480e1030310b80900400c6014904000410300036100724115105c05154000c0c40d0303140d030b86035032045010b000c010304124005039501e07401080340d200310802d041c1200c00c000c00a0140e08000c1d5080626904086c000009407010254009800c0c3d14072600c80008600c00c0d505d6218080c140f0980001003121040d030008000e00e040104403031607030007003e0355901d0502401c0802c0c8001182c607028203d2911240218031650070035090004030408090000e05491190250344201150704a41c1caa541d00c092202030300180b071001c641c00101d48a0740003150402d449280202d202611445442e195a00c00072002845c01000019440100003500c12144c0040b02458001115403464038002d240e071940c5814000d1242c8100140502c5070042d40c0b064154405002c0c00b041e07282c1e0707a03041c80c0d130070744c1001c0c48250090700030001c03420401400e002d90729454040c010031894150341591011501c482c4014007450300280d100004e4803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 353279910 1250 353278660 353278663
    0xf021207030203010e0a0605010e0607051c080a06050603040507050415090606020307120c05100221090319140304150f020d0603061a03070311061909082404020904060e 74
    0xa200d02580e44000da42c0c2d51601c411307200581d0005000000c0140ba2000a02c01390307901682c158100d0408440243d2034010b2410054180101d03810014001003090380e2909180d5001413402d4854460040d082040c1c6a1322018040c491000b25401419604259801d001c5450150f0091048a1620004a8040742c0f45d008403c100c1d07074107030820800b6900105200e410041562806414542e41d0710b44a099040c803640c81c15510450040391500c004d070040355080640205d04020042526a8465000030341040c1d10315540f00c0d400300100203100e190300a1310024950045510020035142824800c0c81c41d5542d4540991003849041581130071503c80c4000d01c141103442c0040c1c004080300080000300a441c42c9001d00c00c441017100d1401104030008649481a500414048100c94102d414500c0030311400002550922030003140c0c03064034070000f0303901c01401e40c0b114008095550a6084910522841c0c0e560207001d00e07500c00040211079410005401402e0500e441c542103446040c01154550402d10420b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 353281160 1250 353279910 353279947
    0x905031908060a1a07030e010e100c0605100608010b1305151b010e030f09031914010b0103090c05060922090b0a0b0a05010c0f080d06080c010e0609040f02 68
    0x80011001e4080c4031407490104007800040191003032010040d04000139580c028054500003030140300364082d07010f9a50b401088580ca9020000f030812071380700c207040000b810f400300160b01070782c142d480c103400104188000d00451081d01e5136520395408a03803824200713404a45c0030100703040440810000000da6901c400454540f41c0c001c540e21030785c03107408081d02e042c0c44070b08006001905a0400701e100915400100460f201d6000d1000c07415560364908010915104000040310040a90003401c08103211020550010086e2402c0c024040340c4451001101510b0f1495005410368110400402651401800501107a20081c040d0000c18a002c0c2654080344c4405070001c01c507070b46644042c002c00406821441d80718052400400140e00310f01c2c0840e010b40d4560041d1810711002d001c4078000e0154008407240d00a6029142c644e54020b1860000d028000034818a0094880d0402d801c0c40c941c05800036104030382000d4501030030855000d04200c0940040020b50302410350030420010107602c0d16190 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 353282410 1250 353281160 353281207
    0x15040e0a09060f0515041a06070b0915100b0715050403021608160b03040201090b0a0207170a0203060f060a0308040306060e060a0305030a050304080904020a0c032709090503 76
    0x1c5a1100381001d40540ea800c1075940009807070102007000c01c841d04103880114000a0300c00055420040c1c0c4190100d00321304d05419405880030816508000310b8410961040301c4840541d0b00d0a01c6400c4008031052095880145000a1501c28802e184a1502811680f030003185802450810640c0410498406450640c01038002010500c1040c88450f030b0580141050030041c0000ca0510a06404040180c050460a400000b0104055a20078010800500300c842900c59442ea5040b45c007070350b180203521843c020025207481d800d240600202d8040411a0064007030681d9030798801c080f0b00302040050003158007401c109404004201d10b000940041c504c039820014460342406002410b078800200800c1c0b0034501b9a0050000901c007000340c4440c4040307402e0054036900d1b940b4141d446402403a0354290007620201d0b507000c4042d030142c000400140251629415481d00c40080708180e0203e07616214400c1e1098000c020340c0d400b82d4000c10342c2c5406201070340c1c10030341c00103800e074003682e05030341c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 353283660 1250 353282410 353282431
    0x50a0b0d0506040c14060417010b06040905061c08030f0703061208070b06030a050a0f0c03020409060f0608010203070f1407081308010b100e0904141f0b0d0b040215040e 74
    0x304400c00ca210740b0280c01620315100402c9620707148400180e401d07c902e0080c0200c840c1036080140d60a0000d40000c40d240c070300244601d0300c441e221030114004040440d034903407140014581d0ba046256021103c1c602d07260304545190301d07566408528003811034016140f001007664850780052007403014406031100c0b51040782001e0381c496560a00c580a03450141c0464802d0704001c0040c0c1c0000d000007202c050040e071189035481c001c14241444000002240d001941041c10312140700104241030f8803004603050781100800c00c868441112900300e000c1168600d0208140c400350400c10340c00f54a89808100d501400c86162503c00d41da0004290088a0602109210030f40706001143c400e0003080e01c118416503000400b0310302004010409035540a02c00c0c020135800003c0f40070300076000014a2500c2d00d0004480380e01031070101a441c0e85002903240969140341c41079141c80352503c0e8456030640c5030401c503c20041d850b140c017002254500d01000b0391240c0380801c07002401c0340b8405803180c800e00542030b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 353284910 1250 353283660 353283673
    0xb1e0301060507030315050a050108071101060b0c010513080d0213050d1b080604080304030305180a0b160c02090106210c0216060201151413020c03071a0c090103050a0b0d05 76
    0x134001d800d407100103010341002284481c1c1840390b9103400001c0070031180240381c61421070b22440b03802e8072016284055038000f03500b00000490881c8010004046204103103000b0403203a03841100b001c103008900c010041402c0401c1010b21004085500980b400d42244046028640e603503200041c1c10900700c00c41110741d5800d607045440040881e206c9940142344a07030203050070b86410313540c41025210040000301451f542d0303c0811205091100403107584d0000e10304940c003001d61030911a0090030202e0718880209000403184c0c80c803d200c2d00a4108480c0d02600c0052541d00301142074418019a02c4c0110720310b011040201c004002d14000c6030404100e50f005089503140e400300e145c0c0782030000e400500c1903a044c4020000298000000c3d48112600054038150b10411440020000c1c20301e0b04445043c40d0001c200b0120030706000c00100f21082c4104001140c40301041c0d282c034460b4004035560395150105104040b030550107600007a0340080781d110000340c000b00c0c403400541c1c4441c1f681d005880590142 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 353286160 1250 353284910 353284913
    0x30a020c0f010918200301060212130e1e06010c030e040c0e130506010f080f040219090c05090a06020d020331060206060f120a110402040b120702010b040507090b1e0301060507 77
    0x101034002803a0b600c50161791556040c103202944d509207028582020841c0040c40c0ca14030282c0001d80005000c1514052050b800c0210380300e0300417005104075012400740d07400824400d40c09a0b00501f001c1c3d50603119442d80500c514100b1004105600f518030038800c400101c01c07003640c0e500c685010b64880e400030001c2d080c1400320005044c00602148101403220510a105008008018881e4480e60403030710b0030910800d021155040d40c51a90003100c00a0030020a140d0198011000d85003000c016604040c0c202d640324000caa443c4d643c2d049050240c0c204000c0c40800e044950200c2168401d1000c2100c41c1d0039181e450403205440c981d03c00f00068000d40140b2a152400e1034007910130400403540c03491031480200a207621100380190040c1070b00c900407000c01d1651966015900240f0412580c99103030900340c0b0329060b03509030849101c00194600078800034545428840c2c00e004900980d100c080c854100340b248000c2d6441250b101c8240d11010700d00007408404a001507020b040590b036500d072102a20b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 353287410 1250 353286160 353286191
    0x60c0114180c0315040b092d0c060a080106120207020d060203090d0309080a050a1101140601023306010e03072306030103051c05070c0f0314030a020c0f010918 70
    0x2e800c424841d4225081203201c00c44070102c1c607034109402c50303541409929501c4030180f074000c08401c40100d651803160072500c2c0d403504412044809a195041d503005030342800030000701d441206900000700300e8560040c0210751180802c50400c0003000c1d0018a0b00446400088100d46406c00403202c403a000410040c2d0820700f8003601400d000c240c01e0500c51002d0f181e50b010520300070102007078200040404d1000e206031088003000c01c0702401c10020484601c1d078400c000c210320700071902d05e8050f200310b03d01c504580d2514052608602da044d011003032600030a4500b0072039248040c0a5038100700c4181500c4000e65010b1054400500c0541c07140641d810b40c20112002010ba8081e0030340c4070b20024401000032843c0880c88906010742d01c140701600d02c08001c0c2c241d515029100300a09640300c290004076a5807040080c420a4a0140495205010f044403c442e600d102c7c9140c0800143c020518000403400c003a09a025454414180120180d4a41142d43e040004002a403400700382c80d10148a0304802c2d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 353288660 1250 353287410 353287423
    0x3110a2010120c02010f0e0606090601020a030912020f0907090503060604020906040b030a022817160c0312150302040e0c0105040e040614010e040c0f080c060c011418 73
    0x94485500a41c1c1088000d018105040d6003154500d440749012021030b8401e600c07002c90008800c2007040110340c002c106076500c0608413140b0f17026104040c08202d840d1b000048030542d2541c96030702d00d075441d41800c2040340742c0808120226044002140c0018440d55000e00c618850034055840c00002807600080600c0c00c00060900c0b03000e58410020803040e501c42104680548107007150f02c3e9902e031551603980300244900c03e0b0550360300c200c41000c01c00703c1c0c000030b600c0105403440ba9180f102302c01c042080d00401807010f580c1d980c04206c1c06c401c0d09843d28011808002514041d041c1201c0c1c0742285000d58042d0703920300c1441c040d207204800052045281c42d05c91102d25000d41001451030042c0c080006c0d085200e94056884038022140c00a01081525084a000d8552502100c2500e50b910007140606450540d4120f4110350710603808101c40b80c038030b0710250490312030000404042e45124140f0100307600441c503103038085d52103c2200722490803055101c0c1c000d58a40e0396107901c80c1c2d4066404c0d0b00348903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 353289910 1250 353288660 353288723
    0xf0405150106020a08180303070b100605181e10030905070e010b0301061d030a0303020a1d0a0909030203120403110d050f040308180a090e010e0a05030307050703110a 73
    0x100034000510045500260081000764403000311030740c0381014056070131107039000b100301607040c80002003078020400c14000e170340c0c012603041c0041c000c0d241e111041611039020f00385050740010080b2040c046103107003041a564403440b8043c224406e220414022034600c1150b0050b9502080d00c0b400c1341c00802c04104a000001c10180302e47c0310b0300c0e505003c04103001c0d00c0b0601c20344082041a581d40c0f0b0008020081e006d111880007170899500d002a89000b4020303400208845020810103c0d06040e10b8074450f9507542c4203c13004180900303007400d10400e40d005190600040c1c04600c0180041c9144164a03085140154026100d4004000a1345400307442c00c4c014420000c00c0007820b000d2080c0c401c8041041d82d0540750b11088a54a840c40c5070101444600200030b447e5009955080000d6000c05581c4140d10101c0910024000358980c1d2110541d00c0410140007045a070040000994030740c440d20251500034440e16000c0912840c0f050b4540c50611411800c0d05c0043c807040301d100c4410580103500d032490 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 353291160 1250 353289910 353289943
    0x605070c03030e0102100504030801050a05100f0f0302120a1b05180f01450b090d020d020d1136180d02010204031208010b0f0f0706050f0405 62
    0x86040d511110101910700c401014005681884a1142e00912540c00302070310a1400304490710340350400508803a070038403942d801130032000008102c5083c031101d00390760007103035407543d041c80c20301203004607520941c803552402055404c0c4401c4030842e004501840c00794418013008030303a210ba614200503440e0b402c1c00300b10040c45070030402a9015002c818031500010b03c00c8401a40b041c2c2d0050041c6c52100c944400000c050002031405140d2030203152400c0d0b600c562500c980444d44640c1c1d5100001d1103910f00031092801e0007400b41240d00d180601a03020301610207403040c4c0c0805410b0b4040b501d80d18021100719807100d000040c0003854203100e0031590815207001480c03803a12220080c25401d6443c0c114007541c0205d117150000701c600d0044500380721800004002c8861103c52618024000d4009000440e06072440064100700795100d030748414180d03201841000d1074411881201c500d554040c90002c52041001c0c070441c00070611038031545120b2540e505468145180610b043e0f0300301801c000c104d0908 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 353292410 1250 353291160 353291167
    0x1b1706061908073c2102070c05030111121e01050f0102010e060112031101061518080d110606011d100e2707080c070807080d0f0e070605 60
    0x52045401c80700d01008441e061010341611070440403210002c2d90202000500d0f18a01c8803400c90054100719110110100804419121450400c441c903c0c40c48401c1d038001c494009008104090b564000c1480c24441d02460061a60341c1000c28203607150034404a03480f45010448a0910014142d1240d002c1d4980007007042507811030400142c50201070007583e01407482c1e50f004103616400ad603c0440e083c0001c000b1074110350394170b03201d003421004001c900b200080d58001c002180781e001405240c09a8291001d0702180108010080741c0c14444000741c9140d0001e20800091401d1092080044d451101e50310002c041c0140c010075842c140000d400c041c1009851220700720b600d01a44d44800310b00408895040c4104103001c002c55010ba01d404000383d10020f005240c0603c0c001c0a000002d03002c4280036082c0240d6603007041074810f00c40881e010f079161b200c03c10121000500c107038000c1c000d44e88511b403000d003002034900e01c0c00300711211029900b640554505040c03a0701c01d01000110020b01c142e107081c52a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 353293660 1250 353292410 353292427
    0x1051507120518090c0405030d0503010e0c030c041805061e0a0618050603090d031803050d1104180603020411090f06090607020312070c1520011b170606 67
    0x52000310000d4041c10058085449952000c001c402012010030040c4144054106094203505070740c01803040d188203100752650b9140c60f030b0069061324126020711090810365501d08600d100c80346d20081c00310450701010800415220200f9180410b400b020308800a0b035464110103011140308001d145083c0307030100350404d245ca0741d200f2032503c043d10f400e884e0440c01c0400d07440b1403102840301904001e80c441808810000c49103000034000c03041e01c1c02c0e80c0d01807003a43c5212400e03c902d07210201000c0c0005e0006c001d60171a1190315045050704d09102c010103850a6590001403940d680000031103860191600010015454603015201d159481115114908119000081c0d400c1c035a044074035020355000b14900e11196203160035940d400c0e03005015500041084070b060085540500d00c100c0d240c010744007000c60f40c566070095040700c00401c0d49905440c90302c482d0104a0200d00c01207400c089648806000d80401440c035800090740010361101040c0c80304611001b4441c4034000c1c451030107a00c05101200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 353294910 1250 353293660 353293673
    0x2030c040207231c020c1f0203040e07120903051b060114010309080d1509060b041503090c080d120f1b0c050111030c0304050c01021209041e0e0601051507 68
    0x980760750f40958404040141c03695040c1041c3e079038040080d90103480d48051482030340109803650b600100b203c0c1c0d40842c1e1032102c4d140343e141000030080001648280424030562510380700071078002034181888000450100e0006060f500c1e280c40480001d0004180d544400a032405100c501820b500050510b640c1001e0107040325200040300f0604050303c90840f02c00340700424040303c100c00d00112080c000302c40c04424070002c2180c540314400311149042c07000105c4424a5041d01c0c162400700303840424056140f0342c02c501810400c50156201c500702c410004000300b04018400202600307444a10120b458920124115290b0740030400005003801081810b03407029105a6508418504000c4048480c44c1000c07030042400744a410340a07000001403101004e031001c0654442d501c80d41c100c1c0c1908003038200480c2c075040c0c00c1c2148080401e003401044d00c103203426003002c1e04da81c0c04450204840320510340c41744207540e100810011550840801805142405840400e064074000c9005140810581d20f14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 353296160 1250 353294910 353294933
    0x6040606080c160819020f120405040506040b042903010501031121030d0b1c150513080d05100f12060f09021801050f180408161e02030c040207 63
    0x2005104000280d66403000310182c81d1200d20f0790031001c0c464580c00c40d000712551801104801201502c64881186400000000c000340320740b40751001c3c0d40c101890007051101500e00504429031207511641019415182c610540054160442c000894421440701400e4510502c00000f0300030703410a001030010035500503e04034041c00550fa100300345102c2c4d4501c101e9607107071403005480034000064180c80948268010301d1521104980f4440c80c22080b4090101d040344d01c0b103004104810342e400c0481200310030b610550f800907614120101242441e52a1803072580000d400c0420076548000b48800740301e40c2d00d90314028150b00c0744a40f640c0c81c01d1040305080c40031a81c0c00246100c1e11000800640e112036001904020b03030150000311400d9040b000a15858006d0003501c0c0100d00f070301d041c28900d1400310350075407003100d10140e16a0030384c41d035445440d880d9100c80d0724103007003036548002140080d22619a0701070140103d4050480e8150600c105424a0103403103a0a20440c010300005010a8040c2042c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 353297410 1250 353296160 353296171
    0x41104090b012c04051006171f0e01140f0105040e060a0906062705070219110301021b0601030309080307080316120e011d07030b0103120302040b0a0302120604060608 73
    0x190080d110f2007409580c81a2030745041e18254207000c3c2c20b01041110006030000500442c4800707000f51519001c0d81c150341003a10040e8043c1384c1c40449a82000031040403141a20401c655022038100c0700340351000d0079502007000301941988450108044040c0b00c80803076000d01000c644c00e0040801c202d9030240d80c1c060182400c000641e55030032040c00c10681e41d00500042c080702c184043c500382451081c0c3c00c082140428045c4942c2040001240720f44040f4140070b18284850b40c481035084261281d039680ba007140c0340c00d13415641c04c00c0510700b1030010f81e41c107103507002c0360310b0081441350304601e4010403080c26584041d209034414003082000a03400025a0b85c841000d112030b12003805c1c0c5090032103100311100c0715070030580c0c584145019865010741100e070300034041400b500c0c3c10070600e00784a0380c1c0311024400070b00085404001400014508140d02403107903c289000349c1401d0703e0341c03200122540018103e2011a60015041400c01010100e0303550002c002c69041002a141a00103010f00200801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 353298660 1250 353297410 353297429
    0xb090a0606060903111e19030b070c0311060603060109020c070909051c050a171e101d040206032205030a09090f0902030c09090a0c030606080f0604050d0e01030905010c08041104090b01 81
    0x55400c2d80704115001d6401903400050012860401001c042e2031761642c0c01d2f007034000034040b100d0100041c0c0006810340c01604080d004004036071030000c42d080290882c10f00c0c003840c0e02682d0b030005a0703843d03140100c440c07890007403001d841082e0a040f03588030360003080030683c4240176062001065154001d240d0041600603040240103079a154944a11082114a004101c85900b40f06000e100c00400101e9002d644800401c078903002680840143c01c29000c4400a41c49041000080d0541007411081e144810519039900c0748034015035103481c1140c1003844880c0003e1261041044001d80c80e02941481095044081242d1002c2c0d4020a40790795080c28540d0080a4080124007415402c000b410181508144a01038154a901e050800750071b1610034088d642c410052050101400803035464010795000009140845100c041034426043c5841000d0515554142400100d203080c0a410101d408542d1542a0b40c94245000400d41500042d0203001d04e20741030003100080c41500e21941540c85401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 353299910 1250 353298660 353298679
    0x241d010e04030f0c020d061b03141311061c060e0621070b0f04050f010806060a030507050f0414090c19050d02090402070807140313030b090a0606060903111e 69
    0x1400351254813a034030001350000040d0f5819418070880c0d60000f00409501c6c0c10104051505401c110306640045a50781c0001d0000300210b0b518166900b0104c0c1928030a104803180101144e0018030030b80c200031403401c41e035203880440c0d919140051245901900070865501c4060500f0f9000c00d42c01c3d00c403442c0359402000b00640302c2110b05410000200144607074010b0030b40d03800b84c7c1f20b0007103469041846050301807519808103100e40e6009499513403096002500b042d042c031706505422005032101400f41020300904101d80c400c0c80c00d8040007800980501e4080744031500c204c0c4240040750300d008229400210b814410741c010301940502c46213196200e4a002901c0300d40c0081c80c2d030000d105244003154800d00c0010420104029003010f000007034001d0400488290b0b960a0064491041080c44000108958030900005c2c0e1110001074222110350108d4000d02d4166841400f00d0703490b81c0180c2c0118010080801c00c01010a10468a0020076512000948038042102849121445000d031003900d115 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 353301160 1250 353299910 353299937
    0x803102306130e0a090506090a0b270118261c0617060702070605071e032c0a0803040315021b01050f071b0c03030e0301241d010e0403 59
    0x2103420b0081d018070398a0a45500703003590103000400340410100c030359014a00000e4a8000c02292804c016500700202d44076a60b1003501080328100f400d6030341240d1f00c2141207010b041c180309106040388628a8a41a07842100b00e081002050040501b44880c3c081c41441c40e84850491501f03407900032031b2584101d03400d1006172001c0c1c800b5005c1b9410002d0089149040f00803000000035100d8080c01494080c0c48803a6100c0c6000c48091003100c07009800714019103120100614103120407880240603141c4101144007021541011001031824810281500809803529142001d03c04000b0300c481002145040d245959810b40c030344c1c600c40d0b40311140350f010840b41c51148800384812030116000008103c4c074074042032032404100e002da403004002540c01d40700b8880e80b5843c81440d00000d03084030784095264615a0101d80c071060b40c330f400b140c0554031010004e0380480750400b215a0084442e01414006040c000f1100f9420520121070071120300c000010498118801a1241c01c543c045c5481420800c18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 353302410 1250 353301160 353301187
    0x911032514070b01290405010503040201121a0103050a02070201120e03130e01080105010b0f0702040f060b0409020918070c140a0803010605130f05010f03091103010203040803102306 80
    0x1020600085160006074071410450500c0703141c0d041c0c0300440c0702101c030100c0d07211005c03080d10368207240e80c080c000040000f80215030150003c1e5030304c1481494a00241d40002500100b500c00f10214800d109488801c4071003603680502075558044040c075000c50a200c0c16800003400c90844440c81d205585c0d03601c0710001c080c031040c011241085802031040c4409595141c401540e240240f15140c030703951a160001c904d9054000c11562428a10180b581c10540103408000c001e01e8161200020269140000541d003113510014000a08000b0001030301d81120344c0912560246d9047c14200b65191501007124542e0003944101c120b0f40c00c000006101a000c4002c40d203051030b103410203441164080000501c035544640100703440000d2003450100c50b5501d031f2000d010b090907030090902240b418150010640e201c2c0c1e006031840c50051000034004082c40c4003103822607000380c5059030341007000410094003254905c60007004209080a420700c2c444084800000401000704e001e11030000050503240c41d511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 353303660 1250 353302410 353302427
    0xc1a040905150d0f060b06030610110a02131a0901081e0307020910081905030301060e010201060905010b0318070303050405150d0c0e010f0206011a0903030706020403060609110325 79
    0x201400140b041506814149030152113840101e030110b08240c00f81c5503a0900d001030700c1c06070f0303c042c2001c80c28150754101500c500243c5151142940f1030210751001594540f07490040550720540001175104d1400141008010303ca4a4180200818001004101c00c005062920403210714003041400c080850f54600354450240c0296005a0030000e000da0341032040c10316802c07502c2c440301f1101c1c000c2112000038140f000440d030180031600140b0040100501034020341103202c44c14400005c0032038841840c2000c480c002e030460041c1c0d0b180841082101210000c086580f60746c041e0081c80b10300d156640c01043c901c524021203000d1810001c0700c0141958060641307107001e0f4030040910194514100041c14181c0022a090000c0d1450180004403800811a68141d585120b05451030001411603540365900140b4060f82520040041c40b000c40c4051000d0005184500b00c0415424508180c00040e50144100740c05442e41c2001403003662240d46649072140c00c61620260306c4c0400d50041500c2440703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 353304910 1250 353303660 353303701
    0x21100902030a02031e071d0d05100b091b0405060702060c011a010e2b0c0f0b0a09061119020307050a090b0901120b130501150803070c1a040905 63
    0x103002009000450210740c0145200d1480d0010400000c0b40c559003040680b0b00a0b12040c001c1200132012414140d840741c00120a084060410100401e05544440c40d240c007010a40030350703036900c40e0410718501c0c0400900d03400c80c9080030451f4984071044030112031f0703200310321410748203480005481c0c0c11506c42c201500c00b0900d0ac1301c020814090340b2002046488550810180000c00e946190708191500c0e4008801c0d0f1603440c040c1c8551400ad0181d001409018030200385c40740c3d0018480080c0c0c40302102118406006c0841000d612019144005080d6042c542c0000d020710615066120b0320b000002600106d0241503082c0300c001d40303564000320307003042c1694002541046010750082110801c0b50040c4031148416210010560703a07403140e034995584070040050171007842402250000521000c02016140610000a030270400d114100d130001c0c24035440a292034001207540000e000204007260700405c3e1003258000500000800725505114038000c440c00907a0b40d9001c104038415a110500885 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 353306160 1250 353304910 353304929
    0x10518280203040515011226070c08070911030f04030c1b050f0409050606090a020d05070915030c08070302160c0608040519020f0d050c090a021e2110 66
    0x2640180500d4060741c81140c042d1190b100b40c9003004500b02131280928100c0b03982004e240001103d0741e0342c400c0e40d8000d906500c01c0751030750110b2180b0700c001c0b00c02c010324070240314a910740c0e2030b40d1030105550708080c440e40c81145d01d9890030306407101a000d0141242c0d4000c0c4801009000c1d03546500d015201044811405049030001c210300301d12182d0f02000d43c009541c41143c450881400394020441a41e0961000038441d81010340403131264100442466040b110615001d81045141601c642c00c448007102c5120001c0c0d0551010080003030180300c04003a80c9403914040c44001000d14015019040240492041560008001501c4d46203030581f620400d42c0108080d24040c1d0345c4800610880d000c0c1c4040d940350041c1900c8100000b0901006a41a0f0b0f0250019650b1404082084803001004409403454040c40b41620300568072100701ca407040311080001a21007918410b000500c02e82080111010f20702086001800c0340030041032440c050510f0084811035841c10512040e405d030550151075076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 353307410 1250 353306160 353306221
    0x303110705100510240c030932011112160602040b0c010608030c0a03030b0607050f0f010509010c0206010306090303060b030a1a0604051f020715030501080c09010518 73
    0x1110564201a0144804c20f0051020b0354503041c05106020a80c07101c11340340c0424038068070095008075031740c9140364040d08003028490307039034060313039194a0710480a43c15002c00380c0c518512130703a01c080300d0030a240001c0c6400b0b10b0042c0c5854540e942c42e01d80c9004503200c094041500c15030b1b0407805030750043e542c1d4071400940d11b8640d00c510040c07c0c5d4011910351401d9500740b042c003041b504000420340d1041143d480003440c5500c840c0d1000da00030803c2030700741c2e500410104040808180100081001071015000a1251041c01c1c5005800c450f0081e20981a0741d040903403107541c00783d001a0241c15aa00041c000441c103001d454254018007095100b1403152a0100402000d83c000780c0c484168000d400c4062040041c10004000e000e21450003050790148491444068606c501d03601050044528012500e02d00d03141c0d03413400150322600c840c050001e9140d00040c480458107011842a805080e10f030038225504040000e201d000000810105048174200040c0a6030208022040740310007202c0015403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 353308660 1250 353307410 353307433
    0x10e0708010b03190302071707030c031b14010f083114011806020702040f0203010b07050c03030403021c0609020d0f0b060a0302210a0803010902040f0e04020d0303110705 75
    0x42c00140c032801d0700ca80550814400041800d801c20b0b0b400e2a0b056010381101402c04c2004500101c0204000c402d91041da100480020383ca0240b844c0034502503030121b0040d0b91070b52240c22442c02c4982008111181d41071140c8550398010f03c001c1e03c031603280e0501070820303a141b0210604488180c030b01c803e19003111591144844500e14191011203004844d41e54002d40c00752181070a940341074130f00380348001d070140d0198089a155400782207030610052000c903000140c8140c40e070a0740c01c01c3e0058180c0c540b0000740ca0741044403c00c02142c2411003038010b142001e15540010b01d981410601c241c108160104621080051030360058001e40e50052100c58036000c01d0400c01b0354450350800845154940401003107232850864101000c6a6004028030a49181c171000b00007d00c403200c45000461084880410006080d00061406000740c02401070320340b8036145c205100404580d020040c2e412005040c8000350311040124000f498140c1000715001c0c0081e00070601e10303c0b1784c4402804c140140c030740c04403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 353309910 1250 353308660 353308663
    0x705030106020d080105180603010227010e031f1508010c0e0108010806270c03010612030e0a060518060405040216030e101e110307060603030f030b09040b0405010e0708 74
    0x103059a4466086641d80103c80f00c2c00c1c0c0d1020b800f8026285d201d10000c8454034000140c21f51940e1006020b4005402c1251810100281c0041031415052090012031400f1403541e100220090310001100204148844142907a494094011081c40701c3c0342c4601510740307000001c5810000410201d0020082840300c03410041040651000060000d49064000209000c2c001070840c0201c409001103985030002e0b95280e1195130218100e04c1a40c000c10303410a2045d9000c0c40b9900c0103101003000050110010316005203200075441e050ba10a51020105120b542d50040a03202c07001e4402d2036201c240200c002c0011414051503004583c010700016405c405141d0300380a00364814840d071102d6020805503c100b240f40d00c0580301001c0040e12101c0c0780c110356542240c1903181c81c0410700b461070710f24018001c19411540205001e03a40262110300c20010103600c039031100154401440c040204000c024009144d200c0003400c040c0c801c54094000ca01808030a43c8103800b00d0090b40b04499905070b56031100c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 353311160 1250 353309910 353309917
    0x20a030b0f1902040303020309100e0312030406050106020303071d030703060f0b0f0103051504020702041b0f183c090b030c031c08070c02030307080301090f0b06181203030705 77
    0x1000c2e28401d035103001425110300a940542c1c0c5d040c2c010b10704124110080c000d101078610544000c01082d54144101d40c0c40600c14122240803101d031a07680c0785801d08004095800c1a4440011940104100140598413100d4058010780b100d000b080d2254105001a1406050303130000f40030782d4078025800c0c40c00300ea990b010310282e034401c0c0c400f00d002d0b942140040d411150102c0b07184003c1c5270b114101440a2510b0380c000c1c031b00148001c00006580c65030f1241e05040801139849180400d4410344030094094000100c4459105440b1188901c0c6040040244040ca06500c030004804841401000d140c118000306410020318649a046160350b80c501d40005001c8904805000c0d01075010040807600307002c24a0140b0004811050210175600d0368210fa01040044c0a00104500d000f0700c0001a0f6080c00109442c17400740ca40d403a01c03035040c43d04007000c03208002d1403469028903102021810380c440c00f0640f507009000101d0400028004408145030301c0324000c0002c01d500000042002403034126014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 353312410 1250 353311160 353311171
    0x3507030c020c01021f020d0f05040506481b211204320a060c081b13050d0c09060605030405030306060f09060c0c0102160e060d020a030b0f 61
    0x894100d102e40b04010390f2152807102d600ca852680600c404602413459030020410708400050004045030030361400800c45200b0740d411606500403000b404000001c4214036808120700310140322109502038003502560401203500200c0d41040d540b503440031104003050b40c819800844090300c44d00070500303280b92180c098510322001c640007510f4285203010618107407a0044802d0f050810503860b940c940c400729000c040700e44080804207880c1000700c0034403522a05900d442d20310017400c1000051402c5000c2d0360b0204280c034104841c510400c40da00d900003a48183d600704520100fa9501c0075160320306501c4009400450300562881880f000b0440300e90030880c212128204100020760320f4100480f5a0303c4182d0b40603102e41d10500100c0d1051810034001d010702e1100c0c0310b0452070201024003142081d00b0400090b1080c1d04a031410a9265070144580414001b444012094041c140070366840101006080d46000e40c03104030310241151501c0143c040a1508010080d44600e0002e05588c50b00c0307000c485 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 353313660 1250 353312410 353312413
    0x9031b0608090f0712210314010b190806013f02040302010f1d04060305010c0905010201020a23070605091c020a0201050306060304020a0512010b031c3507030c02 71
    0x10124500403c0311520840800d01a140692502c02c084820743d00c030010035650481c000d101c2e907100009107400708054402d02e46000c1401c3c0a09a065015080e05a1100034040c20810405143c003403846521a040521810906c0c03050701c60900484182030116509503c035558148507801000b060814541c04100011a01c1d5420315458012800c1e80035505c002400704480000c04c90100740500361510b51440070710210740b40e02c02da00c1c0001d03050b540682d1082e541c0b03945d581070440e40198420710140107030200b070000354507011240e50300400c00d41c0c1d030000c0070b0b440c3e0750350f005c2182801c3d42000807100314a81040c0140400e0808109182c1c03640107292060b4107103010389000d40d1800340003141030b6218640584560741556100010b029040e40014012030380207562083c00b040c241d680b80074904003814080c0001600c9a24038041c03518112100702c035080c01e00f44580365017601661001150b0a0208110b4040d21440c03840007040d054140d85d030842c0b09055600d2420802e1039036040e48802843c030515030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 353314910 1250 353313660 353313677
    0x907033f020a020112140103060f0c020105070e040b01110d02010204081c0c03110109050f070f061404090902030f06041b0b120a0b030328030b10090905040309031b06 73
    0x1201404104445214002581007461242c0240d80102d20361103000c44141408a00c82e404502000445070098108076222a40d544110115004502c00c1320b100c1c00075400200180c0c204010050300c03580e030308503d0b07920560329561580081e074130a140c400c405201348400c0301c03800d03002c4481c0a03004c0e401c64003d070302161080030440b01c107019000541041c00e42c0e05840f200d0450085850440f10f03c90043c040171065902d41588100154040004603003005480c000b42a50310f081c900106a00b0101d94403660400c0200e80090200c050840c0c02c41c7d0849040500011780054144086401c005034101d9604190203400f0400040c03003845a038481100c60145401500346071550082400e40c020140c4400f620310340d44000a92100d45540f0661051600074200c82c01d010301000c82c50244903035800100c02803001040519062074141c0119800c40b54101c56400c3e0108119000510711040e620500a9498645010609050003146020060342c0c000c56800796410f1404802046a2014400da800095604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 353316160 1250 353314910 353315003
    0x10c110d0b01030809361305030304030f180609090c1407081c0509030a0309030207080a15050703090203120913021b0c0f030a02090606310806070f08090703 69
    0x40303e06506c0f080d44114005c4242249080810f00c03644010801c0e80329490200f000c07800302e10104091071049109542d0203061007014240109207140030f00b0403401540007924240a420380013401c0c2c00981d104200c0c0000d145043c0c105c01c49026000d02c049010301c080000392070301401280c400902d140f10076240c0000810174000d04490440300e0443d003c0038590400d0201d440b890303100e600000c840c18082e104480700c490319189404d0a10f111000c0894000750203c04220b0307041d17414024a46c0c002c0507820100b003c0b07a9240c020075124481c074a03034000311003c0042e01c00c1490340c450031102c480d0340f480c0d4800c5494102458003118642c0440c4112407641c0305644d001131f428541140c0c004414180600585013021440e07003072045407c409850240e2003174040c801d9950725111403030350840b050340d00006800f0940102c00c030f0101c2c0c4001900f250006422003020011900d0300a4101d681c0003800341345c003642983c0c884403020b050803400d0300b0050803110440c001108900c2e030300b45c440040c0030391400c40d1003204480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 353317410 1250 353316160 353316199
    0xc04210b070212040e040327060305180d050c10090b04030305150f1c08030708040c0807240c05070305060106030f020c070e06030304080703080d0e010b010c110d0b01030809 76
    0x448203543c010b4104010501040000451054000d4480e00b02002d4400c3e90b10321101521441000c07691f100020004204a03150307060050503000034620860318180000c28045c2c40c1c40e030501d03490032418410300241c0305405034010025a034480541e1103080091200d145000c0454110548042e0700090a01000c102e904621555411041d00000c0014001482d424140038420443c4d00049a48030b02c071550ba9008121030300000c6101d5511661a071030a850b051610200000c5c0703035040b1207450382c481c448c01c0c8404c0406004001608194500b40340c0c07002c0984500301d0302c030303a0301d640001d2903806000000020803000083c101c0c141c0d81036440c20f20144e045c05540001b28001c1044030200e560080e4800c204400001c190301e900040060296071800b5240c80d1164074043d4540c4c0110361810002031110640f900720301c50301c030b2070102140083c00807000301800204103800026010700140c0042407a401d4640d2107010303070300c0c0303550784130641c985150781d6400e08006a4000240c0b40303021b481e460b40703104401c41c41e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 353318660 1250 353317410 353317423
    0x50f060a09171f02130e0a0f0e16060c0803071d0402070507060f030e03030109090218090f1c0c0212032b0b090906370f0b0405060102150c04210b0702 66
    0x80e05c00d484600b9803509241609409014100f103018a07071351403120340a00d81038019180c075148401c0c028840c140c0000d07951002a40c0b01c0d44080c0c00c100b041e245c05400144038400320380d0032000d54509491000711840f030400b281d5402568596010348009002d80c1001380c04240a01100d40300d03224000c0d03241454000f40c0a80701c1c0c2014116481c1c00810042c015140580d20800c242070026040c07a4513203403483c0507001441800c1d00c40f0005540081d040c0321961000b08030141541c0c1d000041c00c03606881c0701e0009401c02c0c131210b100901c50b2040740138080420350f0030000d50310002c036508039040a850300c40c802030003500f0064100c000120305025030a071447c10010090341c011804080240010381d03a00c0101c80c080c00d01700d01c05107807907403504002e48504d0300d6103680c050b00c1001c00c5100003059604031046104441180720001e00440c00c110800c0074503078020690115003140e01140a01c03551303500f0f0034507560740f180b50482403403007000010000c43c6128241464030b40f540328030f20748041c030389034040181c2e95000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 353319910 1250 353318660 353318677
    0x23010311043206040815060a030c0b0a1103041d06150909130506010605180d03050d09020d0f0305090a0605030c16020d02130203060f0109050f060a09171f02 69
    0x3900c07020600001014a074800400006031040c9168640b5001e0008085504c00e41c402000e5a000f41d401007120b00944905581015040700c1c103c2d116440c580d50b001d403e881500c25901440760100c0c007214401c0c018441c448200c102c00d010f4950b220346480303420110407000345600c004004081d001031800d04090902e500c1c001808183c080c2000040410000b8025000b030010304d00c140c01884400010310200f180a01819650311103a8595400c001078820308005040f03014410310480e0880000311b6009030444503a119007110200e5155140d0003ca0080e00029400401d004104104041130550002c040c02c048541104c800342c401d691070108644902042d1040740d5150001c00c14120300c0f4500261181c041480688810002609900058801c1100701c1068888640000401241d881c01d00040d016a50003401c0a099241c20440031551068141c0d9025016180c00581c020200e40034514034002400103030109280c1a46480c00b65440314440329000c0b620110403600401c80c00320b580240e45821 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 353321160 1250 353319910 353319929
    0xa1101020c10200c010507030b040219030c0504030c030b0702010507080412080406060e0906040c050109030c14030114040809041401060e01200106080703020a0518011e2301031104 79
    0x480340c0c80c50000a02888602c241802150111029450103c80c0900320000450000040710324080d032025040d6501086a148a03901c10007040b8208200700d540810f09081c14580003030510150701e016103ca00c1140c002420b460900580002007100344602c4900c039a4240e402441603449038036050350111000c0c0c4004180118540b41000d0541c070a0109551007801020007042c000e644145c00c2c005048166810301e4240c100704c0c03c003c28012100c06a0b80204001c0c600a084076203103031541161040c15003e06405020300c0d403402c0505a60035008080c051244644809a600700b6103070040c000e0340140803160250b41009415103801d00001a85d5048030803a072541c02d5942d40003c0116a03890102c0280000c0710300c0ca10420044010901c2a0030280038aa002007041c03e0842c01000314013a280e601071403203076000350700e20b0885e01700302a00176046400c0b0b54002003401c000740780c4c0219070f0242504040c1030002d816998a20000e0451040d00f01c590080c1c03002c2088080100c1824524400e60141c00d480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 353322410 1250 353321160 353321173
    0x90b04030807110603091605060a1b0609060509060a060f05010509060703200d120b010c021e040f051e160f03180b0403080c031006080720030a1101020c 67
    0x1003101d120041454a03c501c3d00c0d00806100c010005443d604140c0d0310381e07042e9102551403c040400b01b03181002403d01107503010308002c010320300205619081c0006410606080e08018100412500444081580400103002c3d5260540080d5500c29045502d907564a040c55000503030700d8280070b1607005071030042c0e480615000106080c0046a0301c155801c40401600d0303540c24401c001c82e059081130402d200406040d02041001000303042400c042c02507410240f909030f8521607613800c60043c8a4281d41a40c80347e000c0c031840d901d40380b40d41d544040381c203070418101224407041c50301030392106100c2c0340702a80b09400c0c1c4040d156140074404044071012900c1c44062000b007000c81c042d07192034072202a28a800f00b039503018841e080c0700702413445000704c80184104080c803081540140e0425070080c0b02020b00c0b41103141964461558040d18450441801941b00202d054540710b49800800065001e5414189004a9001035502d0f800200648002040362611400c0c000d018001c44030f08040180c02041b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 353323660 1250 353322410 353322413
    0x6050a0c081b060103051c0201020c0a0b040203031e09040c0c0201020d081902042c130f0606080303090f0610180b0f0d0b01150c031710050d060e0d090b0403 69
    0xd080d40030031400401420340800c120b0003204100100341c040c0d0311580241c464108500220320300182c1d070303008840c150390041c0846034401d078001076140e201941000894030b40d5140e5001007400c5210302080d1110003000d03001c0d804509200c241c0103091420042e60100641140c10310120307071520318204004d005822001d158940d151040140513002040304028030721107810360305440b0890784150301c045101d0031070a09500e01015040f02d1b5041e40807400d05e1219040c50319000421020f207140c04020a5031080100d008240702165009070050b0281c0e0301141d03900e09001c1103c590f1410240310f08550380c07080000241046841c04800307401c9540c3c2032501d070b00c0c1c800511800d0001c5c203483d1f405d8a030003e0301c003c210303245540c8000030010454003600da284a03550402d1358a90f2501400303a80201400501d202070380003e907100c0801154401d04407600c40f9640c9844001c58460394981d803003250711131540c41c50407041c0160390b44004c40c130401003070440d403020b4403040302a1030403030043c0300740001118248400c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 353324910 1250 353323660 353323673
    0x8041a060a05040c020c090c03071b030306030b040b0a06090b06040b0705030904050f1603060b0a082e08150403021e0313030804050f03060402090115050705030d140106050a0c 77
    0x180c11240041101010365111000300e02210110f203281c90060303006030500007141c2071058070f094110703002e441224914940044c0140503108415a00c000c201900e401000071315200f42e021134050740c0e000e46d0f141030314102810480c01d0359606580ca030b07100500d80700000074100311600ca45045a4806000c49007407500e00315078680c0320b403c0719105841d0340c081000342c103409170344600c07601d840752030380600440351420640440c201c102c46824034541410b203085010702140360400b0607076051f84d03c40d18080f6001e96840e50700e03001d10040404100003000100506200c0000026140001e880804045440c022301c0c80901000d624015603026003d81c010b0341e1a9030203d141c800e00d102d12001550300b202d2500c400c0441151a80c0d1150f40241c6103002c0109050040f440c041e0203081894400701c0081c00755040640006820071740620800005030000404800003034000c00a03034500c1c5070001d0959032121a000f0b0810040c00504400032140b540b079070004162240280d0170349001e6007079541d840d0700c040600d582d9034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 353326160 1250 353324910 353324963
    0x70608070507020a08030f070317010506030a020304150501060806030d0c080306060a140a2607120b01020a0206160c0506030712020901050f0a0c06270204230f070806010804 76
    0x2613030402c0810402040011080000348611404075015075075901035420014030310180701d17221000811031900100001c0c0e41d480140ca803c01006000140e036a290781c509509642c1070307024031641241c14070300005041ca8001300d50520810003034064031100240550121041001c9842c01000100c0c140041211401e105c00504244009401c2c505603001c4400a880c80c0354100c5450703080050a401498a001240c902c180b040305401442d001c03c4500340000301400f90041c0550b0340b0f0b105030b925520b00301268400c106020000380c0280c00d05d03954860b429022000710b07680d020280c03001c0303807a010002414207040d41124410b1546545500c3c04e0f540890100c40a940b0406000f070400c04207024503000001c00300300416044440d51104101d0100758038095083d140702003511488210240c0c400703200050b0b00d0010450b11981120001064941c0c0035151841141c14002d41c0340440c60b10b01001a100c3d140020b242c000c003095191190141d417540e00444880a04070b400038120380346000f00c5014a101003c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 353327410 1250 353326160 353326163
    0x30f090b1305070f12060f1a010f0e13020301091422020f100804050615210a1b03030e030615240c15011403030f07060b04050a02041502070608070507 66
    0x40d2003269a131080000c1c0d0807032154001220020040e4004c90810050f4030a00e0005480520203010300e542e030b60340e012991000c410340d0505100c404000030344e0440c0315003015440c043d80103106034204007140003e04000d410074015658024075051990000722005024248120100f0b981124a035410f5040b000e02c003080450200d0700a1081118110590b44460819400340b0103550744e2001880c09046c03d600d0250050804003c43d1180c0c0e03a1001181c030b0f200380050791208014421000840d403070704811b15211204034050002c10607080e01806c41004110047c040700d0284d40c60320000c0000408254841d50305961081000728030390100411170074001c5079820302c03a4800c0c40410030150f42c84a40c1e1070540c00304015040301c6c0c0140c660410400021042c0f64090300c4851440e444040075100440e64a114120260161030804143d201c1084000d8020884444020b00b040c0600e041c089a484003030740181c01038414001e5040c1460000310320011f0309008485041d602d40040f0344602d002581ea80d0f212200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 353328660 1250 353327410 353327413
    0x2010c050102120f0910060311010c083c0a0801030b13020d0501201306051b010f02070b01061d011d062106030601060801090221040b0106030f090b1305 67
    0x1203005016111400f02d12070844251121414600f1400341810415006400219645080c0f014008a6548400000d0080e400c0c01d14001c04071150500e6030250143c0e00141c52990ba620a14180324a0710ba15182d860005803031850410f090040482c0034140a5284c009002401c02401000410a144c0085030064050b25091a1408058001c0f42d02422440002d480340d17912402d44904401c43c0c0d80c00689600c02c1ca205807420003070036042009448015205403003c1190200b50300340d003140300e8800d120031034100f000204060301070340d04104069000398009a610300c0d10500001421f9004030352405003000c8140d42110003035070036001950b110b0f029000e4008481414002c01c2c140d9101c2a0040040340d100410f0882d580d0310b883d0140d03504402c02442c490083d040580104000e6411884860640300c0d442c00142c1c03121800f40c0f4140c0e04618207d08401c0d403600340c005200500c024603910905854043d68148014101402d2950581d800003800a110407154000155843c07058464042c80a10420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 353329910 1250 353328660 353328667
    0x11d0d051b06150901060e1815030a0b0703060501030e0a02040504030e0a03080711030f15040503071a0f0903162402040b12150d120908010c030903200a02010c050102 73
    0xc41c4035240c01011609140741c40f004080024903440c04000b040d004003840c0c5884c0002d107441c074000c11074101d1500304030361100b0f002501003080c40e841d1030180300d582ca1000d42204c0340c1d015542031100110300c1c2542c000700442d01e03004000c503003544a406040e84c045000802081074480c107909100041800820035800c10610491030b1005d9640e140282d0015400b5a040b80c1c0c5404013400c0030603c003284c0040b000d06c00d5124000514034610080344580e40480304804051203503580e4101107003503128424004010080818119940384042106c55014030f400c0312030000142d6410744003d81e07070300c2840314041c440c5d103098004000042c01004d00842040c04002e1200c2c0002e0072032200400d0342c0103500310a24140700420311034070808514462560140812404a8030181d892021480c00f060380c000141c00c0500e060b2600170942d02545409004140c18002002100400381c030090040100ca4002c8001071408545015100d2415403200c01005c0648081c2c507148200380e006440000003500d04440325502030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 353331160 1250 353329910 353329957
    0xc060e06071e02100510030c0e071b030302090616050c0306040302031e1b150c0f160204091a07020d110c010302130b04031b2301050c010b0405040f0203011d0d05 71
    0x34052075014441c1b1983c28543c841c203500e484c002d0341d0000d40103411382c5103542042000c0c2950200001c5d8110300c80c1c861200030300a0a0070100c1c00fa22414014130f400c11400a00406109001c2e82d0468800340a0b8041d90007000301d40003015212a019100900164070500c001286071003041c048203a03150684007000d2600005d41d50074540044003d44411041e0080c00b07103c038828512516451348903d5403a90280340256003800000c2c01d01409100c0c80f0289541c9031401c1c21502c5680c40212038540101c04100c60741195201e00c56042d0040b030b0560014003034910a0320569000d10300d49130000c0c00b0700c0054810f600c24400114001c0d008002c402840c10460380c40001c54120f01e100400195010700150078180e46400f0000a510803241c0c012215103a540504400c1c00080c510007140301c07002440d0495603041e501140501402509440681c003d03e400103000c201725681c4000c8880d64420340080c410310140c3d0006456481a0709020350054004400c3d111342e00d8070075801024400b10b4401ca230a803601c0071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 353332410 1250 353331160 353331193
    0xc08070e010e1305040501061e12150f0501030201020f010b031e0a0b04030302040905060f03030d05181504021309120c0c030c09051902040f0b0702030f0d0c060e06071e02 75
    0x9056650f0a00e640d00c090001b445400c2c080c60026206290500454800d08107400b0484441c40c071800c069074014444082c00c01900760480d0385520741820003400031002035144203006001c2840128098401c52a003002d030031034180a400070300070008020303100304600c1c0304202c1418801e28408850a00404d1080c3c0c00294039058010f005e10700a5600688413800c143d00b040c100d6501418842c40307030130101344403c3d15a800004941c240803102d0300c040307025110381400055450700d4000011160203400041d0b1440800d00840d60f02c201d000301c980d0110350100c070f240c1908682001e10040c14200c0a000d802c40028000e040314030225100e01c803503412040d56a00c0b1007880c042c540c0c0000b0300d01920303038051109240103071a0744420070448250440c941850030f0500200203040788200c841820012030b54806541c3c040c0080c9203042c007000d059600050f44110001d15008100004070307141850180c0d40e500e00c000005550340301e82040d07101c0c0034031800312100405189054188031011489601c0704444200b80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 353333660 1250 353332410 353332429
    0x320030402150a0512060a12080903010b0303040605121e010b03130b040303050f0603010507080613021b0604031223040624080d021f020705030c1204030c090c08070e010e 75
    0x2410790b04e4540301c42800301c01c50700e000c0300a80700e103110b9400b0017014440000c0e0003007401241944443d180303a136100d8070f6000ca40035011401d51140d1500000c1400030341240c100c8010084101d803040ae2130b440c2c0e03813002007044225241904d2400040200d40c0140702070010780004640040c0b0f0140d01701101405c07035a0b00c485200d012942100003e807501d0900c04d000700400c1c0310315000a4201c00910041c54030500c020300101005040c2c6100d026140c4041c5040b01c45a4110703240f420103981c1501e900300c0c00c46280c1d59034000c1568214000345c1c1244002001c01164032030202011042081980c0749a1164118841020090420ba901a584485c0b61400b01c4541c0d00c001048c001141061040b06c1c5401e070340b5420001480c2c005015504441c00f0061003000760220040740c2c0d0b2a00e540141c4440e068140315180d80070307038900514148684cc00c0a1302c01d0300d83d40040e104880c401c4128201098540d907503941900c0300c40d1000c6011078200004561494020300c0f0307035241da440600d0080080206580010501c45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 353334910 1250 353333660 353333677
    0x90c0d081e090405180c01080c07210809070b0d09080c0a0c03110a121704030507091e0212060103050a1b080f060111060a0e07090e030c0607032003040215 68
    0x7030002800c824582043d004269021070346461810000048400701d0307032070302c02a10b00750f810003403000006280303841e002d819203d481e0341020034042000c2d084000d4000c101100510f40f400324040e840011103485000800c1025902e40c0086213041c0201240e001025140041c8200c41c20b45050015020000040201101d042c0c0103030b0304420303e24598105030942c5890040c001c0d000324149541072000d40d03e0102d01c0a4610350041030f0702d409043d64078104210307000341d810003000d9006051000590240e10340102200846031b540e50580342d602d03034900c2d804034800d42c40e50400640549d4006050356020754841e55018403d480c0201e0303440c0d10120035840080091113600f01251900d018054001881121503500510a0920030b0780403c00c550250b82e202e000505001ca1161501a502c41c6c084013070100c44000c014a00d01800780c010000c140d603803070b500440c030214204d1082000041185200340600c0c1103140910a460000e141e6040c0c03601000d500061090fa007060700201d0010030011030000802a05 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 353336160 1250 353334910 353334967
    0xd08030f010f050f12030702030d09030b010603050103030e0f040905030a030903090503120306151608040920031803040506210702010e0c040c17040c090f05090c0d08 73
    0x30319000c408080340c220103030421080d1210701c6506210544640600b148181c90840e074404802401c2031100349540b0810302c009415002d0303405010480c0780c02c016081d06491007202012a20b0b170301c400c000c6003202c41c00d20001e000200080001e000d03505242c4c0c8402210040500003085021203034031258503551000d841c400010390b403041410240756100d08a2409400120054207120482a481d00b0641c000130341100e01c41e03045910304040300708a0b041241c109910b40180403503410540e0400d0140741d00140300758480ea80c20a641c0d00c40703040a00320f2501580044034242811501d03996041003042d042c1c4545c045031807201300b01c00324035946e8080281042d03810307048a0980c0a03906034844c645403080580100c05582c1000011200d10002240181080342d05613000542168514002c44005080009003103482102200b031005000405400d842a01c1c0c01100901c00460520583c1c421500300b00c0d1040b55541050b002142c0a01d071200041880d03600071404030b810b00e21040c0b80c50040045202018052 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 353337410 1250 353336160 353336167
    0xc130510050c1615020a0c03030318140c09060d03080103030e060d14060414090601061209120e010f180e070e1207030c052e0219050f010b060f1c0b0d08 67
    0x80030b41116441414036061010384186c0d24240c1d51400c018410740001014140c94041400342d02180704010000d030f941082e80042d80344401c4402035265801c0c4540603014405010004000303050a000340c0d003145616684000c8280e20b592412581042d0300202a540b245040003121031190090161694001d207588190700345041400c00c00c0102e80c200b13103502c2e1141c005e000400c0098500455468119120760501900d180042c8248070010090742000501120001c0f48801d40345a208041c4c2000481c00e0304c070801d80301f054035829a0203002c10700c15103e10104100c001c0c0403075280710b0080341d00310229040c0b01150340c0581000844410306a10805215400380700e080050200c0703030624074003c0405448a98451070b05000080410340e09042c0b007040c6107003880178080554401c000e407603403150600a10307888600c0745103800da0b1660261100c3c40e40075030070504044450300d040000c6400c005c0800818a1a240800c0c40b02e8640e0714850007800c481681e56144c00910761070717000d610921288220200c998 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 353338660 1250 353337410 353337419
    0x305040206071103030c070e092112060102030906040b1206090907031502070f0b040302072102060a090b1b0610060c0b220b090f01110d0b0d06020c0102040501080c130510050c16 78
    0x10302b0641c0307014810f03860052881c0e24240b1030510100c4410000c03c4491000d07581da1480180c1c0303544104682160881000240003070b01b0740d0000301a01e4107482654900120b41c85070300800c41d416100381c0301c100341a040660100002414170b8134000c1c080e185840050b00300091600d40351180392100405039299240f4504210406a0501240015011a4a814460768500c80413540a00034000009005281c0003454440350b6001d40c0311a8010400c404815a44580088400754603091010034011580b1070700307020403407000500520b0340503217103a981c40444062a589132207520742c4000d0000144041301070018070b4807034410385400f180c450103103d6210003070a1500d109031614070304901c03040c00c0740d2500320758140301e905210840c1d008020840001c22840c40c1030b000100300644020300103100c944000307035050003203c040d00030300212034090f203c60343e4945c3c0e95035041516100314400e03a14500c04056003403080c1e142c002c8054006140a150480c00d102082c90700e14a820640c080075444800100003c21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 353339910 1250 353338660 353338663
    0x180209010303170c07031d121c0905010c02030607031508060a09031106060d0605100e0a0c0216031505040f1e02040b01180e0711070e06030d0305040206071103030c070e09 75
    0x103070451090300f13002e4a4001a43c600034507a000c42184800a00324641c0780759595a1502d074481410308500c4181d9a41100340c07641905c0a4008110210129000c80b100041c15030007610402d80c402d401902070070f0150f4550804400074080c000407110609518440450841420020244140c90a110000706080d40d4100540083d02c1c2d111f04080c250300c075800700a0309495400365480b095034080e4010030303d510782d030700340c2412040716130440306006000d681048196980b40e04106000201ba400391307900781c00d0402c0a150600e5081c0405418210700411103405154140d220f0780d40a409850b20b00596283c0d603a556000c0107410024000c1d0261a0090380c007589030501c42e0f071111040034201280344c0041040d03124140b540c1c40c490401c030086224001a04580030f08002a01503c803001a5a1119104e6115095099094544a020744a159102c4140500903c112400ba40e0010f019034146520f81d950844200d10f00f0307000a81500080c4451640800c080082c00041c0080c181348100503e042000e25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 353341160 1250 353339910 353339957
    0xb070b19060503030702040c1101090803010e0a0507050403112b0b0708090a030804020a0b070b0a0c020721060f0f0f140c031f05100504080d0c02060904180209010303 73
    0x321100e85011400c015070755000045a00041d4180c3c1d000c01d031481e420506036580b02e010030a68040354207211f1014100007041000750305070b540480711f0a18036244d6156003802c484044814030003082e0100300903c04200c0000c908040303c80c00a04102c0a01c115501d0031070144200703107402c00034003880b85180003080f00c0452456840269868001c0d09403400c07410303440e900c404d954800380034086c00f44045429500c5a00c1410f02a199020220303582d81131515102c410800122004210301d03140404c5001003e1021800b0003c682081e400c8441c0740811034480d07041e00300e040c5402c90340181e4650b0480030b100c80034080c0070041100c250700050207056035046c0308183c0e0300c03000c440246202c24001700041041e040056070341061035068200008040e05040000510f05500955840341341d81d003001907540e80c010000c20550f01d1f540b00352098000010300c02d980301d0481000096220005000d281c14a00341588501220496955001151603203038000c2170344c01c20207030401c2e0005441014811000da024160380c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 353342410 1250 353341160 353341201
    0xa0c030f18050609030a1a090714030d080702010b0d080904060e1017120315150901170601050f19080105010c0f02010f26010e0c0406090b130b070b 65
    0x11210201c0c0040080403425080c00380300c0c071501c00401c0000d0a51000c100380d1154a40c06200c400b07015030000341802c0c01d83c0e01103d00b40c07058401c0e81404221011641c14911031448054010f11021903041425034408800805000442d940d85642d00d0440d560003082d580058040c0c480750b5610302140302404190780d2103801c1040c0c007005000500c250403d40c08540c03412117001a80782c00c040c0c462203049078201002103241d42080c000100234424481103034030b01c017a84400111005034580c007071000d00c608280103421116000c5095540c55800c0b51200d00d10840d0321540514006240108024208809070031160f201501d801c0d0814041a0842e08150780502500d02401c00720078143d15651031020b5051188402410807005a07103034008107000d854900d0300c4950364001d1100307404203800d0844035508240315500e0b42c0320f51071010800a42d070410844003074640a41d40d580b05507042550300c6980380e01c014001803500146141c0040e41061b00c4d006056424880c3d11a540c041c18908030100c1040c0360540c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 353343660 1250 353342410 353342417
    0x5060f04051c120801091a0a05100302090604180c09181518060f0501021f090c0b191202031608060604150203270f041805030a09091409061305010905030a0c030f 71
    0x551f0341581d500d020041080b108211841080039820701800c901078001c602046e90404404100814141c01c04400c8018140d8001c900300200400e42800b205c50382014420010000d4011900c039441d001135400211544299030012085c4030340e11009000c4104c08110401d540544e05c83c401e008540d070300107008000300001d1004200340c040440c0440c01031181504504d10041d5a140c650041056151000700100703d2010702c0c0b52176a0401081e192840e0383c8a9040001849038003403d22000007071301c2503a000f0180c4020200e04c102c1103100075100e0203070160030305c2d92202041c040014401203c0304a02c1004116a01079a291401007003001441c40300100c500c003402030f1500010308903031901500c210700c2c960112004500c0d104039880310000310450400180480c080015a074031500d8100610070201e80450030708004280c0c50703004400c00300b141656050015040751340800d0315100000100e405d45406040000b4212249907141c51031580950742e60004501420b10324810f254000c103400c84007000c2c2c0d08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 353344910 1250 353343660 353343701
    0x203210c06090c090705070c05060d060e130c090e031608220509070503060d0510230103020d11030f0f0601051203030f01270906090c05060f04051c12080109 69
    0x700084900000170501010004045500800e00c031422440c0001000003908003543d50141d1800100a80100d000d044821002c000100d0361103c00c2080783ca0140c1d420880d0300c40304c2414880107202600d003596000c100c4d0b120500490414131a0a850340600520800301580e031000f42c59801c03101ea414246400207004a41d04023002107403602c250140c0d01010a14000e1707a07aa4619001400e8041c801b1b1000c1d216110301c1711351202c020b000d0350050400454420302c20800850780f006400c407440003408000c3d0440d4041c200b102c0001e07000302c0c001221a03c003d003541d004070b03188208149031607003824841c01d651f40301c030340100001c0c00c02c40042103200c845440554038614040f04080c03c40781041c8141c540c0480003001d44c080207089401509a0001440c0060240416600304940a0008001d06990b00707a500300300000e180c03902c2c00c102e4170100840320021b81048e00e032404020341d1a410a4079580a5522001c1050000d50b1032182c6890506447c3c540d0700c0d0380e505201d1104102c0e800051861036071106c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 353346160 1250 353344910 353344933
    0x50930030a021c0306120b07030501090903090b030606120c0702010f0f1b080c0106091401060203040e1b1201031a09061b0c0a12050703030f1b03090203210c0609 71
    0x1103a0050f0701c407601c00c00b1004031064000308500404050303100c440200200c01d0390307400304800921400e01645a03603500780070507600da088060849404c0380008001c5601c000d000c2040705e2503e405540e114000514990821008500d01219a501110391118603007000400d01e08540e00701100d0702540e0070a140c82c1c030800340f10400180500248142c41c80a948030036070030004002c1003d003118441010f03c0000d11103290b881d2108c8000d80b40551705108903044000c00482c03600d1002080d5811500000d40041032a00c030070403800300c1c401c1034440c107a429010800c8040507181d2180c80340c1e4003c6201e0b80030920008140c0b98850910386000d8900301072508500284580e0070706011120070503803425241c40c2d50b036421001c012441e02d007075820001c040b0f4041115442c44a60880080e0042da80291030500c103440800569200720760b9211410004590101907111006200341d000702c1015101400b202e80018251400c0b112130403220500c40144840015034480300d0030240042034010b55424003c3c010780601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 353347410 1250 353346160 353346163
    0xf050604690308030604060b130503073f020a0b0a1211180301090501050f040b01080706020d0e01030207050601091d0f03180a090c08100602030c06010510050930030a02 74
    0x140d20001e80b03c0d88020011984030340e2668000c13001005584e0403647d545210f190713482c034003c250b80300d01da10034007172041c00050703141c00c842c0c1c084201d5030030384401041c4038a481c100c4501104a0305083c1c12035955080140c0068036448c12050240c000ea101c140e40744d40c00c1c81c600404ca400c2c240703050f500e01d609084400b03014440c16402c0d5040c1030101065100d101004001203801045082c4000e1312640c00c00041c03017941120b074801240034a014990060b16a1389940007142d03030700203a10420006911620740c101503580300302c000d199007010525015103810500d448251a080003a04848001a500d08a80701c44100c210036010311182c044d07000c0d040814118100d540ca034001c641c42c0780f001c03004c00352803003c160342e40d0744605018080e90032080103c22150080109402000c84071038803445000040442c0041c000416940f504105000030940c9a08040034401c0c0d0050007440e010901c4070502640e065030340d4850a03500840a0b90964440d1411010001c1251210b00c444002d40d13900f0401c020403044e41e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 353348660 1250 353347410 353347619
    0x60602031c020c0316150c02030a05270d0b0f090703020a0504050a060b040e0f0a060806063f120a08040b06060706020d0b0a0f050604 59
    0xa484001600d5081c0500d4032401c51217440b4580804144143c1481e041101010020341c10041c0d020341009020200c1c1c4060b42d0728812039005402040c0b080c000e511003860328140304c1c241c04d48119440f001c03803070480010034861140c00808880c51007680301044114180d0303c0d106640000c101005107140344c039540208001030340f01d0281600a41d240e0000132103a42c0381c1d40041000703100001c0582e80e501d584619551110000342d40300220f000800001c101c02d8506030042c202034403040805801240c441c1e02c1044140902e034424514000c454004005008164184031619400f0b8603c04c21100c0c14501e6040c1d0421241c131410301d029034002e200724064680c0c0488101c5e481580180324942948400f4001800d90040700390080503a800024480e2840605030000d01c485074082c1c400e0501030342c448420107a82640742c000c1a40110090208101503180001550028406401c400075840803100b0400d25100045503644914910341e1843d048202da000155110b8010f40d002a101d880324051072006c6811 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 353349910 1250 353348660 353348707
    0x1f03030302160c06050c071a0f0304030c020a0f17030a0e06030a0204030b040804050f0906060a05070309050a060c02030615013606090503070503060c09310f06060203 73
    0x41d400304680491040d00902c803a8074a421401020040d56a600b00421541c440349040d0964040c55400042d81c0c100b20801c3e80c10042d101e4000750801d050038503118641d4100520680c00c0002913807100026071102d090b0b40c00a004000c14401e2640d0038080b0220510b104130400420b141d2041100365107007a0b00524040403030340b086030155a25240c446504010380696000a41400e030a24207000400c0000d40c0140200c1d00207070344a0180e07075001410045180030899035a90062820007184800600c40e10091903090b04c2810003071840d60f15403002c5060030710141c000d03030041200003015030250700d420401c10f540591058590f201405102c00001c02c051411020f034401c1001003400783c00d034400030b2039850704001c40160b0342480c0b5955698000b030280c1000d120b464024040c00701c0200d050f04000c101340d40705910781da051601e44112a02440b0004007080c01105881030604802404c2c0c100e480243c5040c84011000800c40403203074030980e402c8400d5940030500f954070800607038000d80e00ca21512481781 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 353351160 1250 353349910 353349917
    0x120503070f02031c02061006051206130906021204021c0521040806190c02070608060906040e0307050a0b06011b030c0606090f0905010c0e060301031b050d0b0f1f0303 73
    0x3107068400301e0719041c00001c0c1d0650904c8011000c00c0d119030300086417403080d100c210807004032035601c140640d1148165620041001016070002d501800d10001140714441019800036042c01e251b11510206d8006405256400e0101401d1000b5803801110107041c0c00c000200d44210011a561896136a01c04c0300c0d40503600121400e2b03c851031240f18000c1e140100b10700000d031040d9183c8603212541e05804040c03c441d1440c5800035080344030b40b0001d40c1e04196280c9482c1c950440d2a41c0081095502c0300a214130380c015210181801812818405007a240f8407500c02007540c0400d03480c20300d80d0f10b01c00404c3c2c10704003c0305201c4a18411203020030b28103030b1501828901119111814080302601194000d821110309000501c01e50203210391200314103a000d58000c03c0301102e0042c04440e660046d5040903484041032005001145001480300c0c06000a036140000007a910004111540c00511058418024113801c0100c00b01000f00a5070b8000350080143d28641050101c40c01e00452030300029040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 353352410 1250 353351160 353351183
    0x414010e07020a140c1203030c0f160c08070e060904020a0306090f02190e100b031611010c0504261c0c080318280201050a020a02040e010507020712050307 68
    0xa0300a0166030105900030045000b9010701c1300c450b555640240680724010300f0f071942c50045038a000b00c26a4007544032070715494541500a10211a503820196074030303d80340e03451408a00080c01c1650f03403030010241c00f0086c01c011860002a00b041a0000701306034001c180e02410040140d4603000540c00f1307280d100000040300021410003051483c01004001d4001c0d000c150503241d04007540d00000d080340c1e07599400401c02c0e03980305c2c500c1c103c0000b140714804255a0500108501180c07054008218400c545414660b503528000d030316080d10911b1024001003140001c1c140402001140000c41e035040c2803001c0c400504900100a9427104050039249642d0202400c9111803446420305c0301242c0c0e0018001916400c007142c006040007071441d07a50046204540d0360014100010710440c0f601441eaa4403c05161035540064075280d100026034400c5000303510343c00c5d0040e03643d0b00c074404802c3c00e20400080d903031a000802038a0300c00d00d80c2043c1404070403440701a0001c0c10010868041640c0004031004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 353353660 1250 353352410 353352421
    0xf030c15120c0305060f030703230a0b0106030b0a06030b150f12010905090f0a05100207031205070c050705010e0604030609031e0e01031a01081803090d06020c07050414010e 76
    0x1030030a85407181118003400c148401101c0c691681245018030030480b400c88003110240c042555840c041d100c0201110950402042503800300d65a4400d0111160155080c12400f66540c0301041426041100406c1e0340300d00079411801c0c0341c00981e0250001e42401c0010204100018002d81101e414508071000c0005000b0050f4500c91300381d0b072202d141700303000c0c02c00ca50315080124090304085070b08014a100e0680348500c1002d0001e40114840d80110142802c0220b03c4c1007400a507014000c01d80501c40044a02400940948601d81c4104031658480c1c2040405140032410a102948660704002d81e81c4282111070350b984045034112540142c0004d500e094a240036940d441030a28440c80100445908941803a044060303107100d5a000d980800101c00802c04150154841d09100c80c0041d901a0018544460510f01210381d24440002c4908180d04507001510300141203904594258001c01c1e00c0090983c2000f040c00584400c40f4148a060806103420307403c0380c014482c01c940c4400c0c0d00c0110382c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 353354910 1250 353353660 353353667
    0x9140907090503010c03061a031017010b0901030f031107060e06090d020402070309030611120708040c05090117070e01081504030306030b16120c050306040b0a08030c0607090f030c15 80
    0xb084042c00900c00a110340c40042d00411891048000216940030100881424501101e1080c0080202402c0c01c2d4206a082500750382504a000d5140d942c54500140170358903050b0a038029072207242c0d1100369807614540104100d0b11031400b40c5580c1d0040d0014442640c00000007241c1450542e00035446058003c0043c40a00100401940282c0300040340420705034004442c01c141d81c042c00b020702c03280800641c040400d01c211840e030440b0080440204108505c0350003100d80041c042c0d60228207031502e900c00500c581ca002e074414120b11a98200118081e2400d00903440109a86d40340e0300003661508003035540341c00040700003a03462400400007a04050080d40309501968101c00354021910304000c11703030400702864540c2c0c404200600e609549201460007429100d01d0b09503291400c5403549414400a02032404410764002d015800c0421865410009840a030121400920540c02c11501c060700301d45403908412000e246131201480030440240c01101101c54611004200000c9250101c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 353356160 1250 353354910 353354927
    0xe06060f010c02130608010605031612080f0c010e011b0c1220010603030c02130506180c120f0a0608070f0e06040905012d0e100507200f06010609140907 67
    0x460103189040781c0072903c840150300860645100b90114bd000201503a10584080050720a181d03803110340f01d20b070100051030013006d44810440242407900346402c40321810f080d90211030740c885041c1c1d9a03810112054031100b10514540c0300e00c0c14000d81b61039081e1030f00002607091815400c01c1c48500c0b00144421008044076440c03c81110008008403030701c034076006101d004446800da00c00d5290b0020409107400600c1043e000e101c0003456213055003114801c00240c1203000705400400729043c480315502c03030f01e103442240c40785c40d01030f5441040d842c203a1280030440d111600400c0103036014600510214079503011070022784072051803050f115600c8400160190131a148000c0682d42005c0906c1400f08510071403c0d454100e0459180340e052181c203815017181ca040344c0583c0325501480030160f0446044c1d100c16001405482d1507001459246251941c83c1d509198403002c69009000f640c02c1c5006c00d10134503014043e185025115103150020741d00c03a5442001c00184208400400b10303c6160060700030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 353357410 1250 353356160 353356189
    0x607050a08070c030b0c03070201050114032a0315061306030b0a09020301060b1c05090d020703080304062409050a0207110907090302040f06050f030a03050f0304060e0105190e06060f010c02 83
    0x9811724a00998209000c1e007040e104a0003640c2804004a40c0440c00c00583c01d4040014005101c40c1180c03007035050950005a68ac81c1141054490000c0a80c03018400003000041c440c0e101d140383d007014000e001d80f240c2203840c1103490b5458050284009865464503d8100340760b500c01091050300c50000138010422507118410025000490034600703040c2803c2015100100c000c1082265140c4a0b00341e02d4480a80d41c00c0c0050300403c4007480000c6079480031799001800f403540019075030343d8503004902c0c880090705001c8041e071090404200f0280240a4150700010315002941003400d04d81e0380800385810812168403520280c000111013520900c0007400668004000340315444039640740000800640c00f03041e005800c1041121180e00300007901811295059483c10320b805102c0308041c105403c0030340708450342c2c0e85448040f28818002d0164600a080d00003c9003d500501610314046698880341e82e29150050b07801c1091030b41d90600441100d131020300700710006120600c00240d0707500b1b20300700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 353358660 1250 353357410 353357423
    0x1f2709060e0f0601030b100c0c08030409020421020901150e1f0f051c0507091502100c1106190e0304030f050c03070e222009060607050a08070c03 64
    0x60044121115640900a68080b200c6251154401102940e41184201c1d801591300e80820717081d18858880ba00f0940d004401000d900354440c2d5542d81187e0180c1d1007a240036030046802e004158050801c00d407800105079040303408600e40e502048a000c0144500b143c135111030300c00d03810454000d25045c144408010001240038400307443c8182074440160703030391001510340c610580c1814000e00855000603040342280c0b03a52a03103600c491b000350400074820f0b82041580d1200145030b840042c41080000c0ca1900a4010610352060b69400c17294840d0400c010000450090700f44018041445030308403800c1020007040d05400b007200c602400c1002092581440005400024404960342900940e840341043e0360700580b900b030416540e00d400c0d005402142d55604045401110340000b94141344c804003004d0380b80c482c01502c554000c03501400c0d540d4a400b41d42c02640d00149010f50b841c41d844801115400d0406503107031552941c4a000510040801c1000207001d000d210b10003540c900150390164 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 353359910 1250 353358660 353358671
    0x606080613060501080d021c1404030c06140f0d0908040f0902030405070b03162607111006060c080d020d0203042d0f081303080d0b1f2709 61
    0x640c61540c0e198a00701a02c0c664030f440008034814030f001c80e012203817000560050448640d91440c907100760700d80702100c10178800302c0d603e5024011003c6000e0801140220070324007a0a19003100a400916003c1010462080030050500c02220b6607094808120391903200256000441c981640c4d107110303540100d00003504545d00082c15500da900194411071085007611401c40e07803070b07c13010381d6070101303032551500e122491514185662007041801004c001c84140112054404406044000e03801e0b2a6240001c1b03c642c4404034600c820131080c51076840c3c12008110081c40d1502c000d242d05c40c0110000c040800000e400c0d0342c910001e40503140300c10050074085540381441d141081da04104a00c10300803c44406800f00c02c03604000d4407905a4a42200e01090002450350300c0c4681a80322186800c0c400c03041c10001301c0458080005401c4180503214001031005e940c0040020790b11040c1e013200c9640c40030805c5084a150f114158511071a0b41070101d6403039250300c8000c5103030200d4a07001320700e9031031600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 353361160 1250 353359910 353359921
    0x3051005031f0b040b010903022e080106030c1814120f010605090c0702030309090c120103051e0319052104060903030b040b10080601090509130201090b0c0a060906060806 75
    0x8100c030340c1c2c0b401c41107070400903049250300b84400e41c0c2c804640715010030501c0c102000503050010319075005201c11000c1c40700c0489006000c1e660814072a0701303c03000500042c010300205070588102d8803c01c00500384a401e00580b00340d94401300f070450140800b00a0140910b00c1e00d0b40703070901d10b0044002c0da541a5660020181c2403140204203900c46c092080510101240c0c1c5032046c0400c03510744a070040c001c3c0d480c105c590818000006000791008a48010402c998a08850f2041489000c0c0d8840c0d405048400c228858000700d20303814000079005600200700d002c0c0078240e48030004030300d404203041c820740320344502030b03807985200c042c1440d50f4840c0c1903403003004204102e40e4440350131280b003518100300c56484001448225141c6201041c2c01a2a01d0894101540109100340e40070a0501d0168085a00d410100703662000588a050307904141c54615011985c0005d400000740030300d1b07900300d4101030020041960780d50300c89030054109665030380500c051007010380016001d460750303004503540750a04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 353362410 1250 353361160 353361193
    0xf0b0d081b070b030f06091b071502070c050a150507060902181015050405060a080402042c0f030903070b0a09090606020f070605031b030a0e0a030c030e0406060c030305100503 77
    0x111440c01040407a50300154840c1390000e1481d0044108064482004400741c10403511603005100942b86165080380210610280e400140381441c0700d00d03071801c0c00c6442c08090003051030140e0008000000e4004da01601c82c0e40c0101551511a08480c000c0303101840c07800400c181c118410013511500c690303207003003001c0000300d01c980204460303540d0028071030590ba124080350140220b01030759502c01c408110701c000c807510a45106811030300003080000c580300074519014400090844007425460888030b407007070300d5400b40b01080c50207038480c024600d0f01c44441c0020713403a0342c1240110005c1c1e16000c508040d0284c800c85c98003020b841c50704003c020407034642d40065607071010842010440d100740b00700400e070984200300740c9008441c40b442c4a0901d03004005244829000200320300c0785150345080580d6103000800c1140040c1c0e000f600c0d047c901200358100241410600180113003c0c606041d4100a030b0b035806024250303d5601854000394546900240c5403140c5140da00c125814070500d54410100d020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 353363660 1250 353362410 353362417
    0xf05040305040f0602060106050f1e0a110c122e0501060e19030b070e060904090c05090a062603091203041706100501030209031c080105040f0b0d081b070b 68
    0x207021000d034610384c0c1c2c4c1d1541260b80c0d100c01d01a00001440c1444241030340e8504002418008105400100300d82c81c00c0c0e550f10865801000002001483c24800c00b12024824480c480b8100d0040e1601c4070000b1050f0101599103c035451501642d8070300c0c03101103810418100450380000d404c0c110500065075030b44130040c07081c100030300918482c1c1004940040000c0000402c02c1c204d80e44803c91240c41d90300c8107010340d00100b0703192131903801c0b850070449990303203941d644a48505103201e803101004403411b00f13051001c9010f0051915140528100080c0600c5850030362401c40c0700741141e41040e00e1034180400d40c7c1103000f0070b00700940110b070a00101c50480e6001c800b90094441992000042454582d0840e23a41d40c82038035003000700311007010144115480380c0c0080c840414060100d818a107032110044030510390552540d0001400c590040c0118030b090300404101a180140a12100f01460300107041144038100040011400185103c03949510105100748076903141d007541c1c0038030380d80d0030091807690 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 353364910 1250 353363660 353363669
    0x1e1a0f070f1a0403020c041a09040b0109110a0e300a05010f0b09190e1504020a050d0218040507150c12090602121e07030f030606050a0c11040f0504030504 68
    0x1103801003550002c8521031500d80c800c0340c16500070121100f244041c4001480c4269034554140b100c100030340416201c480c01203000301c0c0304011903030440d8503141c0c0980c122140000007402510341040380748032460307001680c140c5c0030204071080100d04100300e0f21840f0301844c8605a01c4030201d1140c21160307c8401003907a40f43d40780218000c2c085d280d1038449031022109040d1398258803c10b54030103d1001c5500505942d03243c04000c80006094642c007090b10302c1d003010070865198001288003000110b08180800c1401004107551103603c0016a50010f50911841514051044c408900007024414100040f078000c007ea841da50305a2a01800b00030500402080c09950a08145060704c054a00c29892101110500d43c05080c10035540d9030010b050f540500f015800300c81007101845404c00340300005145040c8203845044400b10321a5024040d9065984000c2c14071205000e20031119410021030840203511400025221050200040041c0010851711448a01e42801c11041640040003030041c0e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 353366160 1250 353364910 353364923
    0x10605010908070608060d0812010f0f0f050108060112150927020d0302010e0111030906090c030c060a030608010203131a040515150d08040f1e1a0f070f 67
    0x151a14015203036522144a02d14443c1c1c0700303c1c01040402e206803601c64100c000200303200029007050301c80800540191012a500b101503100403c01d0103034000a640062842c0300041000c2846c040020035503045502c9011f061004071000104030b030703100b000744070940b048001d000c21a908451411365801850b60150700d040c1490080ca0804480185240c8004244c8080181e404035186500f480a0648104001c5042d503481d424550b04140003801075036090f607000258142c50b4030b0559041450190050107a2409800206800b036240e00c010170310030502c0038151071703495071000c0d030100440003441070b54061a03965102009008601800903140b00b4424001c070485404414000400030030780c0b200741c43c0105240c0c00044540b55139102c207039009520075140d00d00d42d44c50350907680211700d4400c0300190455103000c0000e004c0c0400390381c00f481d403000b0307080314000240c20030010805030301152281d0040ca44a4154040007020404c0c40d1021143c00e02c90014509803281030518044e0380040780900101c0d80c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 353367410 1250 353366160 353366171
    0x1506030c0d0203100b010c1709040b09060f0114040b03090c041b2a020303030702010902040510060905090901061e0e1308190504051c0b070c02010f0509030c041b0201 73
    0x15071030090078a16003290014050481904440d40600044c08104403880c141300c4c1100b4100d003c144142584c031480c00d801d25202c1c1e5621056007c00044451003200c85219107148030900400791184602c20880100a003400b144030031008041290354000c66000140c00d680010130084210004540100313000300564007400007002054403d40407079445612000021203800c0e181c80d911484a44103951036568028901c20b20a40f42c020030b007176600440f504000b40c0c2d1105140d40440c00c05115596002d20348001054011b07040010003090401c80784545e030f11444041011515005003907010000400c8100300041e404980c061082d81c65040031300c1035004902400c2c0010382c11109a0383c0f15160103501c11a0640340081c800b1205040c00d510300e0b643c10030801c0610001c00d0f00d80301c03050315480904004014940d4018980341502c1d0551b0b000301400104140b4600c0303a40140d1b00305407040300f03514150600c26202c3c03010401281c0341c84e440f00b032010f03802400c151806804079101d140545540c0c030198003d06c507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 353368660 1250 353367410 353367433
    0xd020a0c051915050403090e010b2703100207060e07030f12170414010b040507090f090b060912010b030607030219020604081602030a06050a1401170304030b0403050903150603 77
    0x4021252803014004040049561100c403d255000562081c820304048142a88554008200000c01d80107481d02ca1000144201e0040c0034004000685400101d11903071019403902298481d0407044109013030a80100711103040001640000014420610440d01c486583c1c1c00c101c1c01a054030001503481c12120620010120310541b400414039a842141d0340098845a945064041c0740402c40500e5550364044252a642d5034081c45014140300d0781c030342c0d50303d41c2405500b020f04000ca510000089103024a01001d54a820003622101e6100319807903500700c400503d1081c0900a00d200d03460b0b0602a80c07081001c1c0503010b502910365020001c0481046401d005410303640c2c0c40d8152000b401c004410302001896181c80050703800014400b8050321204c2c00c0564031a815a801505d0f41e8081a803035550801c0f0002d00c520340f682c0102800d41c01d6001c50041c107101162a803180b4000503001e20682400141454001c104032909100040c0c1260701034509031256071064002500c0e075a101e409024502c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 353369910 1250 353368660 353368693
    0x60f0905190e0c07051e1c0207140406121713091401050d02030601090c03140408091c030503040b060607050a12110a03090b090a12081c0905060a0902060d020a0c05 72
    0x405090b80800104840800f81920004c3c480c1030660b080051f00c00c112100c3ca0301100c42d042440744000c260000c28080e4100f039183d1600c800208151170245140600c20031401500e2221000420f41040d609681c2000c40012418203115054800d903d12900c80f00018402100390f02050401051140626960743c0302d00410a000008010107541030f1300c42c00040c0a003c440c1d921041c0d0440e224103000914a200a056804519040f0360030b031200c54021900701e41a062a25040c030707980b4804402e12410744415a0040d02d14080540044e284140c0c8400040564552404131350141c0d402c6400c03035403000d5040c907210301c21400c1e240c001c0307000501d903d00d4400e0010300001e140b0741880d41078680f40304082c04c0c02d040140e00d41010707003500d50000041c540094801ea16001a03e181130040341c50300e54545125451001d0a81c2c1032140c0b0100c9498580f003d000703d132000c110150410300741100400c2c084083d00000302907018810450441610020303e81c3c03051a00030b120408528800c1c0d003511840700c8141c00c0c52 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 353371160 1250 353369910 353369917
    0xc011706010206150a0f0f03020901061418060f07110a09060522060b07031d09040c03061a090a15230d03050d020a050306010324060f0905190e0c 64
    0x34050780c440d0020a4010380c6070b40b10389494050150042c4041d50361103801e01d111b8481c5900108042c1c0f0303840004e10550038409850b0303001d41000e0800c41c5da0015250901c80d41c82c401c08280851400104228003000c0d60341000329892095900602600c981090501c0031400707040034295841880340c4600041c1c00e1525000c1d817002c60300b00410549208218900e003c010003415000543c200d070340c1d41c2d808610350620001030004c580c06039603090302c200385106188003004e08001e1501e00c41c96401c0c0408c000100b1501407030040c0c9501c030a003c100030071780207444600c0900c0d05040541c00445001000044210b039408190b04a60b06400919001d6036000040000c075141c6021503c9800103944002c0241084c01a102c40743d846440c282d441c1c580030900e400121307008000d840c00020700000910031a5a0300d80100c0c0380f40c1c0d0740c010303600c410506a0f21240b41d00c4076036071140e10188107100b5114180c4a016070303180e40040002506400c00640150030111a03000c4901440340d4191b40c43c0086000c245011054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 353372410 1250 353371160 353371171
    0x605011502240a02220e180109080d0f0e0a11010e15090d02030307061a12061003060b060c01140403090614161103031201030b0601030e12070201020c10020c0117 71
    0x285142611890000c002079444000ca04950b44911524000301d05c59442c160300040100d000c10f050b040c1000702100740001c0402d0a0f00c0c1c1d0a03814030301440301061400c401c84040e074902a800080e040d5180c1c400d500506030b40a10403219000321400c25082c0507035400314025410007640d460707541e110b0420800517000c0c10306058201c480c900b0b00c042c1c038141c140004071308034440c001412030f03003004026650907044d12000081480c0d00031280c400b800081c04c2c220505e01e003c001134000f510451424004041080364075110107051a621030070f020405441790700449200210040080c0001c90103805441341000742036508030005034000d1000240148980450200307001d00e103025600d0300140d64046030070400340480030750b0004001120740d1015035040000703280c4801050460451503145003059410004003c04090500d810480b80039110740c00402c8503c54205c000e1000c3e5181d03038036800100e00c2c1c10801d201403a0010000044c2c00c0400b500022070b03000c040d809a80d4001c03a000c45001951140340103440307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 353373660 1250 353372410 353372473
    0xa080109020f0c100614120607180b12010f050d02030a030f0207090e010c0207150f0c05070801090b0f0109150b032a1e0306150a03090605011502 64
    0x40c400a00a9002000350501c5240054140201c00c0f112600b44844070200d0700c0c01c540d403000c0803c00c079074540c8a0328800c1c1104489550200d0307802c510b02074139500300824050800001a468060206000c9032190103000b5122919496038aa45000c407920034007030050810402c02401d0000311450600500721041c0c0c0d0140103860000c1440d42c0c152540711041e0300901c02d5000d107240214000e2803e1040d05040314071100045405241040013034100713031142d0080521401046014426180c0180503004a126103180c00680050282003050400c41c4c0354000000c0b55085c03101c14018415040320560140c001d4020709049030b40d80c0c5010fa8201c40c010000300c03200c00107041c020000401180040e60740b0084500120885800c46140180c000c2c08060700c41903803000201d004032510100401400345090b481c0b0041c0c0c80c42c140040080c1074004a444a65403088001404a200d10f200c4c1c1c0140103240c0d44a1428412540c68518540e0a5030340801200014882c0010044515002c0ca0030860044006d14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 353374910 1250 353373660 353373677
    0x509010f02030c070b0a0e031c0b04021c050703200d0e030c0109050d02030a12020c0c040c09140105040807030b04081c0c0f0f08180f192a06050904091218060201020a 73
    0x440c0d004903280c40e0f20b0304081e000c0d2b46520740e1107240c80d240000c1c5a5454290b500c0b0520007510884e4070b0803240c000d084002014a091080c1140030442002280e060000418180c1c54070800031201d40540703210106400305010220344250b645d5415003000440c1071003181610360381c4001000481c0c0d04d0140e0b1200c8070000701802011440224543e006218501d44601503d09180000001c030b0244c880d41da1440c40000d818007410080380e00c0140000c1004442407030000d24052034a246155900f145010207402d10a07480702040c1003041c40c070201c0b902d550546171a170304402000c0c0c69071030061504410b0b00001c1a003040f00b414005103d50461a00721695032107000f065210205a40c09124a00142e0722080c80351003400b0320201410000440c0c40e02440070f500b1004403151501500315903914021401020500d484140c03040a45064401660143e180c001d0f00c520050700060041e084000000d019403084481c6c0664099100e100b080b0340003200b50a6460f10399540904900301e100382c1d50f15000180c10031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 353376160 1250 353374910 353374927
    0xc0a050304021c120c0c170309090a0204050901170c0d02061204051009050304050a0b0403020603042901090221061507020406080f160f0302010f030509010f02030c070b0a0e03 77
    0x40d0f09001041050075900e41c25400941d1021048116142240c022458500c88030041295a02c01c0d8000340803100825a40400c0c804020380d624081c2c0c220083c424a05400000d03e10540c69042d94001d00c0028014991540c0d1101c141d04110b00701c804002140c00b55900c000d41c0c508000e81003104455016180510303140d8441c0f4030850190b805031084516005406800d41d001c8142c1c0120304a460141002e03560700c903e0401005500030340ac0d8000c014a0000703200c1000035a8402c01a658426008003031940d100d40c0b1400041e1032034038204106010359a607030002058600b401ea010303081030800d50b8011314100c0035514420b03032121402c03603d20764001c40401001214030340910290031072900c080e1002c18466150040c1c01d00700214926006071642c0312001c00cac040e030f4200e110b150006180102c1d50b0b250f0642140c0008002018044200080c0b5896402080c404c0000b50700c07904601c07800190464981c200502d8079040350740b001c00c1c00e491006642010909581d818480c040650444000543c50620b19 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 353377410 1250 353376160 353376169
    0x11e05101b0611042d120204050901290103051312050309071e050f040902090601051e07061b03020712050a0c0f030504180b060a0c0c1a0403060f020c0d0e030f150f0c0a05030402 78
    0x1042d2b00015520b030069003081d103801014440440420369011001280329000050882c0e40040406130796504c0d801c00c80010542e0310700030340b03208595461321983d40c0c0d44004009103441c00e9a8008020003051104007106402c064808070309540c0f04880040361002d03910100421f5481408020358030250400200e15150300075401000c0c110b101d14030603c5072176203902100380682c102c0794040d5941901c80000200c0f414112030003108992007410210f04106c9240c940c00d0320514070124000c00d0003000107452540f00e000d481c0c0031034040d50050303034481044010315008003560014851300a0740c4800000d00301161009000d001c410b424050304440c2040c207560421036480380310300c1080c2c0300c113464043c0200d42c144440c96030281c0d0f010707105052541e42d0325524001040312148003491208602c1440154400c000c049507200b60354a183c60041c00000314400041d0820306549110030561060806000c1c04103450300c02d00b485100a02540422552110351001d5207110304828880080d200700001401881c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 353378660 1250 353377410 353377421
    0x121401020711240c0618160911070501020a030e0106080f030711180708090d050901081501020f030a030e0c010f0203070821011e05101b0611042d120204 67
    0x1101c0002c501d1803aa5055510700344c0e0702208615050b42c102e00c04110029104104020000031444028040101b2410013004052094014101c1d80c2703848040366041501d0b940103071079015030854021507031084a100094004e202e00a060301b455424281c000800711004100c3e85c0c00e4128001c041c500e04215540c445a401500742c540035403000c03a40c0a689810b65111540e2031141d4100d46032f610312403c001b9413462a00f0780000020041101c1041000010b9030720954841e003080405403840802448200140c0c2041101d80507815140700c082206162641d143e001100900c0a01007907401100c060401140c0141d1540100400750b8170800107074002030603400080404100d02c00c00e6641718006e10031a01e2000000384d2003450728600c52003124000502e880040c1004010817581d2001400c1481405007a83e1000030804d040d0100710107010050000a03046514000b090720076407039440b500d9a1803800c0e421a8034110900f503a03210340c4191018209540b0b41d174142d4480f04041001c2161507400c20002d0203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 353379910 1250 353378660 353378689
    0xf1207030b0c130303050c06010905060a050112110a020c01180e011802040b040902030601170103050c010309060902040c0f0f1103030a02090f0a0e0618011a070f0b01121401020711 79
    0x200800c441c1a1001a003550322021314801e684d000e0352041c07400f20403450000c06030051758400b0315000900006944682007072003150820f0911750707021800030006400500111140004030140080c24516940e408582c40391040c200340c8403440307400c030000042034a0200502440407448600001481280c0c14003c0c080b035954010740015252988401d503204040e041a07100a007480d801106010301c940e000714500c1e8000224080f00069580746071241c7d03640360301d032071609814540d582c0701030828000320307401c2b4400f1190041e00600030541030910040c6989014417114002070302074850b055840344500d020600b07048414005508607110300940d07134025448030a000c0d5100100310322000c1180c44a581c40c1c8000c141f81c5501d401c03103191140501c0003440046c017400d02040120401880828081403134000200244400141c503450540707400c40d0380084221700074051885d030b40300016070102040f0341c0002c01c0f80708103941d1008801c21081c1d6404c0c2d001c3c41da4000d101c40162102d10070f250030200b14a0090704c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 353381160 1250 353379910 353379931
    0x8070b13060e221409190222060e010905091501030201050307120c02011b0e010504090b03070302120f0c011e110304230907081b03040302010f0f0b0f1207030b 70
    0xc402800ca43c4640da09542108a001611019001010110342c95065401210318019207040040d04808034040884040b00a101d54840105400c044911090700884400030000800c140e50b19100d4007481150300744a020041c50400f400981611404038501c24480009022038074140d0840d8015681c0d500000c0940c1c0800540304100c4040482034050750000c1e100710b40000602104260300c4100c0001d40b217010005101040103605040c0e68071408031403c8481441c4009882c40d15240001e0030602c05a002a41c4030b084402460281070010440152000c0401c080300c40181a04005580c1d01c0c40140100007003030f000c50f44081e50035000320040c3e140301c200c2000752031605484022090704859800c0c01340500442c10700c81d007141404d10f100825040012810b0588980c6006c0e014800040581c80701240c8070b00003c00800c003018001d400c042d50f49104402d09200d400407943d9444000e2072100c036181d100b02e100c0460302269091103464034011942c058094a090303401c40c2c8031004108400741114002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 353382410 1250 353381160 353381179
    0x609150702010203250323160203010f09051f05240117070c050106090e06161701031505060d020303090d1b061707030b0a03030305070e04090c08070b13060e 69
    0x10241a0042d40591000c06980505c0d00f5040e810000c01101c2e90380d07440b8804e0f40040c0b5019821005071010b4420200c0c2003003605455084610110b8054610302a401c4035184c10095940c040081c081218000c1e080c80301088207611900d44803e0056a005803030310b5004603c0c2041c40401d40d0520590300085001c1818103e0301e1581c40401d243c05220115101000980c050241200b044421b004103c02000c00c84021b01450301004215078480f4405000d030051120f00d0010900d68500400400710102e103240b240080560b0740c1d041800183c0c0070900300b43c142034a0040080c62610707002c1c500442881e0003030300440c10019882e05009441a940e0b800359807520000039240f001c1421116400d02405032075468640746c80885004a55405010f00319100341401c0c065030301c0c03254841c0c042c3c06040300d4140c074011666450b60082a1114030b106840e164000d810304410000340302490382c080084820800031114001d5035400c03c3d1100c1c1c0264400280415100301c8104912481007a844903044401040c10f2013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 353383660 1250 353382410 353382427
    0xd09150c0c030b190213050603090a0804080d0f02150c090d0503030a2406140f0d0504260a05040b1e0a09090617031e0d0213050f0609150702010203 65
    0x39010340c1c640c0b0444411141c0c20800904500031030040402124100080d418a038511003200100705c0c1d0790203110f00488000c070005078070090412800d071800350040c0328155100e85503c0d845072912007656002001c94034501c100000c02d44002580e00300406007805018051b291a10303542e5551380054407850b8056104400c84011940500045018901e103d4001802100d0b40c1001304640c070b1500320040721410485c804002c9183c00c250800b40d40c600d050f12079a5035207680040d00100f030080e100180d80c61031802e820402080380760707a8248040d040c0e1004103c54070044200484031032081e52200c0000440c00e00040065070f1040000c1e224244111001d01d0b10600c2c01c0440c1070141c2c1201a40d580020080c04080182140c1031158001602c60484010540c54424551550301d10480d051100c0004440d100f82c101203004c00d00340d0301c400d08940029941d8000b50f18004038071102070701445101e1080b44000b41d50a07c1d04508459001602a2446407100c94020ba862105e800100b0181d0660208014207034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 353384910 1250 353383660 353383673
    0xb18040b0a0b0d0605180703020d18030e0a150905010e13020f130504110f03041b0605180f010e1e0901090207030806040c0518030f060103060b01110d09150c 69
    0x20003622007007155944604240c43c03410141d400307581c0142d00810791a041c100807841d00000f201c1c5e0140c0c072410301580c1d5100800f0404001d01c50465480e85103450610707400c00b0168031039030310040090102c0312034840941310503605048071781e0041074101084003114104a6540211908050080001e03c5140244012140802683c0c0074260740b400e9404000b4803aa00d035801101d04002502c01a602000b80c00512402004182b0800409100c241004000a01005045a45071094080a0340f840c414240d8030070001e030803078100c5846c143c44104401c01e00042401c184042a03084501699000030940d1108203004003200858160b007c0d04220320010182e031b8a500088a00070565078400603a42c4c0b1071420002d001100141c0944c0c850f905010308191781f00e0744582070710b410000b000040038100b00030500080c1b40441d03d1a003525680201d81c0000144081d59104148681c000c0c5c80741183c007078508400d0b42d1250009900314020500240051002080b200142110f0b04080d0916001d103558540b181c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 353386160 1250 353384910 353384929
    0x9080606011715131a15131223010203090d260c0c0a03020d0905190902160f110a0815010311010504080a120219020603040f020105070804150212040b18040b 69
    0xc010f40703070200c0702c01e074103801c21400400d690b111807400242042000c464521480c69644140c88c0700c115450582030500032a801100c2100341e40c010101600c1c20048400340c041c1d0402c545041244c01080484a1401d000e1125850518a5050228000f0341103945140700080c02415111807210144011504c001040050b001d11038020740051100b1400f50100504007600c58206d10b000d80309000040a0040e60508100c003982e02803800503854546804d101003100701d1641000d0071051210218000f44a04107800810345070b401c0d6001301c9071507203480b030031959084609106c01c9403000c100c00400104e40c6c012900c004142c014904103107095920030400d481c00c00b050105988144100440c6e951080e010403420502540b0720b50482400c0e100c640014085000050020380b401e142480540308682c4104212071101d43c0c0208820307240e548400d22011140d10781002d4a0162044000d04811810080103540495003401175040c501550364000c0c1c80c0007941c075070300c8980141d10b5884040243c0d642e417164 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 353387410 1250 353386160 353386181
    0x15030903070507140901091b030f020921011b050315010c0f121812020d02040b06070503180312041e03060204080c15070305041e0509070908060601171513 68
    0x15800030650b61381000904901030340401c06451404104001c440001e80da90304150619081c0040e404402d50f20400c049d20031103001b254000f95140c48060186032036141040e040b04014020840b207243c2017207a2a107640050030f00c41c0452020b01c00500340000c549103100f94102c042c0f40c8501d041300300c2c0e0380c0d420281c099000c1c00c03249212880e00d200c12082d8400100b0a00e581c614040041a40c504410000b200030076220180c041c244c071100400070741d190380c0c21511600e00040d211301c0d6074003400e0400720380302c0c0c004c49860300d101810f0741040d0300c42e4a000210340c607412001080492410f0714100000382d000f030301e504026044458100c80080030440c14400343c8010031020000d802022000000c100340004078034168040040240091030100354418141e805952882c0364011100d0000140c40800c45010f900030740c1e0290311041001320141c4d10550550468011104541241c0c03035620064070300d604251710141c0e0307102829002074039404100d492881c000901500718400020401848010f44604480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 353388660 1250 353387410 353387429
    0x3030d0209031605010e040c02011415100507151d01050403080709120c091116083c030612070807030201180b030a230f010501080a0204030215030903070507 69
    0x901c41c1d8982800e0000c284108806248440d4050034400041d016910142e09240280e0766040c40020141c001d500c1002070308001e820604040c035102900c001008107050f62180540d1800c440f0098060080d800d81d20090b5028640700390500b02c0340c10b65801803800d2040100524445201e000300381d0400e1290b44e00541c069507030b10800e850481070207001c80700b16910944a42c1011094100410035502d6240300f5284402030100f0156404074140d0400e001d20060b0044043c1010440001c01c041c50008110b5942c02c1c41444642400d58800130030a130108000403010407500c6c0c0e64080c3c02d200968015030b0700460041400f4051100309541c1e500e000b01980000c000344d40010700c24415581c12440041c101111000c90000c240e003010720803145070002518049150f0303180c05408489040c0140c03082032044c1003020101c072900d044600c040e01540203100e49408101804041058a0000d0089038140c81e0003034000c40032403000155002c1154002880c003000f9000601c04500001e40901401d00240504030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 353389910 1250 353388660 353388667
    0x1302030105070921031103120411010c02030a0f0c18050a0e010504030c031b020d080d0b0604150e0f03030a0c0b09010615050901020708071502152806030203030d02 72
    0x1060508480c030242862042c8245039400f0045100e00303255041090101c00d4001482160a103400d8508441c80300c0760011501000c140300c0c0318203c0344080380d44607902a8013001c0c0018012001942c0c0500c20940c042d4068100402180210310036001c0003540324841c2c01804422513603098036031311011668205a0b4420745800a0050f00710301d500820b04c11800401c000c0107617042c40c0d9005415048412001010306c07003004221034100d005006009540c07a00501244c4540600703140c000000c1d40101d580c10301c0036182020720611820b0400503107080c0c0d04030750000681000e8080094a1f0703214a19100c56100c198800d10818944040c0080c041d603e0b815140c401440c201072030480c0a09c80300038402d45031680b405000300301c1d07c4031401480d4050000703814071581c1ca001880c0103e051588540006e03a01c1c0c0708103440090790355a1111405400c0c2141d600b42d0f1040928400d4410b5140c41c1510038443c0e2199a114602a81a0101030740180080c1c5c500009029a075030b034046403e6401c00a83c0702c0c0007580c00f2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 353391160 1250 353389910 353389913
    0x415020412111c12051603030905060906040b19020d020408061909020f040c020c030a050f21030622241409010306150e010e06030d020d2106090513 65
    0xe0140b10300904121403018038600720030448036800a41d42d4000e08120329200070f500815000d9011601003000040d40f20b0701e046c0c1c4508028025010b0b01c0c4084401d8810030000a028100108005000e20b40c049512212368503009484124124002440710080d50b0030000c06003140500c0c4000c000402c00000074001615200e1210517030207200d000050300c201e0425101d03100507a560401001c1e0a1012100054030071401e00d412458070b100040125098442d1224240506c0400a070701e4116141744400ca80150582100d4800a6140c075100607031501005d00c0415480e10300100c2c210600340c11700da410707000c03060141700c4e4034181d41140f4034220b07039114600c82d0088a04d9102140704003400c8a80b0381c540e00050b040f0b0100c5d8003108140320140c9070980e2000c050710380c5000f02d00c0c144000c02400000c00300c5035071500c030b2030600c584050352514401d10031405039080660002c603511031480e8460b25485007042502150a04503d43c42c034840014036030303540c80403601c1c0340a4400c1034018900c1d1038000c800488107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 353392410 1250 353391160 353391173
    0x1e0e01050115020309100309061805070b070c030204053d05100215040204021b030409180209011202060d0c0e040b090c07030c050a0b0f040302010c140d02030415020412 74
    0x60b005681d0034594080d031204029000000c42d496070005440c5009544520031048000f410700d400001c200c20f00341039480c400402070032800c5c0750581c051010740b10560b03520074040f0074512640400420802d003040003003002d86025448164040700e50f415080f4a5207040f02c44400300d1200c010107040c5c034840c81c005e045401d40c01480321405400113a495100c80d0140b80400b9603a03107004a1424902a940c0d0000750454483e80c054400c0c2010401101e2105154400c85503242d03001405180d551902d0001c1443c4004180e8074442e0320f55401415004059003009030228040d544914283d81002040000c03142c030001620a8800845885c0d4414a15178402403c000585801e0340301c5510403410b80e010b0213000c030000001c81e41401e0f030508281071420000d162103401e101c203410000c0c1080d803450b4104800d803402284030600c00c2c0e200e94002c00c4480403080043e10a8082d00342c080ca0261014816285e406141b42e00850300b16008131000640480903d1424080e40d00a4000e00d0003403010441c0f20081188 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 353393660 1250 353392410 353392421
    0x17130f121106101514040f060311031611122701020d021009031101141801020703050a031a031b04060b090904020f12070b04031202010e0d080a1e0e01 66
    0x112032002c2c14103400d042000781c0d1110748070b0048100740501d590850385018020000440001d40e492150394803650340d03e001c800035682602c5900003280c2800800700003194400d046070f00c1242c1c0c902c04421840d03101c02c801c554442555800c0701c89072107a051910546000007000d840000c00d101c50740000c183e8114110064601c441d44107a066505c0074002a08040c2c0100d50309d071045100ca180041c12100d03508085450b80c107042e102e03950552901c805a000f00320b6000400d441800e180f9a10f0110342200c4402c5400c0340305103c0007500003241070000303c040e28070a810030740c0e280e44518a0491b580460600007030800031a405210b0070a600301c00301c810181814081c20b801030135001c83d4a81041325003400f041c021540200028421442030094840f00d1359505080d540d46651902241c400382d894a25001c00c0d58020b0101f41c1da113200d991103503800c075407050148c1100c42c01c010303003c1c0c090a601144140e0798a980640b501700303200c0c0c440000d055169050b1034a100c0000d100603021071a07000440d00e0a08598 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 353394910 1250 353393660 353393687
    0xb0304140a0506011a0403020402040f14120a03030c050408010e0f0c01030b0a0506030604090503030109050405072103031509020f0910020106081225110103050a0203060117130f12 79
    0x300715030000400302c1d00228071030341155613000008010014840ea424030510894000950151021501103000c11500818905441001c4603100503142c0201c10404801e007414607050b03d951200c0d14100009100742c1048189000605080b410a92900829030a4480740440d00c0d0f4a075114025030a4600c60030041f14840c10800c0c07c0422115a05101103542d1304650300030140220400401301d0500d441f0b552080807001c0d0083c064a480b541c45103400310140105a07010f490900c01c02c1c20125449849442100600c0e9454400f06235280349650290041c201030001c02c3d0040604100008050201340000c000074540741d11820781c0c402c061303800c1240e0b812403485180111380c5400001d0103500c0700028040c0f040320142120a40315038101d151780300d811048860013080d01a088a20f10308001c4001c8400d400d407042601c0034442caa42d6069488200d0004540c1d43e030000d6400200c144008541d1400e4036003000c400c41c180030508a1503254100c008100d80821100c5812000c00800f100303a00402c0c1c101c482 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 353396160 1250 353394910 353394913
    0x1406010509211c0f03050109151403030c0a03020a0c0506031006030905010605061917070905010c1103070608010509180c0103020f0c250b0304080909091f060915150e0102160b030414 80
    0x900f240304270000c820114001c0c41aa06000341c84540290740030016a022400042c0c00c44081a80a180007500e5440c48030003202c0000d4486404100c0c2d29003001541d2041c480c40d8034602035585801021809402411006d4900303558500c0042815110350300101369000c260b40001c1c4541290340e00003019135901034070a80051240b1410b00000710340c840c800400711003003440c103a032030756140b420170001c81e5020040f200d9040c0b0890300c000965640151340300d4102e03201154182e901d503a8001045540c44d0300329001041030707040f07881e40c05d00d01d6000358080c101c0058000300c4c080c100803007080c0d0907141c400301150320003403254001c010540c0480c030b82003482c016060440700d25003181400e40e500c01003070003020f2495125050a200160b1032505c200004104120918031183c8a8010304462600070300d03007030080f44a2542020b01d55040340080022100440b03050024009070481988821031b09040701001c070750b0440c0145074032800c5105188034000040d0500e0110607580381042d25140b8910b200074821418a13 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 353397410 1250 353396160 353396171
    0x5090a0f0807030206030c13091b080f0711030417070306060503030c0c01051e0d0f0e010e100c0513090c0207060309030c0b04050c12011406010509211c0f03050109 72
    0x14941d002c221070040b41d6040d80d10503125121340c1c0b03107114180101070000341c40d1250080005481c0c51140c0000090f0110400d0341d0383d0100581c50111040c8008460704002020080041a0700c0340c4515000319001c41020103881c01c040e1540000e94511887e0f001d440d00c2980058010f000703100041c801c1000a1000710000c5242443d1103038a80d44440741940d085041c06008100c89043c1c800f1109004c213103440c0c0c00241d43d40c4514500e4100c0082c02c0007084e550115240508900c10314070b05129a40404500900415102ca241c58107c00035001144500c0208401803040c48816100d9105070005489a08ad0108011003038400091501c1410342c828401c1604000021011a8001001725805900111003445030f40d56070404038500a20204110340110040b001c0e20041e070010351083e20710030a1307015040b42d103131100c40c01150580038080341598446440500407548100031109a001034002c03c2c1651400108120120f04e054080340240b03000c208240914800d5580c5031007014054240c0f14401c018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 353398660 1250 353397410 353397419
    0xf0216030f1e05100b010207030605190e071a03040f0609080d0c020c0631140a05040605030c010813080a170604060807060c0615080c03070918121e05090a0f 69
    0x19100e11004c03851aa6503910152008280d1080c8864005150000c10a0000f8100200103188901482c51961011403404d0011a640e0401040103c11034001c135100d100d07507112203206a41543d1000c0d03c101c8cc00000408541d0006010f400740c030004a0242604c5a2940806c05071441652104640c56046401c850350302c0e0019900d0b030301500c9403403804c95204ca4405c012400780c407448031100156120020010400050b591340f8581c10f16012010070346106289603920014441507411b540191581600240c0107240594131a448095001104a01c1d1012003420380d151144154004518907000484000d031440111074a0082a500050252002c00500340790988030f580300d0040d405040108004a00c40005100441e041038800414801b840c8048995490049949003501300f4a14041c3c081c2403c0014421007901c1003a102d8600c007001ca6200c1d1081e5a201403000d4140d203100d409100410b01051201101003030ba110a001c00d50325225620420001004080420b50744000401592100e0a20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 353399910 1250 353398660 353398663
    0x40806070903050a0b090f01050108030c07060e0a21150506010801060f020a0b0916090b0922080a2d09080f1018080708040e01050a0b0a0f0216030f1e05 67
    0x103413850b081240e448442d01d50850301818065040c402584130341c00c0400118001601100410760042c40c2011120050303a540800c0d141d00c0e40500c23485a0008005000f0402e0110f01d8020042aa00606150400244507500c0c070003004c0303c580645030210743d03980400c03e0558004480138090038090804003072880c00002e00039034400100200814601c040c2000c00c0030b142d41000641c1032500f4614a03c040079031514081c6005221275074a1601c20240d030070100d031600103843c090b081c1c01d580000c403140380d0034003a86801c5155403000c12144208140000c0c842c4511a0f000c001c003202d400b410341880e0300003c034000e0060102c285500044e0854000c009020201c810000d04000d55285540003c5115201c0f405100d40d00130b1010300280c0340d002c2c0014008204042400208283c07403407218105010b1f4bc9a0091104c44006400b40302005d8000300400e01c0814050301c180c001d100c1c19413040740c00300362030107400d254040b0b140e520031141c0c800034034801d508004034442c09ea186601d03100d00303081d5501d20a03220315 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 353401160 1250 353399910 353399923
    0x50a0813051c11070b03040203251505090406060302030603010b01031a21030408060103050709050606070204090606090e0304090f090804210501050f181b0f010302070212010204080607090305 84
    0x307401e040692407040a000380180100c0c1c3c81d210102042e208030540c0d81c1d8000400e40d0045034102e2281c000c030423404207a0500346225507610700f028518440c0316070410340c1c0c540003842e0000c0c090f8288003060000042a9940740184005040e0640e80940c503804d000c400d0500395403c4000e4036040c1421302d900e100f019801a41880486001114034151000d001101c036036000b801511148890f01000501151120000651604983c81070b011140600d6542c41204111b070780c1070719039585c010005c1021030054a0f240e00b1000c282c5001d1031001400b969581d25440440e0300c0310820304602c0c3c2000c2001c002da041548514036246841c44418081d6181030303aa5000c1138402c0c0d0140001a40309211091040280794102141e07440d8404002c01c10ba003000d0070005079207401240d143c07110000c0c0044142d024500400d9600401104107020399880d6140c404101c1c010b035040740e8613070401d0390900c0464096542c45000304801ca851b840016a40e83c1401551410070380020000c00034011503003c100300041d00010345 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 353402410 1250 353401160 353401183
    0x80901140126060f2404020a03020c16140603190c0906030c02030906040b031b0d02091f02100509030f130e06010804170304031b0606180606211407050a081305 70
    0x9800d0540030003142d200e020300303005d00b1103802c507101142d030700d0b1004d41541c000c000744210f85040b03034145003181491724607010060085001c4a4801d00c46e4803043d00340440515002010f05e80a81c24013400501d0f000f04448988a141707000501002082003541d80501c121101020a0310142d8036048851001ca061880345201e20900e084000000580e42a42e003107014550700fa030a040f003542c8034002c5903040c001e5000a10301070310031101001e4000c566a030740c0c07a410316020465006402103c240c503101c0f6000b40130003800900035000400c507405104900c0e2005243c04900c0c5002417811a0610305020919003008199506008100c824000490105990140f107810f44100315684e035600c80c6000c550f10225089203080e64144500b040c010801c49030405002d81d400ca009141c1d4011500c2e1560060320325512841000c0380110b0300c0c04002c681d000200d00c8110070041004510a034406604446ca00302c12503010000500100310031120710740c00030b9229084030403071191800c151543d495040c0c44002d450b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 353403660 1250 353402410 353402431
    0xb03061203070b07031e0203011511011803020a0b0c250303021b010504111e2b0b0a0509120405060711100c06110c070303080901140126060f 62
    0x142501020410001c0b03403074295100000c5401414681c2014014044d40380da01c00c810351024620060080c41407003034074100c80500354800150031181500395a01c00c09c82c50304041d50b5407601002c0c10b0180700002c5400250744264018050380c480d5040103500500041c105103c500002c101040c1d0000c505c2c109180132121414801ca0f10540c0c926003500244620215000010b01a00b510701c11242c042d844a8880d0780500701482166500e0000c00074010b51403000b8201c5411404038a4807142440c4030039030054080c10007061200b4603032040c1c400404000031001c9070f0500350300c0e04218a022032401281d400403100310080104d40c2321040d41030028019801035a00440000c54000203000005541d0031031044042c001d80c0c2440c899000081c400c0610300015642103050a0000142011041c1143c140c002c01c00701071310908d825075404403021900a05481c501d5900d800d505914021200ca8050080030094180c01141c80c3d03208101003401c40c0312508070380310380000c0104010403111005c155400400d040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 353404910 1250 353403660 353403679
    0x30606061809150301140c030c0d06030206031305070b07020a03061e061719020901060804211e020303070e0f120304080705011701081f0204081615090b0306 69
    0x400d09801d091004221550091000082c800700c21030260902c0c0814809400a1001e0992201580c0d04100c041d105490f01107410000164000318110160800084929020540300c2d602c6c0c002500036002912404254001d2240c400100002004890020001d4083c400e06143c0b40e81c00042c80f00c2064880502503d480d0003d60080c070254000107140080020400c100840c1c03104100603481d0111282207520784100038903480818500f00e0714403c03165008018800321381c20540110b0721070700c1c0640101c8100e41581803018000c0c40039861841000768a40d100d0011541008440c0807000610350800c09540042007808207495002c1460316910b43e054905e1103501600a010030801951914800001d0001140c0800d0701300001c2103081c11500c0c26030710001c460030400c070308041d000000c0c402c9502c60381c450035814405004508030700242d01044400141400d03916940e02e400c0c4420900c0580c140c0c1d00494050001001c400c04c0c4d461035444502d07200c0c6060703040508400c45403001500c09441400d040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 353406160 1250 353404910 353404927
    0x40312020d0e1903021002040b07112106040b0105181303090812030a050703180f24020c010c09061d1302040e04150902280e15090f01030203060606 65
    0xb82c10050780c51000404071112920b00d07504416050410300720840050003405100c41c8040c3c01030082d01c0581d4030b11100c444c6040281e558a4650f1110398503040c1d000032807030652480c460410401d041d030052104020f05201e180c03030302d005401147c05030806842030120711440b0510300100021305900408101d1000c00c00b0456090a4504226650281c4410702c03d42c0e440c81c4880b02d00e076011f1401448180c806101a4582400941c2600c0c0420030301d40d9881e4007400d083c004640c0d002540c40405001d0310200c001d411030752021416070b0841100c0c056805400049662260401340f0550310302d00500d04c0d15002440c02c15000902c6a088003044046030580f06140c07410b503a45100c0401c0d03000907016021981c5e02c5e030b11020140365840c112400c1e42d540103010300c1c6410f461f003e4024081034a07801450302d10174090001c00d0f500070020a15070246502e81c1c1c0d45002c10b0b0803d6014520b40906a0310910f96078207070018007001002071005024081100c80c0500400c010303103000841c55000f00d1f0031074262b6142c9400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 353407410 1250 353406160 353406187
    0xd14040f12051c09060207080f15100315050603150603031603050f0a0306050907020102030f0c031e040c092f030c160f1202010b010c03050d0b03160f050904031202 72
    0xc0f25240c0400c0c16080c07040b0203c0381c0001c0d40c0c400b01e0b03045400b0355a00d80d81e210040758440452101e030091075080a50701c03d503c824500324644e400260b18030040d481513126203403440e070400c80814005445989400744081031030100706d60340001d80400c9218805140081c0801d459002d841201203104020034001c004150041c0140c4000061240d0820b0b102c280d2001c005018001c80e00c07446009a42110100f90704601c18021a48505800e0101803a00e031034802c2a5501c070b501c010445100d03041d80c07684c1c544000b0340c03544450780940c0c01481c031440010f007003085082c11521340c403180560071840035130200fa448540c0c0307411070007203101c00a0032a1295a504103a104512548a519002c2c1074841e807003c04010480348038401441c050690340308000800b01041e403c8808015104e400704011025503400070f0302c680c001f8210007044502c04684a00d555020070302c5e205c00441103600c6009802024061040d011900c4401000115881089410103031800303007400d60315123282086c040e00010380400c200d49 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 353408660 1250 353407410 353407423
    0x200a03080d110c010f050106080903030105010f05072001020f0a022206030b07110c062506020409020409050402030f010c0f03020f1204050c03010c020f1509010e0303090d14040f1205 80
    0x3220a0400d40e6a0850783c1418001c3c188500881c0d103261400e000801d849100341c60752449500320303000451859003448019111801840c20071410400c0400c01c1d0000258410302c3c04c024501002d07494800210b81e0000642060184426a01c02d0381c8000c0c0c080c0c01595070004c038909484002d4030803034102d0f01c031800900702a0065030806003104023610180541e041d44000922a905030500030b0310040b0038070b0020030030140f0903900303130000d81040c04540c0c000741d591004d80f07188120b00c9400e0042c070700b0b50b80b0490007082ea00030707900c90300405603240200025404c0c244290085100300e00020000381d00742e108080c20b0b10301c11101c1c1204141e4049000f46801c4000340440f101170300c2846108499181501c4c2c41503480d40c528552900035401d180444003068000648030500806c00e070080c01d81001c2e200c00c11001a14010120115076480b00b144600303c50060008600038402d5901401e006071043ca8003424a0011844a2807403002c200002c0003140030480d24a4281c43d00311410040c42841403c3c400c1ca02007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 353409910 1250 353408660 353408681
    0x7051803070506070c0602060c1827070c0212120f160501060e0618040c05010e011e320a0c0809210f010905032a030307020604200a03080d 61
    0x95040502c41d2417000d80f0304907201507089450703903695101c0c049568082c01404460344803008059a00a203403000d104082c26007a20000c0008610611820b401b09409a42c0e04000c200d54020b0300017541401d40f00380080c0d48690300103080020301c0741c0001c0c040e4030440800b034002a001182013a4080182e90102029a80020080c00a2a1141c0042d801010281c428600c034240c5451101d0829140b5903c05100b0798228014800f014a0400152216104508028100820344500707c00c01407000d401060095401c1d51108400d44210000c00d08440301020884a012841344250f18100030741c40448485c10042d2522200818403440c0040043c021045d8195000098240f03450400307a8100000c5d21103541002103548400f03850000901322a03401c0c902902030303001049005407044496040303010140400440130992081c09101c242150001e81c2d0620040e00700000780b20070b0107080d0507290b03016410320a1040100c002080007840098107440018281000807401152082c0e480d4400c64440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353411160 1250 353409910 353409919
    0xb130201140f090a050d0203060613060b0309070311010206010305193e041e0b0d080c0c03011b050703030e010e1615080403050d0f0207021c0201020f06070518030705 73
    0x90a19400241e4603402000f4101d01426000100045515141c1441180039401401921440e25000d0a1004105402039100c20080d140c2c100080c901d00e505008503c1034003a00080c01c2c2e00d50843c50110520f0341601540e50443d03021000600209102180011a40b00e420918070941140380c0b402244400400980c503072507200141b0700f101d03800c0c2440c00c094191409142c100c480540c441d0200000c4940021805004c00d54500350803a80c00990341c424080c5030b00043c017401004480d661b541606510a0f002031105800822015a00d0304090191103075501090780703100740449280d40000c00178003440101504158440000740c424540070344c0146240350015068590080d501030030502880000e1040b40301da034002d2060307005d201e48a9121a0b000d01c0e815500e00c0c0ca4003035006c10f0b10002d880050589040c8660030014080142d036031581002e029041c20400318001341690001900f0000040e00d005625040107003000301269011044034003211211600c482d9800803000400d180c41c0e480d820040c1c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 353412410 1250 353411160 353411167
    0x120908030f03270a030807021b120a02040501120606050409030c020405180f03090a09060f12140a060f14010503060a0903030b060a030603121404090c0e0d08090f030102070b13020114 80
    0x741d03c00305003000540e001c0e440348925034840310401c070307a03914602c0d40c02d9050009009070142c0626001d00e00400e00d055500444440c0006a0009411203d00b1380c011010b006030260154100b0100d405080020401101d041140384420340b0040c01920840c0002445a43c1e54000204c014030564a803540c03001081040f0f904821280c080241d4035032100102510850b1044070001d4800d025015a5050341e201d80300c1c00c6440342c0361403640054002c0e401c40c1128010940f000641900900304000d090700d500841d4041a0032400c0b0496500b12450301a03081e001601000050120b51800a00190000030710040061181d29604017100142451710503e60b02040005103001c03600d03890740102c4242ca0194500610b4030008035000d4803113951030f40c44c0003180ba9040c80308100b03820071544110900b50640c02c0c10011504400c0001e012040c0340c500403142c082000ca01e010a50910800314010b08006500071031500350151190311105600a00120084040c88081c20440e4032401c3d10880c210340d1040020386 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 353413660 1250 353412410 353412481
    0x1806070504091103060a03020d020604180209042901050c0f2d0d12020a120e010915090f020d02011715240703080a0204050a090207120908030f03 64
    0x8140e100d40709007500c0b141043c00703083c1205036000449020700802040130591620316424001c5440c6040c41c16079000303100f0702c4005041d031402c0742c10ba03592086200e40180d0f94140c903001c01044070b5902c08280340c50b0383e4404000c40c80b0720281c0300b90b040c151000d080640d1110910000545000c11940448180e80a22000400c10820101e401c450601500e040502c000d42203000e4299202882e1003810700040e0030391050f52070944150300500011441c3d213015694000c4a25849060701d200b000d15038450703950f4160070024070984503607080494440c0e22090003440044c1d120702d468055207003000780c403030124413008104580c0180070110300d0f0081c008440c011803425850180321011500c4105000d0103143c480c0003805a0a20640345000c01c036100024280705440c3c80441c3d0003c2d000300700c051100e0f42008017042986c3d4a424503001007001074005683c6060a10300388040c83c011a40480502c1080001801040404801d03101250001507680b40c9a94403852948420340f450318180055040b2a070740509e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 353414910 1250 353413660 353413667
    0xf070b060d0302150a090f0809091b04030204021c060f030611030103080d090f140706020f030313030810091a0f10050a0c0201020a140106051f0207030209180607 71
    0x5005a124a20564480060248149480704000c005811079070064480800781a0400d030441400840050310018542d074070251030940040550b800c00d0040b91070380e40343c503100042a03488076030034142d413a214a4040586402d400365000c000d21031600403900c07800c03008410300e800500300d00c4980c0034000e25580f03407103500c40450180801d071551405c04004001800e6500c080740d04076907101d0070f003928000301c0f000e40344010040d0240c1201d510407503849001c0410070301e4244200f650aa40083c0c11a54946540030340707019184809040c3da50801d1040180b9400d070079256441050300344c10207002c0381d039a0140a416415058108502980c54024400340500480d0410181d804c0b00340d913000310700301841003040b40d40311001c1c1174034000035400c0090316180345c441c540355103c2600c1801141e1440303510380d84240f010003810080c003426030354a260821442c5024034050028400d00b06c9a0304200083d000300a45038400c50101138062a0010041500a460071040400e0700409a06403451401d142d54000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 353416160 1250 353414910 353414917
    0x3060112081309090c0b040e0705030603100c02031b0a080301060302130b0a0e0406050915040f0b090a14010f0605030f10030f03030506010f03020f040312030e1b0109121a0405010209060f 82
    0x1d84401a05c0200070810900c2141202c054810607000c1d10051380e52100c0450b41648028032a54040c02205032000d040d4420780108420008960061610380341441d910580000c400e044110195001020250115001b4000ca0741511503a10300565078192601c40c22401582642c090101e03a0030000b9020080c07984a82d009030300760740c2207400348005650794040003204038040c0c4842000c07503121800e0100c81d10303182c0c0c00311040d0040e01c100491210f2a4030006a6010340480b00700030041d403107140440441e0754001074075000d0301d00607030801e40709404e20f0070080c0f05000007040c424800142c113000c01e82946d80040401c00850741305050109040c1d01c0d10700107014080036955a40420180c20310042440d00a00035198070b00004407005060078030350b4445428102c041d082c0c190a1640d508071114143d0000e1140085800242c0ba004044401c10030005104803066800036601941d03a4031400000380740060b512166150101c0b521605840d02e0421500900c506130a060388401c00041062100c852003025 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 353417266 1106 353416160 353416163
    0xf07030c110109060203060a0501020706050f0c0c0604080f010b0a060f0302071a0c030912030606271002011d030408060f070504050a090b0f0406050306011208130909 73
    0x101c074215265800155107490f00042000b242e800d020303030184002e02c002e200501c115403030004000c1143c0200a250503103000000340e210038518080041403158040100500e5986076207002442d039420b030408140d4140e5080070f5050440d440d003d02a0f0b4111407941e19040301d414181001103000b984044000c1305c0098284c802a021000c034840c0c401c0c820b48064030050394906003401d0640c03910720010b1041e0450340c810810400b00792100e40c20750726078268015401e1486002030310121031440302450b10f182c0002c0d0014031200780c83d5054118003e0030000d07640c2062100040707106503850303101e18000c602c80c5911200104051445c80411107a111005140c003600740f41d128000100d010845600c0880c103151948450001307403500c020084a2404103ca04201c841d2074080404d4591070140f003580600414401804140305122007110304101c110340c00b044c1401d44402c0d0450080212040 = true := by decide +kernel

theorem cover : BRFrame.Cov 353237410 353417266 := by
  have h0 := BRFrame.cov_init 353237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 353237410 ≤ n) (h2 : n < 353417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
