-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:22.699802+00:00
-- url     : https://prove2.me/submissions/11bb9c43-f333-4a3f-901f-7c6d7dbd77c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 368884892 ≤ n < 369064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 368886142 1250 368884892 368884897
    0x909050f06120309043b12130909080d0e0303070c061107020a0b0d050c04181107060c080a05010501030c08131406010803040e060109052103090a08070510050f 70
    0x600441c0e1100102e10078040c20360075405000c00b081e0f0700a240003180d5a040c14410809600c08401501c4184c3c0c5c01c02944d8203501c690040c0707502416985c440c007510720300d4821700343c000c105c400c4001030301620059507042800709a07109020b04407011100441c24804190090081800a410300d07805141189002c680040c49050104009080d1580b103130303103529460a451080790f90f10780d0042e1440c81c034161a04030211907648480c0d0700c82622850003000801d503e07144401d0700c0503100c20854240080e1590810400034000300c0384c034100e0440c41040041c0010320075101d0030341044a1030300c460360383d841d08260100860740160b0109050500708180c0040b8642d000010507884022508280082a480d0816260a01e07026012291500c00d0300004161a180040a0001c0720111615002e8540c0e0b823000443c2c03008801c1c030640c0e40041010b0103c1707940b403d04821a20001805000326820030b13001c40c00040568803168020a0f40350081d440074401824048840044605181000780c6000b0343c0000342682031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 368887392 1250 368886142 368886151
    0xf090602030a031a03010606111006240918051605031303030207080c010216050106150c020904050c13060e0c09090417040803030a020904200d1a0307060e010909050f 73
    0x15940e02101320984620700d40c41062140040c000b08406520390344007400280703024403403448510484480c0364003200240910825144140070050380e401c4411112104420040c102005200b06400045000801004a142c03c0440720a0208280c105003074154281a02a145402040410802c024000311001050054264103180040c2c1d50b0401b800d24004038010030708040400d500024400c0810b02c030851f0300000c2c050003403008224940d031326403540c05c245a00040c0c0c04082001c07001e1500262610350b1780d455000340218283d40c106820403000400c0e400040c92400702066480c1d100340b10f080045000281e00c60a05e2005626015040000a4060301c0040009011245030301034046150114015640200003074822640c49041050620300a50088150b41d4000c034504294841d402e1004104500c082d41580c200b2480d24501c0c445190103411840b03201c01080b01040d91201150700c0800c0158002d04a60750b90b0f40100030905c000515a0b11079500800009040c5810300181e411a2800300d07400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 368888642 1250 368887392 368887397
    0x24150406030804060507080f030405060105120c0d06050705130f06090806131419030c120507120e0d020d0507080708030703021209040605090405010506040c02010903020a061109030a030f0f090602030a 88
    0x90311b031103140812403403050300000b82e166140481408200540050b542c2c2c1a0b95080307422102030300744138015656031000c1c0c08440703500003690020b0101141480d07000c1d0b6002141444c0843c50510714800324be45c40d07182c0d54010360806100314810821580e000755800041e01d800c3d40504494285174241e100c24841e900f030094003001081c0c4007410016010009104d6105000d119003c204c4680d05010301451148042540e0307150844070054002d51141d0300b241c09103a44080140c0e1111b000c29404c8a43d80c041180e126008168005403202682d10041600b03240c41c070a0006008150510003c00d0400303000e503101807850790050081c034001a4004c25940301611f003540405482e10382d8580017030040d2002c1d0f8021707074105880f042030005101040d080544150701c240c030240010000100101c0c00c82d0610387d8040d005030801321192002030b541ea0040003030050040c0d54241041c0c0c10900082c144180e80204070b0100fa03101d03104031b020079008401c0118005241c1400c0d2412072030940060740324855407004904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 368889892 1250 368888642 368888647
    0xb0105090a0b0f191e03020f030411040b030109060203090d09032103150b0702010f0801060c080705330c0304020d061e0f06080105010905010f05010c05241504060308040605 76
    0xb1a03e21004e0b6106400c540000e841384500b02030000d858a42109000c201a00c402090710807528004d00881354518000d8200c0f500d1640c0d25140c3c40129100c0e2881c1c40d52203a120f0410060390780d000d0086030381c280e00500006a0740c0c2070020641c0e00c0d042281d01c102e018411803250800204100da011915180c041c1c1c182e450300c04050660440050604600e0304518000c80c0c24013181c00100140541070241c800e88600400102c0d080054070360010900c03031140043c482e10380000000d03180b6806070000e90703c542e04a400040b40d02102c400c8101d40d84070142114000924001c440781e00d408402604000943e9040c0e00e1410960007041040410407405002d030360320b425403402d0100e1050049000c0803420a0704000c03030840800380001a02c1c0520a2408640c2080d00101e107100061040078121034001c1ea41c041024504001926010f01004c0161a6809184c804044842000d4200310002d0754000500045160140c00d07041c500001002681c05140780240c244006003c6504036402c5d59440c0c00c0c00c58 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 368891142 1250 368889892 368889907
    0x503031f0911121305011b030f1a0105071b0308070c0f05010c0605090f0a060f06050405101205120310061103070b0411030a050102120a0b120703020d1502070507030203010b0105090a0b 81
    0x40004d80729000400c20343ca000403030703550503043e2601900300c034030b10340d500b401110311895550b02545c400d2204100c04a55510f54260a503000d400104012446400e1024004102d4140427034080c5081c3d00c00d582c1842c00240d420104080d558440c0060a04041804545400c3c400020020081090b00070043e6643d034001c2540d4840801c4107803204076450341103484d40917440c40d002c0c001d4a01c0d01d00c0f05c60784a04140011a10749014041c8500c201d000f00c1008000303d182c0168003040030400c20060310140100706100d6008241e081c01035205604050008580c1c03850706900408888900700111040d400500110b800600d5860720250001d400c490381b10400001080003900f4010080401082588002100c5400c000040c06451050100520800c003030071095042c40f0641e00c0070901c52480b50010324051006181c07040b541c01d801030045c030402076104408043e44003283d00c411019500e542c400c0d9010811407a09010301c00300400e0a10340f16041c2200302020555607215401102c0d07441d9004035203103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 368892392 1250 368891142 368891161
    0xc020a0f080f09040c0309060b0a05090a020d02090a080703050d090308092e03090210020c0120101406041d03070803040203160f2405090609030a0503031f091112 71
    0x11001c00c2c42c01401000a0a560100036004040071f074022900e42c1c0c1080750031032191402e4100f10342221070140143c0010f0703441880c10002984005a4505529401e00c0000035035110944035001401440c40209181800c60414a19096890000c1000c00046075014000918411300f039981d030f58002d85144d28460005000481c500c15402c00d41d07500402c00002e00c44c03480c0d03410341001310342500039102c0e260524040c84d001ca03101d403225110240400c440c1d6a0f4003056034480858940703074a00b40406d0710040d0707005188000c1aa0f100d09400d03400180780d0780034049c1c00d251500c41d09c520b04481072803803034001c109004240c0e1640101003029100590120024056480038010802c244002e440c00700645a2a000400c40c15000d501032020b00500c0d000b5850003c10703c6500420032190141c4405051107001d00402544d94054450705805024842c070000c0040c03070810240d0b004148501003c0c424140702003d0300303031407040c951102c100a81029200341c00318141d1011200b141480e12280314195aa407010f4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 368893642 1250 368892392 368892397
    0x30f180204152304050604020f160303060e0a0504050d020615060c0102042c010e0402010e041122061803020a06030c050c0303010803031b0304020a0e0709030c090c030c020a0f080f 79
    0x45911491560950380074041c11180ea05801000c0303500b0010f0351205021f000c1203008205400844000c204400c444944012400090079886460003080007526550f840120f001c080d504000c04984482c02c0c00100311081c0810381c00081e1520040076541351601140540c2c10b14115240d00405000495024658003901194050040b28400d840c08240d520b88103c403804549a030803454145960001c540401d52105141c080c90301652031040d40c40500040100610014408400c12082005548000100380e2041d0001c1c8650b101a0103541d4034040025001d461504400540105d9010080c40140e03914030380502a2485407800041e00c0d114540140c90034421540c03882a144004400025401300000041d0310410b11075210300c1a144010385200018001617400035030080304010140442c66078000e0469000d0b82d1071808175003c40d80c03900c61034403803482500a1520310b03843d1604040c2694050154480300c420078802001014441e4603840001c5100b0341c0000c006400015581d410040d40c07009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 368894892 1250 368893642 368893649
    0xf02070e01031118010617071b030206070e010c0201140c12070b04030f0306080a06090503090a140a0807060801170304180903080a0c0c0f08071b0303030f18020415 72
    0x1995421542c60781429090b42c645010076511a49007160b03064000a160340c4114121031450b1160b022004041070915050180200401c00700134800700e83d64403184141804d400410702a030040c2c0010300340036000410160f801c0c020181444903907078a800041c2d910241c285080064498050348682c80301070707800d090002c11803900c80e01e800c012402e0340a00c1241d01c88540207901c00c1d1030303001d50660b2040050741035404078440c11a04e600080d0001021409582205090f03a00c01ca00b600d03c2c0101d950b00040d280c41141d040701d6015044080941400d0802c800d540025002480040c01d800340381c01002072050105000303200607401c081010400340c400420654000c1d20480d80300c400c80799926090341008164524040e0009188140418420083c038442d91744c008002e0341c0d98581d15407641c0c0303503950500f80351402161440c4c02001200702061143e80c10750809880c00c00c00800080c510b040040c291542c844242c0714061400b5003480001e01001000d80c0c2065040d5070205172a05150310581e40000d041c3d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 368896142 1250 368894892 368894909
    0x60f050d090210020312070c081207090509090a1a13031107050a06030c0f030c080105061e041706070801060f11150c0309072916080c0c09070f080105010f0207 70
    0x2c55028a03e0303008006080343c06010007400903d5a0341200864501c0440e00015001ca0410400341040c50070344004694407442d5420304d14081656070f004100102d008494005058000625403000c010f16481e41c0401c1d02c030480d4181406060040e204050044850001400e0203104035a80c80480c03024031443d0001e00c8010007010410707545100c060040c041071581880028668188007c4907802031180703540c001c000b0f81d1820480d81c00e02051210552054480595104401c1100e0020f402188011710150543c2d48811902405291480d840e20b4030160140c3c00b0710222100610620354405105194017040b403038850300050000e250641000519a4035440c18816681003003848800040218004d0001600312000d00c0d50343c0c2c4403004e46124840c04030106000c012511000315031202d01514950303038400045c0660703682540e036400003580402d01c04540c641009540d51850b241408900d9401001410f060807518a203010081884105001d42c5040c411440c0441210520030080b01c0054815003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 368897392 1250 368896142 368896159
    0x3240f080c060d0903020f1b0127090b03010e07090902180108151302060304060605030606060f040e06120703030e1804260912030c01060f05030a060207030e0402030f0a0e07060f050d0902 82
    0x1d940403060323081c082c5018041000700e0030800c0d062500c420544007500141d403030044c1c0c49080005090251020003240c662540d01c41034080301381d61091000d403005014088000810190501c113000708592041c0100c090b0101100c010040220080780c01c4c81315006c42129058155124100301780c0128104c00080e42008010003040704000565102e80c0a40ea03045049803140c0c3d0382d18082141e540b1030321124008598040c0320400044640d942c030240c10000003080c03006200d03402e10102c2e24107046a4016000036509000c02c000390300307012171440520080c0440f480d413586401d40301e4012144107220a04c2c854258259802d050000c404159040404010f000b111440032400b18103a41c0c0d0408111966603505e07000b000608008401605812554040c0113000d0300160781c0c0701c040c003e400202c419014805484d40c2c0356815a200d10045126524a02c90b140c20340c10039015070005c44a48844484940d0300c01c0d54140006030300010503002802091030006c1d550494100940040d0851100094200642 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 368898642 1250 368897392 368897413
    0x301030b07091d041e1a180a02010e2716020102070c152703021c0308130c1d01060f0804081608040909052b050a0f03240f080c060d0903020f 62
    0x8032000f1261015114078403446d94489440c0003140c450010029140c03680010b030b100d4015402210000d51290380104003a21404103551403030095012410304414640d1a8000c01c8035084845107516080d5245100840c20282c0c103598025041416020b24240c031501024030104036842089005180c292440010b6440210301a445e140894140400c900c10810000007140c1c110007041034610f400c1d015a5100104e450ba103800c1651803440f8281500c14544045002c01c03068a50083c44150303019005100c02d46d90715013180200782a008600034010040b00741c0901000c5807141c07003034910480c10905141c0103980a03180a0b0f59501c515800301100d1410400316030184400460030072040c11112400052084281c004440c084181d81101004541c081c0b10200f000c920070035910b04001d8a5050000b940b407514221803502071141c20341000b00303640144c000d01203488800c0d0f81c5401042100000c00801e017079003000030f01a004a03e0081c403020b654004c1071007450302c208500b1000c6101d820649040524 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 368899892 1250 368898642 368898653
    0x170d0e0f010b04180305091c05060105280501081f08033103030503060a050405040b010503070609060206180109080a050c0706090e060f0a08030f0301030b07091d041e 73
    0x61040010480c0e520300140a5038506150140c0307854800902d140c180d1208041d036003550140c011041140d040003d24001c0c60903000d10955403d80140a04010001036142004224980d0b50f40c501d0500034000802402c3c0440100d03102c1103094030002d081601d80e0340e99001b80c0070301e03501200c1d0301c0100003002070340001180d003070100040c00c503226009503040300c10078010703007216056a111841c0c100c10300281408201080c0f06901658001000501b082003440ea030300c0020f0b05850b0155400c0c2d618602e0440100100d150400128000381420305140d00118903117074029496a030000c000f42d030710304d4001c1d0001c05140f5082d40040016a030080c882c035110072200307000400742d400031a200607140c40340803004541e00f80101404c0e0111403501d444400d59607194014400640008c104440c2c0001c0080b0001c614160f0500282c00894030144010f0740f00d42c55401c1000f1020000380c0000c0602450300024480c0c2d03803191900000c0701111092403c2e0903251450002110007030001070a01145800c5605401c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 368901142 1250 368899892 368899903
    0x207110f01121410090c08010e13140d02150114130e06070207090b010e092d0a0c0305060f0603060603090309030316060506010305070e12070b030c040509010b1303170d0e 75
    0x20760b40e600c0107515176240e209440489000c0f08440011440400041208241201c0719540c8603019030031900983e03a00d55920100340245580458103a00081c12640500390704016000c02250780c41d0310701c00194034010300c07600080f00e02c1c2c06140c003d01a090350a1a081c2c0107400040d00744c0108402c8034000e250060000b034490340c2d07600408407024140a4079004541c4550070f8070240000007020400543c03624002c00320701e0340303045600070209c0d203010040b000041001841c0e01d21440c8448070104505103c140010100c0d6001840c852085205049012603a16110190396010f42c090707400c0e96817600d5a22030249903001e07110203da45803000050320141c2c01d81064a802ca4940700b0542403100e501e5240040d41070f250f08403500e800051041d00c048006160500d45070030302e110004240c0703440b540c4640b45000e1a07030086039404e1010344000340420280c00c2600d22240104800c0c090981481035440b208502401e55200c040c041c80c13221510400c14102100407038808112000701000360321514800d407038540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 368902392 1250 368901142 368901151
    0xc0206091309121103190e190513050f462712050c1005060a06020304080309061312050f070603061404090c052d040207110f011214 58
    0x102000180701182409900841c001400d4080694200407840940070400070503c2095010011440603028048c0c0381c1003040140203542e070710300820050405041c0402c282c203a600821031180303010200190b0040200710690030042c0c8164680c044800d149011000d0120f481c15a44e0202c030b040714400459004080604881071800e031b09205884803200f002c40c40c000b08101d40d5402c000c0f030050400009070003018102d00143c480c140142440240642c00789040b841d228086e601c50b644000f84022441e04c0802c010003032013240300661138107007001c045c207032640581d0060700c1c000d003004243c403d10024171506000141403941c00c03d85000c452404c04035514012900031a480f0b02070351a0202e42280f00340614410b440c113003281c0b18000d18000003400001c002600d03040c0d42c4c19400c030002117950755448458800300e45c1c03100e5001800703520311000d64410340c1040700001e11480c8104034040025252075000d1040c5c4008460040100f100b20005a4211600d49040e20740c45140c414440c04510480506600a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 368903642 1250 368902392 368902403
    0x6080103021507050c0108070212040602011d06011a07050c13020702130c0c200306130501050f0402150904200409051008030f0f040305120307120911010c0206091309 73
    0xd00c2d02960408581c2d105000d00945190482d80144400e0350040d8003268100900f48100c808007c1a00003908a5130040e40120780180d440306022001c90104106000d00c04440341c001d080c440d45080c070030307141e900b104100401c20743c0c001042103018407405104881a540c2c018001a424404c0480040b000754040202248a01125084a42100f1031072080071a005100e403a0075040d1000d50300e4401402160a01500d001542000300c0705454506200243c001d603460000802c0201d07507407600034251400100300a025880718070070030025948142200700f0954900800302e540f1000382c000302c0d014018003010340340300c0d102c00242c0e11620071030400203000702c40d03148504000b252100d242401c043e01e01446080c3c425401481102d0140d40c10f10010044403001900701854540e40e5520113007843d0805d45502d00800010040000765904100d0301c8091140031002001040b040c1c3c1e682200f41104902c1c094108846030b541d44d07085480c1c01c0119210b800c3d0003048100007010780c0b81e10002030301003114110f44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 368904892 1250 368903642 368903659
    0x30313110603010b07260a03090501270b1e04150b190512011b05090a080706091d06130e011401180e03160b04020105070602120105030c19051302130608010302 70
    0x300003126112207101000015003103240101e411f01c1100a0110288241c1d01035513581e204843c03560171499030300c402400070600400c0c40c400d5401c6c6004c100300001e10300300320244144140703070302c0803603068480b5405a4480365840c400345000140300010b140c0785030000c3d0007603105500300e101105038004000881c0c0c0115445214a108011b80ea403c0e19809890380301450b160104041e0180d006801421010401400c0840ca0a545400d00c03450454580c0c02940891b1303002800f405003d007010040e50400b8280349008829041840129401079030381e41540c00d9141c0d4074146850075000a410452102003c241c030541e855031550303030380180401c944a09407182403070204107209100012098032049403c1030003d140184040d00c0f400d5904100038803c80c100030080102074006400b034805010428049200448030b50304100a051510b07034103a00441c0f282c5010420442250740c224205400d0701c1098540341200e82403440c51502034007400c002c0f18000c244103980400c00360b91107980c09041f68000c0304c2988 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 368906142 1250 368904892 368904923
    0x1050105120109110f030319080411040e06070c21050408010f06030305030c090109051809010605060f0d021b121306091a1b010e07080c06040602030313110603010b07 73
    0x2400c95600f804010903c0700540c186440ea407030815510201000041c1c283d928001d901003a44807525800c203101004180e604090005020034101001a04d1806490821410307100c15a155903801c4003c11200c2040b260088203010826821001140c1d440c46041e286201d90350a00080e000e44c01c40d0080034001d6181801c0d20340310761254040c0034212605a19414035517119204c80d03154580c016281e16052040140700054a43c94083d451240c0072000d01c0d4005c41c50801002003400d5411070303031002d842400140060714490001d01c049801011400c40c00603580c1c0190036580c81d5540d9645001c5646001d504203909010701100001c0004240d020018112207031104000d840c0002a4095010314114a90980aa0000c4400203284441a0384101d401c4c011005450909440c0c25142c101030980101d101041050820000d28007c120304542c00c50905050000080d5680030040000c1100c04040b40000c041c4480c0395070f40e080302100540305a0756503841d07880c0242e042c4d100e200300300d910610240c0c000303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 368907392 1250 368906142 368906179
    0x11502160506091002031204030c02181b09040e060f040510110405010503060112060b0405040e01091109060a0f03030f1116052404140102010b06070c06050a05190201050105 76
    0x150a45100400b510308148444051011081c048110201548400c1040c210710f0f041d002c3c1201c0c4614441c1ea240c44ac02c480910602000300c1140782c0f86005103044070244103810f42100c1c40178030004803000420307440d03a041d0303400035024101c0a44442268060301040c40300d5201c890498a01c01c0c0d009004480102007141b041d18201c4012a110b840740101c24802440300c1c4d88a500110f80011051611803c0d0030155158082116245d80c0101c0b0200300028041006c1d0030580a0030011100441c02088500c2c459141e101c002d0000c8a160b0780304000c1140080c045954a07500480900cc1700740000d04410f40300e180107001c0c0c40020a002022400e40911042038841c0090b19100d03016030b4004d4260083e00c0c107800d005014081801c0c000031491180e080441c01280349010380001c00f02141000c1d00c043c4040006421184c0019020303004a0341080044081000440c0110031604646081691010700d480102da942c082c007071150b1000d00c1226414010681e05421040c1a10070460341d038080f1400f250402d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 368908642 1250 368907392 368907433
    0x70510061203050304060911030f1609110405191701290303071704050409110f060304081903090f0303090c062c040908040e0a0f050c03042009011502 66
    0x2c0004a00300b0002d0001161904414156032244030b41e0003080072104000f9090030240000c9080941c440340c11000e84100845013040240499942000890b210303004185d00f03031003140a002e01440c10600200c0704800c16030317800d10050445c8440c2921102a42120b00c2c040c0c00e501c0ba0041c2c2c5003841c0c86100c20040a8403071480040e1200800851409446075184180415882c1080200343e90500c07000880c0c0d03e56001da200312600c104810324030244403c1c01c10040410343c4d140d05000700e00610810000548240454041103d000340c07005010681000c110050201d021000f0203003000c0e601003104250309a0001d0410b14425006004055210175044601c0b08510101503502c211030840307000f402a01d402101a107210103000441c0c640d8440d11025181ea1040c1c0c84003148034122420040554624880d841c042040c0c02b000744035504000c5010f400c01e00010300003905481c0c04505041204105401b803454003071000d003000d600d544e52480321121100c2041d948501600a41c000c13441c00c606509007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 368909892 1250 368908642 368908679
    0x70c0c09020a081f0b040b1c09020307050d05010f15090c0c02100309030504080a080c0f01061505030a1b030506180108060f040c0305030c1609020304050c042007051006 74
    0x40d001c1c1c1580c1c43c04481500c4c2200c0000e5200800c180141c0843c40d515918000c201508014044a580e06803111184c03140302a90407483c00403e20b402600401603401280c0481160000c9034021a180740a0070410700401540c0d000c65070551600c01140744a00350090030004448480008003c00300882d1815940c40611b007000942c03180501c00f00101c114003903800b68035414000e18042d03003459125640503190025161080d80c0c10240030400b02d00c416400c21001c2c01c524420310080c0039803413030300a61202e0480201c01c01c4050103004000100401d040b50300c00072030010009119145a1107019024008210558555002e5a01c172a091170554000c21440c1c0d040f101580c009000e2070f6180016103280741070103081140c68071100040000417034000c001a007000600d40c0c016000211081d684110000d0341c03039028a40d5140180108400b00c0d10100c0c0c24100c2501c207540100304807000d8020041ea41040307404a5406a42c0400e25005004c03000450540000780c42c0c40401a00741c87d88000c2a4020750f009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 368911142 1250 368909892 368909897
    0x11010305070915030e0a060b100f0906080712090b01060305071701030204020a0e0a0602010b030c04231504090602070c08060f04120c0606032901080706031a09070c0c09020a 76
    0x1d81000002c1003000000b01e400f11629000402c5031192401c541440c00120060f504c403901c698440ea014a844043e00e00e030390343d05003841f0f21801081c84025099824902c00c4405100704040000c09490086080c02110140214108017581c05850072140c000c4084c021440001d1510000401d100c0c0149a2104102c120711082c141c0e036840c5608200195100341d812004001d1002d01620003504c0d0203100c00d024103135580000c108110054185854401d42c1c84245100c3d0b400c05414840d078a203446034059118000300611109a5645907043c10344000700c204603900546030080e50010b04c5a240d018140d01c0d44a85400742d5003030740d05d002003640c504054811250241c0782502107400102ca81e40420521695070901e072003c4403458a40008903401d6034002d0b40c03514640c00c8103854040000ca95032090002c08940c85125504241c40c1c01d5031007c00740180d50a00d961028182c0b9021015046d216440b07900501010041c1791200c00140704040c2c2200888150182d140040703501e10300790080d10603100e0642e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 368912392 1250 368911142 368911157
    0xb030304051504050613090f0504031d010c020a08030a030609020c0606010f0903050304060801090c111b03070e0709031205070b04020906210d090602060108102301121101030507 78
    0xc020080d80034003030050b040041e2001c110019003603c8103409850140607000c00c1c4a4510b15000364101a108880300c0c92010b90310b003008000010b60040c04010140f03c121180c1d2907440f04941c0165a00709008001a41c820300c85000000c1480b0008000c241e1040740f545c1c288151075a888108042c1e01800f40c04100980140000a8071940318203d04010716945241244c4150764130b4480c0b50850f4007540000c0001184803006001c1084540160402c002c00c901e0001000c01c0d103685015112070248285000c102101168240d460307400708044d0001c4c05103d00d01c50412b0400001c0a400d40003a840115200b61318415504503560052080d0740446810400f402070580d141c3d403c00c45e42d100b000306110340c49445d04c2c182d1407200341004040c3c010300c189500248040c6c8018003003c0c08203440d40d4408400c5520890040c800c0410200e12401508015040403034200c4407041803440c1810341156182010f8280f100000e201104828410102ea0190030500c0200800c6001181a104100c4501e00810b040c5d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 368913642 1250 368912392 368912399
    0xf0b1b04050604270f1407210209031614010806010906080105010315080f0c0f0a030201051c1409160e010e060d02040b060a1d100c08070c03150905010e010b030304 72
    0x90000300310000304000c4840107803043e44201201191154440115050354408080350322041000c41a0340100c21410b0540b6842500301540b058200030b004230202c03186d000300e09220aa01c2c02c005a0b007419803481285003401b0f48480040c00c42180f03202049000540260204000354012400354050382c040d640d0359041c603070800d001900606490f03034010031007403100900002c144031305201c8040400c206001034404510008200000122011070452003013007070b900304000507a040f03001c030b070007102003000741040e0041e103004041c00410101c0c900c0c5140360b41c18820400300d01004148030002c22171580b0701e503400c1a1150b4400e403482100b4083c565003564000d011074100d1400c04840e400c02c0348000c1012445072205004508140c03c1a4074407404207828002c0289501d215101e00d44901d5030599501622500d400d01c0101141c0da1054040e00c513440004a480030b0000c94115480a550008401104400c20401a00c028800810700356402e504e01541c0600f90342d418013889031419002802542807606 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 368914892 1250 368913642 368913659
    0x3060a05131e080c06101401050405150706060e07021002180d0203010618091109090a030c11030714090906040b0c0c0f0a06090c0b070c0e0402010c0f0b1b04050604 72
    0x6607103080350711184101552070b0002d583c402c000c1ca000c040c000701811032410000410f14040b540c40d01300c0449052000110703034850742d0020565048600446110203802d113500c6c102549440f440c18090440e03406c140c0c02180c0c0540c8240741c507000b1100c541c00c94203110302020104049020b0300341d00c040402d0221741844038a01d48039030b030428094001000080c120342d9500d0604002d50f2040c410b12945901e4100700024002c6989000742450415200c003016850310804079030312190b00c018000d0034401c0350a100750074130408007200e031401034015046500094440506000c0c186070005900e118940050014500c17034004507a09000342c0e031020300c0050b65142c1c4140e80803580c2003003007102101c4c801c0020508900c9401c006512585018a00000b032203400ca0625001000050308191a0b2020801c41040020018040101140c18051069041d0344a5100413150340746051809014640780e41d00d00c50901140880c08c1d4091248000340c55030945410340a000c02e40220b00c03441d07038051401e0200304507242 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 368916142 1250 368914892 368914913
    0x10e1513020904090b1e10170f030426030c0c01200610090c14030601050912010f05010e06030703020108190603020d0302010c0311030610030903030f0f0b03060a0513 73
    0x16032036015080c0050a070204003110361094090368034a0702e440610000c12982c100e03d40c03500c1181d084811642c60b04203100010520303103102e281c0074101c3d1003c07041c002174418480d1920a40101090f01c2c4e460f99030305216000750180351502c0000b441058186601080f001045031b120420000c05042d03108280b00040d00c0d43c4141d00d05000d848441800c0706241000103101040c0f04402c1100710786000c500300700940007100d280030f0b0800305101800600c0c0626400702406e80303502c0074003440c2148d5510030307210104084501d00d20440c46070750308000d44500400b5854020724165907000c0c0044205030344c0d10042542d54855844043c1c0401d21044c0455605400020701401608202902243c1e42d9a6a804194030040703051050700140d6503080c0e10000b16905008102c4141410a112800d40c208030f40020100070000c0d002d4030078140d44601181c101030217500403404084a0106c1002001e41103900c40c130240c4a1519618424080d03200001c0f25181140f1070313107001d00b108071003446800005954010214 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 368917392 1250 368916142 368916169
    0x21e032e09080d0c0302120a050708011406070b0c03060f1507150207080c0d0206251d04060b040306050f010b040e040f170a020d080405120d061701090308010e15 71
    0x24070341004540c00c506030f03901558065070107585e40142e032100300303e2401d5015900500014030641c00d1009100002d54400c1800b415a1074858150140d40d8403040004d62501c20000003d2602400340200948100310a000e103200d880c080e0b4949540e49416000c1022845101e080506125014007440300810300a144807003030706405400c010b04e803144e282c41f4240301d0303041208181e1080d8850541030901130ba0500c401d94000d40c21900043e2850075240b07154000320412100344080000f0307501c0361501d02d450075000c01403410300540708118a035280d00c2800e0491380180002d48541c0d040c403000c9400707581c510307003894120784400f44401c0c00d242c00d161800601000140041e200240703030400e0071011452800b007400c3c0c50844000241c6c4d0301d19800102038100860f0030384500a004410f070070840401c5011965562194003100107075541c0c03d80e24402401442240c1008414a4012216003170840056101c06a194000e443c1c2c003c40f03030380c1c1d1011400b81c000202c90052103040030031102c8030181071041c4d005510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 368918642 1250 368917392 368917403
    0xc07051903230f0912070305010227031002180a0311030f0c0a03030f020f0607030614040b420d0612050c09040303020d02160606120308150d021e032e09 67
    0x1507243e14102c181b40a807107401c2640c25950001d0260300c90ba402402d514071001c044444284001c1040000030f84072902071316001d02a070b170001102c0c0c400811a10f0b078a680c103840140203114071030316420305490720b05098803064007a200d1030407a000f460300300003050b1040d668010009810035013141d038103c40f012400c04c401810f510510704282103009084c0406441800c00c3d5900245881c5051441452101e07040c0d45a40603d2500840d20002d890f840c200002c03140600300017074074a03000c00501c3c00c072110000f504564000c2c0d8031040c01e119084e50780014071288410b0360f010300c6000d40712000d0598141130a030004041e50702503d41d41c041070800c106410342c4140a41401070400c6400d8044c001664044c5031a8001c5c00510a400403c10460f0b2103682e01030170036107042c0d06085c0c680741d402811000e005044144c05000001e030482c103035a41e184444080c9513014011701c2c8441c46850030b0460311200200b01a00c139000c5c0e00741d0240381658074165002e40b4070001d112461600081e5444c08014102010161503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 368919892 1250 368918642 368918659
    0x1808071a3d03050304060503090d0507020105090405060a1203110f010c0206010e19020c03120702060106170604060305030c0717031e0a020c060a2f0a02090c07051903230f09 76
    0x403c0c0240050f0005154075155659203282c0703900c040d410004036940d440180701d03040c071548000d80d81c0f000580e601d211068800045a4444030006180d02800740e2204000e080d0f414003031010550310a044a59031245101203903502c011800406090b54400c042c204010b9010000400c0003581c00c40c5642d0704040d003400c1c034911100520711104180ea10429070300d100c075440001e009505005141020790b02140c54070107003540d941401401419041c107507415500300c000c3d04000c650540c1da9503000c6001103910408a07583c500900780c100d6142d01d85446005042403168030104501403003c03088540000a081560a89001c0140c8119540c3c1010340180c04501c81c43c0868540c030b458800c01080171501644800040400781c030740d0720200e0a16a00c400340144403410642109540c00160031110360340c1150761403800d0baa0404000f005000350103001d49507205a4a20b13401040581c04508002c50081d622610f00428101c00c0b13151070300013030401280390801080302814201e84031028010341c540c010304022 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 368921142 1250 368919892 368919899
    0x1e02031506090912040504110408061513020306010c0b1302090103030305012d0b0a020a15060302011106040203060103061e15090507090602060a1808071a3d 69
    0xa1801015490581800e001102801294075042003800d0b4000310b400000d101c0300e54003200c405182d003c0c0d4402c0c07602540c2c80ba0001c901d40700c401803d60300034241b0507040303629603d03040032864440324400c01100d008a410085050042c101d03802120b110b0617040c0c6565a828055585904240b40e00810075401d58440d00407680040e0381d0112503078000c5009030340c0480d0650511b910616455000c07191450055020000d40c401c00346143c0b008000c8440c6140b400b40c450301101c205078100f10519a00038017080450764440d00c0c041080d404030040d01c0c000e998540610080f00c1c0500c1c0d0f1903400b83d0b0060350640c42000108001851500090600004041c00c0495014181c134000151908070603051940780d1a110117002c90b1586129031035200040d8030f0b00d004e4052802101944030380015181800c40c1da180e074014000c02e04001d218458403a488541603035030340240e0070400e155092200480d00c0d020125000300314403203281801000010042030241c03000d00b1f4444000c41c404012041d514501036880c50000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 368922392 1250 368921142 368921149
    0xf050c06191404151805060c0724021201050405130f0221070515030f010603020d021e09030d111207020f0307080d0e0a0311061b121c02030f041e02 65
    0x140694030a9107003200318002d030400300061742c0c5651034110318402030700b10000100f4000550b0700e401c0360b08146000d68400351810100021082c0a40301c00d19403001201610700d888040d8000c0c544176806403004040350340c8620410041c0d40d401d0b2a02042c580c0c2c01242c1c00c1c0400c4030320410742c5800e44000c10b880800350030070704040c0001c01392007440d04584d000300c101002241010004010346100585c10345e442e40c43c2c0290000b240301d10600a0000f015404100c1500407001ca80c1203c01c0c0140582814401b900000707a81c02c07030383e48134074504c138003d02401c2c08141c0c1c007a000e40b90054900d90b40002810742c0340102100480c031a0044001603904c5840745441c1041c075141440010f01800740034025080300c042404004d440c46054405603802032014100810100d0030321401145c01d03543c100c500d150303507000102c203114040e103800c01d800c00c1c3e900648440d61620b1392800c004080e411400d6882485500341402e4030002c034002203034007003e58009940010002103641c1e07100040d0411413034908400d20141e4020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 368923642 1250 368922392 368922431
    0x40e01060e0a1d01050603031909050d0609050c010905031c030609060314070b09090a091a0f06010207090b1804020118080d080a15030206090402040306110a0f050c0619 74
    0x403260b02c16554140d03d00340030314035902e81d900c10b0f00c000300a1280c1d00b003040100b03681380301b01d400c00c06507200000805c144442c480c940b01002060300410700c403581000c0341030000042001c83d1089609219000700c2c1c2c01694001d0310450226107008001d4860310341d100000341080807001008000b01981d40002058030382162284001170350207200b284041000502c94a80b800c082c030b4010400211043c4905800e5580c5c1802c4650712103450360740030886110501c0c19403044c41698002d180074043e03002c10440344410141c1c410384100426400c82e080503640700303029012243d185036102c0d04002d40910300c40403109042c2c4c0c0e4036046031040c502001d8400d031404c0010b800000c0764000c082250020380001c0041c0364014403080e000480f5090400900540c10000100c1001500c00240039000c041131014095032194141c2d0000c5030400e031f082c00b50718112030f20583c856101c0390809001c146a0b9400d0208584a40d05907898014050000e210035103d64403a404119850504103c0301d5441d02d400c10003141e1007011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 368924892 1250 368923642 368923651
    0xf03061b25030e0303160f0809100f0306050604061e020c030709090b1b03060d230606090a140a0506030307060612020906091308031015020708060106091202040e01060e 74
    0x20060030803a0502e802000580408120341c42039000340300e401700c2c0c20003242d10520000e40c0030b4050343c41d00040c2d1a152402e400740c1d4034030b103510140343c0d0b004841d03440d049131140700c0903040380d44c04100071515a810881140542d0140400060b1a001c0e028010300e007003149900307140024011100d400c0c5001c00041d10302030142c0c010304c0006803a82d128604018032044807070303000a04030301c54000d21104000c0d80d80a03030000034903852140d0120766060301802200e41e42c00c40d0040e10303103500d0903042c140440c502c0d40d145030950305075000d0303150180095210303c250300c02e203400700b00204002c8105845103000390b400381c48003514a0364140010401d8100041c1c0c82c5c4a0b5400820500c0110018019230380104003a6800013012075001c1c0381c0300e800300300e1040705074002c8000b9075510069658803900c440100c65142c00341904130350362829484085150058000800a044640400480c2c0c883e80e01c4250464005402e8403036403003040c2c031140103040189881e0304544040100500000b0300c1658501c0a405141010749 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 368926142 1250 368924892 368924947
    0xa180302030d050a02102a0918061701090f0201080414030d060602063103090305030301030501050906070201200c0a05060703020a030b030703080915040b03070314060f03061b 77
    0x40704a80135405014038681590178190800401c012a0342c0a040c280c1d0007c13000e080e820000c1d400c8901a4019075100c009030034441444a543c031022002c903002007840e80500d5011001d421070302c040e002814001d007140b1507400125440360842a90054902580203882141d1106171001410a00081080580050b0b9111a00802c20b98034215020303080c1200500310114141707111401c880ba100708480860260100c101066200e400340341000c542450b031030b03000117245000000000050080541103240111251415195103445a1005038201ea0044130742c0a42e1160b119054008030f2806001b40820908143c142c81407000c0030765131f83e802c059040351948003180d80030030120482d6a0601c18119030a80c00d034018007001c0d086444800c13580c010200d00394818152200e40d14104484070007030b50000c002c074610b2562241011a00a40a01001c46000100301a0000001d80718507181420440b0140c0240207052607886426030081200c0702041c0000c01c0c00c90411030207090601640c084642c00741ca51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 368927392 1250 368926142 368926147
    0x20a1206060e0f090a0305090301020912010e121201030308150409260c15180607080106030b0d02091303030b21061005030607050c0c040f0207060b01020609030a180302030d05 77
    0x82c0c1040c0c61100c0c00341000c44980306030740802415480000d5082c0005070142001c581b144000307070000f40a03100344007450303410400303190240e009807905400c401c82c0d40e83d00b042521510518500c0c0136900340a01c001d84102c410f0070030010000320340211000340c2c00c086440c8840507000c08510108040c0c440703051084030070345400c500e01d07a140411a0b10180c40184944042840d080701c0c040065a280c50f90412404440c2d502c0000c908100100720541510003100010785246241501016180700024411080480c0c145001c0ca00d20f4901420b140c1440c55004207810410340310941141489800b2810840505689901045803030ba103000c80300503980d1480c14001d8540c5e00c1c0c8815181450000f400400821280040511056402040d250f0384100e4500e0901c2d1181c4034040c2c07092612040c07007200e5400601e03000021207a916281c00500b22036021720010700080c003542004a944400c00c545800180d0011300c007903010340d44180c82c000a442200200e09020a0300d07900003d00f41000c42c0358031000300e10300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 368928642 1250 368927392 368927399
    0x20f040b0304021f02072105060f070e060f0f0a2109050c030a030c14031e030603010c1e0c0503130b07200307030b0a020c0703030207051309020d060504020a120606 72
    0x2008408040440502c42009248615501955030410703402032100441c90b010b030841812030350701070005107642c1045c02c42e00d0324241180c2b6109810030070307034036a0006408401e1031003a6060081c12140e9143e0104100c1d491b22540111000d45a00407026070300c10080e218683c006c40c00b40c11911740e4110032140381c00084507109454501e1400c0d140402c03443c081e41203041b90001280d0002204005982c000d07944032000380003115024214452182001500c08002c02155405c0b00756002551203800143c008110b41820b01e0f0064841c080745640203811031620302c4d000c00e01584124408450f80c0d02ca48202ea003000f520105159052555400c400c01c4d5010104541d820b00c91140c22440561513000e1010100b16070170b5020076118038660001a001c0c9031024041255485d140d8111940b00800c1001d403a41c990700c07450003d44a5403603114141c0300d128046080d000c0514030b0710070410703074580c02814048076810a55400c400b4110041c41660b1140d0b0000c1c000030307100c040d110020001c2d0710038440080c81e0b504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 368929892 1250 368928642 368928649
    0x50c1006080d09170c060a170709060813050d030e030909040609020108061905192102090a1e0f0905030d140c0307020a021219080c070602031c0906020f040b030402 72
    0x6040d400002c0b40313266031140d00040c1d01c01048030618424140e440556808001d00e00741c850500341199055103044c3c074803c01c90001c4d841100d00007560f03001c0e0349100c51038480c5403145030301050006008d005908040302d40140180240e00884c441c000c5402075034200101c0200150a05000311005d1300d4494580c009a0219070744503107040d80c0310f00102e40e02c0110340300c11071003140070704814041d0500071000600d4140180769040c4085001b0100012400c0d50301798802024800c080c0c3c9020700700c1c0500144404503000700c4207030003000d402c3d8001c100d050b1901d00001c0d50300c070003403d11805950a9107940f071240b440419414001000d00c106a0380c0003052800e1241c4103090b0385000240103804016062060142c0d8540c0450b280c030441e90121103d2202c4d40001102c9424000383c2030301ca4901e201c01540070820000c6a8014080804001080e034403059a00c1d1030503a107911030740664a403542d44070013080c0004119584a0400d1a01442e801418403410f08030109069005400400c0d5091021040004514 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 368931142 1250 368929892 368929907
    0x13b1f0b0f030111030112020109030b13060506040507020a0b1e0108070f0b0307170402130f150e1005060a0e0406060507060f090308010b160203010c080405070b04030b0403050c1006080d 82
    0x4005400030000301c0480403015134240410f01940c0e0748103410703008601c190780c4a0000d48000c1d54014070769817030368201490f02034890741c0005400c4039080e0030000024114941486102d10410158014003008031041c5d5640d0060940100b6a41142e14508104002c0d119240c0031039020b090030311b006100850904115588100040e440780078948801c0040100d69684000c000d45c00310404403181e240740d101d40c400034241010030700150318660b10b00321090402c0d40b10f54004601180822101031a00c545411010701030010031140303000c40d01040d146c10812414004018035001c00181341441070100c8250000701aa0415408000010b40125008060040718812140480c900c4501003064228560300500300d190305108081e84101c001c1042100c0c1d18156194215180e8014001c0209550380c0401030003180c1c003030b035058a03203200b1188080b416000701000c84044d6a04800d06035917640c0c41743d401701c41c00d5022019400403406005010410028035000700809000d241001c0c018285d5a82402403545 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 368932392 1250 368931142 368931169
    0xb060312040305070501080c09031002090f0307030b070c0f0605040f060621170702041e0c090b18012a05012004030b150603010e010305013b1f0b 64
    0xd180070001007000400000d02041152000e0030f0019581d0340303101d480c440317900892a0003901405040c9040340352104a90060459200841307600d14800003c1040c19a1542c1e54000107060481c07240104441c10b00402000c07510074484d0079a40c0c0440710960f175580035203400740c030111100701d0022007170b07020071490b40120b502618210542107400b841000c1e0202d18100299005800381c4041c11103940c0c1c20340d20108841e500e41d0050310501205043e48040700403810620060123a0b58900030807586001d100b03000b407404485021301c5c02402d08181d080f441c40640c0c60f210b441810f0088010414203440c5c55501448620390a030001c04402c2e46850078a01d0944450320908800314204100c061a030102c400d00759801c0e00e402007502c8500366119034001c4441d02d02240802d0f0b00c46030100000400501401445040e03c3c4a02c000340031811503411400024400130101c140c08041881050380c0921071040c07019507024803070307003101c1901e5803240034606140100d40080b40b00b82d480d011103800500f081c88510404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 368933642 1250 368932392 368932423
    0x4060c050702013002040b09041a15090301020706060b2205060403030c050c06030907060e030307020a0e091c020703030810050d030f0302071a01050f0f060a03020a1403040b0603 78
    0x41c000740c0d038002019001005030201d54030003a4030320b140d116807062005a036082901c0300110360701ca0700c0d0510302e540c5402085030710b0f219030300f0400094512248102110081040542880303030f5045010350b0fa010720b170441c100742c0342c15641c28002c00011403000d0003540004d111190b2081d540c0c624031100441c81c031030a0301c030700c00e80300045000400c03141e1600021a01129050f1501c031002d044145000d50828807800c503c00e900480100c24440010b10202d11a0101c500399101e0305421104070f000d1507100e01030340a001c2d610240e41802004030003420340080b98001449029129840c0703015840740030444d02d01c0700390f10061380040e109000b0580c01006403500500f8104082000780c0c68000015002081404002c0401242da1100118036019805444081d0b600042c0000c1d000d000e4001d40c030640c40b007441040c0c81900041100321039401c2c043c40c0381810b07442c05050207150490000d4290041d500c074031550000c01820f041c004110322850005580a03501c240d8015500f401c080342058070348086914035146 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 368934892 1250 368933642 368933647
    0x1f0603021e090105010e060706060b1b0c060d0c0c0507060509041a0906120f0a0602030f010e13111527031b1011030c0708010e0a0201121109150304060c05 68
    0x41c0395200242141113940901c3c3c885006c11030200446d03a640907078003004107150705103140824211501405006501254001c0c180f200003410100e43c0d031000c0c52403855412a104101d8151801501d8101c091052001d00b040d00c08803d055641038030b080d40540c0958002032022900740802d14050150052041d01b142d031100041e005a0002800ca01000c1c11340d9200e041c1e02c1f080590320000038001c0c0060948090700f500c404059504003900654001c840702109840c00074001700780c0049041030580610300b01c01140c00c000405a0301d100012500620ba0703036001e1104070195079a218140014011140039140a001e0b4498180103468a03c10911043d842500a61a070115030410508903507421402115183c40b00011900281c805140545020541d0b000000311017016020001d6102e0846070749000802c1900d03d0415190303260b0100e110001d00140d0302d0000684000c000c3c0d0400313585229411929842c1607180000204010340107502e0070a03038079011040100b4040305115440250b4002d003022072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 368936142 1250 368934892 368934949
    0x12010f050d03121a0d081201060f200c04020a02010204030210081b0d110c0a030e060a090e060609030102161703130303180c14150f0405121f060302 65
    0x100f0800728020302a030b60a50361a020954a0380107000d0009000003d0a074014030b400c0390400c3d20169001070307042c04003415000d0001070036038403e000152064410342d84560402c214040503404040006600e15402e01c40e95140503111b81d40c610080503800c0150300016a52071440c410f002c07062082e61182000e01050380b00300601c0c40c0c154504006a869440410f81d940c1d00b48a05140040c004070620b402d0740321010a50b00d040010001e90907000b03a009440b8022041c41c9c8904219031841103400311400151061010041401c2450000ea080040189120305281508020a007240c212146074500300e500e10400c1002e210309421187c40c400e01c540c007174600c1e503d041255528100031180000b17041695602348034000c440035844030400c540e1700210700c0c0780751030b500c24000d507041e10f50135220762040c40c041c907280101403240e01c22507080041820519040a2419081011005500c0c00c004440d000f603e00c2036840240c0c500c11801d040b42d000200041e16030441c0180112030b2201010340100c00403540e1540d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 368937392 1250 368936142 368936147
    0x11010204291e0306031615050a020a0f060501031205090f0d230304090c0810060f020a05150a0b0102010b03120f070f08180102071a070f0812010f050d03 67
    0x4078900d041c076440c0c1d0540a040d010104000c1c40340c203401ca44950040c0c054000003556580040d80554011001c454501d008004081710a080d1880342c0b1203842d004841d9400824010030260002c05070b54016614034a016440e020104040c040b002c41e400396448006104220402400014044035844c1c1141000020800304000007244a00740d0300c200d200f80420001c002240014006248c00c4000da05603030020340c40302d01c0d0380340c100e802400d17102d130304204804820031312801c0802c0c4900d0509140074001c525120050701c007900c564956900314058406500007291040060200e0200e03050240c540c0d618022913980102d4220590311811641095043c090039580001d007042c0102c10305504c16600c40c019582589184500e000041070041182c01c00428492800042c01408011b00001264800044012600d510366070007490000c2111100110240c8cd0b81d00140c071083d440b070840042000c0003522812000d400c400d0a00301450100030060000000d001e00d41c0c0c008000a95031055034112a0380d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 368938642 1250 368937392 368937419
    0x1050708010e04260a090f05010203070c0b030907030822050a03021008060303130b03190209060706020a1214090708160b03130606030302030703090b0f0301030605040f020405090a020111010204 85
    0x13404d03030031003000800368090245003182c134a00144103505548a000d9440a031401001d845240f01c0980b6228000441d540080126850726500c40240034201e401c2100038802a000a00003800340d05c1940e2022000401030002070501e03d04401020009841400a85001801c650003003802800440f000304010388400030401d58241480c24515a00e0351801c0100340b4600031603515070002101c038680081c0300c01082c401980140d01e00d0b09001600f4003462a1102644540303d0b800d90410301c03c1048001181c272590280158000ca407600150202c103183e00c0d40240c86005454600e6420384800340045d5000c1007103190010280d0202400300b2120401c07550f424040103104001c450030b000000605440c60302380d0114005075100200b00140d94807824000e41d00d40140c8011008100d0200e40810242e0b4514143c0d0a0440f015a103280fa50703003155a40e00140001070000c03194208072001060043c0e0b21030103503501c03955036500100043e0131a80001811000c0d4454034003001e91040109110445a0602 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 368939892 1250 368938642 368938651
    0x7080d060b0f16020301090516030b132105041d0915060105040603111603020715020a322a0402120105010f020a082805032e0e041401050708010e 64
    0x81d000c40283c050000c603001d05500c0030000c01a024075258960300c40324010358841504e000c1c05c4100704541c0c1c1c100560144000740d980c0030700303c2c04254441c0c000310401c00140360210a401d18006003016580c00e40d210144599a0580b10941c140c00201300700c407501003020303000d00c11508044602e6802d0400010700b0510450145078109070b2903000711888a00c02034200c039070303d00705020311491500490400075294042401072500e01554080303004610703480001d400d000250081008464560b0300b5942460300c181e10802885200b02014201e11402ea041c00003002d03000d250b50441e0750b100805800031819503c20a02c00d44118810f12070010580500003d903415030784203081000c00c40c0c04140c8146d20b0441c19010080507200c00041120700346417205607110f59a4a60300c900c080042c40c011042d01c4074003040b1040d048002405a40b0407620312114014800030060f4043c0210720342d2140040340fa6250200e07030076a641400d487e00202c00940c244211580f2440500d00b040c000d504250407406507100141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 368941142 1250 368939892 368939917
    0xc101b08030a0e06040c03020102070e07050a03021c020c0a020901050d0f020f040902060316090608010b0901030c090b0408251203030902040209040e1e1903111207080d060b0f 77
    0x100c041c41c0c182d01c660f1010030010210780861030a454007060f4503c8600080780140078604000800c1c3c0302c0d219010f0700074583c41c6c03111402c1180424044000350030800030340f980c1d044c80f2300030011000003e1000380001d900340703005407694042d540140501254107038400c3e03000d40a4010610049540c00e501003841c158120392510540300e00800040141152100203540260000144903c0c1c01065505140410140d2201e03a00203640d40420b507082d510900c15054900c0c002c008a5000b90300c254040c583e0107030641081c00145446100d00c14054106800006c0160f103c0c074020040208020854001c2414100c1c04600160a0051140c0c1c141070004004041c1030321262102c0441d91680c05440b201c820292040051049401e209640e900580d10300220120283e940100034080c085103c0d042011201c1c07079160b00001b2989c04451007072021200f202c29010b12072000c40d080803200c0c01410454000c0104940b644181c2078414108c444e942e000c54070602e810405071111802e03450940b0409001340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 368942392 1250 368941142 368941147
    0xb1e0912090f1c030e0907051b07090f140c040b0a0f03180308041509330204080a051b0a2102030601170709060e010509180601080c101b08 61
    0x1c008910380c0700034180096402840c2d1000d803c2c0306250242d10302d0249000350b031840920b8503840f09200018038262190000581c0400808180640052480c001c0060b04800c655400350742d44031b0082211444505103c0300c076101d01700c0d451156501c0180e2a00069800b82c0d4900d043c0c50f000f0420300f1846200e4007581131103440300100340a140039034084c0e800203000b42c4410000190038600200100000c44017200c85162080f03440605504a00c60441c005900ca4140c00b02d502051280844000d81c54506240c01d00c0b0a46d108090414a400a840180a000c00030501c1607610300e0800d0401401c889400e07903082c401c01020f09650346d2200700300f080f507401c1c40500c0300d5842014844140030038204000381d00741c0300b2100002020425454400e007144c07030342c8060784c51290b110850b10055445a20495101184440061059161800c0201d800402040201d07003400c201c001d055003082c40c26880045244c000e00400011801d00e880303152555041840c01e990400b1030807580c0352181c042e100c5c000d0403d0401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 368943642 1250 368942392 368942407
    0x2240601050d060311130506180606130e04030806030a03050405040c0e06070c0609050402210a060806070f0f1e0311130b0301080c030109200f0d0b1e0912 68
    0x140100d500c000e035155000c0c8040394485c217140124076080c02c089800386509034216070600310300c0d126542c0a2070300181119015010b044070b0905002010300a25404a030420003007a00241826468004000c0400b041c034142c585420080c0c41150b00a080502a40010980600082e800412101075800c2103800040064100d0402ca603501450042c1e15040400040c0407401c1c0660881000110384d501d540c0e4403411034a4100f84416405100d1114500320352240c3c0300c085103d2030352030300c4d644440e0002000550964880c412850003205580c0a4045590104580b50a551001c541c074072282c824104101c0040c000b40101c000310010203111810150784e443d0354503004030340608544034548240704080c4c0c400d4540a4442c20b030380c0700307106610003440307907540300045801c1c10301031120b044e40c09c0b451204445050141c608403040c01d002100b588100c40320800c104a90316540079a090a0064044007090310b0300300044070f0407410701101407648058030010050401c40024a0712886031003049040d031565403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 368944892 1250 368943642 368943647
    0x306040b040c030209040501020d05010f080304051c0b040c141e0d1b180b180f090f0709020315010e090601050a0207050901090c090e0403051902030705010c05090f0102240601 77
    0xd60030017544001d001080c0014403005401074550010b030080c08004990740c51940a09081084c403c010447d04240400c100516210308882c030b0504403840c03001e4000509030340c4d11070701010840302140d1500b0b05250502003064606494111540240c0b4446040c1960001c0d0150307010b4200c12181c0709000700340b5031404000c070314065468244600c164501125440b80c0720201d090200c1001c0d140050701d05400760f46e451810407102554100c00f03904252554507240400b015481004240100c684280300c14001107900c02c004040041400510068407820000e94541a030030820f45228104074005c148400541d5400740c05036040642420410303500c142c804001c2e03003000c16640c046940310040e40000110030b441600984900400340c1e03100c80440d80c4900c0c400600c81070507200640090400c0c400c0d007410510340044100241e6071401102d051000030307582c00e401d403410390030300000049021072031410500302404401c00c0c4417402d001903c0d40310403014900d4100f20400102c0d4a0402c02c00000c40c08070790 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 368946142 1250 368944892 368944913
    0xf0e0609010e06031903090602101a0f0321030a18020a0603020d06090e03040501030e071203180e0a06080c0a030b0a0902010e03060403050c070608070e01140412141002090306040b04 80
    0x1a005d51001000070101c0c10040d00003404d511501001d80a201c404960383d4541f88103030030f06001c3c5003020070004603c030002c1c408140d520401e1640c142c402e0003409452001840310740e44241200e5016155607181c4a0352443c03d0f112800411402d503400b5407501e100598139808080c06840480c500184c0300c0110300384030805040a40c0c4030010541c5041080300b8000008401001568130a0300d00303010000541d035480d90364482c3c6208221900300c0c1081c5140000b0b1241c0e00d0008800c10915565908035120115800388110990703c071076840390394500400076100207003c0300c1003e00c0c007258400805403039a11003400c0403100418804240d9901da020400316805003503039940300b0b5006000c940e803600c0c00303140280495000c0c8240074010b2190700c2000540503c1001054442c0d0116a500c202c441407000055541808001160b000c3d44424840170400614090a002449024600c070410b15800c00044038200203400f080740455030300403c1b4240807611700040d982d0f0081c2d800a060b1907541c9d03889c1800400b84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 368947392 1250 368946142 368946163
    0x6040b070f03091d041202030313030c03030615020c0411040b040306090c03080714070504050601050d09150c090603051f0302060c0f010c090905090f071505090612010f0e0609010e0603 81
    0xc01000c5140c8140303001c00c11034148517910070308000950030410f460030303030f581e0204032002050000141030b00e2000034400c1500101182c42420f010402e15141c006183c0c45101443c0483c005a115550200d1b8524107400341243c00740212410518060601011082903c16030101800c85903c5105281c200041402c040c2d0003543c10071030160719080585010128224180441c002601c90414046074918041c400c8034080e4005071039082c644100b920740382014008204040c0d4055281c80d0040d8040d00c1d20b80180e880300001d42d51050b19607418500c0180448030081e00081310004800680c1400d1120107210310140c80d01202c83d5522008200b480c5071134030204004600507542411600d1900b650820645420345041d42c1080c880e540e030b11120540c0c1d503803c40d00d0714415075000038800c205060580031a40c090a0760340c50154a40a24803000c19600d43c0b0030b00c141140e0241c15401086801000c6000a000d012000f0003120a820407200190f803020f81802141e081080c0b05000c54801d540c10082e00c0400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 368948642 1250 368947392 368947409
    0x50708030406020901080f06031e1e0c0315130618050d121a0f01050a0c0b04050a05160602031e04180b1002030f040311150d06060e06040b070f0309 65
    0x100d28280ca03154002e07400c0780134024007148888010604083c21591000d02c6204003400030b010509031003c40c400014502801250b050141c10b40111f94840c0300d4030180e40c0c10040c1030080c0420380d90041450315054900082114551195052045001880102c101e60a802ca13001048030620300d11080c00741e601000000340703144245003e05040c1c07500f0400c04d0354912403890082090a080e00270540800c0d00e800c920b01d45c0300900117400c000940c00340010344400801d03403402c070041e410350341d072104c0d04400240c07403c0d43e15502020b03183c0304100c402c000e0060003205001040542528000019642e4098441d000380c0b03044a038039109003c00e43d1301c0240c40040c05000c01404000c80c0b010312080c001e01c440c0c1941400b41040072840505c450002040303409040c80c00c0c1d1814300d401e00c1e50f100c10403050200380740503510140d816640c0d10a0a11900507100d20700c004280014174920f0014003400c2112080101401100140b0040103052004000d641c60b142d040f40c0c12406000761898100c2c0c6400141d04074105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 368949892 1250 368948642 368948647
    0x140f06130507090b0609090c0f1602120d2309130b01030e210f1905030a15030b010306200a020a0201080a090210050d14071119030519050708 62
    0x46121411082035400340c000c03001e452109868a8040082d42c118000c4036401c81c00c1001160100d04103c0d070480d5004e20344500060404e0032124a480b52948607814003140f10102d841c43d8400d51800b4210b462980070490010545071015000144c0342c034031700e142890b51700100e4008600c1911944001c84d410044010240580340d130842419400520342c40189078002480c050307100340c0700b070340016500240312506900f00c11100c0d48444139a101d81d224803504080f2240070302c2354020548400910780c10765003482d1655a285e180031503c55007220200f44a00e00d004100c910304002081000d900181900d802c51000301c0c49500d010782c40226020360700080d0a0a140000301e00c10101c0c0d0102d24041007078400d99411490351a80308540003a00d070140b80c007943c00040b944800c4412800b900050109076281640422076094480c2c250400c8101210784c9400701c0e03021402071001440030b02414a4800a081980c7d44004881d1001091400f41d5031444140341c00340b025880324240124142c450103540110003a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 368951142 1250 368949892 368949901
    0x14060c010603120c050f070f051311030705040e0c211e0103050d03060e220c030f210c0c05041d03030c0405040c050a0c060902180a061a16140f06 64
    0x10164000d1040135170762402003240c8051241004500c5000312a0790b4a40c240700700d07051804000c40f054540303c041c3c40341907461842c40f101e045d194020303500c240025201c05450310f2078038060304001c0c00000d00f00e84803103404101514008000b40070b0780e100880783c2081681e00d81c1d11000003520540383c0782040b146800e4503030300000800c40000707030640c418880740d58280441c0b655603495001d001400e641c040744a480100c070080b40701e83c00400310708255000301401c0c59901da41c3e031075043c80d90807280004e4401d0009419100503d00e060307055401001e655281503803801005455086084919014445c8940d45505046091405425000501c0d50700d1100390303039403814840c0103550154024482c450240b4100940c41110380d0042c004d0701c203524450740b03d030102010717142e503108007e1003d100200d0b03201621130b031188101c129070000d0310300c10721804400065181c1821511000108103031148409604200710f0150b0025001213154002684403542901a0b40c013031031110b0a002d9940c180702d000d84141410807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 368952392 1250 368951142 368951147
    0x1404170a02031902030304050d03030b09161b110d1115070615060929040b03061806310203240102070e060d060b0603190b030714060c01060312 63
    0x60035491003101241c180300d01c41a6941401c0c01001c0c00a540f40c0c0040c8420082810701c1d03502c51900038461b24000030064402400202c400100796140c2c40561282c0901400eaa60002c281040c401014801040d000c0800c0d0b68490703403001410b07100c90044400318841ba041110a288031001030b54003c16603440d44200e024140170a80000301e003a9199820070050806055400300003009440e0741e65100030700941000d4061060a600004c00ac075021440c2c1c81c0d601640103408081e2010b00805030025569051007000c01203101130b52010b16403189941d4050040ca644e448000c2d042c00c840781084900916842614850950000c00c1000c0e02940008100f00d80d41018580e5901c58082c3d00c0c2456061112102c01280c3e504101c2c00b400c001c62130300c640840d40c00d181903813070710207101c1c441c90000c20701d0710501380415035540058a0b18082000e2911101080d801c990044c005003800903401492200d140580119180c64034241c035501981c4001640c03901d480083d00200c0141da00030302d0303003c204800710200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 368953642 1250 368952392 368952403
    0xa150e03160608040209070c05070f03030206091b040b1903060c020709051e130501060603020307020d17130c0902040305031b0a0f0b0703140a0504020f030a050706140417 75
    0x40d00c28090003a540d031001000042620540e05540d03a80b09180e0307a19400c0c030201150240c1000c0074025007100d1030b00010010059003002e00b05e88200200218510300d0003030314141020f48a84810f03000b0400b0401050014900c003241010700b01c07000701d403680b21040801d6106800d010385c041e03840d0485402006020403904071001003c5550700f11040e10f0350301c4044108551003070b5141401d01c40140004400d806c0300c186419000041054030100c00e4038903665031807c48801c2e500110210381c0210030003000580622a0ba41030118034107214601c416000c141c565070b10300042c034408461000d00824010300014810010280031030010440d601c40e1681000e40c2d503074000b0302100030044c0c2108500d2840c8600492a50891035101da115181c6c41603075a245000b80303e00a143c0410540c0e1410b080c03540d580c20f00700e543d024040c0c5040c00142818107005000410504040031802540304440f6880080d034000f541c2411076040e40350a10000c3c58542d207841c043d22666000c10900c000600030320346000c401040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 368954892 1250 368953642 368953667
    0x1081f0504090c0e010b1204080f0c0313030c050d03080f0703091205090301060b0712030905030c0106030f12030c050f0306030a020603042015090409020a0e28110a0c020a15 76
    0x100c0513096030384c59a9104103031090358000010040e80ca00810000b40e02c0b00302400c851141100305030304160320038030440c3c0f07190803800104020811034441082130202c51032001024080659130b0000015850314044d002c07180c080c00301101d5041c0400044c00080c400e502a40711a03503c0081209100c1912000418a80100703e0a52080d485d00800144101803182245e8003194000c18454080c0c504400650003880110350a982900041181403410388080c030480c4003852080201301012130840c00c0c007000346082e140944061604d014200140a6000702c1036400c448007411041d0759940e9002e0203e03081c5501040700942010010040c0010010a03800440c041d00354120100742080d0004100b00841b00713120f11411525001700902100c134101a0810700b00e440c00686480304080c2d46070b480304501038040354150b681115640004001440c0009210003288022005104401c40c03014049841d102e0804a00280300c408981e04045440c2d00c07503224000c00d0f4060400320390103108900034004119890 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 368956142 1250 368954892 368954909
    0x1021050d08060d0807060f060f09110c1515030102040b09091303140901030b09072105010501090b0904140703050714120604090f05060c0910030b01081f0504090c 71
    0x103610050303144035544542c89480d0090a00e070310714200d512040290381c0031240544219803a518403525030380042c00f0b550002d210310740c50043c0c0c481c60407441e601140c40d8480300c100d51030030400c0100444200010094031040311000c030b21a950b01c0340c001c0707000021035611100da0954000b050004841680d003010b0b010f00070050741c1200c0340e5500e03100300e40310000b4007103c0100425425100ea00c030505906002d84149101030400042c9a041c4400142c600181110050000756203060491030000f031544c002143c44152150611132541801e001a000000b18000c0c0c040510b40840d1440b200e948507004120303401c0120803182d1342d03801c00b0a13004000c0d180445030340012031008109840200c04001c04c449203841502c0c1a0303141a240c010411024000500c0d054038041280442540400d20500039240544006460310350b9030300c05a42442101700c8400c2815013414544600304815903001022a5802a4565400a00484a0340307900808061507005242c01c00d141c0b1620204022646103402e040e584581c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 368957392 1250 368956142 368956153
    0x90504080a09080c030709050601090f09090203070f030c03030c080706020c06090601050303041809170d09030e060309150c1b03070b092d0307021509040501050f18102105 75
    0x1c03c0110340d11900c21140d42e82580c441300302001808004e600a941042052401542c141d45d5800b260540107020b8202c26203290382c80c0004801c52030100301070750091440d4000c94421501d55107400e42c84c6802844060300f44442c2540b48020404542d00311504c46a12140464940c0b8102d41c0c00c95955004403044180b91251000118552a0010a560403250f03004411314603480351248007000380c00802400c031440042d1549058400c440c00340034064400d150a00003560b00303020309000f400e1020504080d40035050400034400017400100d8801040e45900c1c882e1105030300c50b2100d0032447d02c900640880c2141d0040c90222010b44048000c10407507018551051031519a141410744450701c450110701903540000d03803d003000c00541300440c04801044161781c10120a41c0204881003800303401e55410b464001000e00240c580391007403a0141c001941c801074003505003c00301d40320000600000b1003c4030080001101a03145e107951310090101500402c185001c8444c03118003200b9042021140c0b405078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 368958642 1250 368957392 368957399
    0xb120106110c040e030c071e0603021206040b28080f0313031704030b0c09040e0f0c0d060f0603050c01110f061303030e06010620060f1b04090504080a09 67
    0x1888201c08100740200030304546100901040000c0032400f039121554002801918845c00e01445800300500d07030070031268600ca28002034880c107044140c00c518103261050011240010700c080c83d95620884c10b44001030707800503020000f4034002c040c160030008060303022141100361525203001c00c1180d0101c42207039104401403401584900a42c0c101d251441144079080010402c1d0459140680b0b4015400c00c1ca426169150300d03205002c1250b2860402c4000162007409091600c92822300c000d4590240c00c5d4071403a451003035207402001852034031650002d03141c0c005100c00c0d0351010002d420140c10812104c0d0b40c1c0c0c80c1090b103070341c1d100580601090303d00e80742c0500c0000106012148106200c040c0c501c9230380d688a6078409032003040040e01003555034000c44001c800b003040340d00d0190441d5210201c0c0c02c8c072007030243c0100740e400c03080722072aa800500501904200e0420a82d4215540700c099218107440030f03190060500807a4481ca100314101000d22080c40807000c02404009821f0341d41210340d50301c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 368959892 1250 368958642 368958647
    0x10c0302040b070201081b030403080f09010c2106090501080606090f010609050607152a050a020601140d080a0806040b0103020903061306110705011a090103080a08130602040b120106 80
    0x8a100d4280c1d02082006440f00640c0b0403c40c03564410700340c0700385251840d03500030321404d50340085074102c011031860001e201c66400005001540002a04001d1000b00944400204200d2564681d4607268400405140e13503107172150808030181800d40400c1042d5a96030503420395405040d1500303800b44900f140800d4001c4110490241a07031125228800e480d8a84428001e079030740500070680b0600702c20f49040520b41c280d40181c0c515103260482c03180010388050a200390031550b51442c2000c3c05400c00c200a105a00415460304588a00001f068612414004901c07001200b0000800d000000584a00e9954000052500605040d6001c0003400d60120040d4101d01ca08800c8d242c2c0342d40003800155003c148045c4031003100f4412000420701c01521005101a608401800c0300c959442c0e481e0300d070b01c49904104100a00004030365008495140d80c03904600762054400080800c4022000035954030031018900282c0c0ba88000110b41e146d07901e1400a940ba0001001000c0c1c1d40c01c1da00000a180d0f2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 368961142 1250 368959892 368959897
    0xb120d0804080c3f0313080904050a0902030606120703030c020411040b0c12070f0f060b22240b030a0204180f050f250e09131e0807060e031605010b03010c0302 70
    0x21401c8140392a544400d010030b0441407032514204d407c0042003210001507156802020b02642c1251380100e2000b071780d1320405007000c600034100c80c0902c4809540b800800400503031081100d0701810006401810350010074081c0ca00c0b43c40440700d90f02d00280000700014513000400709440d001e016031303030840100c10b81c4c0301a900c2400030180c00351003014600808141c903012065980c42c40740c0c0000a803441010f0100d054110614134132140003e412a101140b040316000d0b0307818021860154251107042c0301110007a41c4030500401010060200000c2c80c802d600c3d6040700c01034a2640380c1520001c2404d80907801521f0190200100e041c00c00b80800c40c03c50340c001808d4000c0b64481490450072010003124500c10200041c00c0d4200484072401050726150486543d000d202c0d0480c0400344c1e03581e0b60400f082d240c403044002c0301610350311003000c1c0081807081c02a615178030341c400340c04140e003420b07481c449165000d186900da0b04c802d0b03030a41c07040402a0540c4850782c0c0b002d00303400034080200c05101c15412070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 368962392 1250 368961142 368961253
    0x70f03050f0610050705160501030609020405130b0a030b130c0b090a05010f020c04020d022512120912210605061b070e0108010b01030b120d0804080c 66
    0x40c141001c14000c0c03400761038803149403071035291040c1010040c4d21200d16058020068260001f4000c0092145580c140280009805916030661506107460045440c40021113140446aa80c4011000380303070351804a0080110341000e1b8564070b50400c04a1450340d008a0082194241040f080028003880e40304180c8551040081c0403810311450301b00151440c0104403003800450081e518141c515903100d2002e80b0105072505030047e20340310300f00d44204a111b44140b80c6203d0214a901d20400146040d4000041021a14103804100c1400c0c0b10341c409050a24002400700e1144111001700c0d55100040415801030542d00304c40700750a4a041c80c0443d00c10307002c2d058112800b081003070908402180f82850303031760300c4c48229581559075607240c151640b820303040328009075140d88a9100c99a41400744000b80c05084603911081007031021065902c0e1580e0b075540080c460b613000000d00384004141504c0100341c5050a407000c1c80d45c2c403201003041126140310184030760340d0004203807d2a0715406403007008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 368963642 1250 368962392 368962411
    0xa03020303150a0311090c04090c030b0f42030108150106090602073c0306060e01050d06050414060a0e0106120206030106050309012003091e0316030507060212070f0305 74
    0x1060605401c0c400722050052100d60301710b02c100000a9401c1403445215400c52b4207a800103048505801082950001410000d10604904508031541848000c00402c1c80e4a010030040c0106c4414504214245800103280306401000c400000c1807000802c00c00b64038100c046da0042941e072149000d440701c20090280f0300040e449054180304090400900c25017014600c8400080d40d2803118a0221101240d841e0b11007001c0c00d1182007040090600410004d80103c105007041d80d8108000710f103400044400144c0402e4490000c40d0074007020404c6285000c00c0e500c151082464001d1150014000d45003541c8850340ca00480020742841410b41403c51541c000c04091540c0d203044022551500041c1500030315560384c1e118991001080001a0384000004802035100e1400404440c200445680c40312009400101c0c900356651002c0102e0340d05c0c00d071240e107410f03010700f007414215003902a00c0c41c020a503a10000b045c20745500701c0501c041c0700d040c5603590126580540c0d03004800740c0b5015074030041c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 368964892 1250 368963642 368963663
    0x90c04150608060919271109010801180204110903010f1b090506121b0c0a0c08030705070b0c160803030a3204031e0801080105010b0a0804110a080a03020303150a03 72
    0x31700c1400f43c1c01404000c481d03000c45a203815500c0701c100180f80304980c000c85105868221980082c10101c0d81c0070700404842c0004c01c8000c1e40b04106041044020710001e109981e030b8a44034081c3e518110a070365013000c003e0000c11111407801044170081c1000303200c5480d1420782810415005201783c0022043c0d03080a040f843c00c0c0f06103800115003040c0007502081c4c1503c07400c00c505098100aa014190b2002c180d4024100356149040880345800e440d00101c015400400104010540c00110320040794500208659070380c14011040d418808041215003002214840000d200d8800101a41c029a1942410042c61480001d16289080448181c4c0302d850380101110441d00b0a804180360720038000c1c14049881119040c400c56002c00703e011090120f4291401400708a109120310360141200110b06450a4241140940000380040004100348030f1a61034500503145c1e11030010040c20b551044442d29001480e010b512500211692908a1009095000203150469412080340d810600420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 368966142 1250 368964892 368964931
    0xc03010c0c080f1902030d06171e01060803041e05040212150112090b041b06050f0f0409060b120705070b360f0f01060b0a08090c041506080609 63
    0xc180e048201c0c03200c81c045042c03007a4684c400000380485030000581e80070316560302179801203008888041d048041000441e400780c1110007c0019400600240800003101416036a100c03240500313450b0300042a075020120740000c1041d00e04508803861944040c582901079140c40a00049002d00e45107907074401120b5000c221001c182a080004407139047c504084c940c0b00d04105442a44c1031a403046a0010180d820082400700c6484010110007003501c040c81c0c00e528122000345280610b4007100200d04000800d05440031001c0100c400400d000c00041c081c7e55550010326083e600607115807515400803c00284456120304201c401c030940c84030220105803500c07544100079555201c83c0c1031034540c440c0200581120b0880d0081016401c180045c038241d08440d02c01403c0aa0410b95035405078141a418442049840c040c4e0b0034800c102e2070040c3c0169152001185450501c00b68107030803516105000503041007800440058424030744139100c160f1a90424003035100380032150320010f0010042c0c2070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 368967392 1250 368966142 368966153
    0x51b0c011d211222020a170d020c150c01060312080103140c0105040312120f0203011d090a1b030c141c030801030b1003060e030a03181a06010c120c050c03010c0c 71
    0x44000c00700e010f103104901d06540810342e0703a0404e411000c0000b402c5015000815820230040d000c1c41001d101411140450b8000310b103102c03480c480306008481c03020402424000d0253300610045412098840348811440e1300034051325400e020966502c0c8001740038428040f00010f00c01141941a2354061030b1a156407520806d940100c0400c40030454010100c054111882c00340d09852074021000680d03c0d450500b002050036007001013403119005030b00400503c10300c00f00b50107080f950084210703408034804040d004070040d80b5420007000d030b0001c00e002290003809542031b00c03020b8605032194000d40c44c0c42e404a5a5010070601d0050008a0480041c000682d1403500c143d040012221007010303a6440c0d5584400f03542c00b000e2075000503840803a60030b129540c5030181c0d002072000508040c00398400c1d61145040f900c20000403c40d07100c1d01c0c101080b101d0f441031020550541d085500c0000c06511904020000d0f000d4040035200c0e44500c804030341a614061150180401d16501da8920584042d40ca1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 368968642 1250 368967392 368967421
    0x8120919031409040507090f140d06020a0905060307030f4d1215040506060a050a02100207260307020c0d02060c01020328051b0c011d2112 61
    0x2d0b004003003841114910b4036240509402074445840d6400ca0754208000b215151340c00b1f80c8654159071007858001181e0301d03201007220f03003503801520242ea01c15410001341c90031080c40d440705410100000401402d0356043e40212405217005000b403100800c043c1c0054440d4200400d110380682c0e0500e14400c20002c0f00d0000100003102c0c910000303581c015188032100c1508807000b060460306d8140d04000041866242d0101c0840040b502040681440d201281882c00389100e02c0c800d001c400208030f00c50900812401c980c08816007001d640c2e80080b403074881c0800701c2d40446441d4990b403000d0703801c01000b100010ba84c0300e03031026401051059407040421070a154070b56002c4c3d0700824100200785d01e10b1400e0005502c2204c0d13418801d00f481c045072041c02c418469010704100e00300c2c07030322040c4240b9400c2c81c000c00c03011802c6400e240e81c45519054a05004180380c603400014001d8401c1060071040c4046149c0f0500d1180c88200003000d0300300041d030b41c802d00c15101540c801380348110018500c40000c25a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 368969892 1250 368968642 368968667
    0xc251707020f0303030106020d2a170d0516020d020a151a0307080d0810050117071209051b040207020f01051317060103170a090302011202070209040812091903 70
    0x5000c0080c502e40c2c0800c3c04c2d64001c1e0005001030300720348174036010150401540968001d1242410040032003010303400d80b0404050b20000c1403682402041c450811b1280c0c1901c45c2c00b840c200042105042c015540d0711a0004100d45001500804104c1d458941c00850300038409500070049141440000ca900e0307000304050140e900440065a2078140c1644040002c0170180006000400d01440d40c51406006224002d01c03545620071207510038401c50341d011b118982803080c0c2005404007621442002e40c0da44480f00f80502980c0d00d001460003e0000c0001d107503900001c00550310b00d8040840b41030100341c0c4980040a50801030b01c0103a0141548940002c04404e100c12111071f90340350b141c503041c14103499100f11038042507020400500510108801d071642c8003061600c0c082c51300540d0000502118894480a130600181c0082c81c4075181068048800a903401402c488543c80d052903c0c60710340e040109140f6a600310311340001c2d00310000080f021840c840745944115000c036550740459541000c181c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 368971142 1250 368969892 368969899
    0x40f020405090a20040e0d050d02030709120b0105091b03060909150702060405060612340f0f0e040b010b0a02010207020d0b0a0c050924070b0c25170702 67
    0x14034038010944140c4400c84c8031036000140d0040c51186020401901d03400604d00d0f00c1c0c0d805c0007406140e01504101150000020024003607100d95030404c0176075610882d6071003007a00c982c0b0800c0c00410003800d600450305880c005c0310082055111118281207205541c0c0f01c19a00c0c0200b00007140041c40c061004650040d2854200c910b18609070908902121040c0da000000d40e005005000410009010b0380794404020b0790351078180aa1418080d90303a4408052520450742d10020790440c80e03076201c40d454500c1866a502d0310344280d550580464011140c0b00c3c3c200a03404154011074084044500e03140a0790f0865411036440e420301307180282c2e13079110210b01415913508004140040e111500c070fa4441c2402140c020380300d4078008202c0d000303898800c0b941d0700c100030080107180100e0381c862100c505022030803130100030400706c05070420142d4800c07100003802210301082080b03080c003d0748009004156400801c121844210f181710340f041203000e00010b003c0c00c08101ca888072a0943c0c0c0190030b0407400203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 368972392 1250 368971142 368971153
    0xb0d0212010908120703050f06061602120106060f111507082809020f0925113003060a09020f0d060305060601030e07150c032a1703040f02040509 64
    0x199034811003944001c8030013100c2a9580100690b13280c0510400e41d1140480000e00064503040c000a400d41c030480f0754140140381072040326820354948120b121700c80c1041c0002000110b4030f841f00504003098008900d400a10201c4019812200c04615000d0312443c20f03091a1181c1c88060080da07503880000c2501982d100c40101c92540d600b4400d0441c0d00d111400000050105014010b1000301c0044200365805401c9000a0210b0b008040d629043e2804d031301c503a88403d04500e0501154402c0d100b000e103000600c1001400b00e1000e010310b4018008c1d201e0040c840e07811890014410a550000300e5203a507014030440c8080121807180d4000301485240103401a2505144d9013181007200d0a540054903180d006100300078095826104125520b05050010f021891404103070291400c640c814103401c0155000c1440e04241c000c19010800c1c0f000c000358210504e000700c3c042030364001c0004060300c6000304c045500d0f4400440d01d00300e038043e64111941a00c1c01c07605809120203040702900b40c1c811032240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 368973642 1250 368972392 368972411
    0x1403040b06060c12040e1305060c0d090f06240f05040209040902091603060b09091303030209090c0304020a21020103240f0e0709051e01020a1203020a090602010b0d021201 75
    0xa02401c40c10412075681a80c07178506000c83d00c0c3c800a0000c105098040000703445001007900000c00f50741c0072820702c8040356a040e280e03082c5009000b5002d0018140a8594281c608001c21600300c09003803480d09034008008006c0b034401c80c4461001c0d128140d031102c3c080314144200d003499001000340e0240500b02141d00710440c0d000c1032060300220340d4101a07610017041c9002255040c0940c00042c002003066500380010b000005200c42030180c071300d0040654400a980c1094080d40580d1000c85005080b401a0300d0106100c4281d0703403085401324490b95004038080703054102c03207981800c00030108000d84c00c802026801540140071a6004001e0181c2002216030450680c3c0642c0d005040790000049030145000e01c813540455014001e0310510500000a01c81602d65141508505580c2032814460480e02ca0050307043c039521050140404411303895850b801509500104440c9600c0d503501c5840395a1103404a003200c1e9006005540194108015005840d00c075025100c80b490607030000650800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 368974892 1250 368973642 368973667
    0x140d0f030f020606040209150706061520030a090506070213150515040602060c030a06030b15100915051b010203010303200706090909080903010c020c040605011403040b0606 76
    0x840004500140521164403000ca90511595070030100541d0b0550400d0503c100262800d8240e0740007540100000c81c11005100d0740da00104000c2a2100e001000254400001020303070114551200010a8008650703c2c01d0400004460707420301c0b142d41d155545420101001040e9000c0e40042ea030080c1404003184441881e1700c10040d01050700c01070265410710b4000ad106012000301c801c4003a445007440301700211500131400d40e5100c1d0940035800e560796542230b486001010fa5401c00362070030b000c50080007002d00c00c0680d0403601034421149924100c00c481c80031a908130f000d0103a0f5030442d10002e6144001c1c0d01400c0605000004403c0c924488110500501c1c01ca8209900503800541030581c11070802e108030000d9602919940d0140c1032490400a01500d01111881074041c0035079256408020f200a01c001d817030010400070024490505020340081d1307a007a880782d0715445107150100c00541503000b491404118101c900301d160642e070780e503202e10340d150074001c0160b50000e4007000f50220840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 368976142 1250 368974892 368974913
    0x3209040f0510060216031e02010903080c07300201050a17040c0312140720130506040506060901020a20100306030501050c04120b0a060909060209030f030a0801140d 72
    0xd0741d5000c0b0098261812000030710f06038030000303010100100e409061012809510b00c091140a000a400f0b0f40789006e440100c07646650b81d40050403140300420003c010401c040740c9502264842c0844420500c0c94a03014400304082c5851a0703240c000050f1031100550061018001000ca41d040c00202524680e00039108424103ca0848810b90496018030800c181c00d4881002c40c9107074901445000404100800a03216200014044030344004c00400134190347c050010314108e0203406e241140c51171951010141605543c0036100d641010001074803420410140c5401d0302e0f059000340b036581c80507200c0d1843c40c20142d500c0320510142200c4030243c2d40301c0c0014000d40b43c0969800007201c078a07605069003150340c090305209802030701308810894050940f0b41d0704041500141140071580f214801d52008000a0344560222401c0c016000c040c040258054501c214040e4259480d0705280240d098807441500741040108841000501c004d4144905482c101c40014000456a40c03d6449030715642 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 368977392 1250 368976142 368976151
    0x2010908010e0304080d03060302030706050702130606030f110310030803090c0907180f06080621010509010e010609020a05040e0901111c0e0f100e010b0a090204063209040f05 77
    0x290b10000d0200203031780c8104100301e0704108501d404c0001c40c0c11076000a4448000340300c1ca900300301003ca0104103641d00e0b80c50f0101031149012080140b07558400b8007a002d40069901540198a044180d072007030080700c012248901410844a00d41605544d00c8501903000508090003901c1010994600f40e200c000030603026005c43c0e03d480c201e40784800114600142160000c02a002c107441b801c21040713801468164000c0070894042e40c0c2c0260000392410f0304d105d540c82c414010360030701040c8003c5000660090801e80d46407002801103c2c0c80d41c0600c016031041c0050000001d00800082004070800d50901c2d4000781e40c080003003840340c4200312660792904a070031510200034120808110800051050400701c0001c10042d00100103844e5515031201c400b03203191040c075500d641c09600004029031104100d010020980c41c40741c0d4075031038460002c0d081402400080340010300702100c03107248100f1a4610003403800d802440c84000310018038040d0405240309401030744601c3c508200261078001c40d80304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 368978642 1250 368977392 368977421
    0x706020f030f0f0919020f040e070e01090e0705130b01050d020d14071106071b170717030c0702011d120a03080a0207020a03230f01140106030605010f0c0201090801 72
    0xb5402d00515240c94900050b160310501d1380000d61400500d45502128000c65404032500c1110b021141d012030b0140c0740301002c00c152800b45c6c15002c0b405441000e9460305852155908101c02c0c44400000b50344e9000750b009950b40010b501c001540070041a4021404400e0107143c0305041003241c1910030b084e0703041b4429500c601600c66200004690b16803030b41c19030102c12032910300034004480101c0740d1240c001820039400c002001c188203006440034060301c07030019800b0328448040e40c030f003084443c4580c1042c0390885d480c005d07641110007011821010740c0d00840401104500d001e11540c01544c0406a070200031404040c00a00502d040d5104440485201c1d48040503002c10304aa1500510062000346420380840c818000040981c40d840d040f441500c0c0e000d4403014078214404c450415442401c40e075903d5603c40e9821407512500190000c0321803102501200741c440c0d032104401e805881c1a80a000c2c001107100e042421400e101c1c80e0295501801814903601c21a101c4820a00752280b40388003c86 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 368979892 1250 368978642 368978671
    0x1e05070b030907030219030f030c0204021902031206030d021e010b04050a1b1805041d0102070503070326071b0c06111212040f03030b030102070308061305010602070b0706020f03 78
    0x250b08044046c1004101d15000d1040200d046640da0940881c212001a003001003000c1c2d404110b403a1941120341030040f201d240b071614920614000e60701e0b0f015100ca03102c0b60428001082c1103040004200f410000b4039000381201c100d20442007914207200f8000200e980d92600c03102000c1391210f201d010f01400d80ba0801007005030507030703c12030307010664030206404101280e0708408200b461140c00130287d0301d08840c0400c0010911608050758003415a503928207500c001154020030500000410995120352600c1400701e080d84040c5a06c45403005a85c102c0c03407841400500e00d00e1290301d2940c481c0c00b4040b0f00e081102d41945510103001d469421242c081040801140c02c419020040a6001d9902102507850445507643d00703c0c00f506c021344020144c15010040d0740c20540030340c0041011030710182c002c64941047e410010b000a01c15141103000e0103c0d075180400304d0710710f0b020f003038140c920f0764004200840c80c112450b0f40c4da0740441c000707131015075081c4008405000084c00441c0954000a40c0c0f42 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 368981142 1250 368979892 368979899
    0xb0c07050d141801120c03020304020316060806060c21250804140328060501051c0b0c0403080309010c110312060105070f080c100e07031e05070b030907 67
    0x2031070038410201c0301082c440107100000c034041003842120442c407000c500140c910100c100c01a83e003000850800701c00130303080945c592807003030741030307010f54030031402141117030030f140c5c5d10010445d00c1e0300302c50140d8070001e0184c0e000101c8500300f110040414050b003208039100164402c0440d02c8044d6000c941d40c0302c0c80b500240b18800d0701b4501c00c0b10203000d2403410050445604075903a00d14070384128441e10f207041c90008034030100c0d541c05120b140071100d5042070280a0a4075441085d0001d4440d00c0202c41461400002041c00c1c01c00d40d400e0540c0003032010010b100900980c40b407018081c0000e09400045100300f0020001803c0076002c0d5000341c0c00c41d8000b01d10503151403400740521050303000d40107d561091001d04a2260511960350700a00d0a0a0195a80850342401078486054000182c0b0712040001d0302001050009600b007225103080c00204480300e0b2540400751641c41030f10002e810f0040120ba120130450f40b4038080c0450070710070021900181e80e507000d6015560400c03603004403280c02448003007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 368982392 1250 368981142 368981153
    0x110904090605071e0c3909060b03010302090f060f030102071103011416050d020f1204052b141603020a29010b03130605010b091504030809011107030b0c07 68
    0xb0f00b00000f02d250f0303a00100d028001c02030143d0101107020748051143c010101c00340c0d0b031b88100c1c548056100e113a4543d03401d2400580444418171440340e0601e1910b8a40c0000b82d0350344c00b505607070603030754000c10004980c0c5640c4094001c00d8000307800d442e8484204a81c4804640d8240b000740081c038400c1d40002652003204040508403142140b0039840c0214644c03c218602c107080e0806a5030383c1d05410081c0c0c41d03030700700742c2610024091251203e2800742c00188682c079800d0010400c61041d0310801c03c0721000d101e100d44080d8140c142c8881d041a9640320b80d001d4a00c5030184c3380208140c0448100107042034900c0450340f15150200205901507000556000c0902000512428030703c00804c0703072000308d080100520070859030b0500c50001e102c06e0110100d20b0005145488019440e0000000e12055864403011100da5003c84071540c03086148030000e0044500d82401d8804494021440394100581c000041d22003041c4a040d443e401e004112011002840600c0014002d6400710003007515130002c0d1904 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 368983642 1250 368982392 368982407
    0x6170a0207080901050a020f100515010e0f0402070201180f15081006200a241104050405060a03050d0f140c0601060e0301091e020a0b070b01030611090409060507 71
    0x2100029801000701d60041001c4408a031075514083ca010307680e070a080b4034100d051071180c031001d40190080806450f080368168108600400604c0c83d003282c40c400200054a5130102c01d2a502d803c50101c1c0c5148810f850143d019114650040c140126107946000600707055101035000110310055401c01445440c20a04040114100034108607a0340c1c14110070700c0c595690b891003820104010366801440101c0550a41c042d01e841d44c4045800050241c504040d21415404140209040003908118541501e00030880442440041e075403409051030148070203880c00400307031600001141c20000000304c2c100a030100b0021140c1c0c50b20f56280c0855401006405038120421409a0a0006201c0303c000400d1150466201d4100400c0170a40d03680400d02608030054090040c00903000c50b03030f40030401282d407030142600c00c440c0080c03141c2e02c50300760f03081e41d00620340054aa800d5034401400001c03581c3c0d01034000380341101102c0e8103000b0141c00050564106a01c21201d0588a000340300086400041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 368984892 1250 368983642 368983651
    0x6190b0109061d0a032d080909191d1b060d0c0507050708030301050a0b0403050d0804060e07060206100f03051b1306092a1202070c09060b0a020f06150d03090506040617 74
    0x80c6d4080010058985110901407403031110b114903807072408249202a10341d0a549120000b0006103d10340d28034240c50384805c002618080980144041c1030340d1011486014007600b04014501d43c00c04e2944031482008102c01500c01051290400211010440803c0000000c14050009664942c18a400e124454100b40d1002d08031039014001400011004100300a07030541a01c2d0041c00ea03555070400c032002e440002c030307100014004c010f0007088141d40801c810f03214503ca103072200451651342d0074450b8101003905c005403107508481c880d0000400030159403d0322950091406080a000090180803540c142d07022a01e0690380f55045401c1c16001c040810f86410402d81443d8188010340e07000e04801c220918000607194005155070401035071a1201001d804041c1c02001070b180c8921003100c0303c1c1d00c039200940c058418103440d080410400250035226020006403004015400001d000e104020f2010071000d0002105011460f034484001400040401d5a203030402c0749214503190000c40390160 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 368986142 1250 368984892 368984963
    0x20306040c17010c17060d0b1003020103060503060402010903030c080909010b0414030d120b061b070503120304020a120501021b0d1b050304050111030409090506190b0109061d0a03 79
    0x480c80c0c00c0e01c0e07420140b04542500e414000c07009031b5480d84000390b000c06000000400c00c4008406005910341c25014140c15603100b0f807020403805880340105a91034504070381c028001005a030081c070002b4469005004404c1c4a003801e00d007844101c200190f1450400d810100031044045010007066924042d09500c0510580c0506030f0003882e10700c0104405192010840c3c0b42d070700d0344144645a00c4000880e1907007490005007110501903240c003691514171901c40c00d8031a11800302c400d8016503683c401c03a405554002c015502c3c081c40d1030100605c0c814901c0054071555030030710a5041d0421004104030740005d408020300060b0f81c0c210005003800024002d80c00b48070704411201c0c400103000000304d4060b21001d0810005104003481614503520490700403d10803428400e0f070400300640010300300c3c01086004000320048182e0f42c0c48100700c45c000110790307000401410b8104080c500a000540c1c0301444100d07000765003152400401c2d0146502d134421550300701c3c0d511405101c1405868005659036500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 368987392 1250 368986142 368986151
    0xe01050309060a110f0408060702060f0f0f060d0206070516081b061b0d0c060b0d051005040203030415050d060e010b25060f020c010501061b080d09020306040c1701 72
    0x8020301e6503110002040e03842910b940d081c0d904149564030007925540041c203060f03e41d403140c460300200d13182c80095840002520510002c60303d1204c00107801480b6041407000c1604550345c01c207414100c0b10300542886d8001494000510140c0c0b20800140301250240c40200f681c60b500d00c083e200b1340c10070ba900440040e0000011440c9010540c00c1408802008403000c0391902d140140b8402401100c000f1820148500c1c20501000303500318841401d5140103000800504400100340000d10150b01e500a0464114003043c0c0c040c00815801146c0281c0068100d85c2060b4a174003000d8040009103103144007040d03010490488514241c012040a40004410808103501d0700d0745849035406850007440c0c184c80e0380f045284070b881101c1c500340140394100005210342d40504001c44000d500030509000d49500b0a800441c00324040c0101c421041c85a00d0451000c43c01c548419407a82c2200c0c0180d8002c1e503c0b80482c0025a0f400c0002900a0b402031804a900c2840c00d218000d4200861024903010b9040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 368988642 1250 368987392 368987401
    0x50a0210050315040515040903021b180712060806130b09010615050a021005180c0a05090a0e01090b09010e19030203090d03110618010f0203040f2913030e010503 71
    0x40814010400244ea0216040c1c4482100c01002094035090075041403414980e81c0c24150f00081e07451440c20700710401c10158908000340400102d402020f08020b00300030010034010340c403d100025440d0703200440001c4050302ca414950805030281e8401c4410b030746600c81e410503c0500301e0090b4107c500180200302c12403800c4682c44203494585041d509001021480c6403a40b40240003140c2d6401040c81c081203146041030f810343c0d0f490741e84d80fa101e22620a40500400030300703001c82444290758005001c450142d40380450305000e0a0f0040594a45540300d9000000050014810301e000c0c104400000c01c9610b00e60501ea880c1510f54070300441404241c0c5641e0001ca5000300031207180c02001d550382e0700ba84180b81025101504240c00c010414441c010070840d4a030080c0d40b5074000c950703400000340f050071089643c0c00140e00040d207002d000e0015035400200040c02c155001100107500540303442035881c1d4040c041d25907020842ea061500d01d042644007040640c402d8800b05444001d02303040d411810f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 368989892 1250 368988642 368988661
    0x91118010f0b071a010603051005091905150a030605041406010f050603060f190602011104050102100207020d020a0b090a0504061401030e0f120415031112060f0d050a02100503 77
    0xa0a10038540464000103612040c000c1864903204c1000a5850902581d65100001002060b040352010445000c101001c1803034684010a00c3c05000240001d000c00c1e580c18519400800c0e010f00550300b041c00100c6643c0c0561100010f10006600a41000840b40382a0070100341c2e43e10924213540e001c2e0000401401108041c00310b010654000350341d9070b0f4403036489002060040000304122a4001180801402d5000139110754400b9203103d60700030b205800140a125a09010318060f41d40941c01400c5200450b400590151106500040810301001036680110b445c038907003608209507500c0d0000e0800ea260910304402402040c05903800c025031481d0a0140007001100b640d60790400d0703181c03a0703440403900042003581860070215003590b0007968941c811402960040c422150340c4404261702500507070207407040c07802081142100e00d18180c4855690350b01103900400195000d0848250a4002d407640643d10007094881c100800f88144c50340100a800b1411307288e0032003088030410400c0b10262 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 368991142 1250 368989892 368989919
    0x9150606110a170409090f030f03060501020d080907030b1603060b180405101a0a0305060a080a02060a020f010f02180a0f050d0501020f070305030f07050301030b15060d09111801 78
    0x6400ca81d030303020800710781c43e8524607070f100d0b40e8840b00145051072110400d0012500d0040e0040c4e2003a201e15510340e0460906900b55441c070b02c5120b000da045000100c08403030080100c15400b0300043d05840341f807600c2e0743e03442c41c1e8034070140c4d04008090320101400d01c4050300351154801a190700071059003801c0700203104204201101c61725070301940e101c902107800d4403040440d841c081d04d034421230215082d1041c021841d00390840948880040d00340b170003150312801d002d00000244d8074120050500c0c1000c130f400388204c82e805481c540c5d0841c402c00c0601c1903140300a2240b00e5140700f00034030242c0d83d603d10b0141182075120305007260b03100d08110740042200c410303403108000448400b903401d006048018100070b402805030314150800804002241c9003090780c40700c02140f01e51200120220f054590b0308044405000901000303145a2100300450000c0b8040c0070f410800c0d48004041620b4822040c000310292034525200303c0380c403240003e4052091030038074141d6a100d01c07094001311017076152801381b50b13070039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 368992392 1250 368991142 368991163
    0x70e010f060306080705010507050a0b1504180f02060c0304030c14010306091404020f0301060b0d05040c0806010303020613060621111e0609040204030c0807061707020d0f0e040915060611 82
    0xc04d001404c002002022f1052002c041d07040803070703022149400f4011042d1070300d8204005c0d103c3d42c548400010240462206000f0040e00001100c940d03241603420301145038800303a10318480d4030082c000000003031214a454000390410f40c82030b120a0f428000058142c613516000b0340340d52400c00c42045104401c10109540c09501240c5016940e104040400d0061a003500411041c00c0001200300d0011065040107024a1044821320070587d41c440040e82c4940080c0401001a001100418004041511a00d403501d000d810b001640650316250f2081058024100c4e0480700c40d00c0c08a4011b00c6140810084100d405403400341030220030140d5154030300080e816a51003140c021440c00410740b07465050344c01459000913454582c03510b500c66180e4451003071040344d000072084115608000e190012481c0034180a4004020741715081c02c1c25514214180c00003010000c01c904070030815903890140b240c003036009405007410424102c60200980300c5503002201401a001c01d0f4200a807000510010031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 368993642 1250 368992392 368992397
    0x909060f07050d020a09030212060c1630121505011d04050c070605090304030201051204030314130b0c070c0b030c0906041d1308041206020c070e010f06030608070501 73
    0x5952072003400e0b1520701070020444040b81c804500341003603981041544043d68000c0b41d80f6190030b001c451409668a20845d45604c9060b01030006109070601c3d51040d2901c0c51082c101c4c803804278403440d0084000c040394000b54101a54494144040c50741200c604010140180303400d0001c1091144a245030361268414a4100030f03110491a40d10240f081c0e0011641000410500080c04c000300348004c40d0300800310580e41d070b0b0310781000300d441d0400000c00c40b0110b0341d06031125401e01c0b03604110b050701c00100420940a058554583c808021b802c8801d0512850444500b00260402400c10304414000208242c544040802210011640b081d2601040300c422940c0ca0b40e4030b6403000e03d0040305014111b8010380113500800e010400c504100303182515000c0400c2c00030300035a600002008120324402015117611010132051204200e035100b9001094003c81003d4600712104440074640002580845000103440c8018089462240103090041902e4076091040c5400d01102580b584111f2003803506 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 368994892 1250 368993642 368993671
    0x1020316020d050f15100e0615120f09070602060c0d090c080f03030a140415020a0203040e0c03060405010b030408030a09150f0501180e1b060f0a030e010b090906 71
    0x1c5584000200310400c1d440420303611954014210340d03aa860811204215112104000600700d4140320280800c5950500100480d41c0390541130108004020070041e403090b000f0000350444c00e050818040c000c64403007035164000c1ca41310074206c6c206412504580e00b15003118007404074504200c0c085d107200303c25003400000e00300d03042c2c0f4101c01403900c0c5a1001540e0701484110003400c142c084040c40c0318900031841440051603601c0c00300805081183d00420225562501484d07155266016010700d14050044901e00b40c1c176a0300303004044c030044906c00e2913503400004002c00b80c01c050043c64010710721298001e0075401c180c1c1d10007206001c0106030500045d5514641000c1c080c10400c260500700e51002c04101e06103003269054040c0c0002d010340303d014440d2500c0d181280c00c1601c83d16000ca4403400c05040b08108026048500100400600d40e01240905c00036030f041c00320100402d002d4441d40c074006521500903d401d82541c06001c10746120392400d07410485203c4001c61010391091011a8068 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 368996142 1250 368994892 368994937
    0x6230714071a070302060a05040308040b190f1a0a231f0302070501050105060a0c060b130c0207080c150f0304021f02010e07050607080a0804050106050603070918050105010203 77
    0x9251081a40c4406000032690045044000e01100100142c034025806d50340d45640c1c40d2005000e480d03040e0f400070005000000041c000c101c0003880307140c000e4030f001000c0001c6026100c2903800d403050780c071540350080d5a8280c41030601a41011034a202c00742550700c18919441c080700c2045c2140030400390a03c010040c2190b80650713444001a510041c0216054103901d0100d000c020001e4000a00460340c42d8170300f20002c13503185003d4081e660700807240d43d03954000081a41e036980c042d1007216041500001400c0c160308508407940134915040d801d42e0300420030145082001d61600e00300343c207428003646007400005e01496102c022200000100814165251110b101207140408a4928107a40c46544c002000c0b10310341c107401001d19035003010100c2c1c2440f03803600100b0070341d4411200700600c250810002c00183c0c40c0a48070441c0e215000d40000100070f680ea2010565640c006c554500005004050500883d0004a90814001000381040080e581410000f035607038440c8000c0b50f984041d1032603040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 368997392 1250 368996142 368996183
    0xa03020d050109081b240a0903110f21090607030c021810170616030e0a051f290f060f180411030702061611060907062307 54
    0x760f1000d40d10041c01a40d40c40c0111048031100a80803e101450080004042c920407820b10407940c40f0810b81c0000a0340d803240400440101540035045040c81480d8a0b46030f2150000d0010709141c4030100060100340f1500b42d500710071922801c402c1d00c42ca138428400e00d030446d100c2d8019a00155818100000d03404100c3c0000348401ea4004035042c40d42080c501040401040d4826078422203007080b2440301d0740e5095404582e1594411904c80c42c5484411004800700ca100382c1042400c41c40103019903003110650b403a600d0510381e20a0741406d200004c80c40003103a0300d030644240000e00c0c80c40d01e0f20181240c0c10701804454980c100c000300b440381010890b91110b90b615035040300d02034940f021615546200c000b100301619071020300703514030a5246c507a2804410140700222803150a071a40901155030312113060541400e40c020f00e0000f0031005026070f0300c52038004c111090241242e180180000ca1500030700034143c025080d0a01e41880d00002c540c4039903420034040d1884540d200c1e241019070705102a90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 368998642 1250 368997392 368997401
    0xc091017280903020c0a0f0515030a0e1002091503060139060608100506060a03090f0c03050606090603010c120b0301151503060b0304030f050a0c020a0f09060e060a03020d0501 77
    0x318502031502d0034102c105600003a403003910680680e2030b05511a90754034070b14034000071407080c20340002c905146080040740003c02950b0045a41100040081c215440c26150514030491035600580c0092800d0051900441d00c2c0321781340b0810345140c40c5281c6180000d003014840c814503ca402440d0080107100c214402d0b001c903280b2800000d0354000c003071504120b80980003520841b174507030040083c03403110711540d4001e2074400c082c05892b031860039800304411001080040b0381a10840d050029010014081c000c0d110011030080c0003c040c4c500700501003151603040684001d1007a8501401c0d295803940190b015500d0080c902400211404100086805004890707180c8100c4d1030070b40b41c00300e485499030005070f10324419541e0412186880300c80e610240c2c84151009404201c0d40482000401e1003900106203c10030703071a0907101c1c1d034000d50100350106403d801c043d09043d04204244056a00c500c500c0004104640c14070360fa605084010132810203840c00043d0042602c2106001446425040b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 368999892 1250 368998642 368998711
    0x26073005011409070e09060705090d030320070b0a092102100501060221040f0b03060607141c0516021c1209030c150e01050c150c091017 60
    0x2c0304249498410350b025103804107401800e0040291801041500c80006489031040b03071251603052a000c1070b05d0402c9850854030400314201922800c0b0f0b40f1400c0e0000041000424503213426548a14252500f982d8029000700038850051030001440c010600d44071040302000008841591108030503130b022424800e1072502c414803203080c8000000c005a002804181000d0041409000360f10140200b450030710407441030800ca0a0f1100080c000200b2038001503400c0b020081541d494180b99641d10070300c5400e40c2407030b0480d60b003052907503042e800c0038400b00d103504a8030f51800514248481005811b00c01007004040d000c0e0440810b015240c0c000b03a801000341c1c1d90403141081c80c1043c40b40000308420800c0c0400c42e18100074101c0001d09550f402403c1c3d2402c0900d40354189210a24001128503030800012004039203e01c003400100c07040102402401800f0410500780e59807103007001d00c510340201c0e103846400c010b451040007401340c0301240e60075001034207030f00389007032a01c1840d4680a01c80c80d4104c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 369001142 1250 368999892 368999921
    0x70c032f0621240a030f0605060d0f14060604020705031806070b0a1e0e030d0b041d1006050607120c0614011e0e0903091302042607300501 61
    0x81c0204440c0070a814041100414030021090043c2401c1c840c04501e1888018920b00c0301542030700000b84960071050780000050080050003181da214540d50b1444074400b619034805003200304020000a000c01a800f42c4150340035840d001c0c030f9a444036a83d116102070700025905500100000d0380e03400c01105c600c03503044070b480d10340c07802c103041c180c80280344c140c481607404000082d094100f0320071401400d070b8111030180a036040a072041184400750840329070742d99000741d0399840c402d02c41070110104030340180079000a10041480101e00c808487d01908280e00c91001880000d00107083d025090450b2455842c3c07a040c03407036035450100050410f1168104404412600110712a2800a594501304103e54950020035503078901101ca15142520f074201a42c104120030442402c014140c8010103201c030750300614155a5100b0b00807501b10202900c0c5403800000c011903140b25040007001d000d060382c81190115043c114018990078820040d485080d43c900720000402c0c48401e50001c00c0c040d2000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 369002392 1250 369001142 369001207
    0x140a03060e0f070504090c06030510030206040f0e0109110403030507151a01030b040b030c060f0d0f0606140a0203032212050309011508060403080912070c032f06 71
    0x421450701c80321540c0d000120b070300c02c0000004407403609004034a4169000a60346941030b0500c00120080c2c14001c10741042d03440419400001a00e41030028402455110100e4040f03a0a10412600c40101a4010341c100c03404c002d0390405001107041280c0483c0d1341400c000ea1740320b01034078124503014821400240b0091803c000e0f981400c9400c03116182e114000d90b4100312008411081008444190400c00d0701603000d61211132043c1040d80c010401100440003c1c0c0c14514403154031401d80c0c4e0f2492030952165100d80d400c01c50503401a0002107180d40b1204001d042071860f50000f580d90000070320742c0c1c8141c03c1046448a82c00e40d8100d50b4003a40c3d802500d8076490b40424000681075510590740b01265600e8840606185202d4002ca6001d0721007585c0034092503112503c040b07555850190442d126805190081103500591038020814548180c145640d40e501c0c42c00c02001c41e01440c0c90294018110035003807800e48854a004010407002142d055403103034200c051608140c20300d0107800d035010010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 369003642 1250 369002392 369002411
    0x7030506010302101e0e010203090306100302010e030703032102071e2303160305040f0e01060f0e0d03120f0c08010801050a06060203072603070507050c0307050109140a0306 76
    0x4603056040c1c034020b40f0040d200c081d000c0021181c4000111151048030032400203041114407030a52950707110380520499040c00e45001c0003d080940648001c2c101c1c200d1541c0c2042156044140720310740c50b2049000c0c00c030041c5184c60144c54034828560700758250013013840e00c141c8002c1c25815502059007000480340503206410074000c0d0110018001e580e00c00009180206041c40b584403209943c02c10b901940c180304400c044103e104c4082c1b801142806070038080402d070308501100603001405d8030010314205501d44a0090031000034900d0300c000300444c1c1c0c200c0300043d481c0c602ca1507850540c140fa054000c0c0c012600c50100810450610001007400d0a20f408101a4002d00040c181c9064070b00030400c0307882e1320105c84126205d500c01d840250704184142c0e0007007284401c015030090f1503400503886050a52030350b21060340c803c41c0c0010109001180c4a420303c001003003949102d110550084c50315a00b1b120019040c41d01034031a0f4000740c0c8021407859802d0304d07480387d008000d56004c401400048074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 369004892 1250 369003642 369003653
    0xa0e062a0d0f0213090b0f220c0c0b060604120210030f0f0207150902150304080403231509191b0914070318020625030915021c110f0703 60
    0x308840400c410349500c00c0200d2146000e10416591686c000d0015100000305024003880b0f0840d01040c1d80b0301c074071032454015408154007444e20a06095038800101c5001e03403501005d81600513107100c0c05030000b0b2005108a40040d005600155012200d0842601c1803c500f10081e10540f08100c12150400404004002141d00a042c0440c850f58a82c0701d40c803e0f10810808031006401c019602c80c00b1124500c0d40e103041ea000644d00140102c408a203455101d455007402c1400ba0785a0402040000300c807885182418424840501c0c02e121080341c00d410800747d856a40c00160701c2070814010100b482d001000714000c60414040300322a02103030601d0382d0300e014100401c0c500588845000d100e00c0051507240c070a214600182c0f181904d941201050380d02400350580040250042c110760888100140d2080d5200e0603400501ca5543c0968080c180060801543e01d0f4038003180c15984000781c6200c2040c2400c2034010b81c0701d0b55150201402d120790105924250500c01c0c0441c081c0110b94001c803d000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 369006142 1250 369004892 369004897
    0xd0e03011e0507200d05030403051611090c030708241206070f0203030f0712090614040212010b150a14120709051e0907020709140a0e062a0d0f02 64
    0x2509450313450241202e225a002060810000820160004015403100c0c0d8040d102a58205000c0d2070940c1c140102c540401c04074222040081e582d80b810320172404080d16200c51340d56400441c8280040c118100035001804024000e0702001a8545103880d405a45041c51034000544030014480c0303c40c000325100c0c0d41d03101d00301652210006812400c10840c003070b00000480e40121000d03031401140d5507540c542198051131a5418201c200c0e221800200440c4881c000c010300001e001070a014541014410004210f030100c040c0341003a411b0800409440d9100040300030780c90161540255035840008084034000300c00005002c0024000c905806089143c0e01034622845081d1160300d45281c0340d0303040142c6503403444404170f2508558829403140c1d040c01c02c00160071174501d00440d1130031a01c0d0840e4400351441c1401010407604120100700721021280900c0038448140009016a42444010341c000e050603c400c3c400c4090200081c01c00d020090340484102082024082001c1ca00542c0041e0195 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 369007392 1250 369006142 369006151
    0x12101d3c07031101030204090c020d09050306130204050606120103050d0201060e100306020d06090f0903020c04060b0412031b0803270601330f08070507050d0e03011e05 74
    0x94492180a0018039504104101a0210000145081440d560381e0003251880c0900081c1055002d010025540c1007070300031113050480a03000740c04080c011450080445125900852080e40140d05000d0221a9841d1040c070240c0c054170081100e541b0400840c44134854141c4101034185c2020000052200208850720030704c18690003031100f9a540d10122001c80000d9806280d86000c0a40400003e05554020183e140a2480114101e07564040840490b40084030034540e00b5150b8a241040582c10320001403143c404840c2000051b081c501406401d002e1782c001c03031081000c0c8091030414107001d0140c03d80f03044040842d0488005592504402680093322202187c455810303840402d01724000300744c0c0980c3c203580000c0c1401da10709041d0800c4d010202141c414900c01403260a14504c0341d45420202513030040d26501c51080003d64002d01e0400010090010018140404400030308046040080309089151480020f25607500082c01051803920381d0403001d544180c004c502c84410380109209 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 369008642 1250 369007392 369007453
    0x30302030403030801120816030e0a0e100618090207080c060a020d0f050f04030e0103060503100504030e0a140405060f04150602060117030301032a03050105090c12101d 74
    0x503607882e09030341b8241000d00c4000f030003000148140d1a424000c450810803190003843c291050044103030102d400046142c11229200824904104011aa1040c160024041071415003006245600034141c408240c0c025461a0381e0001070000c203002603141514040301c2243c05940749402c0c18502d00009520807409260ba45003007042d11030740e02c100c40c403945109003c14426000302c0c0d030b9142e50450b094520010507905066a6890100d19030301c04100c240003040c0d030700100140340c1c00c00e41000741034491134a00031031090540d8001030000480d00307110071a9010702a5408543c40c1c4440b00001d000d80c01e201c10303441c0c1092608248419205050029508031030b419001c0d511142d80399030400c0344046d0300f00a103403040c0d801000108000b543e01c003681e60440840d41c170050300100e007500045460607a280d00c1501c1607034498042c040341030b0b018001074000703c2044400c1c91600c3d00e4180d81585032801f140360790150035600c812075410300c0c03250001d0306c615141000c15240c0b04000c0401c089000712091000104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 369009892 1250 369008642 369008657
    0xa02011a0f09060103110c0a050105180a0c0b25060b15090a0302090411090f0106031a010801060f12110c190803042603010f03151e0213030203030403030203040303 72
    0x505040080000c0c0c032222025251440b942c0d1200c00540c00742805001428460790108000074042a05000e10a036082c0328000219480c14114000d4656040301103603216982c1021030207100103040400c50404645a98103000d0325207480d5000b180c5045162a8413034028000740c40380d10100a042d0740b10b081c0c15182214990b10180e02918040002d0242072949500a440000148058036044405661051050f800c0221410350b150105115030000c1e80c050602005000040c072090341c16001d070b6a1981000c0c1503105542690000091074141e0621403003041c0208103400c115240e12500f0300043c005101d540610101c0220010a180d41d840910100264000c0e1054030084140400d440200d1a4122541c0341c15a00e80344c81d030402503040c2840c40508440020450341a4500c413a002e94020103172403048401c01840c41c03c0032201d1022102031402018a0001619038034600b111210030590800800103071180311a08001d0000030141e040a5072521001c6400001c044d80040240700f076038402d564009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 369011142 1250 369009892 369009941
    0x20a061715010e010302090a080d030209120c060d0c2d090501050301050a0905091e030912010903120b15040e01081e0a030302071a0403080a0b0d02030601170a080a0201 74
    0x180094600c8a2a0009000181d42c03d119071194000e0811184014501c0c98207607511510030b483d080901c083c10f00801c0d0041101d0314507103402c09009007180207410107000002c449000140315880b80c117002c083c0303050303170385090103000d611507122003200302000000702d10715806075120903044012100e50440083c40038040400c00e944600280c904986014045403405801d003a440000b41c079000b41807802600c140306c5038494403400c00d2150003102e00d04c0c101843c0c1d074600d0301082c450280311105503890aa8101503080000a600c02420300d1008081d04002482c010000d0010700130500c110f941606075a40490b010a005d200441843e04031080001106c0b5680045000c0090016104114000f10340001207018042030080e001003d1041c85450705140700403413007680c0c00c1d9155041d64141c001400303140400005ca040c92180403004101100c0b4070100c1542c80d40000ea4072807050240301e4152800710106030501c0010000190341a80c4444911b4031b8403a0a0790080c0282902c42c00000041c403032500a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 369012392 1250 369011142 369011161
    0x1a0f0a0e0a08030f0a02120408070302010b0a031e0204020903010f05010e010806090d1101091401020a020706110a021509060a020f070e011d0702120a020c04050a02090a060f0309020a0617 82
    0x1651072548840507a0455480c4501c540c081e10f4000d19551a9680070000c81e0151001034801307900c00ca104441c4541c640c002c0303040c000c2c2110403034901c0b1401182c82400a01c08180d16544a0030b9101204601c403141ca40c003840400c01a010302001d198040d0b00301003011802000c0b075041035040e41d041c103901c004103a81e00c4417074135650305050b01c150019800099150459a20450b021703104250030348004203140304261384240c404560501040c800c3d95001c1000c620703580d41400340c1c000801d2207141001818940c0e46500d62103078008030000780b2501038600806840b50365801915054500100115200c03000d040010b51148500003485a56010700e10f800b281515640b41d0aa060351003101c046503106c907400080e501c00120140c000425882189520006403031541d00511243d05c0c0c903805000c901e2482000d00c000e45a0285c11118030900600c6045450f85031500c064085541718a4000a07480d6085010b400404480c0c6010303400c00c4c1104004a0891780084481c107080040300c56141c0c5c00c1d80c0384441d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 369013642 1250 369012392 369012403
    0x90320010e01180e010e0406050a06060906110a0c090507020618060f0402010e13020d0f090b0c0306010c0c150f0201020a020c01050d0e011802011803050303131a0f0a0e 74
    0xa140800e00304104800c1c1c9502c40c490f0405054902d10810b10300b00e40b91886040ca4a009a0201c00c4040700102048108015030141a400100c0e8081c14000141003000292448149003c3d00c000c01c202140c000e60154000c200f41d0401c503402078442c0b200d080c0c40c0c415030400f420303007203440e00098031036440401c1039450081c4124101c04225000307004261035800042c3d103c0c0001900681c104039000c11044c0c03442c0d0b50607400500003d03426600583e2004407040c824140c85018040d4a0f03903030300d030254440204001d185a04e0b840040e04150710f07520758902c030059034000c0e005540034182e80141c0c0404200340c031140c0c9101465400740c2c0c55846641d1300500b001c07030a0307209150f00070005030842d01600b50554040e8015003030401c003242001c14810a0a040310782150800c5507000018017002000f4400d55801c000700e81c4080040c0c000ca444c0c52400d645809949200c0a0306490017540306441400a0000940103a20f4616004080200a0602c5081c607000c22005440391401c0780d141080713400c07101500095 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 369014892 1250 369013642 369013703
    0x203070e07080a0b0f06030a0605010906050903030d0e03071e030210180f02040e3a1e030b09040b0402130209012a05010903050d24090c11010c0903 65
    0x45201d1141c0d95108150003034a001c1021310b4000300140c1050090390740703003006188503010541c800150f440c5080001040801d0a6009805202d802c02c0324256a450110840328088140c003000b0494010103010286136100b40c400c00342072404c1000e01e00030400c108260000499001c2d9080301c05180e0003c14100485034100b40e0340c62910f500d007030301342c0018074a0614001440c1c00180005504000000c15a08001b19001203074890580c0004408404030400004101300c2003c04000e81e00201070b0201401400c0441d0504044900c1100380700d90043c801e8010280700700c03003e801c0003540d040138903000d5005081614100c0c82201491198401d9202138820345d600d05c5c070305039150002d441c0300300c05003107840c00c00c100c00c200565041c40070303000461800d0080b601024403a0f683c42d9078074641c3c81e00440c11502c2c1c0051003d40c89000d40d9484003c1880b046404040e40c001c004001080801360100381c500110004210800f5400c00c4c00c10300d541074021051070304a900801d01800c5481d001010002d855140747da = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 369016142 1250 369014892 369014897
    0x80a090609050612060a030206041401170403021905030915030702010b0d080a0c0206070218180c0102070303050c0f0f100b15031302030f030c1605030c090705032a070203070e07 78
    0x31a0f2400c0345000d04007280c2003600580a6061b240c0c580c0c001c604141d2040d00f0201035200568460201c559100d001e01c40408508100440c1c14205954025143c00c0d40c00081e14500303100041120903c03c0920407101503960040119603009a020f500b004e20303030030032207400b0b0140d442d00d01884c40508080084a510a9001803e40d1500542d40707010341c3c19520014040c0c2c1c012409000100040c2c030f030040480030030450391405002c0c6c0d2420003480384403141b1584031803440b600b105100752056600051244196540b6040c02600e81002c4c542c068688126156040403910841c003110802d00008140285404000103050000329180e03c2072144044041e29408a1200d081000880701103408112540181c8010243ca0039203070001243c904d55044180d500015070081c0c0401446070240d40850b8009041c103130f0250440743c205c00c000030f480c960028080800d04c031001000418030410b26480411000700000c480c5602d410f031800351011500130050890080c4608040400c40e40c220317007401481410300c0e9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 369017392 1250 369016142 369016147
    0x423060a23040b270105010e06010504180528140601020706120f061208130504051603050603070909030c02041d07060e030a060501060519030608250302030604080a0906090506 77
    0xd0f690b082a0740d0009280050190070400c00c000f128003a0700401000c42c600c180040b501e5414500100150706028007601d052120800c0200100e0380d8825442c07098480d1191300242071b544200c10742d00301c075400303042c900c14100c3c13858400c882130130b0b9030391007031016a10502800c030b02a40c410005a03a40c0c139041c0980000702e841d000003843d410516410041034001c54039000b203a11130b030f9801d40a800c41e14034441214020004039403c00e00c440d04100302402072408890904c964280b444c80035000c407006048410400d610361000422310f031810800c0c40002c2c01c50020402601c02d65040040c01080036502c200c0c032079410000c1c86080c5110800c00d81400400000241c012189070207810b84030050846002501401aa6002d201260f401e104207402030200d03450f0b461b90b549900f0500c00503202a0301d0100c05051600505100070100024005910f091341d0400360744a44007882800300b1941264070095140c8030315820481009140c1c0b01a00902269803110f800c0b15403204015507406007a402042c0d0801801d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 369018642 1250 369017392 369017401
    0x151e130e0408070512040602060603030a0912031418030c090708010e191b0f030507090b090a09091a24060a030b100216081b04050423060a23 62
    0x84800035908144924032103031418a0b02c2d44d510741030001c00c40e09610ba40b540400c0c01c1110139010700c003c82d03018100f200658600342e009003000d00540d00038001c0d5a900042c0845440815004001406d8044829008152a07481e100c8003071204100041000780a4001c0e1007002c40e20b030a000d140079008101d21703110300d16540e0030100e20920110005040d8500c03a1680308050080c14070500c075500c005074080506d00c2c0440b0302401e028040f840c6042d64102058038104c10001c070103502242235800d23140340d07800269a41045400113804103009400c001c130312134a040d0401c0300f040302d49941c1c600a944107040c648030355030710300103d07070b08003040e001c46401101c0031940000d603d4913040006140e80c1d419070030000380e0582c00d103000c11011480500008051380c011000560003880e060030742402010170b20300801c2e51001540030744105d2641140a00d00403510f07100410700b0800e80e107070505c04d041c2c0b0440078104424203015446550314015642c42ca0142d15150208000c00e0361022460712041480d040c003091a01c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 369019892 1250 369018642 369018659
    0xb18010617040b13230d090b0a08060f060403050304080a1e0c05040203070c1e03020f03090d020607031b0c09050c03040b16030e0d050d0605010504060219030905151e13 74
    0xf8404070465036805e03c6001d040f06102d42031002030340304030040c1c010220080891000751010001d50421088a10103125581e1125840100c20740d0040f8242e4103e140c20051a02003050b42c052500010320034007020402090302c0c800001ca01e40002d005074a61620100c20900e518a0b82d100a00c0c06005144101001d2003c0d052640055402201a01c0e00560034080368031180040c40041507182c115905100000d0b0601d0f604221194405503104090340c075090226001540440707582d074009018040c082410010705001e91a00b061031003544040042c03040e07052601d03049011050090031865845c01c800b1506045051040d82c3c4103541c0107103060a40c3e15068600e810344035004409400701a20b4803030f0421525414440502e003442e01e6140d050310b65040710a414241d56190f005241041006d000c1000354550000c2c40f000b00e020040c001001c4040305050845811941c0d80000d0f411103c20a13001e030200f0030040050881d10310901e01c83c0801d222881040745d01340710300b07014101013416801c020f128900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 369021142 1250 369019892 369019921
    0xd0f09150c0917030c01050a02031e0414010e030a1d09010501111002190e030d170a112a010c050409110910022802061902010b18010617040b 62
    0x10454140b0300d10855403403814481d00c484142d081c148a40003c03d507450091801d00174581c2003000c80e0b04c1941540b40c142441c5c00c580349410038030310700d840d1b201000c9014402d078403001c44411301c01c6c0b0700280703c018052041c05503207a0101c082000001c241d4800e1040b010310200c4440c04600c802003001c03c01e07034a06801194000e4005e444030341c40e401641505640000320384014402c2c0304080c1044030130f10340e20650290503900320030402802908108000004283c1c44584910305090300d0321000d800d80c41d03c0b0244402450302400c088a0b0b114001503106608561445407185c0a070501261000d400205038980c0c00e0b2681002d60b0b00c0801c0c8140000d0040202c26044220001c0350046420b00746051003000078100d968101c900400341c0c004140d0b400812141e1900049448030401c0e40b000a8052580805c0307461048510f5100744510390f1001d18a131074400e403c05020a14000c064980000c00d102a41c0180c078428410b20010038103102c40c4150b140e0310000320300d100310703000400200103030394030b104079201c80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 369022392 1250 369021142 369021161
    0x40b01170f30030907090e03040f12150b0901230303131a07050d0f030e060a0c02010c0c030c02190e0f010302011d0d120210020d020d0f0915 62
    0x18000c944107102000000c00c44000b49a000c0b1003004081d200039411007510072444451640d0406007002005104030b030010ba42000c41d620058000b0b110750382061a0f6085014a800c01240100b100000041c0c050168244102e56802182340000c04d02513800020201c0340341c0f80f007164121550000400400603c060004900d18034013110504c101c10900010f41594484070340031440d0054114140030a40e80324040c048100111201c01340b43c8a01502c48a0783c94a4065000c800c01004201803124948650043e840b40048030f8111203540c14003d4007071020f00702c1c085030780c1c00641c40c05442280d80f6100344412284160980ca8801c5002455000c1c080e000c51032840c820b08602c00300000041000e1507413400c6203d40d0141180c3d440c1541148001020114481020000c280e11445000c0181d550705680c0840240c1c0000b101c0703480d2485049c16410115043c0480269600c0460001d20200c140d400404680351001ca0802004030440504c00c1100e55585018000e01e40e0700280340300410b155407040d03941 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 369023642 1250 369022392 369022439
    0xf0503031e040f020d140106170d0f020a14070e01030f06050702160b13050603010b041a210703091209140901080d0807020f0109120806010822020111070608090d08040b01 75
    0x603410080389990239180d0a078812026940c0840c56541100002e01600150001a01c1c280341001c08008000756640e400060141016a155541c061203200401c2148010f081c0c20180c03803c070b981d480c1462038040c1c400d003000340c0d00b1600b04000036503103a10102e4101c0c0401c2038841d0482d00c0700d0800b0034003116500302440c0060750b228403680104450f5038010285000301440400c00707554600b040118206502c40840084220500340241c1740346641141410002030003032072801c00e0710381d58a00308402508425901602212122b100d03091240e51095509080c2c51100c22000301d080700200a212480100744500900c0d5004082501c01d51032140842d50703041111841101e00c0d00c500000001c0c211102c4010844401d01150200c1411940220f640c2d60301c0f040908014800740703414041440083c2001800c07010004800d44020704581c000d001014408500104450b200780e1078038405440c800d8183d6090030513214109101070400d2090001030301c160382c481850347e0344d40d00e011a64030305084003840c510705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 369024892 1250 369023642 369023663
    0x10030b06070c0b070311060105131a040603110a0605030903160311061003120201020304050d03180b0109060f050319120c061a100e03150a02070f0503031e040f020d 72
    0x1003190064400d01030441643d20035034a100034038001d4044032404a80d00004d4004200400141c2e45200c240110221440d0300482c0f007001c688d042e494600c00b011880c0d0313031040c50030402200740508200410070106060b1070394908591290f82c1615140400c4500b02500d070700c2040081c00d00c0314440c407039640d0503100b4203001e0880c00d800072030181089422100d8491514000d107003003042c42a4801241001002400210318504080c0c82d500d8807091a1290841815200e8038140c0c0740c20068a8110041d075082411a000c9503180c5481ca40500701e14410400d005a014002050500c0e001c60f442d4803030f41103c1080d0030800842c0d550281003003000e64400c0700780415074000d5001315805000d581ca0400b03030041070842034460b0b0341c2008500e0f80c101c1103040400003024241c40050f100050310724482c800c107403c4c02700c0c01d550b030301d00a02c013900c20b1440082800c41c20f00040b404101001001d1030103589407080d40e09051000a0303034082c00e40e82c111400741084004541c0100582011a816074100780140013192 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 369026142 1250 369024892 369024907
    0x5040b010306030507051c080d02030717010e0403030507020f0a0302030909011406160305160501020705060c0309101107080c3307030b1201290a06050405130e011a09060a030210030b06 81
    0x14049d420948a0701c0c19680c00004105c0210351042d0760554560b84280341a070254100301034030720403500050004060641e5100070a18145c005c1280c003074001d016004a817401c01003480d000b512600440c10541c01401400c0c001b0501032014016003184d450702404e0b06007001500055201d0026821304154244203081048902c40c40c0110a11900f86000e4400940d94068030702d001c501d4040e0003010594200310034401e100104d90302007680700f6000d031140c2020909043c10050742d100d601c18080021301e4040c001803401401340020172006400031008a030000d218081d5610f03840740e040d0400a140c1080c016500040d60b0500a5115000312080502244d00c0fa04c2045c61890031500d13480085100c014518084001b28664042c0840700020240d40781c0c1d85031840c0c010701401a02450207164418403d01c102c020328143c2550050488209180003400011010b48403901d1170303115855100d014400d05070001d0390300d081c0400d5603c01c80341d01500f11051300c000560114014170240c180356074041c0d030400201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 369027392 1250 369026142 369026153
    0x20c07030605040510060305100c0915020f060106020c01020a080a120e0c04060801110301050f01140f091315060807032c2832010605040b010306030507051c 69
    0x8801840c4564800a550f04040c10300364a041c8842c2003100c0380a00b00304050000034000b0900500400d240780c40420581e08560b0103881c400655000032004824003250349401903400540080c000007400c00303942d6580d0f00c2c0c0c1c004076200c900c0c440000703002da4009030712000040d400d0381c01841c1c07001881c94420603004400285500b070300c0341400c00f01410b03030010303006070050b00d018410300c4010045100200f18001a98404406900052040c584620218015819143d004458005640550104003030751000740c00c0d03c40d4150303007284060382d02030020410340c500800b603d80725800840e004a1007890038540b902808940400004140e01d04068071081001c4040e41c210f40d15219003111100f942c0c880d00d0085801a140c040034444030700c1c0c0644690000c01e10169103041c030075038464100100040c80071240164010030201655070302000c40c502400c030250300e58194810350a031501250140840e0034124011825102940005000782d044140304112514041c0d0716902e8514103003800240e561a1501ca0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 369028642 1250 369027392 369027403
    0xd0905060f0c0d0e01020f0a0b01030f030c120c0b0114010c1401020c100501080d08041208062205040311011a0d0f06060605030a0b030723030109120504180e1f020c 72
    0x9910204d5072201c4201305035a0140b040916140030320700244902d020545810900e0f5a0610002c0c01c02c1034040d116005040c819a00c0000c001e8001c41400054000340c000100b0300040c0060549880e4a281c001042004000c24480342e0034005940382e43d00c6200740d840703800407084546200201590308016000001c0420b0098081000d05108005040d42c94585020708044111210504100c40503041000040c0407040169440189242c9031800d581c8010224020390960150b4203008810141d502d80081c416030001031065110303680e02511610300803140707402d0799692200365400090341039240350603090001c8498030050080100d070f4403680258403594111001900020000b1340000200300408085005250803000160001e002007450068484c440b1451400011a014103809000c59565400d40040111070303004000c4440820007944040e007103900500c030f1190419184050060100c6807440303451294032107030b005045144c0340000c0d20511010641d20020302c207030342030101c00e01501c4104807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 369029892 1250 369028642 369028663
    0x3031d100212090609071514030c07060b040c0906181a0909010f050a05010503060f0a091a01180b03131a07030e0615061602131a030d0905060f0c 64
    0x140180da0315030240d03581c048102c0041105105a101506204e90f000c0c2c0080c0e620700300d0302c1a4104000400300b10b002260301d940212200c1104040203c180300001450100506046d440394604000008484046c40b0070341b201004074501244c1c86040400031180185260030b01911002c061510090320b40001e43c10600d042e00d4011100e205c00f10b50340d001c0d81001c116060252240c0701021051500d4480051580401801081d040040c04004620591942080d4911801008250f00300040c0c231072001c2d100510f0404401007110440751494415540500b00031003091b0000e0318040c64450410750380880903440074002c0400c4c7c9142d18242c0d404204a480d620368090b440104111150401000050946a0140152075035403c00e0741488408031a00c0d440e91011401603c2c1c0d42e840d1103804e110222802040724029400c507a80b05030305c10045071164400c8070010040c541210b13403c0356170400e069807507a10011345000b282c1034100c04c0c400f40c6416406040c44e09090120a494948003109690420345150b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 369031142 1250 369029892 369029923
    0xc0e100201021b0618072706031401050a1104081504031b030206090601090c0e010f09081917030106020a08030406090c06020d03110316111014100609030f03031d 71
    0x1e0170b00143e0283d004610102c01140d000420080d400c00150f0074090704c1c14803c2500d0700c060840d0001e00c85602d40c0000c0c008580064265804000c800d400074060710048490742c50191420f01811079641514046e074054071100001404a003150700b8070b04002c504060b00036014000c1036035070740c29442000c51309003a1461080d809402942040d10185e480c080d4181c0100b900c072401c029010700ea880d80f0248014600809183c450012407040e001076444d20002e4202e64200c1c010301c4000b0005100b0240108030f824801e0340c0070f1070300307900e12042c00546000a000d10340c01078100386240008039040340d0145805c00e0040c240011168216030b00c0c84104411a408880507803c910400402c1036018815141c02d07206410140f4038500e00f086d108000e01011842e504188043c1241600c407003482005450559510010108114208120340758140c80c8202c030350781c02d4004510320200b5854400c10100342103030740c0700c2d51550698078103540a50141840e91403108144041000c4d400383c10004005030140d01d214103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 369032392 1250 369031142 369031153
    0xc010c02131b03140c07021e031b0102070f0f03020105212707150c0c031208061212030f1f06050904140412080c1c0614040c0e100201021b 61
    0x240001c0e083c0c5030f013000c512181195070703010406172458150440c4c01555040f501d907640c266400c458200d141070300c25000c941610071175030401a5031020381e40d0801c0000b070980071191583d6550b00019521a0381d401041c4920304030301d104200550042c005019038103411001d21049485000d000899580116800300c00410000240c0c81400c0e94200c0000e6000e8008028005860522407800190544803c0d5281080092550303101400814501e01d8003444d840075166520750b2200034024200b200c265150741c891010b03115800c03061040000c241c03c0702000c0e42035803801c5580d0300286402240c0010420422000000d03508009001c0b0300389178001034143d03510b03025102c5084c1828002110b4289541900c00e01031034080c03001244085580420380c20302441c5c00c54150303035201c0d41c2e40d03d1400741c1c1e1000500c200d804403028041142907000801510b080b480b10122503200c050810041d101d5041c5014041799a4654000007800e003900c00071200381e150b0001500d00400c8a8982040031502c070782229854206 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 369033642 1250 369032392 369032441
    0x7090903051201061d1e0402030406050f070203040f05100c05010221010803041d040303142517041704081b030706030b01201516031d0c010c0213 64
    0x804032050240181c1c0c41c0c805d031000100402ea002200b103030503c2e14411102d18000080c04003000200b08003029003e407040d512801c0c10318005001d42426501c0104c0c0c440040d0020b03101610001c15581155005680c40300303158980810700c0130403101032210804000342c442c0c0c1007020030001d00040500c2424000b203001703805400d100c00c0f10100f4040c0c010521030381041004100e07282d40740c940b103e20115080b00304015600c81e8942640200800000d601440740740b0020000414800403141c0b01d96111011042c0484aa448044840b030940307034551000c50810002080c040343c40070900c0c0d41105c41d100440c52405485615140c540301d001110790240040200f4000313624102070161100404481c01d043c404884103400184c00d105082d5032444d900100103058950454041100c41c04112041007240e4060804410402486000b040c4600119041c03900b18100880425500903201c00312034041c02c000d1098a00454940b0803142040c0c1e4002d1040c2e8114002c42114800e4490f40116410500c088084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 369034892 1250 369033642 369033667
    0x218010f03020408030f2508071515060804020111030412020a090c020312100504020d0506030d09270f02040b0c06010602010209090a1d12030709080304030210050a020709090305 78
    0x200d40004008142c0107101c01c0042040000650303000c0003107020400d460344690700382200b401d003400609400010b412854030040c09580d800401d8910b00411035035405c1140602e400041d1381d054901038030700408982c000c1101620803165140c020784140b404c0d50305000d0070a00145142c12a400803205682c1150540b011803511401100c000c2c88020342c04d2245034003074030f0041d440740030303158020f0260b8200d240055a407222401182c1c01815006008544845408001500918040b140d1500034402c4c481d1070300300c1500460502e4210b0751440038400d80303208c0605125000041004080140d40d885069424040c007481c005000548000c81c1c421b07865040c4058041e241120607400706041da441080301070559110074031010341c8030301c08080c041940d61002c4600d0380e1107502d0510325101e902429004451182245000358004c013510343c0d5045001d178448000315200c0c400c6104c000d50003050b058901c4681c0c2d014501a0240c0046030042d02d81c01903440f007000c4243c0d03015020440010740001801d1320001c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 369036142 1250 369034892 369034907
    0x2120f06030705030f07090e1606030221040510020f04090501030f1b080d05070f0501051f05060a05370906020d03050118470f010801030605060a0504021801 69
    0x3d084008064003000540a44d4030b505480c0203041c41580c58400750051a403040240a1120600c000410400380c4c0d5000000e009412041880760944a9441450758012441c510103000c4d80d0807001802076201e08400e81e100943c03217030920303620886003400001595401481541c0c029409120140d603041d11600c2c106c2c00b03005140600040080d0b4001090020010026408245003090300b001643c4001c0d50510315183c40800000034000c0d800d060800c204a200d5200186506102c101c14451468594040118078040c0c0103280b03001900500406a10501e00d5010300c42c4511915688100d41d40350342c3c07000c5010000c291800d00441e1a01d401080b5060341080b41d0036244400d4135082081e541002407403003400e41c020401c903c40036103612503000c4860303602894054994450f021843d40d412000c074115a0303801388449203c09a600580800c01c1c43c208503101020740b180c142d683d001c56130300f981d88550003884098801070704015400000b0555441da031008064801d86400c5030030240a01100062016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 369037392 1250 369036142 369036149
    0x40c0807020d0507031701080c0301150b0d02070c1703070b1b0f22150806040204050a031506030213090212070503030a0f1404060c03080c04120308040602120f060307 73
    0x188810405800d074003182c10303594980c1518156544401d20706049460304d044c0085000080040d60000546040018a2074080c1c4002e400074031181c0754601c2c030f030402003c8902c00c0000d1301c03900f0800390071042d800364024900a4401d04a10309455200c0c0000b0008803040ba03a41c6000e0740c00003a40c1028402402d080340c1e4090304041911a007280c1000030255203004804408000c0c440120b100c40808140c00c2c080480c0c101d049a8021840f07641d01c9503412800368034503201c004103803450042290307801d040c001c5800b07540e400b030844d03900c551850340c2e286600c031101240c0b1482e0b9a640e440200040c0c1c0c581c003210348000503a11010034042030034010081072030801000390140354072240041000c1d4a020042e25486050390030108142c0c0c0c90100180d81c0d90601d003001d944100070004000c03808075044090130254600944e03c8050558460740102805d00c00c0c1d01415100c0354006100c0030000f03100b10380d140c0e0b00500c551030241c00e007100700340b0804295030160f034191580200f40d02040118181008840c00070b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 369038642 1250 369037392 369037397
    0x15030b1003030210020705011b0206010f0f0e06150d090c0518090c011b020303030f040506101217090d15110a05031501110f0607030c0f020c13110406020309040c 71
    0x11441d554000e035407407820262100c070f400e40101e8003a09116080d80030300c04443c0134070a48107920600c00002903c1c2c031024010065030300d502d8040846c04400004da928240e60700900c0c01074441e1690400c11030001c840251441c90004208035561418201d03008806100344603810304010381c0e041408102c44541d5820010140062031030810468200c00a0b015003101d5080c04c00703852101741807036542c4140b0460b0070003070b401d44000018400725219808a481c45180103c0035181703580c55400032070000510314400e18084401c00341c4020040b4002405828944480382c01d4249800e0f01b007808a04150f0b0324250940c3c0d450010001070041c0c03105802413000352601407030010703c1c040c2c9c030800103441400017401014035401e0038699101c0d940d003d20348040c1403804500480d041c0141d02510380b550781c0012241000003904180c0b162001c6409141d8501417180290094180480242c05201c1349000c0c2100000349162a0340a14800180d9400207102510159010716a5124100b0501c0141c0c5c0011b10544c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 369039892 1250 369038642 369038671
    0x13110406030c020c012f070b0a021b12070b0f0405090408070506061504090e07051909180b07120902040e030a0306050906090f04052a0f1e01030209030a0615030b 71
    0x50b0502c980c0c00380da100e410381b0760f1221400000d61400034900705d0150400c450041000403105400c80d000241510f51a084980c41d5100441d00800d0025111541c0c0030840b0680c0622000d001c0701c030100c4080c29449004860844c14213035504002000f804041c1e50655011500064031810f000d030a000c0740d40c0c4014140c03503413541c0c0310030345402502070300c06ca100b000c51480e80d43e1b401002211003800f280c802401c0007000c0c3c0a41d0031a516264032a4152031003000d490270302d050420303100000f482c2045068245c00c0398a03008159101c90094800302c17801c144041c0b050755609004401680c2d17500c1180c1020002400850b00c4003401c00010301151a59003096120b09840400c0200a80e10140303c1c41c0c3c004020071094129454901e011840d108416240030070b124604000c100b00c26000c0b914640c0501e2045401c820740404030018002912524849162408200c3c00700f015154000c1e0020105c540e8080c04681008030540c40310003c03104064080c810b1800b42090070030074803000042e101e4101111109111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 369041142 1250 369039892 369039917
    0x41e0614190b0a0b0a0507120e030f061504091e050303070e0a0b0702010509190b0706061401081b0904020c0304090501081605010c06060e0f06130e060613110406030c020c01 76
    0xf1011400352003094161840042c12003030b82c0f0300c07031800e40754039581c88507899580f010390760009040d20340c18001090007807242003d80b07011403500043e2070b4000c43d4002e1081c0018844141440045e040c01ca9050741c407084078000030540c4000d1402a41d00c268041e20142d500c074140000006c00791f1065130507841c4184070146081c0314102c01e440440d0382a80d0f090074090307a1442c02d07102051424007400c0a1030f10040701d02100080d0183c1000007090158800c6008021113900c401840622003440d44049002840c15030000c4d201d1403210011044641802c0d40c42070920002d5000942681c1c0134958855954101050810010513070303005141c00740000c88090f2804510301c900140d402822841504e04003e29083d444060020b1944583d01810910340d080f0f0151410b94407114200c0b00c03d5801c030340552160300c04480f6691070361051180c000d5007140034100c3d81d06d0b20020800064680041d042c11030f0f80d10a42e000c2042c41d803c1c002c00003000c19441c0414140e8200c2d1019040003000d41d00141400404000c09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 369042392 1250 369041142 369041149
    0x1c02070303050909071e27141207180f0b03071802090613270e030403020121180b0a02030c0a0c0f0b010f0515070b041e0614190b 57
    0x1105140300c203980982c1303c0d0b6078400b4119020000c2405106140480407001e01d01542c0c001c012612010b004043c640e00160703400c090f801400501d02c07914048480c0455030f0049440d1600f1481c0144140108588150703448413010760b0311048801100c0e250701c0d520056a4017685050151501e091b5046002c1d1a500b07240402c04804c40e01e0a1410000c00c0e9030020b1240d0043c2e503458190b40340c030359040e035035030490b65120201701c4488031300c11603072042c0104503068400c44502c041c0201c61142140c80040c5051525540c015a64022144640b1600241c03004119510004a2041824a40740316921034060034040c281140c6500000e00b42c1914140108200700b02941e0302c5044030415200e41c0340c051507800e03071400e00680301c0e031112000800001c0c864000140085a1074400400e441c0708442c506241d07400750070401058403640000400070002c16001402041c40e1000a54001c54162075074610310100c1d83e0740c2c1c0d00f11480400b005035a49018401d201c00188400b48000c0043e107105000c100a6a03500e000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 369043642 1250 369042392 369042397
    0x5010506060c06060603070315180b0f0102100e0109140c10020102030c0304021507020a091d0a15020f0f0a050a0e010e0d110d17030702010b0d030512180a051c0207030305 75
    0xc5001d10000000700c0c44080c4689c1c08202ca050b095030448030307801c0d191901035005004a001e5071040f5030401c0c0301c1a5503850117a403014582e00058008181006d1701e0a086400741500e4001005195038441a05000c541114000000c2c00ca40c80003078900340847e1400c028609484c05400411a80b040c001c001100c1544803c590b08141c04854680e8500b0003014008404d2040d428025048010749100140a00d05500000c544000d030008038441d0310f5521440c0c60751540034640141040d0320000070340d103500340d4a80c014020000c0c1c0e402c0782c0d07103007000c0764403000200e80c810041340001540c00510703249026400207100d50080340c2413802e5150007140344005009041c1890010305039071204a07094503540e440c0c80c400024280d1141c11135003002410441c240d90380d04110740300000345d420980769944034981281c0903807145605481346802c4c0703911018003003035090008281050150840310990111081000803004240c0300310000d010401040f00c10310f11501c4400c040d407055601c68402807001a410009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 369044892 1250 369043642 369043651
    0x6141204020d0821010605090102070911040b16110402030108031e0c07060903170403050d05161509020a140a1404090614011d0106050a030b010c020907090305010506060c06 76
    0x54004854640740006412120600c034014000c2c4070000782c6903844007201140080107070004c40320f54401e07a0398145c15240c03481204803036801a041440140300e481a07951200d5000d218199005081540302e0440a000da4031282450341c4417082c030301230041000501c195607641001d06650a505552510b09030b10b81c0c900a603120740d00c441c81d506140350540b10010050381c40003034102e030840c2c04ca40d030f40e0200030701070801c140402c0d1200c54008215200034a5200d0449088030360102c002c1c00d411408400494035a081440b0000b6400c0c5100c0280380031444d1403c010401001107400041e28101c1e80c0704025030300240d0b81c007162409200031030013040e6640e0604020103c3d0258044002142c00f1040000c000f44209030004100c07502c0d03c01642110a03006558505940b09030800107010f0003400e106c0320b100340e030034411100003e60030405008014465042054020b1041c140f501c040401d80e4001841c00030202c4001001850321031040051107400d0262541045080d2001032074a85089041912000000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 369046142 1250 369044892 369044917
    0x4170d09050609150d020a0e0603130f1e030509040b0a030803010b0d0605130603200a03150e100b030709110306010309080c010501030818011e08071205011e0614 71
    0x30f80b44920b45030400118191140c400304141d90300010415400207400101c22100090600c2000c2c10a03400d0440c1264000c040d60070341c03624559810366600e415144e01002c02c45000b1840c9240224a540110b032511100c0e1080c0c4500b501da2040e4070501040755951118540300d40c406c14402c102140c0130b03104503810745c1e40701500e0640c1d4800314035611016100301c0e803126412089190307541810000950040d425a442406801c1e07034640d40d01030700d50307441c0c3c104a411544440c90801c1007002500b00100700b11040309204004c98071501003141ca40c20400300b03a400e00b039501d0b10b83c040100646024405038000d483e49001c20000701c070140700710700e0b4503010003403849060503034410301c5109100400c42650307000c540c030740300a004540e101d29001c10141c02c00720801d04845108086d20f202ca60080240c03981945a0b0342c2a400142a810400c541a21000d04880d003486a030801458101406000ba903028003100d41c0050001300e1108c65080e92030455505c048200003200300300302c1c040f403030b030000f2101382485a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 369047392 1250 369046142 369046147
    0x3090306050a060b2706030c1801111006060e0312040e0603030405030a050d031b0e10030605100c1b060c030e03150403080a05010b0c0c0d061b0504170d090506 70
    0xb03400926598000150340c5074040303001001ca182d4101c22241621000014100b00ca2400003401442c1c00255100a24007a0501015030005071031000e4441201c0f0501d00301611042000215080c052440444001562508010300072640c0000f94200102010780050410490700e101e1a135a6000f180100c2294030068008244281d82c104140c070060580241a64083c140c02d1814540d41d40d040103171400882d04010380b0680140d044c1c00071400503065519410112040981001443c1c01821240d00a1550b02d0030042099160351450060441c000d49540c04031614a050640c3e0041d0a0b00d40050000c160340c8007480010303407080c2c1c0300c995580e1605000780c450303582c48002030421704403d0401036003030b841c00c0811052580c800e01072401750103600c4040040303903203030700b40070200e81724004001c0e50316840030170203160b0303824a0270340a010207000d940b00042003420b444071000034040600844c400510302250134000030505142581800c580c3c00700030516041151409462202140729683c4544d001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 369048642 1250 369047392 369047401
    0xa0501110304090203100e01060f1707120606020c090c03040203070b030406020403080313140a0206090121021204140a050d030504050c04051f060305130807080706050a0f0b010c0309030605 83
    0x20415207003d8419490b0544d101e260001550a022081c4d11412904040c1d180001072010b00646411103c02c0040d1f440202840340003d040289400261800d0100880b0001070052520f50f88034440142820303034042c2c0640103100c003c109008001500001e403000c010000d12006035000140203046030750200095880c0d80c4d86092200007030141d680041c0900d1070010420502c158800507404140f441100ca05280b15804d4003038a40d00c0b44000c0000303410081c20080d00000c0d60080c44030036140c80c40d209480070000003082c6050107036088410490281b081040500040060310744a88103a40c4202006181019854503117a50700c2003004004010305941d000810103209090102000100d8054024803203070500720040b00010080c42c01c1c0b05d807000405500420818401e015490003404042c10208111030320340c44011040d40542c4080b50480820004580040c030b06008081c441c00f07400c400003075021100064101074540d4609000c2c10890071031101000a078101a01c0019690400300000346c40d900c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 369049892 1250 369048642 369048677
    0xd0e030a050d030510080604030f050d180c050a05180a1104170a03020f0d1d04060e0f091209010503190e101a0118090e01060506072f0a0501 62
    0xc58100c0a4441d02945161490300341d0103400c0903001e04c003201001c43c603140e96007a040b900e850054400500269202c601484200d10a4001c2c003800e14030600001102da00c54041c3ca842c0592080045504440001c000c004500d010380c0c07400c0003081c094401852030688172034812040c400013131030b1211840c0d88031000c40b00c807445041680d01400e81e030307070f00c1861891000124581d40c020310074085006208030840c01c14044000703e003441a16050341c0302c400c6011091103030900c840c3c02030650990080e603108000a80c00e0b140c0340141e40120044040790078076040c0008421706106a0007204010316034208881300150341c0c00000c40b98088040d110301c0100003481d01d0382d00c014020400d50ba600c0c074440c0c0540ea41c0d1100d0b15034800c9104c170906400c2d14150a04560056442c01c200343e10070310350b400c07031024204482100c5810003805903000c1000003d0240d1a9000101a6040a50251042c0d0a00201040c0d4101c2c041800c02c80c2c180c544c000155459002c80c00920464954001c15042040c1d41810b80d04003030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 369051142 1250 369049892 369049903
    0x5360d0506190609050f180c010903170d050c040906061d010815130209010201050a151e240f0201051504090c050d030f02070b16060c11010c05041401050c0d0e03 71
    0x110141081c03002d4100340c5d0001c0c41d0b03c0c00a654001203661007c032880f4100c0000584005400c0068407035001c910700c1c40d143c8908103920a1160a40d5800c01c0261290b9901c0030f2107007a10540c003001c8035607200c038285000c080c2260819044801400f420348401c1030390313420300e050015072200c09180084580d44c07940000003451200e11000c42c0c010030391201041503034450741c001e0229050203900030001580c42105100a03642c200100340c45013440360b43d00b0f120b07003c01d1190308440c5039003850401996603a20826484035403d0391058014041c1c907d4420020607600800880c88100644001c0c080380c18030551402c000008281028403807a5a00200020800030103041300c000c0100411041d00311a1070b01b00074051070003090310303907006000c0d41201041c41c044960640d5440d80c44107201041d44c048542d545001081c01403022410300c02c070040030b4070142c4401d0190380c0b100c0d8083c0d0790b55a2034a00d0074400e01011002e40300b210781403107801d000d90740000d0000100070071034840344e02d070122684900d040441d0a08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 369052392 1250 369051142 369051149
    0x1302040216060f11030f04030c1b0e1b0c0606060a0c0b0c1815030a0b1f0f02070f0b19050403170309060601050304050d080705360d05061906 62
    0x101c0d004941c00c103201e1103600849000380001402d000c0000030301580c031128030013150f40c0900140b0050200307010a21912134440d200344200701854880b801e0b03020500b034401a40e8045503840c06050104204500c0413181340f12902003280d01541008900c2404a8a03003030002e000070300807440403800c804558400d9944030384c107a80061090080e81000da4038403400342e02c001d0007034170ba1300c041030228012402c00799001454000c041c800ca034150307100c0da4175520251400005955200fa2040f6603256842c4843c0e60100000d074840d00c8045c0308610107070000e42480078580c009010640480001c1089582031b00880718070001d1040c0e01980b4143e0403000759610b000c0e80d0400f1344035038481076407103030800803a4000318001c110700f05c100e41031940c9100c01101d5520040342e00810319048501c0032400c29002d0903055401444c142080781c00c10205036140903a0307490991031f00c40c2642280c0284010b0344a440d00d0030032191130940b10341e03881c03450581f1080e65601d005098102004282520303800300030f21650154001d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 369053642 1250 369052392 369052417
    0x130902011d31060605030601080109020721030e100c090306091e0c17070308041214010e01020a17010303051c09020d1212061a0c030f0a03060303110f0613020402 71
    0x2454000e090b10303190219920503001880386844000b08a0602400540c0c4c45254140d50300701541e8200030400004c2e4009200443c3c415011514821000152110030200307400c80d07940004605407000042031030300540300c0142042901e0710b5000d50100b940869002c0585e500a000031401401d685419000041d030b50000740ea00c0074a099000042042c6a00c981c004c43e640103003000000303d4036461041d2210604d20000382030801c204030401810031130100300c42d5a24000c55014280e03c1c401e6001d5804e442c440100c80707d0f02d07580004c0c86d03201240c118081c11a03007a540a14816150f0642d50068400d1094030f010000b9810001c003000d48800702600481c107040e60240070080b00040e146482d030325250031681541c0128065000c0429985160300c511001c80e901180c40e4100101c40a5800c6140d40c4042c4454416000c100207656000c5800001843e1800255400241355895400d0041000b5001c3c1a0740b401600700750380002d41761900082494110141c40040c070f10040030340c40054000c4c86022445c1c401c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 369054892 1250 369053642 369053689
    0x7050306041b080106051c0f15151406070f290411121011091504050102012307030507170a0c0e01020a0f061109061602130902011d 58
    0x20440305400003982c0c2c403200030001480390740302d21500382a640749002e0141c00000101544130400700310404544a90700400700c2d4640080c49440c1e040ca507400d410300503c01c00351034a1007034140c610110241001090002400700c61410300398006031b911b2290502c081e0061801c0c030403d0b01801080441506410a010386014401c8050b4500b00f040caa0100c50586400b1a16064a004c1d803c01c4c0d41c1243ca200d02000c058840300341401194001007001c02c0142454610038020440103459010b800c07120400c41d00e0301c5035240c5240800082c02c0d034040c200694100400e41d600c0c1040110310030070b10b0780c100d80035080106440d039030204103c0d035030712501c00800c100c0200e403002d20000003141d13400311010580561320703e18840e11a800582e40e4044000c80188800c03002981c04010441990014040e0752207a90035602d01080c80d0002089500041440308610220030000821840c0121b2000301290920320180804150f68001801c2d94407888030750361100380c0202c0c6030a1513690398480c00314a4803a1802c0c040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 369056142 1250 369054892 369054901
    0x3040f030f050606011706040504050102040503030f18012a020102010f0203070f020622080c01060302032a041104230406090606020c03030c0d0c05010e1c230f0c07050306 75
    0x248691160503007950b0070f01820000c1071341c40d44580040c04401981184101e85520b4520a0000400c4010405d071210b5609010110381035400380300420007900c24030050340d00c8800c0013080c2039514a41c0c003c514180040c492500c900781901c0ca020540c1d000240c40842858411400103078003404801801c40c010b64400000c0010141d0800c059101501c55582101c00b20354450650240700344018010410a050710300700d10380001e0300400200605000da400108120743d0b02c0c0d021078031705200c01d1141c065032181c0c1d00d0000340c0c00300d43c2c2544001040040301c06100c82e0030405500c00c0c0d10302c501c3c0611401e1806926001c001c440c0c0100c40c6041481014000b00143c6070780c0c811940042003140603050050081d100303103560500e0004144c0c0c01104212001e0440300d4943d0304152018002c503003003207529548588102900000501c41e0040d103034611050000802e580d100006c1401c2e401c49140ca51b4950002c2d007040c031416040007916100309800c1c1056a8801c90540d5492401200303601880d07040c8251000c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 369057392 1250 369056142 369056153
    0x6050a061806060509120c120d080907060e0904021c120318021819091a06100f140c101407050a0c02090604090605070306050f01090b070206030903040f03 68
    0x150458045a515900300c010408464050310030601c203c00020b1000d008a000e5481c080891044480c0b0240846000d100c3c00404030f0361114080c01c0e1f0041d2038003d80c0f03452042076001103038298000594805001003a040c82c42c05002c003504228418052400308001600715111000702c401d140c0104041f280b1203c03007603d02401e07003d5440464030002410444044104400c0700f0310301103885c0d03000317041d80804204c40300d8407078021070b004004646803240d0480000342060140b0034410442c2c042c1a02d0072001c04034051442e00d000c000b030f1149000f941c1c2400ca620b0361a03030102880e4003e010521300082e00d8180740843c00d0841c0035040351370b1060f00070340c4271800d000541e66104070f21040c0208002d00c510b40d00c3e00406e84071405141c22700da02040a100ba034200514215100540c4000c0050000403208140d4542104480d812543c240100380d4075541840a4039110742107170040c01007442c0c50a102e600300781c180c3c4554014031900a00590020020805d980d0090090341c0140511035510f008859503404c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 369058642 1250 369057392 369057401
    0x312041121071203050904020307091208041401080f0a1e060b03010f06030504020307140d0b0f04020f04021e091c05150f06060a0e1819050901020a1407060906050a 72
    0x464502c6074010016441240c0074242400d5034041d225035051405d4031061001070b40c0020003038020405020303c00b040640d079041400b244a0300032041580c0750b909102c2c011040156040113181481182000c0121101482c811554442c01200c00030481c41c00d5040300c2e10201d844541060712003070800d2130106070050f4000155040740c058012040700785965002c10390441e07400340c502a425801100f014001b021120416806241e030140115603111075544842104040039184480c4040f42c000c1031005620309a0825540c40c0400c803411890714152110084010b14804852001400c0c0803549111642d500902c0d8264110304419421281c0f4445c5002c0b625070484a81e03509440e41c81002041305100036415851050002030005803916030741440c107540c101c0070503d040358003646000a40310700d14511014603001d88800c141c8035905064041c08a401e54000900d1a1003603031050180741e8072a40d003e0100166444d80c0c44a841e9111101d00f0004c020300800200038060706d00380b40500c03455070001d521 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 369059892 1250 369058642 369058699
    0x1e030207050d080a08070207030605010b0a08090d021c0908010204061817030702150904090302060702010e0a050c09180f0604060c021902040513020d060203042303120411 75
    0x29aa034403074640d000c12501c00084100504040414428040c5090103041c80c19000f014030700449000907a41d076141410703104242c100b0682c000020030802001600903903403079000380c1c3c80070280080c041c000e24020340d0b507083c0c100383c001014903151782e8050243c0100c1310100a850000c00943d5640d4941c040070f0070310b00185c003c51059103410500002c4011012044800d11a213050155152071540d07001c010003c410102e190200c03840401c00d520941d60340e80301d07851a562003a0041d213420710300000003078216603030701c6041945c1d90002d40400300001d0011556451712501210000a151078035041b03c8024080e0301e40968091080240010900d4000074600344210310a840c00e11011003800c1080343c07908051040010344002c48000b01005141c00d0b005154014045003000c1032841064000690414154000b9100e89a0010502043c0300100020004000f80f0000b5894251859235070035941c0c1c820010000584441e00000c00c0411000f0320980000d844014403a00c003420000040c1e2903800e01194 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 369061142 1250 369059892 369059897
    0x10e0c01020a031e0909140417210403030225020f0a0311090615040306060f05190608072309100207120f050726010b010e090c070606031e03 62
    0x24144899601c00a03160b40e0389a8550340f82c5011918502075154140b10307a1503c1e100344040360304003250348011442030f002203200c000090341c1c00381804e0511490785030404a004406c40401c00c004e07205844aa21910390800906944441c26503036410100c009009042510b4259003002d102d0407905101e41500084070f60003122880d032080003030070030402c601c0518800240660311212510040345007402d4042c2d4445400b42c01c242c1d2501d015011a081e6611682046458035500d00061000c080400000401741c102a113528801d00c03030010f414240300b0802d00c82e0400f008004000100514458000e01d00ba001c0c210003a00c0446011520703152481d0421102d46014025a001c185042880010f00c00111054030701e0000c240395441d140c01107011990042941c10388906c3c000061001e110b8000c88040c16400c2c01d0044c403085541c0c0d0b4007801c5d54800ca504504003c0310008494080e0f94134800f80d504800800102e40d5501080d1801c1030107040280d10141401600103044200d0840d5491418509813090b03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 369062392 1250 369061142 369061153
    0x6090a0b04030f0515040b06040507020c060a05040e060a0614070c050307260109031b081210081006080613140a06050a0b01020f0304050603071b0303060512010507140f1605010e 78
    0x1000d817180004007124058400c03031009000c502507050a0b80480c0d0071a60134410389a21410b5080440d004d030717100c6a0000300054000a08100200c0da500c2450340260080b91403000d542c0c64544000d02480c1e6000c07807550340100000c2c88a080003400c58880008142c05006d0b121090b90302e08000e2145402c10002300038480f1300300c50482040c103061048000c400d030303d502c820701c140000390481c07160584110012203e0b6641081101c0321070030340c120164440d400402d110b403007050034400454103210308100180400c07410010203200d1940701190490780300d003018116803800051f908120041c4603d15075140c20780d002d1801c56605000c042c2e007101e8860641517406009034107813540126698a01c034116020540c1007444280302911707002c0015034002c1120302d00100c440d403c1c501c0100c0511003082e020ac02090b40c0d41d9040000d42070654180305911103050007088280781c044030160800c1d20550718081030440000e80c001080d0f5011040d5042c100d4044110f10810809180250003000c90605001700c900c03d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 369063642 1250 369062392 369062413
    0x2d03030912170408090301090f060b3d090b07110108060d0f0b06010302040819050618060a090501060b0409060503011406011707031e14070302040f0506090a0b04030f05 74
    0x55030a07018141c00400000307499a81c3ea11100c026800c820606a810b54940c00048049010142c1c2c141c007d60140200080c080c002c9410030491406070034401b00c521403e841940441008112211803080b02480700146001d02d021044500146a4008c91120768010660006105c0c0da003900040000003030701e90829071345403041080350301142c500c0d00810601ca8a003002000590004140d50004810304000d8249503d624629050a40c00c0c0c1b20380c01c032a01c591314004148903081002a401490980c00034041000402c202925000300a00ca110340c161607010210802c8025400180284070104c0304075103403526950841c0c00340016200da0f038481d60034101c4411b401110b1501050050005031501e68590f188540c0050807002c00410100516a56103010b600600007192038802c81002c015002540c9102e03100c003041e800c2c8000d025201003500c107020503c000f052621041c801d4400c2101e2081d290140354000032404e200d190005c440d0150040b82c004100840138200c450392510650070740f80b03200c92 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 369064748 1106 369063642 369063647
    0x20901060c151b08041406070c1a0606040521010207080912061501121107030203090102101a120c03010c05031005030a050a2d03030912 60
    0x221000000c0c00c100060548801c45000b6000800c5109018421014141c1c200c3e0448018041c03068041030034440000203443c207003815078044540d1b40c90000c1000305080c805c0101100c408417140081502018000c00a074420030018000505041c40d140800015803001003104d510340046500a03003141c41c00b80010b03c8881d0089084c00d40d41c07003412040c00786002c0d10580b480608e4000c2800c0c0018a060420009082c05003446e207002c60301540c2da88140200340d181d00e003024507480094503008154010019004040c002d800350b90030403045441c00829510f03d040310b400c6554100003044024039280a4074104550803004881a000e12180400e085a40c10503520000c00c0000c4100700f24034001004070005400c003076002e041c00c4145035642d1a030701d0100800c020302c0304180c2c208100e00c07901286400d80900103804a01091880d081c10064020040c07810f094810b0700f03600d03011002250 = true := by decide +kernel

theorem cover : BRFrame.Cov 368884892 369064748 := by
  have h0 := BRFrame.cov_init 368884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 368884892 ≤ n) (h2 : n < 369064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
