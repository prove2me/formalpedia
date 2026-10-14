-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1190
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:40:24.588993+00:00
-- url     : https://prove2.me/submissions/b3e7da7d-5d1b-4d30-a6fb-6831f8f72739

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 213848920 ≤ n < 214028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 213850170 1250 213848920 213848923
    0x9110c03041806050d150c090503060c09100f051206011407030c0308060303120c131806080c060705030a030903020313030f0c0807060f0309030903021c02090f09070b07111002 77
    0x4080000400929045020821745800c822031411a0782000e10384410340070800b02d6500900700c000910301400485200011540c80a00416100314a840ca501d503d0b03401c1d8030140012403803514928010800203090744a41982c000058503a01c28404d0404035841c0d13035260042e10f81821000d40c401e000c0c00302044240400d544050038010307482c8241d0302ca441035250b0800745552401401e0000c0121000803002500c600c1c42c4402070600e41d0381e08040310094507902c01d0b0b049040c80810100d451080d8450b0814000c0403410083d65064103000d6521501e020103a4540715141d0013a96481d4041607111180790302454403c0040d140340b130a5040c0b01514950340c038601100c08182c1858203c0d10f06030b0016000030350742800310b030702c0f02100d18035140e0700c90034040b04900f03e0040c0310f8080c084040c00740740d035804005030b200c1c83c00f42040c80d11610401200795605c1d0040100c0c5500c02895845814403140820000180214040303046a6440c00801d03103500b15850001e00900010044603005501d088034154080e50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 213851420 1250 213850170 213850199
    0x315030106050f010c02040527030310050307050f0409020d02061b010f050708070f09090606050c010513080904090c12030503010314010b0919020d05010b0c0d020f060109110c0304 79
    0x40450081100c180e0741e50600a2026a44030740601060004441c003026042a80000e41c6c403079002101c0070300001c480e41111000c1552803038090b40d10b40c00030041110119490312800040d01e411001040d0503440c2500040401c91121855405180c8510074030045486142101d01455030050034207842e69001100c0d047d410400341c042c0c211540c01c120000502000380d2040320701a4072075a80e4040d040c1c0e900042541e05140c102c10351420003d02c42c030009001802c40c82240041c1029950b00381c0d0381c01c40011110b0075a400905131032880c0000364406000200354008942e004001502c1c04101c0b224141400c07212078800351701a40080b903a80c01c04c4030405500500a6050303900c2001c02c494802402c0c45014200c525603400f5070380104109022807400b13244990100041603456a02600c0d003014800b4002c10344000380c0c012007030901c01103003443c2003d00034484200c0003916403004042042d6103210701036907440b0600c124080c20395581821910f006600e400c032501c480d0605d040320b98455881c01ea41207641c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 213852670 1250 213851420 213851461
    0xc060702011a311a1507021507050303190b011803030e0a030203030d05160503100302060304080c19210207090f0b03060906010302040b18070e040b18061f091401090b03 74
    0x550340c1caa03004651400c40703404141c101da1319645d103050102a83c00d01050403031411003068450f905100240000303404000a62150b50040c683c0b08404040420340d0b015101146203542c184503601c010400c40728550354a07182100c0c1c051a01d0700c1d005503694081950b184c082d80010350113010010301100c211046030440340c0683d00c060001c5615400c4110221441c0c08282e5140d080044407001c01c0002d40380a1001c0d40c0c010303000303a01c0d25103425443c200b1589030042540c0510702d0300340d03081604814410a40712000c6c508041c2c005c010104c1e100d44400175100c09181c00380703000455803540362304201166a4010300040d04085c00319042401c00b00074855903440d003440201c0c0303e207090076000d0b542810200b004c4003042c2c0740003079108500e4070b490743c6c16038202e102c1c0040c85810a070f44200048588d13444418203600031440c110346070302c2c500b00b08060101000e0301d00c000e150300d103250022050030380f82c1c850103003001c9442c03045102106405030001250202410b40c003440c44600301100340b100e1040c0072000c600210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 213853920 1250 213852670 213852701
    0x61527160806060a050309150405061005011d010305042612150d0b06011101050c09120309010804020d0309180605040c08040b060d060905010c02030c060702011a31 72
    0x218840441101e03044001c46155420400a1044540f041d005802a5070400490010b6440c04a00f1440c821456074040310282d42c150300090074002a0300071240c0c080060202868416403c458003420303080d442d5000140b044c1010740e81c0c030014040c0504614000c0b8049000307e80445001941c05214078180c000e183d0005810301c80314082900c01090400070f071900c540c00303404000480c10320703190481080700c010203050600c0700c0c68207440c48a100030b100e0369200ea0600c081e1103444000900520030341c0c014101c06100194000c04c40705429070303001400d4507486030341107495483c4410b541c5800c95804089903c031545203503e000c03c00207056400e401c00b40c292141a01c007080360350000750080b00e44c0c0100341c501421003104c070008104c0314240242400c802c2c40c0100ca0114040040d51b481e2400c5071034800302000141c0000c41c92035034080c0305014954212600c1e1000b8020101000c504942e00c0c0030030545248502c240205400000f20360700c0c2d20040603000c00741180c094130390400460300075244014000004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 213855170 1250 213853920 213853951
    0x30f070c062703060f02310e060a171014061c0309181e060e01120b010506070f0f03020703020102060c0406020618070f09020c0705040e061527 63
    0x301c102c20040b88501500c520011941140b81d41c0f0741c0f1008190901469010355000c00c4618180c030760484207642070100c405030040300000418603016004285400c081c0c41100c107441030001d25a00e14403035206072100009140c16490300d4050842c03800703101741405001d650401c070010b4100828204440d10507070040d2811340000e4840f029207002003410003402004181c99030700500080307841c880301007809149035000007110601c0c160b0030050309410403500c4041e55240c02090007a10400e4007120300500d9030220342d0000303607195a01c03001c40210502032640074420100c0c4034000c0c000c503c0b1261401d40d420144640c1c40c0d10f070a041c000e4a640300380c082a8054030401011030b04509014046400b02c8000383d014003071075180e0001a02002d0407010030b0f0406171048610101c0c0368601c1404050040c145c40c0d0006a841aa4804450600c842c81e88924480c81c54116410a1002d010540b994448501060510050007070000111040c0000941d240c00317541081600d9140010b1080d0540108800b641f101c64 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 213856420 1250 213855170 213855197
    0x30212030718270e0a1403160b06040e030a05030a0b06070204060e07030b0901050102210c010c0507060b0604050607020906030f060705070203060a0e0319050f0a090302010f020c010e12030f070c06 86
    0x15140084101c01095200d0030f041e2000c50110006e1320121001e078001d90303103810f08070701541003a03960b4a6015920701d4250424801a40350501c140046d6000d900003460802a141c4030291190000403c0b4800c048c0d01c6d9207400305607039a66011a01002d6004004001094070b4a4841400d07150858901000c41d260a1411080d40781c0b2210260480d80c0507401007400b090905c001030150004001c10b071403006020b0142d10101c6c4004e028102000e100b669a2548894041c18a50155074484203010f0260400300420300091b20341c04c0498801c1c80e0195000c0b2029180c00c40424500041713040444003034000c04081c000c80940c040010714032140203c084a03c0e9440c2d051400c0100ea864040207100d80d4010070804814803404808441c0d140312a00708507040c0390441c0340400313141d400040344000003192201c0a004540c0c11010b03501070161a0310045c42c100901d5400609500f9889000034400c3c20840086504441e0400407640010416261030361200c01500d049000307100c2901958001c1842c46a80d47e9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 213857670 1250 213856420 213856499
    0x603020a0b180d020303030714270a170706110a0b040501061406040b0304121701060e040507110705010e0a18020c0f0a0503071b0b0310080712030212030718 69
    0xf220280c00074051499a115140252681c1d417030103031200c00222003480fa01000d060fa6013070891428625624031041207464500b00a03041302d0f16004000f051400c41e0002c15105030020300403040e0b0380c07641004400145030040844c070b42252104010302c200162800c001c10010190490000c88103620700c00c480708003d090802120b0f00460048085084051002a010482c5812540da500080707007070441c102d501464044055003800d0300204081402c50480300340390b05103071040c6680400b0518083c40180b4103032020584600300351151a0400c50124088030b2140e440260b41ca0086c40d90075400b50038100ba02d039045020750003241e13142d0124010322903034800da0303880401c842182503427000155240c48255501d0348844050504d020030305810442c00440c5001e0311600542c0214868090034403800d281450b0305107001820b40146024001498a450020f600000c01d000760000c0ca00015460341e4402e28100c1d940b079442040e1040000b0b80a0380020382005402c9108402c010803842c58541082c4460b400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 213858920 1250 213857670 213857689
    0x10605090102100203130b0408070b0c030124050c01140115020f06040f080f0a031d0d050405091504110705060a0207030909051504110d05060a0608040b0a0603020a0b18 74
    0x2078090703040f01e100c18604035460f5008580c8200010848458a0705070340b18241d034181c08a4089420000c001041c8003446045044076500c0038000c6040fa2466040103055030000040c0740148001c0c22407220309442450150042d601c050035014000c01c0800102803c0308242d680070f2054641c0900f81950b080f44503440811a2001620854014003898445681c1d10301000d24828041d500154140490180c000c410310050070300c044666004035120f950701c083d000300d15070140343c900103170350091010440d240e400109607000c0700e504030341c68001e0b41c2d2902c004801c1ca07106103800030f0780249820801c054140c45500603085050003641200d840d0b0b42c42c60940003c03442409405004103a0600c4100503042d40e68000b558032007101c401000d030115200d004101941c102003006d01c440724011030300038412070481c0305040d07000c0303011280c03a012145000b80c06440c02e40f0180002c5c1c0014100b9002911004554000c08000c0d5406080442c0c0507540c0c0708101c8180d00b000f02d25280c20811030100b841d56141c0720591 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 213860170 1250 213858920 213858937
    0xb270a030806091005040204180e060403120c0509090108061008030307020307060e0109060c0302250206070308040f0f0b07030c03091109370e0607020a0f0201050c03071109010605 79
    0x180740c5aa12460108000d0440041070402c210210000209050302e550015000412020b4000500e2010a1042c0e4050702c0c400c40a803002d03a40000100004264040c0c0c11090440c4581c80c00980405080400c075914440e8424a41c5c1020314503000045603031000844a220341070740214400d0158030342c0e2015480344416101100145e02c00e008a4001c207507194070006031700c03ea510000680b01030302e0751340d00181c03882d4103400c0c00402e5020030526030041048152060b05c0c10055030840340c907106940050054001c80c0000360810044a000800b00b20450014103443c0750841c03e1244e02076003d04d0710020364002259408002410440b01c80c03040c0d8040c1c00303910709081d03100c1e010f0b902c07422030b0720306201b2203c070020008866001441c0303ca4501c0000801c218030000590941542440c0024030400155121103108c0c0007952701031000c11038202d60200d0322589056000b0303241d81c10403200d8001210f440c02520a0f12400d800001045001c0005806c5000c450342e405403044216a81e80c0c1d07105440d90b00484a6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 213861420 1250 213860170 213860177
    0x140f030106030c09050907060f1b0b090a120f05040918050a050a02010e0109030b13080f1c060501210c1e020c091006020a0813090c1119080715090b270a03 68
    0x118500c46805a840107280b800f0300b003540d2103500d8150b101d840708803004ce601d066030303500000c040f0014404031703d141c0100b440050610320020096404010070b0b9100c0c51240c0c1889542d40d00800c5c5900034465107281401d900002203403014140e44c20983d031500640d0b041240400c3c907506a0070381e19406000244102c07074100c40042565564103c81c3c50440e0403800003100c1c004420800b02150400c0d90000d425542450820300d803010440d05000c8080382c0340350300000d0601640c80f00325594180441c0c450103c9000c500004601c0d4140b025040da603c03012500000503d422509100c0c1d03032541c1c0080c1c0154200303000c031900c071165203401c00c2030701d0200ca460003928016002600d401c03000c0f646400050100c00d0303d0f08015404c040d59045280700300d440130070518001607071200190103c10300410140c05080c90304401000c411945590b00100c0d03106500000701a042e0800e00c0d00c44032203180d81f01c010f800350443d0142200d45000300d003415240c40c840308000f90f40160303038071a44071210002807000083e984c90f44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 213862670 1250 213861420 213861437
    0x2405190303201c020708030f03190f050f1927111801030506071d090402010201020d06030605180102030c0313170a0207050108070315140f030106030c0905090706 71
    0xc4040300c000032041029a08100c0342c000d18803401d03a081001001888555075103249600c0e10910082c10180154845506a8018010380701540c1c0d5400889411000a0400f03009005803054000e004e0710f00102400802441c04007007014640703288224603c5992504140d000c0c070000709131004c2c1140d03c0c054005804200c6400304a842540d5020200032860066982510422000f070029000c04000c10640c5500c0c80b00303000400400c0030401a190b048032841c00c1282c4204003050b1000800746814045ca40306904220120302564003e604881e900f000c0c042c0c1c02e000c0700c1e880c0c0c28200c1c0a0881641c80800c00c42c0012400c81c02000c040c82900c1c026864510f51134510b460f000f0201400e0341003d81c0a40301205484c1c06942c00012500040400204980241810a2520002406855000300440181418903030f12a01c0760302421914410755076055030030001800050046030300000082c076055010b610340f040120070b000d001c044450480b036059905202e66070310700d040705440385164031a034400314500d007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 213863920 1250 213862670 213862673
    0x31403041709060705010e0d020c03071503050a0b0d0c050a0501050a1403090708030c06011511030304060c12020d060905060612070f031e0b0307050402041511030702030124051903 79
    0x401001c0b1500c00400103801c15550b92075441c01c594203201024199440b0701b000c2403a507030301400280c12254084001c2c0c440c9500d810030382e4010b03504004000c02051380e11400038040e51007662002d4044c000181c0b801a0407452031809a80d120401c2c01401d11420362840700059542c41001107404000c041e03954020541d0030341c03002c4107603a04098103c801c3c0307006403200030030090001c1001e0850a02084000d01065140102c9034601d504070004ea82e00b040185070341024401000004c894211317500c90030008000c0d90446086503d0220038516103225030000803028030580160300070700c0c1130380c034821020002600e80c6c404028403841807000c87d06100700740200040455009240340c040010003424003080c031a84509440340101c500f000c0f1014166070311100441070381802c108000c050001903400318502428852503148020081410f08100304c0d402039400d00c83c0c0c2050055448403940034000344106070741c0041e8001c29807281074000d52401c10180d0f0019403460420300c81c66150041d4150002c525013107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 213865170 1250 213863920 213863963
    0x90f060f1503021c1217060301020405060315040b06030a06080c030d0f082d010311090903090f060c06070302030f0c0415050d020702120f0f070806070804050a051903140304 76
    0x320f03800180421581c0c8070328000304103c01031001c0c811006607a02c015a11220784c1d14400e1b582c010f4000d41c002e81c4144424410760321404222074201c90710703048808180400500050182c2000c040858000e1404428000100ba1981080c1c05840d40300c3c069074026910f1505069440001a2080001540d60040001182c0c09000e00582200c04203d074100e401d028a4010010000040706000c2a400020010400d0000256100c0070710350044445c1050340c1030031010340b40d882c003074000c00a10549429450000a985850803180200020001c1e145645007504000c0d000350000c4a105034514a24000509000c0c0e190b03084400391056041341c2c030302d401001903080b07031590416000181c400c1d9007003140001680d2141c0e10360010106d032200a20381020240e0400d0f00b810b070040380060075640302503401c0c0300302c0c14049030543d44170f49203150a50503075a4500b03100c0d1400c8804a0050280d001c0c5560061103800c81c08208032245000f911800100f03041516803000c01c0c441250041e042800c0608005810140e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 213866420 1250 213865170 213865189
    0xe1f1404080406140d050103080409050705031b0a020102041809020405070c0b0f0703061d06010e060403020a030f031b050705030d050403030f0c0204020f040b071e0803010603050910090f060f150302 87
    0x40000c0517400d20b100402c030304044410a8005071a03421000c1410800c58605025095009000e89491400c60070f040e103038601307840000248800750800c003080d0350030041c1c400d60548000304600e40312140381905000304480181040c0d24103900840c1018001384105011b21403805515911080c2c01c089550380d0301c1601c400481c00342281c0e080588400d000240c0f504034000e140070103000c0041341c00c05810b0140c000b4299400b504e04e03541c0286404d200400169948402c404200ca40004c5c03854440307200d44c60200c1e0070440c00343c9940c14000b811040401031002c00203414060701c0d025011103102112a40b025a000c0c040e9200003030006017542030050101c0d1080342138210b046e10150001d82031582904c2581010b4100d41c02401140350302080b804184030185101494400c4031042c030070410111512120b6403440140100b5052503225008120304840030040c118003a541c0000410041086180c0080f81c146070172401d486d1103061840200c1d21240c80d00c01c0d1001c001401802d20751652442e803e010a660 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 213867670 1250 213866420 213866447
    0x1060c030507020f092d010b090f2e03140c031f0803040b0a020c04091e0f02061206011d0a060c050f0303070206011a09010c0f02040e1f1404080406 65
    0x20b4150b403004c100d84503054114024001d004640180400031121406605501070a209010811100401480310701e44103c90042c07a0559001c1003a54466000c54201075200603801001070741d41c40940088a0b2401c0c006a200b0940d076010301c0a480c0400104484500507101c02059841c10008510030100f414040d040d210590b540104105030341c0d054030750960b007056000c0c0e40c0e54030001402a44440c0d061191445000c81290100145021030316102d9410700d0701100d200c44410280c100005101100f07445c414010b41c0244455642c80110010180310803003640d040d40031070600c1c035001e09098140301e10010011b6019008204c001c0c03616a040750100c020500a079018000c0404880b810f50f410320042d0310400d01600242025403411140c1c500c011a58150b6a400503003c0c00602c45984c3d1101c0740e4a02c06810880e48e20541d00309000040c0209070381fa0f0710410741d1180211a401032507000000c0f550542101d60100000950000c205034040003c590061a80754200018800980124150340248 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 213868920 1250 213867670 213867679
    0xc090a0515130b1c08070b06030a0c06050a03270803130c030b06150c030f0319050406090308090f0601090e0a140708060c0903031602150a030506130501060c03050702 73
    0xa203241d01040c0d42d10501c0b40d540038015190083c1c1d401500f0802040e0042e1450089803101c0d004181d164030a16000300c00740203041820704408200c240d60204102c06100e90080c107000304440e543c1e8006010303a44680343c1c03c40480e0400c0d4015802d0710031100c01c81e8a08845c010920001403a0350313100f040300c0d4001044a02c0a400100c5030b5008601d1451952001d980708045030010f5044c104100300e45c48107400714400707001c4070030000003004040100c1070380c200118410780661652600781402c2024402280180b58651070007041005205550300300226030341c000e031940001070311641089a00d0749440800c03c3c1c1c19500c204010081d030281c0354020910042e070316081d201c041e40550381c0e0440c1041c40c0c40c0c0c001d030180e001100501207050244003031074020503d1004030346045600000b003912401400c039103815001c28032500c0c2c030035510703100245044c642000407181d6603042203540240c0100002e541f90740c0500c00c250545905101c00e0710440b0b0581c7c0712600ca05191280a0740c00302c9581d0301010302260403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 213870170 1250 213868920 213868951
    0x9050c0d0305041706010302091503070909080405040504031d030115060503130f03091a090d0318030b070507060b04021303230d080601030b0a14060f090603011202120c090a05 77
    0x1411034466152111075004e000e030009515600400050010151008401d000c181c0f000d50080c2d070b0000347c400111004a2030204122030f59040150650166611040d04581040204020103503c0360300c100300900503008154804182d80c5c01c0c13508a8210380c0701069075040d10740c0d0911000d8000c6015640c1f0060b601c160320740781203c036030f075440340340e00c001c1c0b42200442c1440c1c10600090b51520307406080e12100d0480f80c1c0c00c0540e41e500144aa152a8101038203221a510040740322103230703455011001c6c50700b01110000a0809203401840d0341c1c03001300c0c1a21011301e01035940546203018001ca078510008020310200540c1581c403082907181900b0303a0701104640141540101d41d04c00c6c0910044070485407144651490044009802e5510082c4000d22682010405000c814070317030144004080c00c03c0c1c0f1a5511001100513200b00d901c54204050783c0240003200000340440303240c1d56400b50342d03c20303602c1030391406c481d422203a5101018907080c0e601c50200400989248110380c01598003450310030580c4035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 213871420 1250 213870170 213870179
    0x711120c010216050606090109150e0718030b1605040f05040216050607081b07030f140d051302190e0406090825140f0a020402090d05070b0c0d0309050c0d030504 71
    0x700280f0302e40200c865130002d90422610340b4180202030b004140400c1d00f80b0903910380342c0c80c1c024040014020400000000380210b0355043c4284d500c44103070444400c0d49049a030301d03070a043c07503031050131503141c0d4921006085d140007079846941a241207a00906202e00d03a14182810000070f50444002d090841d0740276441500410020021903001c0c03139403034490441300c1c01c140340c0d0900102030090114403500703002c00855000a90200910407815803500c1e06510041c1c0c12608480b4620810407011402410041400110309040d045a00500c3c402c035644ca01600c0f00c8544d4031106010b903c1a6100d10086800003004500780d600706002561040c6141460100030003036080c80c400200244123600b54400b5030038401c20010107144000550903000030080d6440184000755210f441d0039000b0b00454000c16190703c5503c4114003024619802416552941e031100485107964000d8003078100c8901c10040e114542030700900c103201c4d01c141c110b40a00650500001403240003280f03240d0440c00c01400704400036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 213872670 1250 213871420 213871447
    0x110d1e0807170405031006060509101b0302060f091603030e0118080604050d03020903100b03011b020303160c020604030b1905090a03020f010507090e09070302030307060b090711120c0102 82
    0xc800030103620b007854480342403a09040c5030501441d04480e400d450800140503003600503040c0d40324244100e481500207043c00c58201ca07010541140c000038550b0420380c00d4201500810300318842c1c0341c4d2180c070407141c0e80c40003005599407010300c0e4264400e0522103001c1c00824031888504400d01c6040c10300081244100503980381181d0140d20a250b150084000d000400009100b80c100c600c105243c1541040900340010f61030311001e045000d0f40f00d0340e6440b900c849460030b401c0115091a4480701000c41b8035001d101039220350044590843c0094040500509107015070550b19050b0b40283c22241042d045954281c00e01001a00186615021101c65884816280222882809040042d000c403401600d0041d160403050760501505034104410000d04940c4518107404907501043c2d1040c20341c40d181e40250038015284c0000c0e40600000409506009003904242d00b509005d0303030304070600c1e0b031b800e08100c846040940a10416410540d44480745041c440040c000c0c40b40f00780001440e1a001c0640f82c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 213873920 1250 213872670 213872693
    0x171305120a0510050403020c100e0409020f0d03020307021c0c030f06090c141008060d111503100e010801050402030607050d1404061a01050304080a12020409021303110d1e0807 77
    0x43c415030b6280d008000c10542d0501210942c040141d0b0700c000400894100a400601030550300d5000b83c0c3c0c0c0d500d0312029075540c030b2590a0b0b2010007034079140110606080c02907c075405104142e01421a40e04848604001110707416106e0350010b441171252400c41d69803000300c2843c1d46050f1503440d01c1c3c9040001040c240122140284000e5400385a40c000302e0082c81448804819090140400e18081004948507070122643d020b41c0b18022030b858140130b400050854032443e10900c07841d032000c0104440d4980e00782510b03060350030b4400301495581e66142c1ca40d01340d400495000b03400d50415070210303000d64011405441103040c1d020002c80c10840b1035180d601141d00888042c0e40c034a445200044d1240510303100c2c2c8541350000e04c0e0241c9146020b460341c0c8240e1040c065402c007007100889080981040315410798000d007864030700940d55540e41c203e001c03400d041c4074081990f40d500c100c4a60001c1c0c7c94030b002c2c480d000c04e6112420100031540010000b030707850401c1400ba00d4005081110100064001220 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 213875170 1250 213873920 213873943
    0x1080721083006211c0c1a060a0b03060117100503030c010510080d0c0f230a030207090c1202070c0909030f0906020c06030a0506010315080109171305120a05 69
    0x815000746410800c01400480c141e00321813010310039644c0c1c0050f0400218040355240c00c0000400040420480c0c21265262013800141a44c40000440c0d40c0b1b000030000600d01485080320700c5510540c6500070210188400c0e29101c0c04150820421114840d284103603540c09414a0000801c055a910200b802d503072040c9440c90381c59541c4c4007005244c100e060300c080003509990b0010542d0650200c809409401d020300003030150640174402c0804c20184076509030820a0100034006205018042e00750b540c00004002c0380940240034020840001c04c1c8100e2201c906075595021070383d03130449042e00003076206142c01c0d01c150250010129549501c1d0095a001070f02c2039075001c5041110140c0240800710302d400c882c0c1190480420301030117030b0f1282c0545c1e4024200a10001e15500d03003400590042c019110340c00c40b844251000007501c100c06502148246010395041c3c6440e051b8a04203030401d2048080c80c1038285c0e50100207009504050040484401c2d01c0d508640b40c680e51910b80310715140c4102c54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 213876420 1250 213875170 213875257
    0x10c0f080403021509070f230909420709120201180b0c07080a05031801020c030703081806040b070803191505010e010c1511070602040e0108072108 65
    0x50401281071f000707501c00d000706402184500440500c0503c001d0007050214010710420f002d1b80814950384003400000c6504e04603000f9400d001070940802c983d40b00c942100d4152100744001c80020040f58600081d00c65241940c500c0385907400c0811450040d94803010030303030400900444241c09107000055640280076122032203622000010301862400070181c1010a03140c001e032400c0c100050001003a01c0e40b1516801141c00109103000040b4649260707041c913558507100d01070001040c4140d14009051507014904c100d40b0400300001400014466482541d400d03820412054020417442c0024542101c22041300780c0700c21300300042c21001d035245201c2e0801c3c2c6071800701003000590782184004030390420a0030f00034503c00c0c0300d4540d080b0070790000030044401600ca00c811014003a00720203c030f500591100086489036203401140381e04407401d024080c000d105101c400f181090303444000300800b144401f2020308003051669601001e4110301c1e0360703a01880c00400c5180e2104a1015140b075070480c0e104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 213877670 1250 213876420 213876433
    0xd140307080c0a170c0309010c020f032a030106030302070513240f0608040b06041a06130302040b01050405090a0e0102042105010506041b05090f06031e0108010c0f080403021509 78
    0x8044181aa83e00b040300f889080c2001100320048010040d520f2035103003401c09c00d002217881d001181d20080141c3c201d03a803601a1001c2c0300912030000340c03404d141410a44401006890000906088a030b41d408041c0150780207907010405441c054240c0c200880540001280075820007601c0c100c4401da4180403000600584418041107940a1112001f48410b15002040381070503101d5901c1c80c90040c00c5039008544803104000c0300080f1f0a8010f0584002501880d6282c0340760968a00124207804120b2150b03007084090005036114400f0364050756801000300d407080e03c0302030035136005008807681c02c0d0701d5540a00000641054038001e8248900135034080215030030301843c1030f0382120340082145109038034051099840f25541d1200132a07088040c01c0084e5a1001e2800142012101300e604036804003000041004d01c8034038241c0d141d0315440f0b4061482c020303601c4610712400c0e01e0300100034000107100050400c248502c0303817054541160003801030701ea240c4006e12a014074183c0444500560783e1110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 213878920 1250 213877670 213877673
    0x90d0623040c0608090601050a14031c09030510020301030503191704080a02060702060403050418110708090108010b0c19030e04060311120f0c0405041505070c020906040504020d140307080c0a 84
    0x7404017548112208050505581840000b030600503241c01a4500c68545144900d241e4a0400c84031542500a4200d410400702000c0c008001002e103010441b410b0140c251f0b40c550398001c80c000d07641600d41c03090140d401c0601200c880c511842c0e05103408000c02001242844c03140e40640b509034050741c007031044943d646100b800081e2821002400340000c6510000c200004641e004050754160ba82c00c8610078104c880d14100c1401030001c0b0342c100400d000001a0300002c0200180c001c001c2e0140030707200c0a409a0303071036504070094000d00d5a8034240c0d0304410016084c0f1200f02440b101c8940c401e041c00d0000690f030030081421031344507810845a00790141e01042d4035290030f11100c08882c000000a2489038603050005440f00780c1202d00d039000f5615100071408104400c1c00c50a032041d0074550400492078542c4000b041020a00010303805810b952012406909160190600c15a00501003520191555a4031170515161003400b2105000a10101c00051074000007080362200070401442c02c1c4155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 213880170 1250 213878920 213878927
    0x9090b04060b09090a170d02030c04150503150d060e0f0109031d06040b0c12070602040e06090412351801050103031d0303211803090d0623040c06 64
    0x14041c483d460030010001c800000103031007900780b0b40c0030440003034004100440150030f00842d0304669a90740044204070840c0400703000b900489040035600462501c15040c190303124882950310304803080980070001d44a040c1104a0741c1c44510501c030028141e448256141d043c40c0702e00340c030b01107030b0303515440382c0400c1c1540110b2400c1c1c84054009214030355100ca10024080348503030f2013010a07110011501c110303c0001480ac0103128401d00c418240d461a4919202000b54403c2c0101aa18002080881d90a0500542607440380342c0c08507240e5141510b0036801d4900301c00d094000845030b100c000342c80280c81709640007402000c0e84c4410341000c50605817007550601800060001040c4e140c08010008280d110060250144020304240000078400020074258810000c15245c0301d01440020b00c4401c003442c0141d442540705202606000045911141d200d205940000d80d03c826503c10b003d0205800b13a002c401c7e180b60561240c008070715008050a80ba2030200e0f02074528141600d0300300000c540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 213881420 1250 213880170 213880181
    0xc060203090105091309020604080a031416020402130f0b070c0905091504050709020a0e03061b0a0315030f0c0602060c1204080c340e041104021309090b0406 69
    0x5500240d420003400c080003d01c10300803c11124480c400300d16040b04c0e440c0c0c4a80c441009660040c2c50642c0d10b80e20740b86441c1e59000c00b028110009100083d08000c1c0d00c1c05c0809903007251100d484199000d1110350200000b0307400c1800550040405400e000540604020404000300b40d2541015203400003801c100b000310603a0b6000d506071b1801c010030041345e041c010a5292202040e400c40442684407420290b03d01000da0f0443d0301c144c0d1000800034034858000c50104002e4208904640c03481c0d940c040700d581c02c1140140340490880081c00600c2c155802a0000143c40143c014042d016541e20b840d0885c5400742800b00b540c0500c0c0000052000503414450164404010381c1c0c0c00345004035102056405000003000540049000714007890800c406000c2c00e07202d50041d40360423801c4090741d0360890040490442c070341e56840811500040c5111621080792003180c020666220118040f000e1201079032002e0f03a8118100110b800104140c165403141a150501405040c072282c6080d00e48281100c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 213882670 1250 213881420 213881429
    0x2a0618050f0603041211010e07050a05100804110d020406031406010b03010b030703050403120212060a0f0e010e0402040917030a0605040207020916050c010c02062502030301090e0a0606120c 83
    0x1407448180a00c0b030310b81208903500070b54000015210401c0450701102d1900314180051002d5007001481b2801400015624003501c00403641c0c496100d0f034840030048400c0e000c05800021604610008020880410a00e54503400143ca844a03403c280d82c0094100c07130903038004803008001110805000f038003c100c001d01519104902910b154102000c0c0700ea24040200101f003015150b40008042512505a110a140000300b041d5211440b0960003448107030203c6e186405092101c000103004592611050708880801c012140d1a9080152f41d44004c40001c0c4140d8005131108900341c0040c022800c1c01d60300c14031000e105612401d04110326030603149150322552103a4018082800076980e0311103099084007881c9803007151000008403d6030113016103214407140b035103002641008540c01003180e512414a0000440024030801d503030211200420360a0030041e4424001842094003035488091303228080b80840d1034024040d9100401e49005800088041c0da61060000c100b0954035a84070152 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 213883920 1250 213882670 213882679
    0x708070f0f060c03050d02030c0403060f05190507090905060307121406160e010c032a020f030102040303140304030210020d0204091404031d2b0b090610032a061805 72
    0x83ca540c40040190040c4000c000c09140e0010108078100d0001084500456001d9018050b18025465101c000c20040390490458079003002d0043d80300d5018071403240b080d21240c4815024908161b482c0300104001824250035200b0342001180840000110200e03c521a040c0c00c40348940d070091290820f00701411070111000b8a06014010541041004e1030440b000c0c6040b581a80f032a00341100c041d884845100030701190f0f042c030a003000001401d117001c40c0d0f00944281c800b040c0c405c001d03d8200c1c4114400070340040c07003450510030381d100d00c1001142c0046c0288111000c1404000c5040300326409200307000e5403540d00240800854582d4012505107155039100c000041ca0076440c05010341c008105e00c820b105080c8a88600b00396100c0c2032508204828440d00e24074a0300034805840b03204441d520030351364190354100044c50060000f94991283e0310103241d070b040d001d03e990b4031240c240c1e8018a00003904042d0300040308206283d03541304001000ca0341d40d41c42484010710502403545185400c1103006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 213885170 1250 213883920 213883937
    0x30601110309210c1906030b060412121101020c070302010f0f14090402040308030f0703060e04080405010f0c02041401050a08030405030a02150f1303020f0405091506030708070f0f06 80
    0x4603600d14038404000c01d8800310b200f050088040086052007154015a0b40c0600c031803e81c0e4941002c40d1800900396400d5131401c02001022400b08605401184a0341c4417880381241d414001420200240c0045002030800280703407590480c1440c203a070085ca0786020507901c042e208006569000e44a80000c2d602810603001c1540400d20007030030034498100c020000400041e6842079601c40f0360440c0c0096801803081920384c10b140d04d0885e140e85040ea4080c0c0024140792000c00e0108904903014015a40700202c185824980001521a203030043c14480c203101e500e0900d0405a2658020115070504040310f000b900d40c140810480085950340003401d00d940288000c1c8555100040c00c01c43d400c5e01140e204d05090340310450300050780f045d5480c034050204081111407640741c50342d04a1094a100321007a03841c1100c00001e110031100200c50990740e503441401030b40072002c203c121040c1c10500140070ba803080b50b16841900c1c50b00c0c5180e1700c054071201900c03508200101003c00034501408091600060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 213886420 1250 213885170 213885187
    0x120b09060c0a080411060f0c030309010c020c101b0804080f0d110d0804061b11100b0607020409020d0b07200703020f1314070f020c01210b061b030306011103 69
    0x3043d6004000400c0c1c00008000400c680d83e13000c0c1641d000c2c21001003030300e9a8044508616489800a0703076160110360904044060242c008a0b444640c00d0000d00148243c0050207011940820500c20b001c030300240410390400071400a0300180042c240f504003c010b030054000c4041c1c50b185c88088200f04029000c1d0030607030325040202d0b096452140510702458183c840e802d0090082c40f1801c080700b600c2c4c00110030f0719070049c1c1004403d800c3c644c0460a0300c141e00c0c415424102aa070b15602000c0d40040308118a0005143c1036200d0300b0000d00143c600c03407035000c0700c1c2da031030300da0402c241c4821001c241d0381400d10090a41c1c0300040e00000a51501500c00300b0715603404144c001004040581c03080c0410346002d490207149520000303019960035004030540c204190060422003d83d00c0141c010300809052040c154069118108a4400b19a41c80b003c0c18400000b0070040026802e00780d070120003081038048503000700d4042502e9141035005180e5904089001601c0040300384071135078042d0000d06c074659 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 213887670 1250 213886420 213886427
    0xe0306070f110307062703050f3010120809060318070b040914060d020f010e03010f2f03070c02010e120604051002131a04120b09060c0a 60
    0x250014414108808000e400c0d160940e0104980c101c2c001c058400407450500344403072604401c81804244140c91100869040403580700e005c1c409028000ca0010024240381c0082100206071840d88180c440091031000009514000240d02c81143c1c62803c600501900c0f020092010300180540241003650b60790360350741c1c00c09a001e4042d56a2281c0e00100008020006450300c8040f0b4202c4042902d900c00e0301c3d04040c6203690094003811104620f40100b40d0043c1a1102c0001d0007924001c00c800f0408416508001f500c1503108803c0f4100403c0c5c1c0c50800d42d0f80c0b024040d00340842500c44010039050320a01c10700a001c16901004030320320700c000d0800c1000c00c44010840341c0100c4980303058a126600c6000696842003040b003019007042100c40c074071000e0b45010500d103008a114800781d4102c0c03000080b20800343d019145080c14008a130b05010402c08940c80400d010b00e80803c00c001e410300743c0d141e80e07130b42e1420002d81c401d96070324208004000700a002071200d594484550100e0300d0501c1081403005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 213888920 1250 213887670 213887683
    0x1015030b0606030a0236180f04170a0504090f090807030806030c090a1b02060601052704020412060f06030305030a1d010507090911030112150605060f0405010f0e03 72
    0x80b8000e801c00008508051002c0e012a0030401103103c03003d49000004000405841c002d03150400b242003c4000d554417031801c00c1048441581c00071038562a88c449910180d11404007038400c4810a13410541c400d0007001c0100902080c3e8500c0d00d4042e101e615140a202c05d550329907441303801d80307031605c100c90000603030003000c3d00d1005405281806295503142d003c01d2074000420684d507071084440c03040000005041c1c200c82020b4400150405103048411070aa0b5240700645210307000c42e4080c4040817030900001d0544c01190048103d01d4400200f10300030a049a1140d00980301e1900f0000c154418418140101108a43c00741c004200503842e50314010160300010307007000c2c07040e42c503100e01010840c0c02c5031040c0f02420402d8000c000a05080c01c0103401995244113140b1403d060040c90014061900709682c1212a00f034403504110640e40c1d01e40d00300310441c100c1c40c80c005960b00404281034451202501c17400403040c5003541d1380e9043c0130024150020070b90003e800c201c40107004914545010420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 213890170 1250 213888920 213888931
    0x120f112508060f07081e3309010501031a0a12020108010803120a0f1b050309190b0a05040c03050d02150f1905090c150a09150203090108180a03021015030b 68
    0x600032511400ca2888200b004070300020745c6c1100c81010f01c001c070204541072103090103908034a900d004402e1101801c010b41070108055002801030300411103540290840c60150328031244005104118500203001d030303a00e0790401c82c01100d8a07018001156049038240b805094580020341c00cbc845070101c1441c2d103d00c02408110724075207809070386960300841d0300324018034104c0125500399400444001043ca420407140b2040c281700303504a41d012004880400c1c00b4550304001c0d01d14041d035034080100007500d0007030300445110004050010100d10b060008504000032640a4091180c07003000c44e03442c860b40075044e1079850301c1c0c6209011403c40646841400c1c00081d502c00304c1c240c1e139040805400d003484105010703045035441c6051041030001c00020300304500c007503c03414801c0d9124260180110b111001c05805a0310030025240380d980a0240907500ca42e140340308007400c080007001e440c141440382c9000c802683c811245071002c006d990183c800302d503194914070aa03903403440d02d903000c000c200540f8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 213891420 1250 213890170 213890177
    0x206100e060f0a081b040c050a020307170403020a03060f06050913030309050c03010606261b0c07150c0605060907020d0509120304061d04020304120f112508060f07 72
    0x1082c085916002000d5008112803c02c0d10f1042c41c0c01d441c02d401d003407a105201c034404c5240480c4028564016015101080c550394011400c2140580e40e07003844000c171f00810540c601d401e12000005a442c0e918a9028601c82c0c040410007059188a1605035281d030741115104160010421680c905c100051030f500e107402d840c0200340a5101e0a02604002d00001699059400d040010815a4210500c00700742d40782510304106402d0b9054103101c4500040e134105026801c040000301500e03803440702410010300420140c4110a940740000d2400e00c1c05c4c0e103811310215a8100a16040c00454400d950b072050068900648510380214001e44074080030002800307000000c0750301c00d044c0c0c88600c2c036801000078003000c8036035682e101d00024021030406010021000018107920120381000c1c020b481c0600d0b1b000c2081280101100425280710007114610f408000015150824081040000c42021070b84130310013880300000070a02004040c05070f00900c0b4140c0c004800d0080b81c002202d0126801001c40c41d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 213892670 1250 213891420 213891439
    0x100e01050601080402010804020d120c21020303040f06060b0703080115080c1c06030b040b0f070c02030c15070b010320010806091605040e0115030606030c021f090f120206100e06 78
    0x1000400784002800040e011010400701c009031650000404542507006c1c4dd240711884501e00006170350001c150b104007005820600100740011307089107040c04140d21806003c601d85844847c40c007190307001303c01c080c0c00156060004002200c06103140169070321041c5000d03a0117281100302901144503041412403454074040880783c1c0d14055034469800380d0b81c00006040c03a818542804000d00e5820f41c0c0c802101d8032500003040300b00d809a034101d054694040c002e000044c4991003081003501814a844070500820031485000030f07110255940a58421003210ba00c04110081c182c203410a082c1c030481c10b200f4014148a0541d5482003159800b80140b8144444a081003200315842c2c040c80d070180c1e0113044883c0010464500d0122080035062044e80d0401100741e4038038040f003d03100e40b00b9100303025800c2062041581e00c1d0341e00456005001031030000c41e80033855580c2c030f07001c2c1241c06030030b650744107807402003007081e6605020060300085408040c62a00741440030f0f0703c0b00030001804e214401c10480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 213893920 1250 213892670 213892673
    0x9020a050915040e030a0f0216030303020310080d09080c0402160f0c030b07030209011b3504030305180103061805041106041d0105060c1504080903030c100e01050601080402010804 79
    0x1203042c242e5084060400d211001c19800c1c1039036242c02c40c45103280852054401c010800384000748107000072420405142c515850358800317400a620241025040c041c0390040420500c00030050f00d4500310341561407003015032803c45240e040a4240008500c59801040810600f50344c4540d04030945070130900301d000010040c9001d80190102d540700822404165080118030358140d4090710400c070302a00e6108480040c42241d03440580480b1000780800010021300c1c41001d15607045000210039004505c0d00c503600818a68a0358010354411800200005041d0421841120204d24040400e003010700415081103886000d58107003403050100ca40d0b580c00010148007142c82c684025000141006642c0c68803810b1180c580f01c13440c1c43d244000700c040c00001072182400300455040c00000350203000036500c42c442c0480e0082003e082074500759001d20201605640c00e0004005124482d80200382841c208000b0101ba120348064481c8641d03d00000c001941c0d81201c0903643c0158240b8051005a481c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 213895170 1250 213893920 213893941
    0x7020c0310180515190204210f08040b0403060f150b030c13120506090a05031801051c0e070801180303021b0f0102030109150503281b06030b0409020a0509 68
    0x1050007401910600c005441c100b03c01c4c01c00d4500a842c4450701c0c0c0300b01c0140001c2c20042e4441c610425210940448040c0301b04c404040101e144244601420110b4105640302d00708103800c03941021300540b900060410801100344a02c42c1850300c00303a01401051110981012580b05a10500404080010005000f003d4aa00702c072a041402c00800646c2c0b1f44408400b075409a90074404c44a03845400d000c6041442c001a4401807258440000c0d854500e020381400b4440211010301418000284403000c3e503608040a864011003481000242528400303a02e41c0c90005d80c1d61200c2c086916254071020841d0040c140412040d4040c14096a20010944524400c1c4001d0010003110300900da10170802c00019001141241c6035418103000c0b040140b135120304800f990b8070460394035501a810005101e58414a1f454040402072500201c2a0842e114200d18400441e101308034025207440c240240d41c0c140c8903004c103d00341900c042012404c5540881c5110003180110391042c07410300002101c185c81c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 213896420 1250 213895170 213895211
    0x4030207080106081507021614010e060304050105090d08190213030204020712021e03040509070e0303070b071403090c0d05010f0f0b04050604140c07031e11010507020c0310 76
    0xc8000007000200c0d9140b180c03d031070724049080700080340c1c90200403030006440023505420246840000042207407070081502d06032051000c5807414041740c080c4920050740d0744030145204030300440012505103084000d00c1d04001200200780f0034820483e003403000e40c200015040035041402400180c0d03880d841498908107e0302a400258898000111642046030892020401c003240d038085801011203040f1004102c64055151065a44240070401042c0f4000260b6500843c00341010b1031040340300000f080c255840001c0075507a062a1800740458250f01040c1d0301525440e5110080c154102440210344801050078181c1c80340300c100701c0e09020721600303601000060301c1c0c98201f00544400c1504140c05080e503440c001e442189440005240c40c10280128203c44501114060701661180000507082d00a901c0550400414100142555528411b1034400c402251290748601c01301071281425248000c203440e04541203a04401d5180c3c80014603014902c1106402050038155444030360403200c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 213897670 1250 213896420 213896429
    0x60427080306210a0c0902041415130f031e0f03110f0115050103050c040e010b0313200316260102070512070c06020d0c080d1404032a110904030207 65
    0x240240403c40008030000311403450600c43c4070f4000b0110b964014440890180e403052549510003000c0c602000d144c004490f4800303510007107669040c8103401040860400301600003060703074401e2078000d20600c070081c2d10205801e682801e0b4000303070a01c42e903140e0048540410004041c0b010800040741410801d00c04000c10204140081100342400510001d10440d20311400d0301107841c000210345080d0b00d940881d419564450211a0664a86066015960b100401070708041743c40001d8080020003032007003001519400413034200c03099980d00801d07081000340c50a0501d40103075202d04000300e100f45050114440746694480940300b200203a02070184c481c2d5240100203010752080d4031030720190b6202401003035000d060088412525400141d0b5242c200c44144030219241d00781000004400030002c110104c00080d0105070382d078a51410b03070034204003a503088001c500704444164101a5a4000c044a421040d108092041d00703600c810005003039174440f0382d0044035002c00150904d402000180d0051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 213898920 1250 213897670 213897709
    0xf09150711060705150c0a090b0403020d0b0603100c0c02090a021c020906130314062d0601030204150f081311040509010e12030702010f0c20160608060427080306 71
    0x20b00e800c90321b103080d60344440486c8000c40c2070071b0004103c1e0340071103040d1000c0c0e96014100812071041501d81d5030514800030505581841440038654005030b0a01400c425020380b0f440c0c0100e00700c194030401000100040015900760b01c14400342d50001c6241004203000c6c0055040180c1c3c400c1280089005441451115a05e5070130344000041044442300700310202c0300c00d1600380c0e0069200d100201da0200c040340400c0540e520081c000000240310380480d9908284141001450250790b00b141c00c002440703005000000c2480301c0301d00400c0b50307081050a5401a451914941c80c0d82130341d0384582d0301901d070500076030140342e0780d0740000c0402800354020301c0220000c1e030440e03c428010b00110b0815500031038a000043d400c0c07000c0c0c50381c0e903821402a0000c4c107540342c9610110f60b0321001022602e040c25034510620b8450320241c0014407007440d8200000d00301a50b01c00788285480b034144003e40d446083c203070786807480e17010b5003a8020200420100150780d0100000e6940d4440c070002400d50f40c0c10b0241901c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 213900170 1250 213898920 213898963
    0x5070e0a0e06031504030801032012010c090b040503151b0304050d0215130809040f020c07032603010b0304080708030114030f010b0919060801020f09150711060705 72
    0x1580c4090498407842080b011134a41c20000090700e103404a095030020003081b00e075001800060310f02548106c0c0205501b254010082c001c100003601c06400b0003020b801650741c0e00140c5001c90b800142140070f0a103248030a4613040ca0321000c6552a000e1040340200f2840d81d1005c1621500c80d0001100d265041070300c45078407805e040c24400d03201c0c80d442048070007500c51a0f6103800b802c0d407802e141900c40c4000c05004003110341d098485403120b52051580c3c2e035103c0e40c2c0382c2020310300a041e48003822804030040000d04045040d80741c9400c03c14141e1805030b444114203e282d480b420b041da01141d05448034040070f26120b07140c41c41c0000796030048003002009240701000105448120550014203a2012412030703204918048005088070200c0e10041e0b000250000029210012641908116004000005205950b48500701d007284c0004110358000c64000901a9440ca00441c000d145940d1044407285050b52542e01c805d41010300d410480c0c0900300200b07603a000c0c800d0a105000d0804c09000b6443c1c0c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 213901420 1250 213900170 213900179
    0x9031011090108010e190504020609090106031a150405010c2105030402040f09150c05090a0b040801150605030406230a091718190b0408010603110907050a0305070e0a 73
    0x2856040001c00d203001810f12800010102c007000e0340c503401080107400c490741004507800b001010b000b005100340d030000b40802011140342c95540c00e40c0e000340403039600010b0002c10054040001041046c0007849240c41d5004d6030000c4024808903007c480c02402c2074416088103290030000d50359851840f20007000140714516806811900a5100358400c030360410807071200ba80f181c0c0032100c1d000e00c0680032100702c011180d200500359012102207403d9003082402c2c241d01ca000503401d041c01d40c010002c0840045010805030000b405451103509130541c9001045003400c40060144c000100060071450326400a060387c0c000e0000c2411541206840d0085203180403844100a00150381e41101e00820b40c94414040658000c00d0312801c90920100c1c00300455814104050700701401b0301c1d040c610380c2d405000903942c5820402000200901070010031061710710304188040348114003c0b079000d00d91640030020741d160302008440144903241000107940d1504070088401c540d800440c035800c404e24110105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 213902670 1250 213901420 213901451
    0x120c021207060c1b11010c0809030304090204090b03010e0d2d030b190515030604060e0414010c020106060807030c0216080c0301180f02100302070501020d0204030b060f1302090310 79
    0x80c003e42d160440e107074550000140b4402940c01c406800385001c4400c080c125841440c414a42a000380303082400d00d900300d000641554455031126009950000d400c0000360200e0003001c00c0d15a003103000300004a20403d43c540c0f103003000c1030b81c0720800100240080c0c060040f54100c1c050b25103040d41071614140d8205c4c002d4018920840601c1c842e00c0c0180460f0341e00301d122002881901d402510460a040c1103414181c00b40d040134080c0b5a005896000c08900c0182c801000c85c820b50052503403010001722080514216580401090301f16410801d0600c4100e800c0351881da0406490300e00010201d401039030481c00c3c6822280f07000d544611241e40011403010000c0c3d80d030304d0144220300800401c80c0c1c3c11002c0304203007042e0300000c040119814071705000d8074100046440c211042d003400740c9807900c2a5940c07400c9038400546181c01319404503051040c40b2640d90120760003401038804000249402000501c0d21418a914503c03481e000244500d0355182030251680c202159041404104d02154840e07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 213903920 1250 213902670 213902681
    0x6060d15151106010f05060903010b10091a030906060f010309021203030901061e05060a020a0602030c13050105030f0c0a20030a0212071106030c09190306050604020a120c02120706 79
    0x2000180201e1105504080040f5441d8120342c1e00d0813039003072441c0c902014071a29420181e00c4c44c2e0306560380c2214922a0b102c0a5050b4a402402e0b80c9440080c2c1c20113484894882520380d4910046c4002d108000c580100001c0440c0c0145044900c04404034214004030007509c0e0624009401c0519000500303a82100000074501031410328009100c415200d200c2c0d0b5449225140d40300c4049446250100440c0c10541e0043c4088145803040c2c0c0e100720f01d80d407619021307a4029216501d070130340002007001801c01c6030070f0348030f01a00d001d10b41240756007007585080c4840340e809803070091500d0340001d52050450086d40300e03101c2c0c01c1d075101d40420240f03121000c41e6125045292250003500847c03444101206510080b50f207816401000c101200e12038105106840e04000d1102c2d081c22410480e5212640e1800c071710414100c00faa1021040b1402c46c03070103005039007014144500840c010300445861039000700710b100e540c00c8440d10016821030041b804915102d068092545580c4000a08005100494204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 213905170 1250 213903920 213903959
    0x102070f060e0c0a05100504080303010602030307090e0f0402040e1f050402040b0405010b1204060f060801091130030d23070509010903060f060f1508060a05030606060d15 75
    0x2c00034048000481da4079803100d1030312954440c0c01c1200521852a103800008210300b40340c5085400e05845202c041e156a00030380000f00076034008000c1003025a4801d9026020f004880c4100300d1034101007107200044800500000e209548070700b103002e18504204040c508054042040107111442480c2a00040c0411b5a059025905101040109082c103000d468101d4104101c503170302d40751403010813500762840a4021103096464200104a07a1960b0090502509003000001400301f039a01c6e040484c0110162070354001d8000004036503d2401e00f044500c002001c04109280031148000310900310301c950b400000c8a1850450044002002d09020b0f28003050841c040c00c00f01d80318100252482c3c042c0c411428001440c054013400000c02a801011001d040d610000c1200754440c4070700845a08941c022210724004244075000c0705920140b00341d00719005507059000b2a061801003525580002c105902804000070340401074542544800944041209281d01c220b480b0605442e00398940007a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 213906420 1250 213905170 213905183
    0x80318013f0509030c190c0e01141003060b0a0309020604050303130f0f030b0601120e1c17011a160b0c090a080316060510180f051609090f0e0102070f 66
    0x43c400503c0001100d03a040d2000c00240300c0c60314650303203480d200010041d00f21100f0010040001d543c184034000719001e880c8044030000382903003060601180d00d1581003214109410030a0401902480394202c4012030729514003c1a400503900101d80c09204a0340800d400d8400003c1084400100510000c01e039548100441c3c0c05946c0d4885113518030761a400050304c01c103040f0011030100e40c0100c01070403001c015080c0105085c411804e00301c2c201441c89401101441039071301842c8a40d0781c000030468981700d03294450522541462520300760310b00c0d51010803466500016509520701a910005210164002120100352411800c608980d400146030540905014100070680b0440442601c020430312003041891780314183e40f02c0c400540409420f6440142072410f01003454a002e281c1200003410415010402e0704180c2c0c55802146d1b0000e160040c00c030f611040c511115503001da04641190000c00000c02e02c048510116030082c040c10aa442d80c41d840001d4041c108040002c1403400e080c05001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 213907670 1250 213906420 213906431
    0x170106060329090a06180504020f0a1202090901021603180f06080604090305090301020a050c0f0a050d0e03100911090c1303061d0706080907080318013f 67
    0x121003035040310302d4010303079007420360380580c42c5800c2001c4000d0780514841c8000c034611b40e480c0207540c0d005400901c422103254840b002c000035800e200001e40c01e610000d81e402c400d00e62405402501743c1750708050091082c1210004510100800d406807840032004031036000c1500400c3c60050400b003084041c042c0a81c1c10170700005440705c6030030050300854841342c441070b26941d2800100700013402c0c85401101400410305c2003200c03e850234030151030182074030703100c99503502c02c41e01440785800e01851082c0126440b400309140040c40218500040c100300d402c2860000000d00c0003c1d04111110003a03a86140c540307824002480600c283e011058807080d18135000355182c4115448461003031484101503030b1034400e8100300040059200700c404a140c158a0f0b440300b01c1650000341004282c1d805207001607001e600744005004140320401c010182d0303c00461070710001d407111850100b641e01c0740030305200403145501054009a801030a042c02c40168285400c038180d0003442c5c0c00755000c0e803912082490030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 213908920 1250 213907670 213907691
    0x1201060903050706030b0a030201030e07090f0e0c030706050901050307021f020711030601081f09060e0c1f0e210f0d14120a0207021201090609060b09040309050105131701060603 78
    0xc1c400d5201c0c0b450041e00d40e045848c2150010b4003d1b00700740100500d1071042034000111503442d44030700740080314504008a010351501101c00e2501c2c003091700180c4a60014281005019007000450741886020308056440b59510003041e07080101100301c5045000040403080080400f03a80100300080c0700b00804a02001d10b0300030300d036031000709008000d6503510010b1102180b901d2100304854004031040003140300d49851b60f4440c107440b032000071803021364480e0491590524004450000c2040c5e01200c0141e8a411980c0c01442801018001da0240024400340030f0f4500c50301c00e0803c2c001c0030f484112000c4900c01707118103550f0803c110f592000500110034001c4640307005000ca6000d68840e03040a00c4035120311050a0013035000c4841260b12040c5400d940d40210820b001e0800214000e0400140b007500034140201070f01c00641026100d10000010040020b401030b05500c03d81d0028a0b0064a480c5201e665003108443d50304000c58101100f071b614008504150045415216690790030301c64941310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 213910170 1250 213908920 213908927
    0xa031b02010b010905040e0f070311040506010203120a0914150708010602120301090f24030b0c120415020c0a060b030c06040807060c061103090312060f01091a1201060903050706 78
    0xb500c1940044e440800400c000e103026000344862505032400d48032855440403100303240c02083e50040b1200c0d03420f070490240d0f0340707081d2180355845082800510715116840c02e85000d900c00c02018540007503940c0380c240341030100802070f600407004030204071540301c900ac0c000c060302c000f81102c044000414403000850001e1000c19464404d90040030309070305523420400d440010b0000050010007042d40c4108460400780c585181c04171f4007900003e46004281541019190010300401c5404292020440160f8400d8050318950780150041c20300e621000c203159042001c0e20071044011043e1154055280c01d01c6010742c061024458102e00300d540b400704540a12406004605c140101500300c01410400d140c02039045020070b078410a40025080500e225102c0c45800c00d441c45101c507400460425002541c110449030041004c440000108843c030b00000c1080d0001e014120108100d201d030f905005503040156198142e241c0420f40503076844500007410780d43e40c0e1006440c140726050001800602 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 213911420 1250 213910170 213910181
    0x3080411060c0d08090111190f030b010c02090a150f050108061c12020703020402030f09060a0e070b07140109030e010818060103030507020120010c030b012109020a0801020a031b0201 80
    0xb9640c090318121140381c1055030b41040041840166540340e080e01030802da5500d00410381f1903c0303020105030200d84450020000300d040800c080515241040740070640e0780000502c250070340c0c11908407a09548429403500036040c0280c9000d86040d0b8104085102d400f00082101a15000c3c0d841e40565a156410841d1400d0300e00b081d07401c1d10714141e0340c507000725010010b901200070480c01181c081c103690764049000c99004488505401400c20b0910003400c4040c40101c0c0c00443c0c103641071002c4184040165143c11092150144805001500000b0050b6442c2d05800814807400208100111418007420b1a055019114009010000010100360382c0d0000a010301d800c01005254aa0031507409440c0790303011100a9040c0407503804082c200b02c4121540d51002d49000e0008124940c0081003d42070341c00c0c0c14500c9041c03014945181040d2480e075040070401d68003000011858442038004281201800e800a01e0154000034480300c0d50b50701a0042040b031001e4039061004c50030821412400c070317003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 213912670 1250 213911420 213911437
    0x1060815011206090c21020a05090403090b0c0c0a090e010b0a0f06050a032a0e01050c060c0307140a0201090308010b070f020108040201120c180803030f0a02071e0308041106 76
    0x5840c10b40420100fa8240c1c4403c100d2841040c41310245910b8055148060002c5407401c02600038030000c0e00b08500306400358078000d05090310345030002d0625a50150190000e4001c0d4036503540003280c000c0048004002010501d10087e000c4e0b28102d0f21200d2090240001d800c41e5003196003001c0ba0440a4200602d078042207400c180d240c00c04c05070425404492690003101d4050806495017a010541c2d00a803d40d40704841d0f0b10151020500d00040001d400c1030003040502d8148441800044035142d40862242d510107116040307299070390349100c0c007540c103518111000d105d04180444c1950303000e9015482822100c0c040e8031460b0240c0c0e41c0740d050461520450000800402c0c0c143d6007280154026058503410a105060180014029646078401c5801c40380801002400440b030481101071041c6040000d0311164024524500d003039900001001d002500c08288103500081c0b801c2032000e10702c103c0040e20090800040803c2060500030311807803041c2c8041e1101c04120064034210720b4580c00301c4901c4c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 213913920 1250 213912670 213912689
    0x50f01140a0c14010504110306310602030108030a0905060a050a0804060b12150906090c130f0507050304060e0d0f0309480803031321020106081501 65
    0x21004611060610707080031a104080c04141d28400c40050b001e00091a035400001000091034a081d06100b501ca0700001105030107038005d0010301603000088550074803102c0030143c40320410410450001c40c2c000300c900010f00302a03c0400007050014000c00101189120ba580c0c581401d600c4208012451040c03d0f00740300414402c200441000340203042d1b2a81c064002c0000040e400f100e407021908038480302143c002150020345c0d1000408114068240c0c103e40c450f00208841c1c0707481820903070380c0c0d034481c01c3d541d01c40e840b082840c0007408800d41184000bd0071020302440b041c01c12050180040d0402d4900712441410042e4880d4000d20004824414050b03694030f207984034245c0081540104221801a2440e801c0030040441c8803a400c031440c071101e441d804441482d14103801700c91405520500c1c002c0300c6011406800c0249000020649800400307901c00341036181510310344038070050784e104498038010101b140d00303000f0f1a4040d44048105e880707480540f44500b000382e40040070000240240c01c00c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 213915170 1250 213913920 213913937
    0x30a09081c0215090c04060602070603180c0302121207031e0c03120e0f12030f06030a0c140609030f06010e070e01050403120c02060d0501051305070e100212070501050907050f01 78
    0x1240c10f140c0025005001e07103056510095810010900365141904070801580c001c8504000d11580761064207541c3c8040e05081c022104141d403116810300c40c030b20010f84180d0302e8030b03006000f81c08244a1a421042d4007680603503240510300e00a0f040441014020030500c018001800e000f5010b102005821a49640c650303400152002030007000345a1954052407038460a007215450780070400100a0031206180b6090701d034a410045c0071100c503030007451140a034211840580014032016100c07025159020282c03401c800d10300e00404c8135030107000b0070aa854440c81402c0c1500003400300b41c0700e050321a104004d0410baa506403090b00d5800c83c80c0052400580104030810200c0c0c0c1422a43d86101098908490091000c4e000124150080c1001001559880d00104098500030b010801d000c003074001c05000030314103000c02809071804004214060800040c907254240c1c400d01100c1a9207640c1e10f02c6580b280d44600b099802003c007110400c2180c400c2840101d4146002e801c0c1c00348144050307440004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 213916420 1250 213915170 213915193
    0x10507080925050a1403061005010203120703020909012301080907050105030903070b0709080106080726010f0204060e180f01060c17030c0a0e0a21030908030a09081c02 74
    0x4010082107202d148190124a0100c0c2a540d201594001005c0c0307806180307850b4034880c04160420601411103519503071609402c0255036000300656102000d00300d0004003035a56060140c0c083e00c103d46032035502c1046507001044107002c110100d16a41d80900d000c4011028170001941e00d044d05460000e280e0388554001c00496201d1002181d010b0500426203061140603507030303400c0f10310b8103031800130120300700307000600402400348106030003801c0c610010a40649000900307000b070704840401000c00150781e801945048000d401480d40d044072034004541d1203581713003001007204150381d8019101c1c401510708035070b03000c15140e4071a008601d904c171502030503440d101082c0e508102205003180c0c0510042060b445100e00000a107115000b4007500d10b694044000d0014010421490114442d01c401300c000d0000c4040c149984480c054125107040240e0344504042c0e403003081c0d0742c0c00a0f00910000840751106030b800b007001e208aa0803503003140c82c44040f812000000c4ca1007070030800010b0340309001c00302 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 213917670 1250 213916420 213916453
    0x9010c0c1e05100207030804050d0302070b0109110c0f0c0a14060301091e09050303010f060201050f0c1602131b050f18012a050c10050d09020f060309060601020105070809 75
    0x401c62290048419040c1e0340b0164900381d80213140e055011034016001c000a10a00307010340071400743e25142c1145069841d83d10244a528107004d01d0441d0f550758020399001c0001b0710101d0300341401d80c00440e1440c06210030030307598480e100c054240c0a46941c010002c1e40c2c0c107800940d5003442a00a01c80c604581c2400b14060017001011182c15420310281000001603105124000800c0d0003040919a21741c106032521000440c1030344400110ba2606003000350400022003a44c0d008003102580a5a0310014040d010051181d13500195210b84460191814400158821400ba50102aa03007218402c011401d41d601e000d030414034100070808024a600300e000e0040c4c42258014141454003408203e40344600c98184035107441140244040c4210061000070800c901050b80100c4e000e022a000d41a07000b4050300a50369421320040d213810f00542150780c0d032885449901c0018000a440e4603200c15042d580d04001d0310185e004d03500c1c200204884c0c42c1300e01f0780e10303100308d050344000d1659101405000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 213918920 1250 213917670 213917723
    0x2091302010c020d08090102010b010801060f141909080111070203060114060d050a0b04051f030318120c0f09091a0411040513020405010b071a0702070302150309010c0c 74
    0x100c1c10400b014034024010b07070701e126a0452050080188a840d0342d1018006402c4840601016051060010040004690201803884001d101c0d1a2803500c640d00000c1c28039450080b50103688001c403e0700009024158006070300012500408000d0100010503840317180c040c0304a2202a406420003401441420262071200051443c050490381c586004045404104c03042598954030058403124410b02500e8035003d0650030a4200c1143c07a0f007101030040c0c0526609052000509101d00c2030301c6071481750030328243c040c0100400d05180600001307501d001180f805a6020b010225002c05202007440300451280d2035040b68001d003844180001e0798003a0100700300003401147c00e08030011280d106603c4e14001c0d64000e0324070750900c01072048188100b109076901608441013040d02844000081000444043d02c04c2d0455004881c440c1c4454000b02d08006040e003003e03401800c0c502680c03644402c01e5000b0f5200301d0f9106c0c000c121030000b00d041266424101100035054181a105410703001036041d141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 213920170 1250 213918920 213918923
    0x90213150203160b0403030e0f0c010c11041113060f090311040e07060e040606021f410f04050a0206030702030409110301050f33070501020c070504110403020913 71
    0x450b81030543c2c03030348801800e54060900700e680c009032030140010580c16000d005882030b0040040d141409441c2810b941d103050280350301e0704000032120a0320a0142c2d62081c40d043c2400601f041c0000c04400001d100c1c1640b1601070407154554205000850912490482202e0503469032680c0c521482d540301e1521103440e0a07605540a82d0b9080114091074082042d20000d00407a10b510b40c0700c4910308100011521960700120954000344c0030248c00142c0c850b0302c40c03c00c9050410001d140d48031182e1004070030341d403810040c80c1800581002d28100c100c0300104444207102803644c4050380e407a0f41c850815401e0a0724000c0c100c4c1c1c801d1910000525001d006150710590600c1200c3c14030f6550f155403400e490701303070000451810000006003d01e04051030f500314a404151440c0fa03542104903074049212018101a00700c220507410551030068214044509164000d00255150034100c0003032510b420b103a1181600c00c3e03150035400821550f000c81a6000c0304d400929000144d90307020b12100c41c0c50003d850 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 213921420 1250 213920170 213920173
    0xf0a0b060d0c0311130203160219030503010e0411030304080a0c06030c0206040b0a0e0d0302071205030c030c160204020a1701080c03030714190b011e1a0c2d070902131502 75
    0x40341c0e85e041c4051840364070a001811107807041000c020b4103186116000e81220fa011030126004650424100c9045980540c40c404c03144c0e4071404c0a41186003403a09096042c0030005002441c10000100220760a01440c280028a17990300c01c00d0702201c184013400701c09a007000b40003401040c44210300a902c11004040403411042440c54a0300304264081041c001c284d001c95000148610705c41030555054141c02c003203266050254840b801c500009188401082c40020b800c86c0700001c000c65040aa030380940309540303c0c2c14501d00501280c520328000c401035140c00d0000260100c0002e1054207181c2c000d03000d940381220a413500b9051419500d4142c21078410990442c12020b01c15021082c8180115814030165052510058014414110007040705002803401d1002040d001e210000004402007000ea0741c064041086043c544004c540840720a540d6900710030701c041031104c21200102e150306699105882c0c004803000c900545a0300e030840450b404040c8440100c4200c649140d03c01c500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 213922670 1250 213921420 213921439
    0x41508011d0c090102160b040e2a0f090a09020405030c012c01110d0207320105031306060306050117011505040b0105040e04120806030a12030209060405030f0a0b060d0c0311 76
    0x321b00565188407603000c4400420002000c01c01d01040c05419500500180504614603000485002c99410f22400103062140001520305450501104076400940040c280c0c107042c6079100e00407c002d4016120791070080c0201e1403001115845003088070110003002042a20941041d10445009920714041c43d05000062001e040381c1c0c0000c00032000441880d6001700800e5041c441c400040c80310088561001101e40c503e03900d00d0102c0d0307112086150314286440b98070703036607213120140900c03007a40c0005d03007014901040441800740580205050b1104070180d1081182c0c405403803130803503100000da43c20219058806102d11b14281e001444040d07014903101d81400d8a480100b400d40105880c22a038640d66586403203001c070381000701c0c41d500c844100c3c098042c540d420b842e20550100c07002c2c0c50f10200740d40091040619503502080d05c1c044d00d03016040743c03820750b01c614019558844452003503c03000c40d28000210b0614146110004d5145e03c841007030a81459651000c0000703800c0c12038194003402a0307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 213923920 1250 213922670 213922693
    0x50f04050a150314010e06040c12020309010c030e0c0609040504030917010c030b01050a271502060105130509030708070f0213150b0c0c12070803041508011d0c090102 73
    0x4024500035000c400904148403206400180440fa6407844c43e4040100c4580100240074003112003e501c44401c0d100400c500f124900d040310005030b07095259203990f10200500c8804541580106290300d00c3d6142000300480300c5e50030350740d1901c03400e03180e50340001c041103404102d041030781046d600140b1a041803590580c0319a43c1d500c010040300064a6141e548010382c1d0781469142c00b030f1b034843ca24282400b80c81e0081084009010214550b2010031008900505040c1041004203500003050740b5155880c000350a541c00035152270302886054071500700d0b107084003010301c0d1610825000e003840000441c0303400d0003652000b0302c54208100695003122001003200150319071b103c501609810b44940041d00a07e01301c090300580b00b1a400c0a4040003042c06003256100001030300810030302c070840d0417217107020070210362a203010340c0e0f5003240100e40004200010b91585601d411003600c0000d4480700e520303030380300d01e0710701e19a944500a1b68201c240c1c0300041611100e00c20014085948188191440d040c0c1c01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 213925170 1250 213923920 213923929
    0x70923030a020616060c05090105090907180b040e09010e030a0c06090b010e06091501021018020409081c0c020309011b06151701050105030a02060306010c14071701050412050f0405 79
    0x1041e41829060141c0d003840d0301704142403140340a1021359040c4681840c080e000000c0a034066012110300a20218010bd0001401203004442c9006100341c3ca4094503207490701c159068000c5d21601081307005580100d025900c040c0100c0d0f805d02c41840045060041148007116085460304066982035510140a0040750070700902c90301170960560801c1140c18898140122448024075000c40c0000d404d8980b0406da0340854880d200008a81010131006068180c0c6880c190314400000d5005103040101420421070340050a840b81103c80800200c0e0901c0c104101a52800e40c40300c80140c0003000074888a40c0141d48040301c0ca074189510824030649941c0341d07012241ca20000360b0780b05036420b004202c0c0111082c9140c90191041c8024050355140074042542c40300c226130700911a141c00320000d000d507442910b031540c6241d00560b07807840f400302006150707884130070307500480070310064110004c400004140181806a03504c040320241032521054100c585412240f1081c0416038104000103090b0368 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 213926420 1250 213925170 213925177
    0xc1c290903040e0106051201051e0909010501081507050301060516050f010504110a031502071a180c011409121908090f04060617090a120e0306070923030a0206 70
    0xc241004541d9641865000c00e00100141d01100c1002070070880048000400c0b08a1411100e05881344e480c0d4141d0021001d9051800342c20382500034080c2800c001b58038005400a5040764139000c1982c90030100c500450441000c00c903642d1003c290304000420949105000500e9000d4043c140c0d440806100e07a22642846140e0218503034603034650080c0b20a004231180c2591542d403003192890501c034a156295941400a0384446c4416036010950b0001d10000c580444086043e68020010600d8226006181310180f1040550144101da40741c40495006018101030030b03510075403013810400c40b101001610320005c00030301c050303000f840d15a28035100011b841e00b90b020711a80c4820b443e420980c09009860302c040082074451410981c0403ca07035034028600602903500200d03050796a81c0da180c141880d14803890002082c40340001e003031900b02540310384004107178a42181690025219460200c1c0c0301011406100c00025a01509401032742403100380740307030b40e08000d81075403440c60035500041c54a41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 213927670 1250 213926420 213926431
    0x150a0b040e0712290a0e0c1c0506061b0a080a050c16050904021c02031204180606020d050c011b0806031005070503130f050601030809030c1c29 63
    0x3010140106140c000e04000300c01400f00c80f08110822280c0b8800240326101001e0030882c520344110307040151a00100f91001d01600500c540281c1400d03007000f05258426001c1d20002c04056009982110460103114069100101204d0400310501080c0310315000b8a909800c0700d104800c103400001d041003002e00f00301c6241d0f44a5a4880d408101242d013030100c41e110100c032907022203400748003a988045040784c1080d01907410001495094080391010410100e0181d45489171064200362021035600410a03940740009103207000900c4200c290076600980151005030700100b102201451150002d4103200f42200004160310390080c03d80400c5000701c604841c00185084100002801c04110400e0810b20440c0100305c42d1405510042c52404040c0942c01905400c440e840148202564258002c540100981d1150750352071403c0302c520341c0204103ca0090040c48805581031400c00b4070007d40c43d00d20308c003a030540110340c1d941e20494070400c040001145150b6040c0300aca444000030300f6103d603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 213928920 1250 213927670 213927689
    0x6032103020c0f061014030d03110c07090b040b010c021003020309010f141f081504060e03120f011e09180b0906010302040f020405030d1d03191e0209150a0b04 70
    0x103041407650403222450b986c000081801155401e000241c90000320607081d0125490001104400300138950038170301c0b845442104a100d00d02002c41d00810b071754000007100c00203c40030030108110f08015580741000d0710002e0b502c411402d503848603040c0290003d50b07110170010000200080c541c04100100c89607840b00841c0491030740704118048070313000022030202c2100401c503803066281c8440c841d5070380400c0081d0b503000c61004020a003005001c0d080410200d0300c41081e04d441d40c01c0b06a035060204c0045412014130718900700005540a8500300c041c010442199844d6040e0342480d51a101070a254007100342c20800c000d014030003064407040d21a000c0c00004014007446e500d03600400050314440859841414410482004503980000e4041604082070070507145448c0840405800c550604c074409401d40217166664520418103ca25007001d071040484010070b50b0802d89035052140d05080094205d600c0307801290107403482c00f00d0384910103002001450f00d2a100c61503080030390041ea1061a00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 213930170 1250 213928920 213928933
    0x110f04091506020309060403141207060f050c04050f090408090406060507050606030106120308040606090608010c09080307080a05130f03060903020f010b0f0103091a010f0302120106032103020c0f 86
    0x1914a41c55164001c2500d803000710305141c0e00303000040b01c904c0b6520005020130100c0c14407075031700d24050000f071580042c1140c84545031800c50a048024003244404050301030316240000300c0342d00c5880c0039a0199134000e4070b07000c40e80b20150207000c2e809030f003d0010341c3c4801d420311003000c0a984a008600190866541d80340d00d41174a07203045494642d0282c440e078441e90500307109000c401a5a210004503981600c1c14403000c2d116418804014245074201d140310380c2c1040030100d01144150055136160049030785802d4250f80d15007441d074586c042d45100800a000c1003007003446840c4200e010300343d520540a40703050041e5440040310b00f510078503401158240d484600345010716406004d4400440c3e49000284240c8503440700203181048881e2383c2c181803507610fa185000b440303c1c00c08606214000030034041d080b0f50312000c04520500c1144412032040041d501840f54003241030143c0c40450341d0204821031000030b80b251a9403451802000c901c02c040e4240900a080101000300307440c0100c031240074180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 213931420 1250 213930170 213930191
    0x1008160306051f090b040828060e0c0f010503040b06371802030702150c0702030a0b0a0e0712080702010c0203010c1709010b0607140c0d05060a0606081306110f0409 72
    0x1809505600c603060505080c00104880c55003c0754881ba12000003404900801c868940300780c0101441201030240ad00d403840c4107400000001e0b48038840c03e0111440c0c02900c0310388004607030f184800c881c0203000080d11808540642814900a4406130809802e0340203a4008040e01010001c40d42000c44c0703140c04d840e8104110484440c4e844686006d1050a42c80c6140c02100a036845000d598100c2d20703610100b0000e9071062000003502c0c0201d0340182a14084030300c6041c03050128100b5102102490300d0102c002150074000a03509080750003100c0c000d105c1400c5925000655005004164107100031b806200e001660300703120f03a0803415015150ba4001e851f2801c442e04401c4002060114641c1c5029005c07041c5549a005640000d5440111444403841c0c1410050030040300000f42a0000440469201040f1004c5070b10780c450f0361207002c00c0040a80c1d496003151009000c0c1c3e500425650200f40c3c94021880303503000700e50090030400c005440c080e201200341500303600c10b0f4005000d09660f40c04298 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 213932670 1250 213931420 213931427
    0x705120105010306380c01020405090a1503260c06100b1303080306030106030602040608190c0e010807020c060408030703080f01050906061308160305010b1008160306051f 75
    0x203024000c20302e000c00072107051965407402c0e401c15103100c058800b18030403d045040c0529040e00403600d070180f04640ca0342c0c000b4070000c2c041c0d0002c4c020035201342d00b000006052042030b481003803e482d0070320000030301c46072451f140c41d00c0740444a000303041701c0482450100004110040100380c0d0100300301c000c2c500d500d88078201d149417500d160841d55240008120484400c40024680c2c4156500480c1003940c0b503d42d080024014400c03a4401031031503002240000f5480d81080b0f140c0e11a40d40e80c42a400803070300810304041241c002110703903408118150304c20300c4554419a440b07544103110f030040304d41041156000501c1d40d005940070100c5540002422010580e10145598201140030340c42e10295052000103040b01c0e500074412402204007040320003600c030f4249a05401015481c040d102c1046c40004404218402d0307001c02c0d1210b60a1440340510780c20407190045080f0020381e2117612588a0b000064202121403101c10b0405890b80804035007651202e032203150014280440c203c012484a201a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 213933920 1250 213932670 213932707
    0x10b07080f030f04021f050d0c0905030709020a09090506010f030207020105130f080706210221130b0c030f16031d0a030e090103030c03050a051c090203061f030b100e0705 75
    0x82e100465520049201c060f00001543c606080c0c0150108805e8009c6c0c0c011150036280c4d6100f20b5040c4078500c00002c1400e06540242882c40082da11400c40319202c10a80d401c0d180b058800500043e070300744101c030585109070b000c0d00c2140d10524050749000c61a0018428946a40c0c0100b071001c0700740e001c2001001400c00004000704680c0c01c180c480111441e45602c034010201d640c9130481500061001c2c84840e81c44240c2d4889240941441041d04120001c001b00c4101e40b10708a440040040108084103010340c2503901c2200c202c02c0d5840c01d0b82ea40f0f1b0013600400c0011198106042d15116007444034101180e07101e128400040013041c0e541442c0c1002003410b0039034146c5a020742141d200600120b40d01200c101001505400c0c1581d6611000170200d03164070600b03040c0e10402031241042101484940c0101081c2d80c0202d007200c1d00c41d1a8030001180900341d075841606a00f10701c00003000042c0c07200c11000ea00544121102441582d101590b40b04038070129050303000940000f805130344032050110350 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 213935170 1250 213933920 213933949
    0x1d010b010207030b01050904080f0a0801080c0105041202040902131e05070c0309060c0809130c09050301060f05120705030609100c0804080f0d0908160b0a02090603010b07080f030f0402 81
    0x612400740f550302c4030820400180901030250005100050a00c86240112441105000e0200e50340c0c0d14800c1d00102101002e00a040b03960140c6071a19000b03611500070ba034184c03840410440e00300c2006a081000030411414101e8000b02c0503040105801118418080051842d40e0540301031042000d006040b20402030007030042c4800d0703004100100c1d42c041541401e80d1401d08103100c1944203400d042c10203006011150350b11012000e955020000365800c901d44141c5c050300c0b5040540e464204241c00d82c0c8590062042c2c429002d9810041840c00941a5000740b058106840070f00f51603d001ca4204001180d624045501840591111400e01c0c031444103030240c01c1c41c3c003142ca1305095403200c1c95071142e0149019140d00100322070030381045036803001510507440030351241d4510b00d2041c55949500c82050503a030200c1120000b40c55005a4000c481c48100d00529091442e03003003a03041c11442c2c001c03000c20703242910184045c5c00b180100d10000c6019418031840c0c506e0b5482c103841000b41d0899020319 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 213936420 1250 213935170 213935173
    0x109030b072109030206060603040602040915090c030c02120d0207060903170a0b03030306040c17090106080d14040501032309010203061e09040209091203041401200d05060604091d010b0102 83
    0x12007020171741c007007642c070340141d01240d0f6659a03031140d0812002130f000d00d802c02d8034014038044040e0b0503210303c1e003a80301c100c940030b0200b844480e5100c04142d0446080d00c4901c1c0140e0890807100240b84081d00040075850b52000300181055075075150a0101ca0490314201c003c5502658229520881c114240b82c0c002c20300107050003c8100000840d84070700000d0540c1d0b0182d51200030716010b16004034080c0d0408071050981c481503180031140c0c03038003800e114170070340e6003074003d40c403000c1a44c510400c980400c00b000350314a0b501e0103140100440062502408101440c01d000d1445003132210340201040c00303008820000340c0c490400f58100070141c2854202e000e011022110700700180d4071010a102e60080d0101c0d11400b003556810a000d09004442c0540c014a50000040000304800a420f11010103e6440200b281104080c0051f4092020702840d00c0c02640a00012140c80d029800003030703204001400443c02e00b40d59500100030740d0941456202e1b08130010741360042c00300d03092083c1e101a400910 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 213937670 1250 213936420 213936431
    0x71811030c040303082d06100e0303090909150408040618050d0b0402040b1201090b060307052b08040b0306030111033108040e01060909060b03150109030b0721 70
    0x240c5198440c4550721005040c0100741e0000b03480080303c41400406041d144881701801c504c1b941241003101d0046a46520035a1105004010144180407121040b04050001c43c54030901c2002c00020300710061030350a86d0b100d21b0701c03c4001c4685061130b031402648501c0e01c1c3c0e6265400c2c07010140c40b0390196010301e012868003800800c115622110340c0c0c0c032083c1d007000c15941540c641e400850b0107403400708412030300900914113032811140150301010045014041c0c2d6401a21008101601c80300780c1c4c461650f0000840c80c008041146040314031060040c40782100d030b0004415640c251a81c2c00c240d00050001001000f0048107003428041c95007040ca5580b45a40b643c64072044480d04000315507840341c404d660189140300100c040c2d080999845400c030300d40c0c4d500e03569070b541d41c00782e080000d00400e00000d0303105000040b180380f14040c00d020fa40c0166149402c568903002020318106030314039118108032100c3c40020208081070b0649014107080d980d03201c080c03e610882c050310700c0c1c80c002e9031704c24662901c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 213938920 1250 213937670 213937681
    0xf100f0203071d0a2d050402040b03220b0c040315111602030709051303120c020703020d0f120f02010606140a1803050321130b01050909030c07181103 66
    0x40403520386491414407400d900308101004c143d250142c0e03001020340c2c2e5501d4620b92a00a510910031100304101e04008200c80d48072001c3c0000e0b4086ca00c9050b801000605c00b040041c0f036244050f2646404019400c0b0310a000340c0c4483c800c00c60140d4164480c1100003800b0b10910055a08100300316458003400d000c00c910200d001421446000c408104900c0c410b0024421580c003401403000810b50400d06200e94100f980c2c1c059a46400d40e4821004500e1460074811401161b014140580c941600a0244c082c911b07002e00a148944810443c1c240740c4803580359000442034a040e01100034244c1e5204141c035641503000c2e084880a40010701844a1840031b0b00b1402200c0b821501c034010649001c0441051a0300c800650801caa0001007003400b0114403070359103c02595000d2610075601d03000d0300c8280c8480b4200c0d49401c1c9000f401402d40a603050040c041801e21101140d0042c075010f00300e0780b8241d080e16080381480c030141c0241c01c0d0485c000c0e5000713115402070300542c0c3ea00822441e40301d00d9420074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 213940170 1250 213938920 213938927
    0x6020f0706050f0417010606020f0a080706021602040f060e0c16060b0103060b0423040506090a050402030c04020c010603050d03150e0901091a06090a0227030705030f100f020307 78
    0x114881d04041103400516030021414010960780101013040d078081c580c1d5100081940070300824016140141f04510281045030000100324480c07580022105d4502802c4c3d80302d5501948c0880c011105500c43c444040005850b030b482a903442907588800060014140b1004010092001c3c1030a589090240b18031900d204001d40c0000180354040e4000450360040d41c0180c02815a9600c0051007900c0841c00040701842c00048000b0311480d030341200e035031005600810040b40c81c113503882c1d41c0159800300003034004c0009602a0390403c1c00142201e1a60003464000340c103036800103070031602c16510740008004000082116065002c1182028407500c1070039080018500b40d80c0c403030500100c0302035010816505081d444071092980101a84891a0481c0d4203882c0c1c0403025254a8011020180080c1072401584250b50040c4548080c0071208070403001110a114600070746d0f83d03494080c0046c002560f90f010000e0700804d141ca0009031103941000401c600499081101e13004a1500400410034850760 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 213941420 1250 213940170 213940183
    0x30209150304050c0102031c0207110604030309030b0603240a091b03030e060c030304031409030d030b12010e0705010507020414010e06190e0711160803030105040b0618122a0a06020f 80
    0x52823801070b02d846143c00d03c8100070741e804021031741194001038040103055110b80144182d902880c1150001e488000a140c0e40302240e90600c00c070060307a100c020303031000708626499410107009500851140e001c2e072100300f001c0540c2c45915a01c3d03d81103104108068221112a1110001702c88890804500f601c18540340d22001344000c00300110b00c2c03401402124400c040c0c504900f40078040320b51411510b88068024141400ea040c0b00e80740030604106803200501450381500c2800014100d09460a801951aa0840f082c22a031283c0c4a4100c1c0d0f044402c8012028000c011580c9e00d0f41c0217040c21024446035941c003481d40208809110018052800380051241c2c01c5a41840e141c1c2a580c0b0740c80070f2034100003c4103001181c2d104107400000e680a00000523505995040b54204407020000e820451244141c0128075540142c010015485140c51650075106803000c20a6401200d1140d605030f102c0d440b140e081620a51400344c1c0c1d0326950a200d607640000d00007500042030300c0007007035041d29542c88 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 213942670 1250 213941420 213941467
    0x10c0c0b040b04020102070b07060c09050907020718020c012a05030f0c0d0209190303081e0f04030201060f0801050f011202060913020415020a120203040f090b01030209150304050c010203 82
    0xd00b001c2011a40b003005000c00800003042d6003516000e0624202c40506803020501e030004400b0000403865103445284540038030301c00c0d002050602d01d004102c14a03c42ca2200941c121a402d1001d60b02805003030044103400803001c280c10010314080340f0400fa2921a0314800c808109080c020450240b94011000381c0281481c2c01043c0c4138200d034403010000e44070714102c803a0452451300108111045c0d1581e118261391183c0c540952560f10600010600c4000342161083d011840d0045046551012112a0032501920000c101c964844ac109001c1c0d20300c9912022072030b0354450800400c103080300c80c0c41c1d0140c01c000d042d80c10304002c10340025820717000300c810152149030005100d41d100d40305a81180c0081400078a00c4582d5007400b0300203500c9030a0700d00c3c10b80d00c000c030003002c940c14540701004440940c0d69407079002c00700c1c6081c8003160f001070001c28880e60502d03600b044150425a9100750040141480c008195030300e241c02e10700a42441c000e0601103040d507000340032031400680700c80e07150107655 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 213943920 1250 213942670 213942683
    0x4030903110d1a04050106050105130302010c08070b01080303190b010c061a130e1605010804120c0501181202010e031c060906060e03070f030b0403030e0c1f02010c0c0b04 75
    0x10701000021424074040700c0050010381e606400310000f5624407500d44c0f043e8019002046203650345c00054915109800d641c0941e4018400203000540c0612100d18180b40140f5485040000580c4d440400c2c81c801c2e0411031250340040b0400203061101403103640c1c80b0004040600c21f242c0d1500c0042d110301c58228005007400e0711800590300d41c2000e000e00a196000060404540d11180b0b4580c80c02001441d684450702d002c1c04620001c00d200c44490b0744116401071713440c0d0100399119220401910341c280354010800c40703c028171501040090054000e10780b0391080141d40030100e49031030080382c1c1b40e484881096905200c00360320001408000d40c0c02186643d1049452101c60358031040040100390020403115290100c00b244007a88580044081d910650480f01190f48815064010748580d01c0010444540d110000e40068801d41100864449032411a42d00c5407041c80040c40503000d40034407801c0383c1300300f503050706005a0900825240380060305043d071410f407003030301c0301491041e0040028148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 213945170 1250 213943920 213943943
    0x30c0c122d070f060b040b0904020d0b04081903060e09011b03050a09081303030813050a0305090105160f02091602033a1a0604050d0201080a181401050f04030903 71
    0x4850740841110021640300c2e1040c550541245080b00043c20300c2c1031450301861030504151054144404030314040d03a0001c105800614195444484001c8003c108940c15141407001e05482c00055002c050390b801c0c0c90328040703400e60503c0d40310040c5c01d80081c02c199003030707041c405640c1d84208a00d408901c14442c43c54080b0b8142e445038000d130003400c0543d80c0217103948000210039032200d041091241c00d0724440d03901c20032030751101c03001480e11032102d81d4054010740184c0d411000203402040284020001070600500b40240280c50302030504007400c00740d07190940101c55100310711f01560340c1584101031300c1844008010a0400070742e40e0090000d02044c40111a0900a80c00c11201c6800c2c1c0c3e164412100001012030401a000503007804441111940581d0210171414640001603806407240a0001e41c0306003981c1d00116201803014007035188890b0b641010f1120b1030403046403600d4980c0500641210310400c0101e4070308451005100034010701109041c072000a40c8103807032208490300081460344 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 213946420 1250 213945170 213945247
    0x207020d06200406020309030d11060c03060f09070c020102060f1003021504210309051012150312180504110f0c0705270f01030305040b0c1002030c0c12 67
    0x10080700c0c0070002c4881d002c0115000841c02e84c0040140814a425415600704904011064804a000d218080b81940088000a203205d1005002d9588164011b04c04100850300c0004500300042c15200c0d02c1c001030340380300310f4820765804010481d08a44091740300103040c42e045c5858006040a400001e202c2c044040303e040c425840f440c147e8018000c5821078624002c03507550170900c114208501113010504500340001c082c644104620024440c03a100d288020040e443d2030b20041c0b00c205980c0480e4540400c1c08404030356a130030408a545255107985940140c01000005490300d80d9206900c20746c10003e840d1803d510140a0350301c1c58080200c0d468542e68031580c0a810700c0203942000b074100c00251020340303c00c06008440b5034030048600c1030b4201525280207003030000c90240000307030210b5401c21080002841180003031580c1c442d02c005460ba844000c11400c0281c1c2d0041e9840c1e0221040410182d00c03043d0148446900707401091441ca01d4012607080325031640c15429030f103003100c0c03250503031044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 213947670 1250 213946420 213946451
    0xc0b060d030309060606030624050a031815050709050d0507170f1b130209090415020706020706050609061f03051308070c030507080c130213050909010614040207020d06 74
    0x740d03080e1344104217008080e21144000c0c014041c5100c3d849031008401d030100060040a40c1c1207095009d566950352404c0c550600a4000c2c00c0c070100800100c0c2c0d4600e40c083c010440c903501528001407070403808202814042401402c00030160041d605c2540c00c00f00380c1002510000d000c0b021103280d12803a6011544502035207003400c566450042c554002c03400d00c200540105542c01088540407941500001d11000c2c1100481c020416103a410032854008240401d8020102c2c0100d00c059650242c0b401945968140a0fa003084c00111030413a207650611a092600e514182c1c0e00001c207840307000a0701881041a21022014002c507070a040c2d071040420081c10a0b41c0c0581d4649422045c01a541c025614280601c0a02032000f40c840b030145540120781454044dd006000040060041d0480c01134060f07950000e6000404001c40180200400201916240b03a403a01c120b4446000191141c504210103848050024083c7d200b41e10400c584001239a510001b0441180c04c1600060081d50103190f11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 213948920 1250 213947670 213947681
    0x12080c0609060106021002070b060f03011b02010209030114040209070e0a030605090f0c0a060917150108070314010b31020d060603110306060403030503070210020a0c120c0b060d0303 80
    0x4216900412003002101580050752a048511681c00c030350002c02c405620301c04038003825078020a16907020340410780610f440d03c80c0d5000c1da40d00500001d0f030b88083c40300440140c1a82d61002000d82d40101d900a22880c0a1142d0004103662032214401440c040e40010030b4110010301d82405e122040f1403132182c0361035041c9190b01859016a0400c41d504003048026a506041119a182c6100c0c01d40342c0509420940040c03021603505031110600c3c80d0030900002590320b03940d4100300046c4905420710120f800f80183c042c0c000d0294002a200c003900b50305104e5500800a001440541e0504e4031081c0c1d561030344100038103080880010b0061a40059040c4900140c0001048611500118940205c08041c0d44282c04135043c9840c10010140ca00f01d4010140c001115601e6021805100420103c1e01401c001c5520000f50310546012300d0210007040100e8000002c01000103440c3d4082c1010010300000b0b4005c0000b240c2448031851081d40e4403180b90a030020515405150503880c030004260290300403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 213950170 1250 213948920 213948937
    0xe0a0605100e011218261c140f012303072d0b031006050c0304141801091b02070b030a05270d09060503090d0318170702012d3f05060609030303011208 66
    0x2100203820400c03401c04c403a1b5000e0280b90f4040000d140f5802c1810710321402f102e5040340c090041c1c06803e242c015a040701e50070440d10401d01c0d461102080d506040041c2040018145c1294150f88a00341004203e40300c11a40e0041010b00004000440000c0c00000a640803140031090210f006642e0001280084108280602454001c01d00204100d405500301402c507131040d0484100846d981d5804a940d160329106000030080208042200d40c02d131a089107a100ea10055032214082414090001424040413108215040f00707030324404803580700b100d00380140083c0c5001e40c214142551143e48440c4229a100107060f510100300460707180074815403002c0790300300588100d490908140101554082c0c102280019041580da124150703052001d0550440d981ca0201807070207889005407454602004d40c01c440450000110f08045803a500b81d020004142c40c0e40d01010344503087d0001030310009004a440340505004c402141e44000041d00e0445e42004100349410249013050182ca01c6840b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 213951420 1250 213950170 213950201
    0x1602091e09060103030201110a120504050a0506040f11091e0406110a09081c12020f0403060908071403041a180d050303010e0a0605100e011218261c 65
    0x4204000d075020500c541200d00940017445015031181110f9490710681c4905000b09e5006c1002584400309680003d920500c0341c1e084841c0041191242c61030210100c3c0c084031340c25500c114007420082840d282c02c0d8000c03400d80e8030400ca41030a210200b50002131200550440078018001000d11200303030010318004440202c243d80d0b4031004407000b002c007100c1c0c0c003a0038000d03c03c0340504121034140c141d100d071074640b940d41c50300c0c2904401000a400f940c820081c0b040290418000407020a20034483c5120080c030030f01651b81e0b01c65892070000e0f983c07404400c1c1800560002c1c04100030055140340303400f03041010fa074803050791098003000000c10035071410481d039084a990090303c020850004000c3d81a2401d86c6202c0c0d80c10350750155040d0599030a80a1b0740c0d0000c40302c0b0b00c20880f0500441c3e041c5000541414106000440380d183c3c01c040b90130280400e1150f4041041c80350500503091134002100ca6a52410201c44181d107243c0781c401d04c9046940101c0daa01c03039941c0c603103e5030707680d02050300e0801102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 213952670 1250 213951420 213951481
    0x18020a0e12102009011809051003120f02190f0b0705070c080a080904020901030914010b041113030f0c08060f0a05070f02060601030522060c0f05160209 67
    0xd10255892110420b060400c52429030000c01c400c0580442d01880110420700600d088581001120783c5001282c106e0004101d400b0089560003c0780a918425541440708801161960a2404054a136030044000307102580700750311b409981c00320746201000415008007641c0e0307a03607140c215a002d00391440901914507400601c1402030f400707401024050b006c0e82e110188240c0b0f030709c0b207603450302000700303006082003010850107130282450380203081251414140080d10204039115041ca000f0303910400d14050350764044115552a1911a1040c1c0100099103942000c120a071a1240f00d840c5e07000251161135907900f400200110000c5410180586109440c0ba508001d040d403400c001041d5034a041c45802c2c8800a01034030311a44001ea028000b0358000c2c6400c6d100c5800650040c10040d2002003d21a500c906d007840c1d41d100036044020510501001a515000c420300518000c0700400c1c090400ca4200311513a400c0c3e0600700c00b0a281e03a01101d10f00525110301c0046118410115001c0c03030301e0f88401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 213953920 1250 213952670 213952699
    0x3030f070b0601090f0608010510090e070c051c080103060e0a050a0c081c082809030507020321120712050106021b041b03090501021b07061818020a0e 66
    0xa801c68016071080c0c84500d1030b05d880c0d4064690f130300316a0180c40c0006105000401036031906081700d0001c3c1c407031400c0c44203403541c4070005807608540889551f4042601c5001c001c0802800300054810282c015002c51608068440018060801844040d00180d100d5013240c411040904c07034000303559800000c03603000f61070610b440d0312841143e05c11440c050050201442c80e210f40ba140c00f0f03012041c80c0c0e031880c60b0307544c6042c0d41c03400300e44803031040d2151401c0c0c082a62041015500c81c0c01c0405003e91500c0d0380365195031040526003220500c2c10102c01c0a40c0791004c901c1c000310015100441510714070950180c0d40c1a10840c1c400300c1c60070910712114200b000018031030b80c000c66841140b10a0100030a1111000c4c01404103a07542444900c481d84100c003800020113100e68004050a8480c400140ca002150841828041d0410030b00e843c1c5504448030401500c0e4000c10007191012210094501491600b890a40e0740049036800104c410740005406070024070803100c5580d01c000007000409902c0d200e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 213955170 1250 213953920 213953933
    0xa0303110f070c09050603070302180702010608030c0304080609070602070b030a020706020304150e0c011b0201090f0303020d1101060b0702010507110405040b070f171f030c060806010906030207021e03030f07 91
    0x503110740910245445c000c20064200801c040003130385d070003400c5500c00035100d1041c501640801000c44007155030f5001d000c203800c1030600c001c040a2007640300039030700c0f035003415682414000090b09808140e0b1201100f0000180c01003080812200e25140c019102d5039002c101101034400c0000003031840d8800020001041060044001c4070002c40300e0400c1040c4048c200c0540d0f6403c09901940442c06d42d6482e6040c1000070070680c1c00caa031040c503003098896500c1080c401001020303001180035811403400c0b441400e42c800c00c5202a02c815100910520b0301d081c404a0181c402c55501a0400000007410800c0c00119103483c820400082c200700020716140c188054402015103021000031100920603954034410242038942191400c0c62801e1622410102c41c41204400c030151200d034a48600000810b00c464010710003800b090311684040d01d08a000180b401100d60401000e1510600c04140561550b6034240d04991500382024046042c80c2e0000b859402041c841200b0744070001540000c0115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 213956420 1250 213955170 213955193
    0x5071b03050403171e0c0109020603090102030a150b040303050a0e03030a090e0a020705030313020f060c01050114090114040507110f0318060301240903140c03060a0c020a0303110f07 80
    0x19801c11a00120484c0c9083c0307075120f0740144040d6000c01c450916000b0a01d00f005222450001000056124943d400f0072a250070460345040c2c503075030110420680741013500840000040501c0051501e9003004c031105040d0190b40005020003801280000c2d54134001c1080101d2101e0080c2241c2e21038080120080c003101c0d060090b0400160148081810040c150090f54500c9070b02401840c110b41c0c9400b068020b11425078400c3ea441100a210240c8035201e02c4024660404200d0010540d0360415010400f071980c6c000d00140901810801081120036a80ca00c0029550468012500351141c4000b1100d4206501b03030521107008140b6040300e00d86000000301410b182c03c01c841110200c4401c10031200340400d00c2075184c40e9080c2501890b070b02040c41c40ad08070307118550a04000060300c0341c50321861100c01820095155001c420350400741d203030030003260394000207000091000c50002c1e40020744036080d01800600303054a41000039070f80b03401041900d40d89183d4060068483e00c850404154120b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 213957670 1250 213956420 213956423
    0x20d0213290117090304030b01030507030519080a030506120d020304050a0b16230604230a020f0d03140d020306120703020d0213140a0c030e07150305071b03050403 72
    0x70050841c00c01c001058008900360344058481c80c41100c5085a140c00d04040108900b1481c0810440480001c649458850103140284000d0203078500b5850f1451804806150000d8482c1107054040c001a0390340c012140001164980810343e501c2c0d15001c1562840d078035440e05c0082c000e82d4909403605074000040c0c0100e480c100e5070310144981c0c0d80c000141521a04410290700050b1642010104424640760050076024080707410842c4e003001c0c1c0c40c0307050000070348080b1010801b2449590070207400d80d00709520944243e001e08105d12850740002d102400301181240900c9207152842e083c54019140d0006854540014580c5c5258805104009500441d01c5512808410b500b14101d40400625001581e50103001245926060703002c10025401c402c0700031010585403040000841d00030030704180030750224080400c0003c110380e07010302a42d03040800e09200f83c0c0040010444070307600c03117501c003860744140c00c0001e0251910740e821240d5404081c110035440003100010400c040e0b0040c020821a03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 213958920 1250 213957670 213957701
    0x30207020d051c0804051e1c050712030e0d140f070c0807080a0b010605090f04090302060a0b0d0b06040207061d03030402090109020309062701110304060506040b03060c07020d0213 79
    0x8081000c3c150380c200d000781c0700504a5481014005e101103c030b11b102550300c81100041340c42058215402c40c6204000c0710b5441e00051000c1052820000c440b1001c0c205400503050510000c005001c4a035561a10018458104125103010054200e444412141c1400303400d440c3c65621111414440340fa020fa5200e56440c078400c0c06800582038402103011710400d54840c06030000740c4d2811000701c980790042d0340f00079807041c103410124050b40ea40b845102c400c281703e60054080c928084140303108864140200e01d005400891610780003d401030300360781e482001264016101c01060034104000c00f420214641c49154807800e01042050000c06948140c0c4201c8655145a80700d04105060740401c0d60700c0b00c0e00764800c0300410003522022140641c844400968020005d0100e04564203680b20664045240e050000a006c1802094090b441d4081c2c41031341c1c14402c0c0c20244000c40d54030300c070081c00d48071604800710318075086580d244c080fa030555400a0561515035840c8200600400d001e00e200b0081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 213960170 1250 213958920 213958963
    0x20d0518060c31081c030209100318050703201009030f14011104080c06030f0f1902030f0610032007080d0612140c0a0b0a030207020d05 60
    0x30340d80018072a2181c166618580d061480d1440803022107034003120030944107031485400014802c0c5544610005000c0b2600500901c031201080107400a4980001d00c1090f004100350040381c1c8900004004c911201e01e0001001e507850020070146040c1442d00801c2400354a80000a0007205035170304890280d1040c510002000d1203042201c603070006030880020808051042000c10040950084150f0103401c08007034031040d2002a074210f4005e400c104420700b00100341440461010001d000803104295103851940c100b80640013108000107101401d10100400050310040020403100c0d0069041b201c20b42d100c2c00d104080032039040c021101c1074000c2c0b00700601e20519074484e0286c0c0d20340c0000f8031800c038080310760311034030b100340c0d074001141921505010000030801a40600c21280102034001d44003180c20b820380341c400b4203121101c0560380c056002481c00f040d50b0f46d80300c0d540c00c1100c8944490a580d9140903000b83c000e40200030001e5440240000501d06009e004100c3e01c4c0c800030b81000000387c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 213961420 1250 213960170 213960211
    0x60403020d0c05060c210a06080c0337080a020615180c030a18210810150905041a130c021b030c06030702010f1503050a170d020d05 58
    0x641e00000350019100e6031100c0d012942d590452001050b00f400d02c41d030b03508110000540c001508003800c7d560f040805075070b02400c0106c00d1062004503151101100135001c2c201e80c0154070111841c00071060780c5040c4030280c0e40904c44c020007030b181001c1c0343d2004500340c82d608020700194a958003120006501c04010315000c45a191541028051000003000e444440d00d0f01100c0745850f07040100b85140055956044040c0c4402c03140c111440c0b40d1180440c103008800802c0d2a174070b680c0842131850207005841d400c0c40f0064420340d503488140d860040610300880049141100d442c2d0711640482e0704140f400b80d070b989890702c104d600c0400000e41a17603000d2100d11010034036003c6070b940b0284840181c04c44090160b19004c41c091180c803204005040301c001c80301c40c10000b14994003c0d80c10f00050307951201c41c880d1005241c0103680e20f0301081c40002d0740d441e00c0c5486840d05d0781c5052000801010301004880308500511094a480d4440c00c1021901d032030143c9003c50003005c003512580c440c1c01c0c04418400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 213962670 1250 213961420 213961427
    0x109060b160305090a03050703021807090b090102010609020a0509031506030331061806090e0a09060e071403010b240d021903140f1b0a0c0203010e060403020d 70
    0x22100c0c000c416a282071800880c1c0d44980391001d908808001080100284541d502e00342c2c2000fa5003d04003600c41c0a15600c104070012800750310b0014817052030302c01c0000c5203030880d81c038601320f45511b103209a8801911004030300400003600f264001c02c0c4041040404164400d0107000d480c0300940407101800c42907004558541012207105a043c0d00810604441d50955a099030796085601c0d10b41e464611001c0101c24144030a80261002540c88499103155140051142004041c14141050700ba41007810071021580c0c02030407034003071540382c0341041304002c9607500245440350300d80141c3c0c405a4855451024032034407400c0d82c80c407a6003080142e11041c540b4000c2100b0180002d82c1c40e003942880000f0340140b41e04131034140d0100550038811038842040081202c1c0e501c0e88a60360000c0c3d07041008000d0724034204040e00c20143e0440041c10416481608034442202c0140f940f0f01c15229058140102c843d02c80c1c2280080d01035090071007002906030001344050013244641c00b590b035a00b44044088 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 213963920 1250 213962670 213962681
    0x3111009030c051507060e06041a0105131a03010509031b0304051f09030602070812010b090d020f0409080f030414031305040c0c02062113050714030c100509090109 72
    0x60036207861400c0c00c01c06442e2040c4105502e0301134110b0365050800d942c41d0301e42161085444854560421000c200400c20a5158182c1c0500d181d4029000d6504020105101003414500c003d40140c0e1006007858041030201c2c0300d13903a1031004000f84120314201140584a400141000046d480d0204d07409114640200c1550705a50019004220310310782070604680408107003480c20140012080e0200c0402c40c5800104011b034000c40300030355142c032001036250301910141d01c4010000c1c4280701642160b920104165586601103d654002e00b04540c0042c3c0140141c9030b0080040c403000900d4003081403624051840b6a0040042c6510b0311031402c2101d80302d11850302c0700c0601003803038101070015107003d910010007907400340342111034001e507a80443c0b100d80c09000030110152402607540c84004481054503802403080140078a41119a80c5190b940d81450103901c954290707a55001000d510100407004041d04001c1c0007080080d0b042d071018020746d0010006078050704011780041554160340c00b0f00d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 213965170 1250 213963920 213963923
    0x3010507020d0c02211507120504050c040908090d0f0c08070e0408340b01060914270c070b0c2703120d0e01060e132a0311100903 57
    0x883d0202141c039403c102ca254000c4020290710381d040c0f03880100116003007288010a18a80780801000d00f0142c5000c1c000e10074035440b010038a4180700c20000040c07004140030041c40b8080d200172481e2192494011120b0180700641c0d5007152410f01d030340b401e100b400c1e0300c200c094070301400c0c500c102d81e80c48184040e211051400b900714002803581c0400d001681520040c4012039210901802141480542580003105041c0302c13800742c5018840d1708140403025208900400e024105242d81c2440c03d000c200040401545141c410300301c440d400314044000c003940e00720a010b2807241c009146411008404031360003410b0152048c100d043d000070410101c0a04550940b40c01d00c100c03004500032001100c0950a05001540e010701130203004280c0409081c002d0070000810031340204001020b401c60500715007580d031209140364103070420b00c1402c124040e00082c5140c1c02c414903900004900d580d0030640c4043d441050710b14030140710000709214882511a6090340211050f40b00314801500403907007000107000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 213966420 1250 213965170 213965177
    0x10b09060a0f020304080d0f020607080f0705070c0f03030810230607020301090c03140f0c0a0501050702011b20030d08150114040e060f0616030c0609080706060503010507020d 77
    0x801c0207150300400704200e01d29802e104903880c0135100c124090800300340e0811040481c0403180b001d4080354060081560001462600034010b1400e080d400820340c41c00b40c107440500c0030018518050051004400f8064818000d02980c0e680e079a00d0700400510040740c0340e1020302183c0c0c00100d041c801c0f400c08882041507642c2c14114000c80c850402c40c45511900040ba0b041d03583e100e66200140c2076006140055008101032901c00c442041d01505040c250502240141c0145080c103516075500c0c1101030680f0000e113081030302c8040710b20042e240c0c0d101101e100c0c0c01c1d001021100c642001075000307071b080d1810b001d1500c09425189000602d41e88141c1c80e80b601d0089101d600009101120030601481c40c03135014509040340759081042040690b006400040f040f06410040100310b00b001c0201c0785038010305403036452900c501340010509112040c00001d041000d500c511006000c000c0e0000746203d908035980d9036580300d130b9180c510300610380340c886d0354001d50a100000c0c1c0d000340007107085403c403801e584 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 213967670 1250 213966420 213966427
    0xf050a0905010e0406080a050a050709060b072003100209041103010b030a090501020d140109110304050307060507030f1b0f05180103020f0c03040f080601240c0302151608010b0906 79
    0x15524084188800c43d0030a580e244000380c410307030030010030b0758040c09000038021030270007410001c0c240380042e00410526030504108000105008046580e526040310324900009409910b808400c0e4401c0b94459041c0f04004500b42c4d03d2805500400d240c41c02142c0c20001555101c0100126000034411400081000e000040711618181c101c1b42e000b6101c0d01c0014609035111900500312a43c0e20910700070342000380018050300d40306100c2c100b425000c03078101d40e00354a440c2c1c1d900741e500c0c410b20100800d6140c072200400c0c1c2c1e483c000c0d00030025404038410140500000c01e0070742c52812142d00c0c08000003170300d200000300000e4000c50417a04590b0401c020051800a010010341c083d60140103c184050010031182c3e000540030f00103400901000e40c801e0002e2031078414064900801a001011854a00e24081e54802070030440c00c0540103040c100090001c1d11030509030308140c06080003d038038a80040400c0309140c0c1040640000c04401c0d125022242d0301d64801220b00d00a000515030422404c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 213968920 1250 213967670 213967679
    0x60a0608060f0109150b0a03020405180c1b160b0a020c01030b030d0c1505010801020c0f24070507050d1107080109050c09060d0c080c0405070e030c01050904090507150f050a09 77
    0x15040b50707102001200900240c140c0c0c6e07503940421907000c410203000080e808102882180b4010494245050f03c8075000c09040c107011170105401d201d0741e05503101414401c9403000d140300040c411350400c41050351200000950351081c01e01a50301c458144401401a00803c1c105503000b482a0900c8400140003048007002d101802c0d6907004400005682207001d0b2110f00445010314007626000c0d1582400150b1200c8144072003921784803446c0488000c039044141e00605842904e40c0c00301d202995a01c034080340781c1320090141d03050711038014007070524042c00e0510034500e900040e604c1121003100044071143d03559480c14500b21980d00700c0040143e00300c4610b00380740e45842c0f000c8a82110004000030305880a035501c01c06210240d51140a83d03401000702007249180c280320750b030352201260400c0c000c8048480d000a0303c48501d41003050600c200812003104544075a0320498502d0340c1300040703a9425842d490b940426440f5610740074001600c043c0fa590001e8440d1003500c54a04a07619040c2206050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 213970170 1250 213968920 213968939
    0xf0f05090601091e02030c041a0f160606090504061a0105040501050f09010216090f06140904060c11150f07050c1b0301020d0203041a0907060c0201080c0c0a05060a0608060f01 77
    0x36150034859a80008141102c00741381d2008600908084903c55540ea10b441c90312031000e00c030b86024007152101800b581024800040032282c206c80c0e000307000c45603c401031400200405082d046801e000c2c1c640020001000b003543e00c00e5158480307580c4800780441122004441501c2030307005560001d0b1049c03001001d00c45030000a085030440500580703842c800b440d0300a20494010f90300208605890b108804400e004511400c0c001c1c114031040705d689500c0c240c01107074560001610062649944c0c21842014511a11000d02e054403040c06482c41d5500c01404450155010b8841c00380c5407070498007180c0041c0c00707481218200805e201c040c0030a0905a10111195076603440e0282d055502008440034120781440107622a0b0b00c207030034804001420140440203400014000034403a441362200b0b02070310b034018840e00c032560f0382440c007680e042d65035070401400c82c0070340b4200709190311800081ca0100100411000d01c0b4407020300007001a25524040680c0d181c80644440340208000401807005031300703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 213971420 1250 213970170 213970181
    0x20111010e03070b0a0f060b09090a2a08011202180c16030504060f030b03071e150f080a091a06121f0b030303060310021b060106030f0f0509060109 65
    0x260000180c5031000a00703031400c1d940703c200d04a0300f51907040e08000d0046910303c02c5a98a610040c810000d00c2d0038454007824510800400138425034008001400b4120540c0245181c2030700a025425140d030030360000c00c8554844035031a00414984400814005c0c000c0491048045d0014205d14880c00921259416940c02400e480d0302d0f80000c20442d40098182c41f61a40c8452003665002d80e42c0e03241c104010421510901a18201410301d103442e00203580008110081e0b91001d142030010f00c4142e5983c2004815682c060300d071007101d8040e0030305429000001c0c40b1456089480d810001c1d5180078210088907105000105001d080d80d070703151103074001c0c07003109507100308040d29035a0002e424074901c074a80484000309c0c11004180c42c0d0302180f001c000e4020042c401a0030740007181581041d40002e9201e0348203007100d03080c1960105065031181100e80101c00e60f0341031041550095610381c00d001700900a81844050300500300b0101000d009003d02c6803d101f0720080026254503420442100302405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 213972670 1250 213971420 213971447
    0x1020d08040c171c091d161101020d06080f010b0108090303040f020d140c130204030c0b0d061806140a03080a030b01122307140304140a1707050106050405130201 71
    0x100e600b1138600540c05416500c281c402464448a10a03440d01c0c40825450303c00003950340282ca8590300b4802c00c1f2003035070108100000c40341400040c1c1503030241c51a009006141c409814a428200d002881d0300021907800411102d0750024040c0c140f4613001540c548000340c2d18a070070f80d4004c00c00540420b4640500039011403000f04899074400031603d813056103000e01c0d080c05c5400d0704480300ea03410b03d00d01a2102445209203d90641c10140343d0385820042001c3c42c861600c0003a0006101850400d20b944060080c094480e21000c40010441c540f5000f0300c010300070111000a44245e0305040c0c545620f0740d100b100ea1150780c041c0f600070034100c206d0280040ea02641d0504c0b540160310405403005001e0105000c590207142584000084c0641d0b03500b00d0054400c806200d88200d418560311114001c6a60194001c41024400400c0e003251520704801d143d00a004611500c0d0302e10201402e000060540c0d6004000902100352550300300000c036030301a00d0031211840e80b0700099005501900c0c00c41c0c14803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 213973920 1250 213972670 213972673
    0x503010f0315111902010c0e060a110709091506050102010209130b0109080d030c02100605030d08091f0609140702100b0d02040903050a09060c080a0c0519030e01020d08040c17 77
    0x484020520740554000752115060064054130310222160709200d81050710307400c1d00e424405e040c14440850361901c1071480c0d00701080079042d48500005010804a4000d1002260400080d003070f5003404801c0344060130a1407038240c04c0c2000060b07598414025580c1d990401000740b803041003801d100310010040014100e06000c82101c0000e4002010311013040007440d103480c0400c0c64034858000030305107a10034140b000c040c2c0ca40341042c4655200041c0c0031207048006d00302009203440b84600c10b4034105075808803d41c46650911214618507a68101c0011204850340502684880061400981c00c084806400507408410a4003807002150028a1000006080c000c501e0585170003103801d071002c1c818140d0200b880040c0c40c0d030341310707074481e840c4002441286080040c40f8460780d03a8401900c41c0c41c0710402080161507403503090050070f205d0544901c4500c080596501641c0c500034041a194045903409400b82845642110340100003880c1320b1540700c0b07d2401d0407800d1150103a4070040902540c0b609 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 213975170 1250 213973920 213973931
    0xc201e060a05031314030c01061d011214010f0618090b0f15030703080901080c0403030804060c0e180105041a0906040c03060b18151c05070e0a1805070503010f0315 72
    0x1044140d201d09081720048006142c0e41c04030031801e00c1c00d45075598040040702c1c1c0703000b080000000c1c00c48009815142c8101d11103400c8101400c6c45c01e56000900118403140d403a24a1501024030581e100750201c422280d070078000c0d02c40c1c000d00c5808544014401038490070714100001d6800340c0c0000c00b168089126581481010204008245403a4140d0000c0381d400b5000101250740b036801412783c6074401c19079000645002d05655006064400203040244840c3c0c07240058540207000d440c6080c50304101078030304900d06890948140c418072080c41403a000e1440d000091018a003860141c422200700907040d5146500d035842480014814112484101a40e03030350089000d100c01070007460301c80e02c00320031145010010b80800c05003030086c0860401c004010030982500002d101032040b00c01c1c0000b03e00003629035403036000391807201484078425403048600c58003007494028017041a01c0340070503001c200a5596075003401c0d102e501c020300401d03041c01102c050400010b4030b003580c141407469429902040c2c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 213976420 1250 213975170 213975173
    0x60d110f0616050c030606241608071104050f010501090b030603010204090c02060a1103011815030212030d0506030a0807142805011b120b010c201e060a050313 70
    0x90101c0c2c0d00b00d03040d400000e103011003450304100460304100c00700c80c0b07c0c41040c07600c000244802550420241110700200344019100c0301c4a0012940d140c010b1062039841200e8a466211500800322451003113150101007641c4000300c00050341600d0303040e120760311414100603684d0440e400c000e10b025890741d001c100100b80d4484902580d48a58016002014141042200541a0740341942d00b1101c440c414001000038810f040075202201109660004085a1510f2040754075406600082d4100d100c0103035102e0010b0000000340141014110104081d8840314100750b02c8800c11100500700d014184030b0721008c03500d240c421504040c0f211046031601010b590031252180d410062005068101c06900c0003440000e005400000121400440668580b100701031308162070343c0c0c00040866500c4442030340d9031740070b42040107a06030042081d54580200305100e07181142290411030080e00c200f840c01d01c0c011416514107d000c070004019905000d003201080341c0304d40005140b00e0141104091410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 213977670 1250 213976420 213976447
    0x30f07050a05010e0c0916050306010c0201031401230307080c04150e130303050106171b0f071b0501091d1e0403030510060c080405040c090e010b040e060d110f06 71
    0x11340300122501400540e80807004010140d080244a01310381aa06039151813101d9005048075032018090808050040c03035800101c0041c40b1048008901003403c0d0000304644800281a90350701120409000c0000c01c05018542c0340c00140c4900e140c150310040401c2c0085c40c0541043c3c0e400211000408051580c940f81c180d0800020f680e01e00400d170145a20000340750b0300d40200707805002681000c81c0301c1c10a4008810468400030704007010100004080d005071800314044030140c20a81c120961503071110700382100740401c0c540701d0040382d03210381c90001501d50040405800b2925100c511980002640c4241c210201c00108944071702d0701d208034402d00002102580c40e0040c3d0003603400207424075201c10003070301481c3c40342c010800380581d040101d0000380e0000304440c00d49801356008515040000f009032640b024680080c882d80440300000b00b0581480b00c06081154449003d40b5920745800042c003608004540001d4502a1016600c0d03d0500b03196080d11311100000d400c092601c6010580d11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 213978920 1250 213977670 213977681
    0x901110a0b090d0e0306070c03052a160305060705070507050a060806030f0105010f180b0301091b050d02010503040f03140310030303060b0901050a08070203130f09150305030f07050a0501 82
    0x21a82402640140300302c4250411800b04207030041d050091001e007148000a44d1104001d20320000c001e11078992004040c410016641400e4a104c08848401d003880c0a10a0404001450710400d01c10303c0800608184000e55240450750060060079042e11584001ca030a6840000e040d102442803900002d400e48a00344500018051595461241e0034500201814a06101319500080e81031400501c80402c00c81d04200c100c4440d6041000382c00a80c500b050050600c024125a055207441c480c8003c4c0890101c2c840c81e2032210310a46a0b0b520707121810405e6621a02c240a0b0001e0003c0c07002070005401e811002000030b000e410300d1090606100054241c0d075100300c0741d04c103500103030036400c000b01a054021040038001040f589402d000d01ca20000300603003e103c64020801000b01c0104800e14020b0080390810700c0c0104013420001e440d80d1044a5000b514490351686030700d00a0100c41c181e20054125094940c850099031912100529020580e000a0001da9843c029250810300182c0309101c0d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 213980170 1250 213978920 213978923
    0x3040503090315040218010302010f2607110d08190207020102010906050a1a060906030a1503050a080a0915120c1205040501141602030901080415020307080a0609020a0507080901110a 80
    0x300d0343c0c0d9280c10f20500445041e0314448000701c4542a0043c00184e8002d400800c0303050351480c01808900307004881c0130122507602c29040500036440e00b031007001c90b801102d861002c0345800444009000480e81102c03a04d004680c0803231040000300d189049802c5940003840640e0052002085220094882d102207907401c0d220300d0071407682d807000800f18150402124440410443e8003500304054003001c03415620005010040b0706d070340c4e00561000d4120207003201001e075801c02d048501420481c03410381c1c82c603030000e041c00c0081005803000280c0c1c0d08418046100d060310694440600c180304030301000140a6a000c45c806200e072125984000e200e10340b0855204500800003c1207440d80c000c1c4500003107801801d01401c103020560720382c815075000401c41e520072000380f924001a540318140207000341c0c3e5805c60031007403038000070500c81e117180e1120307030700c0e00440349228200100c50340c0e0030b0003200b01d1040305100004198103010800115070b007000078108445040c100281450b481c004124100701010320f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 213981420 1250 213980170 213980203
    0x150c140318010207050a051806030106080a110405011203020a170d0c0207031106040e0f0a060b0705060403080c0903070608150402040f03030228060b180109091103060f010b030405030903 82
    0x31034240d030750707410004400181810746d10742c03614500301004106031140c8a140341e80719a444401040036514250b000600802ca5441600d070304035030038605120131104240b000341c8a00e08210022036101404041c0940341d550580092603500100d03500c844d00700507028070003481d0346818403500542040c01d0040c4000500c00340c0c09841d845045180040c480c00400c1a41400764030140000d1100040c121401500000c0900f400055903a403c9100800740985402c803640004000c900b03681041000500d00303020f603100e512002d0745541e40c0c00c1d100da0940103e64031190305500401c42001070300d0181da65580c10464560318070080d45a80f40c041410b907400b941c8a080c6c2044032032801c009255061240e0150004180704102d0342c02203251001c50200c0c4440d5025100300d5a4030b20807203c81c3c0d200080c02c10ba20090030807252256070f50304803040040640844c00c1d59001849403480c09149404144607214440403000900d45900307041100c2507e8000500454280c40208282c04d0a42e0301008030844083d04100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 213982670 1250 213981420 213981457
    0xb03010f111c02090105031f080d050c100e10020903010e0304030b010f140607020906010e0a0f06020106170a0b180102190e0607020906060a030603060920060301150c1403 75
    0x211410548410302a0005014030601024045a80c400e0032223801c160300c9039801e02d000501c0000000c82c19010780c041d2189100e980d249081c5140c00001806441c00070005490b030b50815140700200b0380c0e800d20020289600034a81121030880140c0c05083e1045014000149510400b0003451455105030000e2310b40201c01c10042107410b02000b1040040c0180c1d03001510014102c4010038028026520001c1c0714402c10000208607910440c44801c00c0f0800602010205940304100b0007203041078001c000055003008400b25030000c1040b0040c4180302442c0040c03003866020344450050460107030442d5803050079035104403000c031401d00241c040c00400d80c00c400b4101c91000c0000e040519213412150042d80b0900602c40541d46028000350301c40f0050712081c0e80e880c1c01d1242240240100c0d00000d0400745010102414000e003001048038843e803042000c01680000000c0242c039000c244203510a40c900240070350000d90cc00d640b013a06562050078001004100791071000e05680018011040105060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 213983920 1250 213982670 213982687
    0xc1202030105060118090207060e010f0903020f12120604060510030506030c312408010b092208160317010905010b1204020a0f0b0d050901020405010f030b03010f11 72
    0x2c0c441d05410203002d00706a0362940341e4103a24080f04a0302d00c01c01034003650114211081c030150b80c12038000c0d940b1260007001a00c001c2c1e280d4a00425101e4001d1300184100010746020910000740241e554000802682c2001c2d2181062800e00d24001c01c120313085034940000203010340340d101c030007218010180c40c00303d003078a0020107252070007445036061442540216008031002d05891002c80241c0400101c1002a42e01860200c014203910030000c2c01480c1d0f40000d6445a503000041d05043c1d0301e4800082c0444084d4501b040306402095402d0150f1500b421782205480c4420420850318621400d005820045e04503e4403c10121001c401e401180d00261100b000e507a1041400340034100141c010460b5505213500c000c403a004a20854008042d14004601950380b2042c00c0e07001484884c44103a4042d84611b41c80780c0d242c010f100c00c505182d01b0000030945244043c0269015075106030354280101d030104e4021000362928140e11a015540e441d4000c4075014a80910200003094800780d40d0340e080203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 213985170 1250 213983920 213983923
    0x3070518040209060306040e0a0b011511010603080a180e0103110f040515190905250c020105030f33010e01050414010c0203120a18060f02071703070c120203 69
    0xc40d000300c0d119a1041080c105141d803030304282ca030842c03c10340700020300390200311a00c0e1401e0f1212001600f801c856030000078500d82188945120304d06a90f6941090410480e019800d8034840d000090000c1c400b031160340040d5105603007001030030880c5a81910f240b40c0d101842400d01c1c1c0b083e00300380c40c00303500540c1000f21410040c07200010326609440420582c50250b1000740111203900302103100c3d0b40300b055516601c800146110003d4020460200050700740070003803084180008081000c02191022030141440c040c3d014501140c5c0c0684820b480d6540d103031584001c04a00601c1182900a00340c400f05030000c58040540350b07400501003100c0204403001c0054031030740c0c0500e9003504100e0208000c0c4090080c409642c3d404080a09000043c04c24910000c0e040000032032864122100c0030a010802540c408003503c01850710384610f4141e503880b803500310780220240c8002d0300981c0c0440401c000c41d80000802d0a9522099000d80e4144402c035075a105031500b0641c4410068070740020b0103802c0d45070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 213986420 1250 213985170 213985207
    0x3020307020f03061003020f0f040e070f080a050a170c030706060302010207140d020603060d021201050412170f0703150801020913050121020409060516080108010605130b0d08030705 80
    0x1800c4006244500d09000c1e00301c0d0401742e0380402402400c1c08006282c5603124468480e41c110340092003448000200d440e2a41c2d00d408a1007a0b440c10306054100080406010031307070610b0f445d0800c010380820b80a0340c4407a41c445100d1003005856100410200306615400e0025150143c03040c640410500e2450000900e0078120350440c03000c036040c5950130142c1d90b58560f03c410040e0b505840c2c00b5100d076240b00c00139a601c042c1d5003000e50410702500304440100810f5000520032481201101489400060100c0710800c003800001030a0300040c01042c0200901400103502010034038010034840e2034404824400301042e4450040c607034001c01c24000e50318112a01c0e1842c80d03503a4008100541c509810340c880d00c944035401c00c4540c91000900820744d21543c204001061300031505200d281418400c3d5218a0350450f10030300058404000850200410b0040104840b0001d1900303100040320b0a00c82c2c000c0c4145c0b0956a484000144408000394820010b14461681612007070780314411101d0101004c003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 213987670 1250 213986420 213986449
    0x91a07060606020f0703061a1804050d0e01051b0a02031609060b0702010e06030403050d060f080d020723040f060608060102070b16081b011407090e09030307030c1b0302030702 77
    0x10007040054528003000105e54044941003000490300f541481c1101d00140314980140360001c440480403003005e100400300b00c0c0250301c140122820080501400c95a03a0312400d103250010705e0401003c0ca0000302c100070a24030000c0141609ca400e070060340042d26101c0b004514901500e00a441005104070600c00c080061210140c40e52505495030f0009001c80d140d125894810900400450140740c410301c1950310b0030040d600c04200c0c0d1a1224020000501d6620807510140b0a4030100c0d100203101103034460455030690074400c88882203090700031040c841401220303001070360342c0a041107240c035a000e45401000d5230b4032012140d0414034002810b00750650030014860a0800401d82c045601440c604505600f141e0780a880d0131040e160b400c20300e4075035030681c6101c2d82807084401e0b03c0045c20340b00a00440143d10b60030b1f40c469845c41400100441280d0301110350304140001000b0500980021400b01c0092410300e05480c41c03014820110000c084003500140d2010600e8001c504001300d0904644 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 213988920 1250 213987670 213987673
    0xc0f05070503220b0d0f0606030b0a06031a09010e0106020712030e040207020604030218151005040b131a0d0c030b030a12031e0e010c140d050403091a0706060602 71
    0x1850039291642d032442071520341c22448030350b010600c1040b0000000b403000f5004410300b55650741005900903020707100400f200d07489286400400218180032b441102c50204005c0e10980310030b031070800300f600141041d080030807200584124500341ca55070f4001090203041d601246041030b50400300c0081c503001441c1c111801e008680000c03000030075000881c00700c1050007182c003d40c0c0c03412944007041040c041c4c0e5100940203c1140304040c0022000340803540b044a0400f800b000d4030742c62404214501e240602d12101003030042009200302c64488009000307040c03030601894202c82c0d0f5141c4a0b00b1500f1000144851802d01044030140c11900d8051048403005c0c1e850180600b00904002170780b80c1c04213000007000c403d00f00c010800304078002c0e00043c042c41d86103030740e000140c2402070049024104461099000703529008030b24400500859040341000c040c00380c003500f02007030203810310002c01019005509021102d1000104031a040041c40300000840c2e0030715445054074540170054a00707a0b000181503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 213990170 1250 213988920 213988927
    0x60509040506131a040803070311041406070c1a1b010c0f0509130e0c03100612030c06090602031305100614060f12090c010f03060302181504050702010c0f05 69
    0x119a001600790b03005200c200c01c0b01850754a616015440c2d52100c411314100340c40a00c10402400a00d0340075511403034103910280512000d0120300000c0d0b1140c0c3c000c605010351030304501e0000b4100135002d000400c0c41607900a039180c0c0c544008140700d049a104090b105c440000b420366290781c140e007640440340d10b420024030045c0c0a50360f0160072290140b0200041000c08580c401c42682c440d10034520848686034104088100c5079000360715601d0030001030b4020300c5113459082b001c00e80c6124060481d40c80d1240180740142e1039804949508408405444242d00d40d03100601040c10b034401507004002c0030540c140e010b0201d140240c00c1010b40d1003104800c0f031519004104030313032035003c411707060901c2203891584d5003038100c0200c10f42d80566030781e031515102d0010810041d04000103410f1801c4900340c896651007468aa001c6055490900000b900600b450740507a0184014a00680e0402c800138414074401031500040360440d002203900500507911800a2090f840e0403000c1c550000926140c201d15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 213991420 1250 213990170 213990173
    0x4020f0c1005010b07140109060e010c020d050f041403030f0a0206010303030b03030c0a020609040f11120f100909060605040c0e0a060c02010212030711060c030702060105100c0303150513060906050904 88
    0x5000310720000d0800d114205007071041b56000c2d40003900444e44483d04104c00e0407007080303040c024500100d000d03002d072017103000000e2994091025104203420042d8241d02e41428205400d000c403580300345507501440103129460b20040003c02404803503a0986c0108020f600d503050050642e16040c110f60302a030000c2004c00c0302c010000c2401e803070854040d1407071940e5050135004503000b42924000c0110441c9803009400d00300b45000001c0c2955408106010000d031152007480e521381205641081a0704000e0200b0000c60000da0428104180521000030f40280e03241c003c03500b41c50242004c07900291214810210701d14184070400090f1117503207406000b540329540040d6450b101801044c0d28214080005038895100e9540105e60810302020741c0c2050030300c00400107558106680040241c06580008a13140c00d221000c03d503d040241c2e07984038881101e0301c00350010150611070b00043c0107004130105141d02c07043c500c0001002141c00000d00140f401c43d4080460f03241d9001b0b02e1049201509000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 213992670 1250 213991420 213991439
    0x80a080a0501330905040e0c030f010c2703080307050a030e0706020c0105030421020f0c090601050d2408070306050f0105060702100309050607050304030315060207090b0109030204020f0c100501 85
    0x10018604007000f00302508520800d80e4501c0055101540c02400c080307110000343c1c40410364400030042641152484100348500e182030750721111003080040c0d80c41149002c911702c00c1c0ea43c0e01d249a00f03a0344980c6001d4894480f042c2c07a034012a91030340851000101e407000c955061080079031016120000e04074140c2410b00003504c5001502d2a281001f8000c0046000c2c403050103044032030804880d441510b00c05251201039215454100186500c0c0101c42070f031205170602585c0d9510500c4140d489a02c1e141101d085103001700082d03d5591640102c06500316800c0544650250103800c081c4010142c180ca145090020303a000140b81146d44110b000c0100019101d020580706030720382c11200c84a405207080d6044009195441000d480c9200d4401030001d03444d0000011800342740255401d002e10401c0f00000e03103241d456403058a00581c02800b0400c4400d085501c08407090308145003149019980781c000509a0300540d00c4484040300000340214810020841c41128442070702d410b010070740c98100701d035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 213993920 1250 213992670 213992729
    0x120603080d0f0608030403050717011a0108070507050607021c1404062610050a080307030c021318080a0e0306010803120726100b120103120c080a080a0501 68
    0xc1c960312002c54645210007900000082e00c1042c0403241c0b142d80d01c0c100a0740d1f481d4a403041c18414041284c4043d4a08810300419800c2044c85984641400421004507840700f001494181000814030400b00081c00c288180ba01038800c6600a0901c02440402e0f4106130910082c0c403024440c85007100000200c0040598085035458208940ba40102ca620f01c0844030030f01440282c0d44042204000d403080101c1d400100350b0382c2c1980c0070110f05441c2c0c0841580d81c401c03a1005004540c00c50404070045ca403001100060800c504001300c0d10301381c0210880d00501040740200c948000c0482d0b00c0c0d07002c543c0001c44500c4c00400b200104120752400300380c641c5920680c5107024016000758000f91084c0d000c0c281034408004103030207211b0030072104040c064038201c05440107902c14226141c00644852024241d401e40309902d4000315003641b840e6121012060740703403000d00078800c0403852000803810140181a00243c2601e03560318500d0844c400000f150016081600590700e80901c00c0e04c03854400000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 213995170 1250 213993920 213993937
    0x1e020a050d0512031810020304230309031f050f070903061a0d120f05250f06021207090509010303090b0a0e06040b070b13120f11070e040312060308 65
    0x4030503a41da082e0920500702001c030810422046800014089000008804c25106106100544010721140d101000981c881564050000e4407440c041c44140c0c41d0310840c140d82c00c6e2051044130300d002109000b203410051030171205281031b402c000c491408d01d031250260651103e00d01661060a03c0c104802820960b49800081c105603035801074800380d1080d101e40c0a00710f2030010404a0302c0301c40c9181c410080206250f8a4000072204014030b101c10380500143c894546511a07280050a550800040a014035030740c1526010840070b0307041c000c95500d00c010125100c00148100395441c00c1940604120380c00e920031801070b014900100007095100f04110300b03403408000e0721540d030241c1d90003c841034580e140d0001c1e84604005800580e468a0303070020b00f84288101c90700000703640c031309000099a60f000c02c409880000000e60000c02140f045426030301032415070500f0b42e9403168040c03080c0d20b490041e4214000a108040a101c00d0640181d24101118411a000d100f1a4103540d2016014002c0030310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 213996420 1250 213995170 213995179
    0x51305060408030403030906090b061207082808120f070f0519112d0102090307060302030c120103050307061406030a03030b12031827040206070f021206041e020a05 72
    0x3c44c0806103e5000400b4140d0844014095005582400707102d61805442d61032240a61044001c0c44010108400342210101c00141100d50702100400d6000208080f6280742500c0401c1030307100081c505005042d81410000d4124603a1500c0d07444544420740107090700b1306000040381040045503000c4110b42035828815041c845022090005845088843c4035640302402441503c0b10092481200360280c442c03121450341550311100d040d5408c030312400041c0c507019007081f1410701c501402a001190041c1100d182c681c034010521b890804081002c0c2c004644903040022590140b10380750090361031110000c0384c211042c0c2032560004ea507494403c0c10040615442d80d844c100f050780c90303100d808480c001d00401d503562001010102000c4241e501750a43c40380303640365410f0b5071044601030041003519001c10044584d0b1a2902000420780281070215181d00c00304a8050041c0c5a081d06c02c8841904003004014506261030b040d01039074450040b1007002144010281c0250380c5541481c02111030569 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 213997670 1250 213996420 213996427
    0x100e0a090e0a1b0e13080903010f0b0f0f090a0207030509060c01060f050a1404052e0e10050a060e040b0d060f05060f030d05160c030f0b07081b0a11010c020a0204051305060408 77
    0x1c0c6c81a0700780118010b907039242d460b00c80c0d00000c908580e0064043c240c4201c4d064801e82c0e09035800c0000c0c440c40f403202c194000101e400003504040701c50380149105802410200c0c1461a0400060300680c00241a101b0994452800b0441c0411090813080600001c41744002c40b9403c050110000081e4210031502c1141c41c0ca0200341c4001c107000c0c0e400c80848001004c148cc6042c5841440c82c00082c51281503000e4400d00005620103844021030000d80c1c40007030050311230034234002040751040011840340c1e0b40039690304411700440d591600d010300321511510011420210450400e0210b4500400560149640c152040207990307002c245505011100c0c10041d403115001710070070383c20301d2086030003c005180101e0040103000400710714100691158035900002d0342c0c0c0b440101e81009003a20500d00300014041c80d8002d08010801916000d80740303150140342001d02d1405282911080904580941c02007031003081982018019541c1c0081900b03c1403040154030380d680360f919000100013500c2448080b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 213998920 1250 213997670 213997673
    0x31b03071401062d03080406050c070e040b0402090a0b0607140c04062d05090109151502030a03090302030c070609180b0a0e070504090609020318010506100e0a090e0a1b0e13 76
    0x280132000650303000840641c031241c40e8440981180d02ca050b41102601c6803c100143c2403403860a1030384184d500000c0c0009035240c40e801d00c8452a0b018048810351900e85901d40b00c40d854901c05400e0ba50b00450025901260304c842460501e5171181c1c03014012420003905001d425203080c90000502c3c1882c550344400311030500007245d200059013003290700c02c00a10000400024980044010070300b2030140102c05a030783c014012038111104042400341e0001e000e088041d0f40a64044030101d0b0080c01500d1a00454040060030130303030103411200c04680410002d00c42c03c044203294a40d80626810704212202100b070005411001900c03454002898100009218610580030b5a004007520030341402880d8440440b000a90022078544c020070400240040c29000b0500565004400142904014404c071410880c3c010800c2d41c8201d8200b03d00410004054180748a02c2040700b01d208060100001c0c81c0c035100000b5140302007088290781c010142400011400805290803041805498030b03400b502c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 214000170 1250 213998920 213998999
    0x12091706070807110f03191d060f0415120c020a030503040b0a0e0d0c03020c090606071104020c030417070608010f09050a060b03090a0b010e01060c060509031b0307140106 75
    0x422841a490042c05102c0b244170070008003500034180a1040c031083d5000c0e52a0071100304502d002950622421003071b000740141461401043c0560245040c1803419031903149070350341c2504202d203860000d0000b864020101c2090310410790050304600c0502241c031510b450041285c00042e02c0a0586203c1c8804650001d5540c2c0c400c820700d000c48016200d80745060040504241310085080d405401013646c02001803610340c02c07140c031860000b05a9420b1a80079100c4441041c0100380164100e5800c000110204500300050300041080c80106070b04090410310113410b15419500030700c00d00c820200140095240121008143c1d01c21001c0000c2c0d135903448480034040c02084c0e000c0c0340384072000828410481d1003c0380e8441440e00400c0704400c20390742c2d8604041020800d224050004023002d09031800518903801c42d0340c0121850045030706007078183d08860602c0c9048688903001c0d81c00002d000b0108605e156a240e2815107400c020448180f51040d01c425a008110701100c00d1440e0303800c1400384110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 214001420 1250 214000170 214000187
    0x5070c0b0603071d010608060102211e031006090503010c050a08070219060b1c05060c0a0e12070612020c0705090a0207060509060a06140d030e0312030412091706070807 74
    0x700b2101c13a400a00c40382070850550a018140000740c4403400a55154000554031071200c10700d0020240d4840804400009500b004542004501d0410460054801510050b5015140c8a0401d054440c60580e000e8001d1680394405802641080c0440e10f64541160a481d0b0742da0481c201403500743c5d110202282482103a560040300d03e01040180c1052156680c01144120816139108400040131104078046142e4807078010546c0d81b0442c000380d500c050072800360007401c42074107092080c5842c000004002c0515208030060035882242304000c07803039200e1100c20400d030903d44118607104036040100c0e00e5400030b00500d8040e4003102d001c1080020164125019646c000d00108000c0c10f100d00c100b5194517059400c4203902c1d080003001703d03d00800e03041c040031041e0001c0202c4880300325507030151656039400740581c0c1c0c0350107148070036201d10080d4001544914840ea00d450b1048a40200c060400c8085410802c1c5000301c3c024812034403640051342c0e6401070010b04000c0040e0351031002c02c40e075048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 214002670 1250 214001420 214001429
    0xf17070f1505010b0705060121051c18030f240510030c0801021206190e0705270607060902041d2a0102030a051c050f040203010b010305070c0b060307 66
    0x59903294890521040c1c1078000345000c21528144100e07607a40740229070728055482c1c040c3c0180c00200040108080740c622000244800a003030f8555100c00f51155401c112b51400f461000d100301d25801540e050344003160442000b201140c48501504580f208103e020740d03030400411070f4041900715500b80710146800000e5400c81d1000f07000a180980401c4400206480202d0f91040b184001003508003060083d103012035030300e6964004503511801005000302e01c00400359000240000080381c0369184242c40344c400d44481c1c071420340d100c11294400120b034255014008003890000f50302e000e01d0791040100c5450700c0d04401d0204001e051400094002c100c0d10325110130f2001020f450241c405000b1400e0400c03c0940c03030b804030780541094004040500705080c2d0303e0041e003080000303254441c020740180c100070300f082c44032003c2c02c810319942508642003035822041d1038925108201c110b2509000e054202e81007880c0c01e00c000d040c0081c0162591138407000050110f100c1000054090720100550300081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 214003920 1250 214002670 214002683
    0x70f0e100b160b090f0d030b0f0907080906010b09010801030807060b030303090106061d03060106080901142814012702120601020d08010302030c060a0302132606040f1707 75
    0x12548240400140c2105403821980c454000c00015084d02000c10080046040c49024160041e00c40f00210700030035500901036488880c10b81300d9003250b00c541001c03d110361030039255500d15041c170a0540d40b4240301644011040641000040c1041e40d105c51004c0c11254040b901c1900c0750b8951500d400070301204801305401d440f001c001c01200400c150400300454045490310048540c0d007004466604c070b80c01048581503444540100310251054011980c0039410100001c0c52070420b014501c0003442c01e5888070040000048440000302803184840d0f2100c0803280104039a10603403108590820b014882d590072420039403044014500150b00390340482000400031555502104401103000c1c174140c030160300500c00d5200d00d1031801e02803400103060b030303800070f0052031001142410040181d01070b140d0b50041540078040c0202d20310030190468080d01440c4100c848011200301c200c9100c0a104c2c0c40102c03540d124000f0b00010918580300310010302d401c4803c403000c08424040004d071780d108125009200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 214005170 1250 214003920 214003927
    0xa0e0418030302090406060801030206090907110106060903030e03030316050f160507030b0618010b03070c060e0c030f010c0804020f190f030204110304030503131e061d070f0e100b 79
    0xc142d410f40c001d255481e82103c08101c8291241001c03201035209010003500820304028070300aa20703210300c50990140541c43d00566010141c41240d0940b91031394004004540c0d042c80520426070000c00b00b0704506800d90045055240c44103014841c04c1504030303103405206000800300040111242160003883c4681110384080c0550b180080d036408031840290344980d40ba0740450312500e802028844050030303401c0c2e0240780b41d0a184c2758440c180d00c090140341c144001010450006101c500411004400d0391004d4852900c2c88414541810420481c8003a00c1c0d00d000c0350304402a030010a11600f1507010b4801460f108000404140010007000c84c164540441d8480017a42c880001c0320301040c0ca1094406008034403105904610600090b1402800304e90b041c40002d001d40d514006a42c19140100f8501d81d0350110b0700c0e480b200c10100c2d4030703040d40d400b9210241c80002c0c09400c185140400d0f81000109092032401d505200c60400034041d800540d03403c000400c041d1105c55024102a0922101c500d81d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 214006420 1250 214005170 214005173
    0x80316091517010b0712030b0105040e0a05150402091e04020c0102191106070509120c040531080a0f0216090c020114060901120503220303021905030a0e0418 69
    0x1e440b580d50a40510440800400c00460010588a50301e0b8004001c22034124084001c2e0090a03103010b1b410304000c01408000748540050030702e10b000b0307011010700049908010020180c41c0086180b0180035600400c900b00c2c06860380314100f2860040100350768134006408000070080e200748217a0001960020404c003407085807128000c02241002d49810030880400c0400030340b00e010869981d0081181071003009034a040020100028000c40340aa0f040c0c1140e0100203000c035001540e090036002e806240004a402c04600c01c40e4990744002282c070300502040d03075440d5540c4034a01192040090180300540d0084c000c00c211803200918140c2e05401e1a19031005900420381c4840c00700c015800c00602901e10b4100c0c92601c2e0141d40040c041a049038201103220448400240085445100030003840000c4030002ca03d80b01810005000c18003c00e18504000b072130307c1a141c44035640024004960400940004201c2e10f240f8020b0500100d04450880041d00030801c44c4400640303400c00501410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 214007670 1250 214006420 214006427
    0x80a031e0507021e3c0a08031f050d030c02120a0b041a0f0c1b030414030106150203090d020a051201050f0106021b09040c030c0b03040c0509040803160915 68
    0x107400c983c010740001c0d00707050b540210540e6120030b86902100e168100380c41e0484607064001800b00c056012540002c05d12000c03c0482c0f41c004101d00542c0c120401005012281008030004448407903a848035140c60360520001035244140190004c0900c8540b803007000454440901d802d03c040d40c0e4400ba5080466941082e14019508440840d81e1241c200f5007081645860300d041d5019400c0310149907103955454810203855802040d6000000281340e0344610340400030001800600428a120004003008000349800d4804540040c449007001e000b07410a00c0e81c0c000306681c15202e0032519102c0d0380c95140003082144641d9000320b07400966804600610340c40c15000940900c0c2000c000215681e60396404a1700d461000031149080101290610458600f004000d070b000b07401140100103281d520798a039115161503a00c15050031001008200501542da0780c0320b80100382c10380f88200c6610703059860719202d01c0003d00d140a0703040380381c0e24458141e1148010002070b00703851103000b40495880101030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 214008920 1250 214007670 214007683
    0x303080a05070f020a0b07030e07060c0c0602121c02040b0d050402030d1d090c09040510032d02090406060801020a020a14070602031b0a02030a0c050102060604050103080a031e050702 80
    0x150003150610000c6000703684294002041c81c8565406402d0500d4140d80300702ea4884d014002004040d00d9640c40e01200c4402c2c0174034802040552908046040240703010030300a0015803200342950004600e440d008460902100c403070f101480c03c4104c40c03000d0010707040000d000329001081d212202142450405d8016804640079500031030441303800c0015034400319801c404c9600c540d00340e0340501c1800310031418240f244076003045801106030306001e0720002240480c0e4045920140743d6902100410601144201002c0c43d51204a41781103144e5550006039050313441894000e0080d00104001000e1003400d5008402900380c2100030341da41d509001d0001e40d140f180c20029a00c1d01324000d00001e00000c0018510200e500c13503000703582080110912148c0b20b8074039500003c50383c054401820010799080c040350010a1003010320b150168200780009161000003000c00707018501d81001480070910000071b441c0c0140311482e0103e101440d10014411808905140451540c1881c00b8403c0c0b690300031802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 214010170 1250 214008920 214008931
    0x70e190f0b0901030b04090809010507030504120b01050a090c0507080903010b130b1002010209030c040b0d120203030703060b3a09111002060c0403112107090f060f09090f0b01030308 80
    0x10f00010302505d0070131080300e0907035100030180e2904006040303c55009a000c0e100035030203424401c2c10f00b50f940420400488102c00110340068424006010354a454140d11014001d9004200074a0740402070140a9101c0c0810103800e5034000300d018400ca40c1c09421111042d980548039000c0d003040c0034541000381c03460341c1c010741c4107403100d810468030284144240d51800100500810502c45440103010081c03050403152a0000002c000d0000454040d0a044075407010703943c01980d4928016600808031016038104405081040000c140003465220018a0703072255070452020600e000004500614408200c185810b410705182d0703010f0210304151080042015103907044044240b0400301d0b15403104884540242c1403d00091012401c0301c6080242048050b0845401b0091140308035600244041010b84c50340c0555018004000c80e405a05905400b81d0010320425040800403241d5101d1800380c40b009036640d0aa21051020301186181340e44d4009501c8109561a400e0062025504995 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 214011420 1250 214010170 214010177
    0x61b0c010e01050913201c150e040b220f020a0509221e060f0b010807090303030f0209191509050904030c1b17070905070e190f0b0901 59
    0x2607036125940654125003204800400c440d001c440101200d600418240048540d21200480d0769240c4c084a140102450100c54051074002070016074400241c600007401100701610b42c450420660881d090341941007984680c0c09201a61342200840451400007011440c150594510005101045c038088516500030340e07007144500c0d1a8424080000d00c155082c0510f0005400c2c1345450f03501130040e60000e1442840c3c0340c0081c8001c2c42c0c0c0210136a40040058038030640d20920201b0f104258031a001180d2400c0c00c0802c1c003440e040c0ca01130709820a038072015050540324844c1100604003a0304980810400800383c51080d840075214990b00340250142ca1110310140741034082c4503000e13000c03000c101c9400420500b0560713120703502200e0700704c921442200d01e2008108002899019580050b024040c0c20042c2c02006401903105882c085640c0d0155204071300d00302c140004150b218480c940b001805440030040354900585005155038158480c4d0000307402200302080454000f002041c40f500241d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 214012670 1250 214011420 214011437
    0x2160b0406080c09100f0e030321060d05030f0a140a0504030302070b03010b160303021b06060a061d150d020315011e0c0605060f0402040902030103060e0a030804030c02061b0c01 78
    0x10032040d4402c0c420a69441202030f01d041c11000c0c0b26405040000306c4918188005010306004645580c011300c000744600c440c02e401d851000c00d4481c0000781d11207400c40e103081d4a03180540ba9030f07849210303901009840c40c01c0000c0028401c0d008844511584056600301642c034020075400410079041404100c00501629100160148100c1d040d6030580d407510204030303d0000d122a64241280b80c607070302141071580a0101c1c1d000018001d80e22150000c9042c048c04440c0b40c9507081002050141e0808818001e0403c6002c0c4c9e031001c10001e12403000e00c207071030181c03540c00e1000030001c86008940841c03144a00000410103202e2003000d50100007102a2a0300900c810089103c100701101c41c14034800013400d00890b4404901150061508501c01505561507006041c02241c1a644140c11a00c1069000001001048594411042003e140c17034081e0207110311940e802465031402520140400000c0d9241c14255900c007811100d07130b01503100a514403459011012a1191406013000d404a07a510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 214013920 1250 214012670 214012681
    0x30a06030c09140f0103050c04150b0c01061e0303080a0507090e2a040e0403120b0d06090c0b070506190b0a06110d02010e0304060c06020c0105130624050d0302160b040608 75
    0x140c13241600d90040c007600c40803480d1410320004181c2d01104ea620451000000594114000c0080c004003801c000049491424540c00c80040280ca54405840a00e021020000300e548401d129402c40400180403030980c07039026085941c0c0009801403014540d2141c203001c06540c3c030030110907800720303070084908007140242a083d00d01d015038032035142c3c07001d041c01c001000244244a0420104000c0800040a039103103c08a400381c5503d8034116500c560b140c80c00418085804d80a000138103c0001441c9843d4003560380c43e4603030102400e0300c8400480c620185114290f40c0d0003e4031003003000382400240781d644510007499025450300050143c042e84902018036441802610703001940d0200840c0b41c103242c04070841c0c48071264401640c0d40386e0700b032000c01c00d9110203001e00c40c000c0c03084051903101c2e210b480c2046401c41724205044500c101c4e403003e44c01912600c000c1080112501110801e403070703d88900707080e820080d10503988140c5041c00e07100819a00c000901070425240150341d24180303039588 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 214015170 1250 214013920 214013941
    0x60501051e060a0908060702030408060901020703050f0f2116020d020606210d080612010b030706080c0c0d091a030103050c150d020c0d030e03090d08030a06030c0914 73
    0x150107440032500709420650500d070900300010080b00100d4601110003940e201e0015003010700603503401d00140c200160070030030310004200407a0866a420000c602d0596180c0d006030041c0305110402c203101d040862412511081c150a0350740201c02c42c40d00b261b00d0f818202100041040c1221008075a1240101d501203141c80002c0c2c0c0381c9030702c01c950018071305621000204080940511803a18001c0003100700c5254201c2c090004c1d2a812405444800300d60825208000101100c0c44401920340c1c0340c80c0324641c40d6a0005000d07000c0300c0340350500c001c143c3c46091443c1403910940326081960300c01c850580b001c0d503a00040010443d180c003581d6140c0c01044100c142001d200a200c040e21a034400d8a29144c1c524040710454041c541c070940840c070781403c150f540001d0341c10982400c10b040c0c000030000d00c4c041d40c15025041030b0045a10280d403500c08040002a0300048121010300441d1011002554610603544004041d60300b241901c8102a0b452141d0005403a001e0f1f4880805208240810a005d40c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 214016420 1250 214015170 214015189
    0x1030e0c0f040e03041a0a090b0a080c0906040302030a030e03060a092303070f06050f100312030c050405030a0b0a06050306160c0206091008100b040f120f0215030406050105 76
    0x2044008486848010003002d0f0202600142e01c901042000281c0700300748505004400141c1002e07191625940040500407020940c03000416030310400c4403100440d8404205548003040b030000c0c80c3c5404001e40130410500035604001e42501c640d143e110240343e00408100111070f02201140c1d0725070707140705000c030545580c002c00030701d0800061001020301003006800c00e900710041c0200c1e410045940c541095420b01401c007079618540d00c50900100c100416002580078a01940751035a581c51990703858040c1818845a6003015960300325281418801d508032401810014111400c010081c1094020987c09a42030700c2d00302d24203040029142400f0410900c1501c040200640384440700310240c40740c82264000704c0c0d121600300724103807290703841c000c02002c0044955103001c21841d003142481c010700c05035081499460700502c800c00c900b440190b80310040e0368446500d401c0c0c15600e85801d5041941e0b0100c0254444610b00301e1440419002d03010b1442540109400d00a99136200705202d0f4541 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 214017670 1250 214016420 214016443
    0x403081e0f04061d0d080307140304020d0b040f02040e0c01020712021c060b0303160201020c0901031e1518022107060507111201020a1205150d05031b07030201030e 72
    0xc180400c2124501849004504130401000520001c410400146045000013011259000f0100c24804a10307801907402280c103040c50300725480e6003015000039150b8101c02a005000c1904100041c2c100000c10b4410403c495010700140300c052030342c3e005140ca50784842c00c2e50f40140b155490001c1c07103180c03000d1240b03040398010340880c04005040b00f0304807640442481c280c0d4010b03228120103005441c200001c0945017134a242070441c91400b84002420088400c0440b846108024010f10204542100e200810740241c000d1180700120303403071b010508201001c450b0308440e203001540403209046001d5290028030846408564421135080441c80403a00c41070823089034003c20092041c940102d0040c18014040c4221175141a0312a000850308400e101005020742d4011800b1080e40d40c01c44404890b60362505414009071400d003054a40c0083c1d280162480b44500240d907809124041c41120b62008069103000c0100e03400d600b40680d64180c41c8000c9000034a468001145010041280841e94 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 214018920 1250 214017670 214017697
    0x1022b0e030a0c1a1b030301090c030510090c0c0b04060c0212030708070e0d06020309010606031a031c18080303010501200d0f09080102221d040b04060b060403081e 72
    0x6040c950302ca04c002c0c000501140c2440c50801410f00348036000785c00140c942080000850342c3e90304155a01c001d80d0b6102c03c101043c181401c09102001c007c450880096441d60203000609000314001214503640074003029056a54003400c3c481400394a80207015000000e800320350907610200f201d1000d0340310481c4c00c50006480d07100451004c900c00d0401840c0c08100818044250b0615111201282d100b5038405000b0783d903411040104036050700541203500c42d501042c1c14280c2c44030340481c2d11004c2c0010b04061041032a40031017032440c0110300081c0f002d000d0020850000b81c03980c46d0786591f40c0c000c3c0195800700b8104405555080c1300121500c5400310000302602030321090580980700188401c00f000107200a00c039011954030f0091020b00042014a25001051144d02c900b0040c0400305401c440b0503284d6020300c44090400d070f84500394006d544203041307140c00c2e52035082540c0107000341040c0503400a03000800206114507900600308041d513001203004c0068030078040c020745114107014003418 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 214020170 1250 214018920 214018943
    0xf1d06090f0112030903021005032e0b030c1201030507030302151012020d120c140c03120309030702030607030902180106090504020a030e0109060204080d0503070804080901022b0e030a 81
    0xe03d01001c0c580f02c5460700c01c2c20b2198215440381c0c00a00e001550300c80c1d0100141c40481040141c001d427010400c1481d5134186048003100000d4100c1001c0c1580d40145151420008040b0f88100f01c540c080b5900c50294100c84001c5d5612458001c0d156499840150014407074003048401d071096028280b40620310402c00c0910b0a4a08000000f50341d503040f40a030b0784208040003c1c0301240e60960111804203ca5540301140100d903d0f22895444554082503c42c9d44105100c80454400240700304071003801100d02c5460360760f0001c04d685544940c0c4002501409040b06001385907805400a038a19131003110405850398100507400a044402d200d518001801e001080003182800d900800d09980c99107400715a240c4503928403425039440400c2103c00300d40c000741c00c0000c80b60900c60720240340103a280c080e10358107003208018038422001e8130150000000083e0342c0e03c66802048080710741460303e21004554018021501e0307014002030409800b28800700d508558a1401040c02c0180c00c6c1d000514a03071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 214021420 1250 214020170 214020179
    0xc0305060907031811010516030807110304030c0b0309070801061202150a0e090601180e04210503010519082401050a050d0803070905031504112d03070f1d06090f01 72
    0x800005c0b601440d4184a0108003111000c202d50720314070201400b83d00d4110381c86c01d11a50040801d0f1a40da9000ea07203400c1400280001032030318455100b00c82035441072507140d803100388015040c0b81c03060380030310b40640c40c1041c0005c803042c1410a4000e00c900807545800c02445030820941540300e010328400001c0c49000110605141510500c1d070418810324100b08480b80c0b0034090382c0b4030f82c02900100a070101c1002000104600c040d807044611100c0c0c0c0102401400417200980580010b0086600c5482100e07060303007010f051502104024241103040710948004086151850079014501c3d8075209042d00002c142c41c20542c40c200c04841000d00615103441003038403020825080a000b0004100c600e11001400d680c0c00c201200101d040040c0b0002d05051600d4808030030008007100c1d901404400c8440c0c0b1a000c1d582d859043c0b118002070401c0a034222001c006824401540c00007601c010240d80085811232280d4490701c00440c00030b45400742c5840380c20401000c503104071503520710840c83c04010301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 214022670 1250 214021420 214021433
    0x120f0106063009060b0316050312070209010e041506060305090127200901061d150324040e0c0103050a06030c05061c2a0f050a03020c0a05010c03050609070318 70
    0x12615004c1c41c0d000400200c818006414000000c0341c1d8a01d03111b081006010524050258024020414101da80740c160f865000c107181050510603400c00c0c1c0125400207003803200700641e082100911020420450751521001380080a05440d103003480e610344004200a00314a0b40307070381c035241025001403920035110f42e900001c080d00c01c0120310364111071410070380e15511040d844502808440d1101169004c1c403280180d014440c42d003401d40318542c09aa03011050f1044005c43e80c0040d00c01142c04100a03800380700013000301300b640c01160010701d05a0b400e045d206000c1106441c00c00c090b82c0a01c5551111048d10081e11010b01000d4a040b80002c8100110328220000301028203150700d80800d0899410748841c100e400080b00c500942d900b00c810030352841c3d498460880e5024107410407c0702c980901d04010041c0c001da11140040c075500050281d107859041105c10b035080e81c070000a220b24145540028058001a511113009500800128056600038000c9080c1a6220100001d0b144456110700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 214023920 1250 214022670 214022681
    0x90b010903060501090603031d091501051e19091410020709060909020a0b0a12020c0f0a1506060c0819142b0c09050f120f01060630 58
    0x15050104040c40040081e18500071180242403203000051124518200581254040d50042945030f0091607600038607500e0101c011b0b0400b00200010040390102c4005a17103620901510824411801e0140341140b255800182503a0380300c0c4500400c503c1a8000c181c0d4407000354042c4100341e010341c28211072142015803010b42c0010b114811500c7c182d44e2092902c2c201d62a50b001a050a9150700d00341095007440103001000f040407004692a00c9c1914400410a100c1148220b40b141d0300043c0d540b0303030100100240715041c02c401060b607012031403d151400381d0700c4601e0a510640d0b0308102d0005a0203001f4090704011039000b810a9152810068603074101d000828080384c240040c40c2c0c202c11880f180007000d040c0c10105400300140c0e00305030450842e0100800c0f160249164105605109080c0d84039243c10101d48040c1c45180c040c070b51240010320140310a0030466144e00c1566510b4110780c405400000482e6160740742c0b20610700c0804410b542d0145c000c09151078450000f21035010010361548503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 214025170 1250 214023920 214023941
    0x2c0103080c070b16111806120f0f10050714043609050c09190209040902030f060a0c020606010f0516080c03090415080a02010c0807060906230c0409 65
    0x19104565103402c83c64509802c0300860104401c851a140e0080040e2500000c00c02203040b9070b103516100e2105403880000d00c00804140c06041016060101b0035400c0003211550054542030310300000d030699540342d44807038000c03400001c2030030700b0301041140e1b02400080c0000a0ba5286407441c2500307041c2c1c2010741040008103003420341c1a00140c0501c40d400305c0d031804400e040c01c0e44040740007189820098036140108650130312901c543c2052000c015011100102c19010501c1c0150300c80c0e9507000020010022000080c0d0903000c0d5149401081401280861158002410400c014a144201280d40d0181111200d000c900c490090381c21060040300030740545050310400045605060391498490b4101452451840c1c0c800300d803c03007031460076000b08065840404408103189141c40300c1c07241d44a0304d40402034144050102001c090100080440e070b1035640002c800e0001d09503500d00f402c02481c0e02403101191880c0500c0403081000c0403942d050140400e03854090904c0d003030018030303402006680c84 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 214026420 1250 214025170 214025173
    0x3120405030408120307110c010219020f0315040b0a09020f01200a080a09060c0c03020405040218090c01080a0e0c0906061c1b02070e01090c090b0309072c0103080c 72
    0x79240c0010003494090385413a901050312070070080c0000e000343d03208401700071058010042245260341c0c0010151004111000e002c41c0c00642d42c008a0403801c0d40f891529014020000d03601081c5101d1354841d802144103030410070301d6a0354042d0031002c0b070384080e400030760000302c0b1462210150300c100c4810309010500014804c488001e12101440c00c0c061590840c0c2e03954011031000190364014545000409503420200c0030102140d0b0794051241050200910565403200454155140e51041225400079800a4583c1d41070580ca0290740e035040da0f45c400d0018804100141c080f04090146a02d0150301e80c00910585d43c552041120380c000003020160002400c0c084840d01000411480105600c0c10700c0000d01c05207600717600f0031a162040101d005550000804025144e04428110f04460309113900043e00610040100c407621020360081128417804400e000280b1004109002225480f030031075181a03902081c50201006103200c01721100c2e0140c801000841c58601c001d0006184207030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 214027670 1250 214026420 214026427
    0x705030613060902211509010b0a02011104080a051614132003060a050603040804030b0a0f0914010605040e1914030403050f060106020a11010c0201090f06120f020702030312040503 79
    0x5040e00100d82091481c01c40c1842804041444680698951604150500c1d041b54036003012801142c08034034188558140170b0350014100d250f05100b0f60000049003400c90302155910f50342c0302c190383d071008105000c1d12917009500743c840e0b0001c0307046a41c0044a09007548060501051400c110b0b400350440544441180c46006400d500004100080480c8140780b07407940c0c603400c1040a1000d0300d142038001901441041090102265140b026075040b40d51080c407501440c2c2c0c41c080382d24003514a6004410070141000d200e42c0802003e00f899003090001407008000003030341c80c0c0c104802d68040582c00c40d10390300610081c80c00080f076010245842c500801c611081b190200c1981881c5034800c6d801500c41c1d070040b20965054000602105006125510080010108507180d5002070318010303130901d06110b042c403482411a40145c00c00801401c021100030245540d8070f00c06041c8800c00044000000c3c40e01540c0f050b1901c0328400d1750074440d00500110f0030803581482401c091100078200740c1740c912051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 214028776 1106 214027670 214027679
    0x3060114061e0f0c061f120503120a0b090a11270a032301020c030711010c06060303050405040c020c1f030608011a010e0603070503061306 61
    0x8803001551980e8039024540310018150068030b02000220b0600c2d006441d49015080e001000019580c0703554032042c40c0803442e524554549035040d024070042c80004200403142e001c0e079105000300c070718015200580c1c51480c1c1c01102c01e00001601d40d00007003010309041084641000e44403000f4400d846100701c01003611300070300c4030b500032908030140e43c00003040811301460381000c1c0283c0603d030440d4483c10310280842c0100c1050810112040d00308801c0d2805108a5890070648405141400d5a5680b1904030b482483d003058104040003940741d003c55058424503008621a803145540d4a1410041c0800c3e41c6c2c41010440654110a8441c0b484d919450303441d04250014241c03d101012014206030014023581c1c111050750b41c82e060a032224001c0340721103940d919800340c8a07002c00124140821000340320450700b08000074018000300e515030804504254507041c1807500491001d894 = true := by decide +kernel

theorem cover : BRFrame.Cov 213848920 214028776 := by
  have h0 := BRFrame.cov_init 213848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 213848920 ≤ n) (h2 : n < 214028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
