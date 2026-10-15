-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3887
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:58:01.425823+00:00
-- url     : https://prove2.me/submissions/c0ccfa91-7e40-4e81-8d4e-a09550a36253

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 698920863 ≤ n < 699100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 698922113 1250 698920863 698920883
    0xc0a0b0403260a0e01020f0a02130510050306010b091008150d060b040c0302092106071413120b010509010b0909040f12020f210f071112010f0506091003 67
    0x2000d461600d0b680c1c07411085a4070400030038107041050704402e02d2440710a003a000e9502000e03000700c515854802c80c0000961164801c00f2030703244601c0f42e5000f03540c4240025441840d0584400000740b4041090384010700a0000041c520024100703403503034000c43c3e041401e108030305061402c0016000a25402030a0107246805c00c010180304071500900e94041d000741041111952100000300a9400044001c7c0942420410341a01341100c451214907505505c000e45801d45900800321a503520a0044d0303604180c091090a0004030082e02c6500200b00c02c0c40c0c11100b4500d18a0000040c04050b88102d00c078030b4441004100d0019a401100c412400031107000e181a9914a4801c070b0b00001800c000d80300b141607a10b1450100d4000a1030080c0c180302130121000c50401001d20000c055015003420340b422818030090451103243c0f030181011521800400d0100b004507008140c96040c900f8900321142e44812451a0043c030905c145070300220240c420091510703024854200580ca0361000421600310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 698923363 1250 698922113 698922143
    0x20c0906060a0e060a12110c03220305070b07031b050d0c02031002071209150f21111c060803120c12090307060e150610050705011d0c0a0b0403 63
    0x12500104000312001030044d0348460985200030041c101d00d08008100c645000c42c00119001c0900c15a415501c02c10025450020710080300700f01c4480c903210040c0b504600244c040300094090009502902d452251141c0703400046c18001c11244c1e28401c900c4010f0001c0c04098003140e40410106507082460801c80b80400551021a1800a5035007030308414038404500102000f1001c0243d194512181e9512030300780d80c45080307408240c003040d1030131070202d69a05078a54071b1a005984003c030f41980c8441100004c03001891031020348010313250300c1c2d48510000446c118010044208805290003c0408000d03440c1800145540c0784101c0000003451200000002d1829201d213003218642001d1445004050800796122540c9411841080f0b60035410851503400005000601101d44100199a0b00d22501c0314801e01400d0b20010703040c81c040150070805403000c41ca09004112800041c0d40d440c81f42c0d400017980150500303030105900d2b0310850800d1000c20000390190151030559400080c071004c004c00d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 698924613 1250 698923363 698923367
    0x1a04020a0909061403010b1027030b1e09031303080c0708030c060115030b1c140a050604051c0504090e01060e0f1807260c1807030c020c0906060a 64
    0x40c02e030b000d41034031414100080b603488403140b0241001e041c1a0000d10140b0001801c1002d14405090000e0018600100b192098070325030800c010903003404000e402c00282c403a1280700d5003010031208402ca90f2000e9040400c1d50704126080d551108400001c5c60404440c10f052104000191202030003044012640c5510350700c040c0301c0301c17005100640440303644117851f640ca5a1603410034400c206144241e440000c030803502074000c02051500c01081c0041c41c05c420006070380c0d410040d4100360b4001403003484143e41c9400070424800d009000c0d40017401c043c90315107401482c4c01ca800401000349100840e0b40c409050300b00b8113170790580700800c80200b02007000850807801030400d42d204005003070201c2c0c03d210990301d4140e207050080b6081d1201c071018540b00f00ca5581d99080c64420038031156408120704a1010440780745503502001041074800d512100d1001815441040c1d070029200d010002c00d00442c5905840364140452080c0086c0040d440e201c000102010802007186000703500020304030a80034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 698925863 1250 698924613 698924627
    0xd050f270307061d061003060b030d0f03050403170108150a09080712021204060905010f18230a08010c1e0f0e0d1202010c0201180807020d020a0312050304151a04020a 73
    0xb8104445c0c10b807502038820048140280b10550301140b501715101c5036814045028034181e8896222525000f1034094214014440140305904100c84c214031b80c1c4200b09580c158600801c5903000824520540e003010781045a005414404004e01c1c000c01003000035018002e070385645070840780d031074a84580c0309422b81c18580049412203001000080200f226600085240c060f90070a984003c403100308482c1c1660900842e40c400300b00411220000c00100002003100c0c01040841c02d03841c040d0800c2400442c0d00c402041d004000c40c1d94407009507100459204980b00c80c0e99055500020700c101c000d2101421540811010104120f5074003940c0300a91038020400c031400380d101c000d807080c00c440d004000b8000d1260208810055007042540e0300c00c01c040b410010059038001d1015490005581c2c20000180b1140718120b030850b03d03840e00000400d0020401300250000c0e51071341a541d00c1c05161901d000c4944107240d40280703181c1004d42005c1f0403450480d010802c0151001a0354080a01054880c1c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 698927113 1250 698925863 698925911
    0x30103320d0c110603090703120302091503161e0f0c020904121e12050a06030f050d120c27080106080a15060e0411060d050f27030706 59
    0x10320032035030070784840390b4000708984499000d0854120320b030524a003000300b00d04c015603401c0c080d0341c01050180082800d0904440d42039585042c010300d08008400414840c10006c034501d1401c1c14040108203d1518010f00680348501c40d140001c00001c060503034140e07042c01000c09008001441c8140c1016074054040811020340007458000c0f140340900d0000220300c030840c071110002c0c0300114808031855082c00031f01103a80b4142c0300c6d000b400e81903608210003400700500d00c0c501c1540343c00c40000031070301c4000304028090140c0d0140001800040000c0c04010044401002143c070342180da11410f0b92060b020303400d101c030340c0d013000c540c400c3c1c41c00c0421803c8c09076410880183d4031b019000101d9240000e90651041d00c00d040210718040340314000401c07108207200f41c0d1240310b041c1000400082107038842c100c00c1c010041c1458140000030b0448021179008440324206580544144000c4800c00744d40071040200002884444a40f00346105449000d02e8000a14040e00c54440100314119032074400c1e03003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 698928363 1250 698927113 698927213
    0xf0d09051e0a05010b032802030c211204050a06120603171e0408070605210c030403021501060e120c100305190501031a0a140a0606090b030103 63
    0x10030701660120b480c0c503440d8100701c0d01ca40c0b80200c0a41c02d41008201c0316100d10541408514030300303100c4c60041241884410482c0d041c0a0200c0e2000e0309e580746c0320540c1154603040c1d0b5030000d001c0c0004509241500d052844980c0b584244003c002d07644e6000c481c10161215031a0980300d000d00d07200c03080050045900000c2030144543c07510f4290084078005001456001c170041d954980c4d80c200581e10714811801104031940085009201c920b0207500200b221480042d0703221080d040d04034906001040030b8601ea080c000c000814401416410031688842c1044046100c481b0751400e500902000b45101040d0301a09402124190034003080c48814030380400a0400c014002c982c0c50014000d1004a410017003d030108085007190f00035070b1041038144c81d803101c050307007161b0f90002d03403400e40c03803001040d04504c40d49508040c00d03c520346440c81c0e40900a00400421158104840540f00d0465600181c0c0c2ca13003410300040021aa0002c1c010202030300c10310040000d88242088013640850750100c1a40c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 698929613 1250 698928363 698928403
    0x10080a14030d0c120f0204080d03020c1203040317370e030415110a0b07030b0d0f0c030b0c0f090f060c060403120b121b0f0a12060f020f0d0905 63
    0xd11640095402a181001007010444a0105d54809040740210300400c2000d80c401c3c280380409a009c0e60040a8200120301111141000070308200070320350088804034005010442416080041c0c510000c4d000419011020401800b0102d42400140c0403540c0b110340e440850481c000c18011a0702c00c6404248030800e0301d40d1503840360451101d40c907640591100084014114000d2580089a0014070f00c3d4044055141910341840032005001c2c9110030f654040d1055030030400060004811001041c850f20303000b0601440c0d81810020b41c0e10040140c0c41802c401c0140c1200c21003900100c5400300400c6581c46088003640c80480e0980c055040e501030540b04100a0105060300404501c8000c00030300c00511920803140140040c1c52044105032103940d00200300240340342502010203145040151103c558841102c000031400e00780d6034099207000044501000900240d40901191030b002c03c00198981566665034403118803e00c0b031000c0006540740030079401c208041c810170140f10203c1041c0342c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 698930863 1250 698929613 698929631
    0x9040f0209370902041715040305370201050718050910080f0303040615050a050105070609052409011109010c060b04020d1b030501030c1202030a02060a05070b10080a14030d 76
    0xf0000d5115001d44041c1d404030701491040306000140d501c251200c81010b8414645540d5026160390300300c1c0c05460b80000c2d021784008400081502c801c9600079002182e020068085400682101c0003d0400741c10811000c0c500c4541c60b8955800c10101c07841540d40e04956914454020382c43e00141d0003240950141400c01d44043c0c03c004003543c05203005076410082400310304244690880c481c840d032500500c460380c08100ba5030050016284c07843c001c0781e001c00c1c03852480d55183c0c00c05114610181e40012403c600b05c0d8841e5074900c105902c20340200003045078401d11500250b480c007407540c03258100801d001d0901d040040d19000111803c102400954492303203014260400340c1a40343c07103484240c590103842401d4910a0042d2812240c00410300e107026401d1800180d99081a0002070383c040c4145200c2030010386405004042046891361115101e455600c3c01d82900c50002d0b280c3c1d032000ca00b10074140550100400c0440f0744075440650f510000800a088505501070704200100d01840e108820b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 698932113 1250 698930863 698930879
    0x101202060c010f201206100c02030a2d2a03120215090303130809030a0c350c01230d0905060709060c08160f0809040f020937 55
    0xc0e25510614603100d07100c01450310240180c0502da00c104051185c44021540341d060442d140c0114070200c2c54030300700031201500030034501030824100b00e0313500c0301c1e0344903800030741c22460b84001602d20b200d81072200c0c850b015102c1c40303030038242019010008088900503948403041c215038440219406251030761031101080c0040c0d110603419000c103c89035104e800107a5041004001c0f80d100e5408005103000d4061262103099a42d0003040d007164140c4180c0e2100d5001c14101d1502e0401000702c100c400b01a842090406400e440000b0008034001e44000300c0c140a0b1100800c1030092030200707180520080c420f0441c2426600b100200361000804006000004030700f540e0494402c19006000321812602c9140044a00000310b02c141d10000d2804440007000917800310041540d00300185100600d04078680b02c20301c4880d031a4204482c0c484002036150307840d040c2070154008a42800c00110b051002c1500410556182c212900c800e003a6409a4503030b80e040c0d00400d07a200d8101e03080300c6883c00d030384030018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 698933363 1250 698932113 698932121
    0x405062107050d38240c0f0109050a080c070504061e0608090d11121c0f0203060609100903120f1b08220504090b04060b09101202060c010f 61
    0x4142141030070b00210002e039000e82030401d2004404440c40c0b0b00b88600f1041303010122044a800268003000398400d0701500000e1001c008040d10b1480c00c8555030b000d042034080d1900c0c010300d405c040d4690411281402240d00490014141a0000391081e0b4400c01c07441c0342810101c1d56000320b46c1c012702c0c2041c08607944000c0c000b07002e94480d480b403035124501d407103510030746520108888081c02607000112920300d40303100d1140800072810b00f80803161644907001405480360031041d803c880ca440e0210741120020100d008020350001d01780c6085141d8204a40450901d02c115841c1600522181510701b100030710641e00000119080841445008031310340380100780c0e61f018110500001c40c1004400841c80c01c03003051444203544a00000e11b009928840030041d0f0b9405442100050381c01c80001660f910f40d40a01003049205480342201c0f0700d0645454400c64034841452070044c01c14100308a43c449060450301c080c0c503080c601c034495a0b400c92000540620078203000700c08a5080569284031000340d03401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 698934613 1250 698933363 698933377
    0xa030309030b0a0911040b040b04061e060f2c18370c0912210804050c01032705030903060106020a0f02011d1206011a0a05040506210705 60
    0x85004015283e020840c3c0995103001000340c109114803003d21402e24042c0c2c810310f00300c2c80281000c10b84090103c00501101c040303a000c079900c1170700d00f1404020740340011502005400c080c2401e0310f1190002400810400e82c10b0343e00c0c454125000450040d4264491061101d0072004106400d000407540354440b2195054407050391164072040903540c0300d803c62400c1e0301c01540c02d1035510207014150004c1c0019003020103105050080307501010030124160f80403240981c3c0103044881000b03500c0b0f6200030b110201c0100382c3d42040f110606101c0011804103502040792024a0003103070000500d10b98180e0a0254014440c090074404a1384013000350110150942040480036504240e0307a8602c1642c407114104002841c080c0030b5803500c00190700a0719140000c0c01d1481e40382c2044400500890600318052145ca80c0644c4600010005101c1005038404e00307040320380342141072404107940941103000d0750145600c10030020880544040071407034000a2041d01e14020f0344542010140501184c0c4004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 698935863 1250 698934613 698934623
    0x40201031b0e040c0509010806210f061518160e0d0614060415210f060b1e01120b0607061b02070902120a022a070f0e0f0c1303020a03030903 62
    0x1141d8002c0d254041d509641c400074041c8c641021a5888108200c0c1131280030350324600e80c1c804940c111501d00304c200f0911100c0e40d0804000c00040c00c100800080c103103900b6000f103229294508540d074020010550b429001801c4003d8105203d10b002020b4034031201e003611300c5130010425a00c20040c032001d50051000144200c01910143e111241440305a4001d8001c41d650041841030400031030782c6119506004041c1e1000c413901594081e9a40d415a4801403401d5034035585800c8007840314984404103078103c103400c1903a030160820180010b0703c01080c00c901c80355000d555200d035603011384074002110f01d41c0713a1201c010056100e81c200350a020350039030b1184100600c143c4070040350104140c0b003110700300c145803034035003c0941d00c810300f40c0b010390b00220f0165820040716441c03600d2494880411006185c0840240c80d01e40e00b8100c103403410160340d41c0440390401c2c8847c24807002c50144001e00b50400c0010829075901d403044408060001226131000390000d01c030700000070600d43e202241034245c1c0e01c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 698937113 1250 698935863 698935871
    0x1030b09150406150c021002070905012d080d0c02010207031a040c06030b0609090c07380c03130c03080d0f0b1f0f0c020901030b0405010e070f0608040201031b0e04 72
    0x740501c4d01d550422840314401148a501034280945881015996055103510413200f1141e1510303541070680e60300380d1010300012603000410024500140241c5203104030181455240c5240c02200c981d5403041024640600c1100d00c560010b692080c41480c02568000c02c0b01c03011a00c154502040204080f036056404c000d543c0c01c0450014464010344402440c02005a0700702039505082065a900290100500070020081d90b40041d00c544071460602c8806019000c02c50135115020580010403011701540d20082c41c01c1001300d10000701542d802180c158607521100d4407a11344001640c0b015080941600b001255810309002c1d1904454400201d921040c4982d452038024000380c0d500021001c01171414003c00004501c2c41a446030711900d82c2407500001170765450b004103000600070b0f04286c800405000820003400b8090060400d082c2c82d1500510b030091801c00c000c10500114000d007000c020045001c20190ba100350407414115000e0480001e6400c2d01c0c50001d0300001c0300c100c00500541c28 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 698938363 1250 698937113 698937119
    0x1305040f0507380d0e160504020418020c0f06091612050303070e030705040606121401031a04081207020105190608030405150f030112110405040f03050901030b09150406 74
    0x80e02c00380321440580b5100e1018040142000207a50440f02118111624050280d48451001c074007031240c042070050040e00c10350f0082101031541491a400042c011030040004100c0021402d00420485552050050b00c8440070303481c442c03d00c00150210203081c410b0740207001c041000483c01c040301d449402c820703804a03507491600d41d010868955010703200e60814000210b40c0c0307020380d0210480050003020f654030640c07200c000904903005030300524001a200c205c42c07402070350103110385040e000084e5504540c0f03603d59540c8076560b080024484500c0355160000c40d08122040c03050720031140031401c099100d450710900090080100b21021028a5000c0b200b404046501d0b108900c10340740c904000e90314007402c210174007450f01c46200b980540000104006940f52100f130001d14042c240d09180808048010306140c42d120180c0303d05d0314030a0349800c2c01e00c000528000040c09010754141450b0f0307114a80c160050b4010030820300602e400140d8181000b00d10325103044203034207020045404004183c1c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 698939613 1250 698938363 698938379
    0x150501050d0f0b040303060b041502010e061510021f020d140c180d140607022404021e041104091d0c090606070606060201060513180209061305040f0507 67
    0x1452801a00b010124034a07030010549100d5041d9009020741404151107a40b40078011155105601188000b803644000c019240e0303086c05100100e80d0710100410050401c0008207402205a40e54148510003d1600c00b001d10f00900004000300d6100d0808103000a824541da0007039840681c2c071341091445c042c0b5029841090130b14031401590b028036120b08003c9920244240c0304981540c8591004c001149180001c0c0710900d20307046000d41201502190800e0200a0325083c1e4404810f10480010365503240700a40e14900640d015030116038200b19015042881000b0131001c81c21150400e05044841419581c4000100110303851b24008102910a2842400041c05003214440c0540c100c3c04002c1a9071801540e0140c008500901c0c1034680340701580c80c6012110303664407202c00750351100300400c43ca1a1103020b8021021040c1010322183c0c603e400103400d05440c10b10000c0c80381d24a0404904c440c1ca0b103c6000a6042c000c0d5020040d604050910040f2418540000c40ba18412000e01180382c41c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 698940863 1250 698939613 698939629
    0x3030e0d11090907030209040c0905010b0309030d15080102190210020903060f071e11071a09120c061309230f04020103140f0603060106050a020706050903030706060315050105 77
    0x15030810707030450281e11410104119844007420201840c4100070740800581d81c2d560b019805148500000524180f42410305019204140d2240c0c180c1c42041c410814206c10104c102c5855501d034280c0041c07110f00410f44062080d060360040000e561000c2080c902c444800e580b060b1403c0c0d001d40840d4229801680442c0c10307807285103041a00f68201c000881d644000c0a1142a0000258107045c0040c00207038039803c102c09070010030640041d22551040d544034074107001c55409007901030244044203480980351800e0b0b2080e848214050914000b41106014042c825141c040f00300030700682d991001e42803084140303011409a07400b003a20707154520040ca01001054182404180540e408030f80d02d001443e025904000d00a80c145170325280268482d42d8040f0780380c1c1c4503500c1c810340c501c50b070b0a004040c1450603d050b080758044c840d042100002c1c540c1c0000d002d1084034150f2411555964441020a003507004d01d45004000c141401800f004009804440595550694204220507a6510308102440f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 698942113 1250 698940863 698940889
    0x2070c0515070b10030803100f1a0301270c03020c0115320301140717060f06160b010e1905010e130221030a021605060d051b0406020703030e 62
    0x1c203030108042c900048040b404603a01040004a0806031a0b0b41d0300c0d801c4103944105c40b01e07103501000920511071910140c4042020b090b80103c10540c910090999030f40c03034881802000010740c0303400c840d441e241000d801100740c42141407505010000307500c80090060342154468850030350818010b5000055070841d81400c40300745580380d100684200d228540300ca1040303a00480c002500a08030b0401c0e07102400f80b01e07286000b102c4003942c1440c2143c0000d000a80745241010000350503010701c0680e40d6800c1c803c0340520780c21110700d40c0c6c540c0350f04100300071011900d07002800c40009100024030400c5508125208545c151400c1040c02140e0060104481c400d00800b5140d49aa00119051042940c0c503088001c0c8090440645c01c1070100b00c120040c00c02a40d051025440000e440031800d074103100d0200e22605201c1001600c5041c8800a84c0902078101440c0300704c0c0d52880020079040d42c0703e0079a4543c0f8020a8030319030f03072034a80038001d40703500c241d01040e00814a00c07109030556090141c461b80c03030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 698943363 1250 698942113 698942149
    0x100501020c13020a0210180611090307060509120109050106030b09031c1d03180f0f0906040203060406171005070f0f030b030f10140a1e02130e01080102070c05 70
    0x10041088034124000e40048041d601140300c0d40f2206c82103010984102d20440e055007000d021061028604981614120041c1c0b00d2440700510071820651000190302c010754510b400c04545860318400468041444c4850860380782d801c02061406014040d400b010990b4014800d48190382d41c4c0607140d035a28854085c0414132040c0c02c00c1d06c1040e4003482c2d4480c0710b0758803034104450310505034402050319680060b0030300300c008800c41d42a5042d030301c1c140103a8503070104242c445140d100041d600080c18502c00600303882c0107a0b00040000c0207503460354070541c003406500368041404071280508996841d00701541d0040c2c0e501c0c0c8804161424002c0b9110940204680e4400c4180c61030300c8030803030281c00c00040c00354040c4100542c00b428010305000824410030300c5031000800c6110200340c1200c0400150070b64130b803c1d1030040401c172201c90461001e580c40c0004d55003d6910b003a05812024600d1107680f0845d0ba80604100100f8a054107400410455018414070089141c580e01000050802500d403442c0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 698944613 1250 698943363 698943379
    0x50705070905130c06020d03050603010b060d0f0605030102190f020c0d110409080d150b030708061912060504050d03271703010f0e1e040b131406100501020c 69
    0x700e1400c0d8020320f5000076403000048096505a0f1102d100241e50382280313000da0400e40ba02d89805a2510625a00400840082c03109000600108855205804141020544a0341d0052058540ea040740300203080140085580c3c9090210660710000d08a00080000322070501d0302d0a01071001810005541d03004103502d0300d038603140e903481d4000002400c0340c40d0081e80f58142075003c034a0502c0a0008901c0000010a404404542032140000590072080010400b4002d1040c0c00307600c4104c807070703020800f0f031620841c15003903a4209012130391503442070702e40e0401048488100b054540001e030156104200300d41078840c45880903810358000b91702c280c02d69407020b0815180c0001042a081b8520b002d12030400c02c114070184030f1180d82d03109800007095840b81c03a03c208488558180603c0d440003901032079581c4c03e120590801100750020b0310181482410101064044810b2002c1e1490309074410f4118410701d15011f40707207485071411186400d00400000300000e00f540080740340f006421005220070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 698945863 1250 698944613 698944619
    0x30f0703050a1e1a01090f2105070b2503020a150e0f37021509031b0918060f090c060a110115031a0c091302041505070507 54
    0x30000d08000b8100041c070354680e8000c2034040030b03450506448070035603203002c13804040440d058090483e101d0445410014080000c01c4070301308140800c030680714100414100b0103203c0c0034201a01800396405085405055000240816003400400b040500320703407410002190044840406207050f1006000b40e00030804040000f200c40002894042d1302580001d4005c5d850b00b245841e1200000500c00d0640c000b80d41d1201001414850b0b090035241c8100c44203a0162010320381815480c0428001c0c00f03886000e0484a008182100b82d03032410714003030b04440014000e100d81e01c0356101c4c0c00181c180100001c42c0481d400580701905182c01412080040900340c540000310b000c403e0300100502810300900484058944e9280001c0040c0c80c9241d407401c81d00c041c10803650b801c440b4154481c81c1e103260074240810007d0052286401070001040170030409a5500514404501c43c202e20554405004240303c407010903a80d0140c0700340c64540c20400c0802d00c0b107000a40e2030344140d010103042540721070010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 698947113 1250 698945863 698945867
    0x120604031404120302060910050403090b0c0304090c030b010905090c070f0204021303120305160c0f060f05010f17010207020a0b0304030912080a0f1404140102160306050105090c030f07 81
    0xd0707105044846452406988081c0300f05030000d51842240160004400c0c411004010001010700740c080d000c08010ba03040c075642c06031409409120750500002c0104058000340020f105450040c902078100f40001c0c039101c40300800929816460b1404500d100381d01149a040084c242c522031031134600d0b02460049a526201c0d036400440d001280c0c490340801c160300d004000120188011031240c003403490516a02b030009403c0d580c000300000503007095900000c0310717543d00c05401a0b405030000c0c1180b1117102c013401c4c2540940340c0d2a40e00592282000000215031a5080140080717039811503210407000b0304003031a075090348180440a50310420204041c40a00800d00c011034129100341041c21000b6600e5080348210002c04001f034075944808551951000d42011014030880d0207440d05110700022000c0c1c01245025601900d850398080d2104580c090f4000c02c040000c425507500c1030050b1607540d1a00801070002405840d01940080012505401040d41607a004204641688080703076140300702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 698948363 1250 698947113 698947127
    0x61003080427090503131d01090f0213080d121406041817091008060310020d060305120a02070806150f0d151506020c03060a0504030212032412060403 66
    0x4620000c00707109100c20b501880303200c0c000c0c0681c41000a103444180416103c0030240180e80100320610100402a080300302c940b00302815103000c1200014041104008a0001e01500c1d031310021000070040c020566400c0060404c0003002c95a490011052190000310207858800c03040310b0b06214400f010030041d02c2d00d60003210304039400920018401c2c00d1b50311404ca403c5940c0b281c0c4104400000f44090080c2030046069441000508020002d81000c101007542c40c030320340c0030041c09240d0104003120b10843d10707040f81c0d000310341040c203c1e2520446540517a082da400b180101c8054401c191380000c8d01d25010602c3d9204a141803840310f50b20803807105014191030040e00c681d40c4145000128400280004042c4c110f64510145c0016101c2002101c0b07043e0031060f40149080d980b045052400e1550700103902c0e5070100d007090b0082599101e500d4160300d0294850241c042c403032408030400224203000680c00c8444001200e1440001c04071900340042052410b500521940103140001d0110b806500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 698949613 1250 698948363 698948399
    0x14011a1c020415050301030203100906061208180f0907030c030f05011d01060318020609030304120305070c0b04030c0312111f06090513030815060301031101020610030804 75
    0x11003403621500c030040803000850040000601903021900703100c41d2024880c1a103a034103490401c10f10b554115000a540d44903070000c196440754070b40d9040400c0103065004940106440d4002d0020b50b00c0615007925140c0020747e10040c2e095103815a0031080c603018900080a210140081d2550748541304105c0181000404600074992a07900003100c07555a8441d0a0080213059082141d80e80d000c0050104494103038805020141026040c20a014010102014066044403025511601800440e056000d268403074a140304d00780348442c040c183c0000003021414441c05207003910a07210382124006020b42d004c0170740303800446902403002a070300280e0241e406c400fa0805e00000741342c1401c0140b401642c10540e001102030844010f03000401c40c01801c01400b07840000b0301c840e02c0e003e81c00003482446141f0160400c0011404200c002a610b8040309021402601466403982c5030305002101c003103440c0003140148141c038000303030010b00c4c0001c421003583d900411700c5180500d04080302c188095044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 698950863 1250 698949613 698949659
    0x10b04151107060509180f13061803031508030a0215090109230115050312090a0e13031106040f1217101712030c130312020f0f011401 59
    0x181c950059048200100d90083c00395565090390345a00350248868102900d01c1c00e0072088000007849290410250744075400071002070440e41d0000baa06050010b00602d04a80c00c1d03c0b80000600c10503d0782c1500024480071409011b4180182d41d0b2910981d40d1240c2c40030080107800005c980100041d4040a090701f00b03916600201c1c0c51901500d4a40700110040030004103104010f802250404080c0100c80d10182029501d0b00d1451510001ca511130b450440320903080f510006641d10315076602110341001e42261000102d1074a003021074039103007a80e120401d4002c20b5000e000351184000000b041c901c00c61740725400d070300358503400ea031a10400080004a841880352009801c5c604100c62240c00c0d01c20360140c801c0102c0d11b890320040154451490040390400d40045120541240d1842d0407240c010035203c030600e56500314041502804091608020660040c041080540b1680012550b0741041041c082d28a000c500c40b4003076007240d00c41101692004440801000510a0090744298103003180e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 698952113 1250 698950863 698950877
    0x801081b0f03031206030106050a12062708071106070201053705070b060307030206070b07030605181009020310050f0402090a0f030b0106030501030803130f0819080f010b0415 77
    0x1d00300080c00c541200c000084458001800c00813245000d024102c014102540c0071100c1a043c503020139144900310401412061321486544804075201400e15101c0002c2100c50407441400d01e4a000c4030b60001b03909444401c00e10016803214944441141c0c2c046905071180e5142c21031040b07648640341d26101441440741d4050711084004440c48400003140b102c1961581e550714500c4c603180c1c2c50202c001e801140260700070807050005131246801c503003200390041d20300e240a0b40da82204a02415041c3c0040740c0000c5070450b0301c0268940384c01e846008074022500c0308241c0d034070780b6800403c0380821203c0209918603020100302c05c1c10982400c442c8058081c1c80580b03059000d002088680e107180e40890b2084c8400207042052040c5507a000740586031900d400e01a551641c0c403000e00f18000544480310078181d6810362010403c0b105664925903a1022005459605400700c1b26038450704903186a0104000314009039101008841c41d6040c0c407460311045081c07904100218a410b030303010341c0880c140611 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 698953363 1250 698952113 698952139
    0x41407060e2e180b04141c0507060c03021c021e03040906080604020a12030807141b0c100e0a06080c0c0118020f010302070c030312090b18010c0801081b 67
    0x20b4000c0505040c4203986802e4941d60a5150301c80c00307501c456100c0e044051040c0014440000b000520711142402102d0501d890b4201c4460021030f02d0300200c001341544194140090001e40020061311490b000c2c0c1c0aa07540340a01c5010b148031440002c0320400160000d404640d420880c0f10040b59403050420308a07400e180e100c2c090f20703084400c550820460380e80b04404100840c60690700240c007612900c40b500051040705d950240090a0190030b501c14804040702201d6014009426152200301940c404603144586800c4952589810038080d405401083c16502c022801070b081d01101c00c0b0301401c90143e241c60700c4030856215401400c1d404031b4890400072441c070000709008070b22001c5074100403100d07440f07068410050044c900100e058103260050082c1d0002c10340007400c401c200c9415080c1100a075074000c4910340106080d131001400018444107001c6281c00407070785400312001c440020003801e40000e500790344003102403045170b40a600800040414000f540c0c0650380042001d011111440c10b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 698954613 1250 698953363 698953429
    0x2070603200708040503210f033301030606210c031b020c09011d0402090c09040204170709020f040902090f0a092003060109090e0f0f06041407060e 65
    0xc0b041e981070f0760100380070600b0300c400c0c0350510070700042840c242c11016180c0d01400315019180182d10003032003188000b100144450403219050140840701808215031245006511009682c0668031240081c2c13170b200b40400c0c1180240f6100c1510103510102c0901c034441c040001c000741c90341410080406858135040031100c080d20400e80c1e91450550003a120038451b640500c503030120b0585c0100c06c03030340000c008201200f00d8244000d0304541c050301c110f03c0030f665001c008081c5114bc01741e101d03081031000900040340401020881c0b41001204152010343d070350750014034140d0040c04251480100b04000c00c0240b041d042d0f0050540800251260200380c00d1080001c08501c2164440c0c100c2c42d1300c0e01d02c50b801c0c03103284400040005011005540c00c0d0f092880c002044103065000300c9000c950b0310446480c082000704a07144240e950075003210311100307800ca1190388a81c8180d40032582180d042002c5090a08041a040d0680e2403e6a0715000302400d101042412002248210300d100070084484d900c10b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 698955863 1250 698954613 698954617
    0xa15050f030316050c19060f1803080a0306030b0903121f051e0d120e0301090c05060f0904180212010504021f0c15020a12060b030604090503122805070207060320 71
    0x10100e4080180035138038080e0060410921354040d00b0410030740d100c150b0039189e0007240d2141a650400b103640c1e1a00d01c02d001c144d00a00b1079030000f80488444808101c02d8110000081c1520151003005106913101c402d0b28684500d01e201071a119880420014040390070484104618002c00260041428945101040b102400903106aa071350b502001568074144e001041a0344a06d405c1d40200111310640d1101c01c090100c07402594812000000e0000b041030390203013943c1103003c00030010007025420002c0303410b44a14841089005020114040015400612a0758403a079005041002c00074540f00d00314400d24a8440c0710000d020540c0e2003480800c641c0b038040f0841c8011850300581d9110b0000010f04506039410000001d14103203102031202c000d0520580340c002c4070940d0007140c00300d41c5143c0241940201802d14071400740541c104000300780d046003030b004802d2241d03503018044034010342c40d4001d07940122a01c601590001d042081f80701e02c02e52141c5190300904501115014000342e0351000f81d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 698957113 1250 698955863 698955889
    0x703050f0c010209040b1f0305100314010504020a0b0c06011202010512040605010e0a02040315020903010209100806091305030711031903020307051c022509050a15050f030316050c 79
    0x40e035000c101300700142403034410302a160108444141c99050b00360b445070114084601d069040684400104072903d006240c8100a5548014100c41d034141100e00c450081c881210180d118200304a4001072400c5520b00300c5280d082250042e0410741c1c2041da60103010074000104a040001c00c1002080030081d0968107401584101804905549014100d0b03046481c0500b401c181c0610400040001401c15604440c14628503d0050b854103501c0300043e0081c014034a01036080000d031012028003e40c4090114403030b10301155a202c007500d625184004402c1c0f101c10051080e801000b03245c01149200b4a60849220000d08544122a40010180f03000c00b80010450241c1c3c00441c11f030b02001740c1803100c1c1c0101481891001c11210071300d0002503503030380728030148140785134160f0107030201e4000302c0903503030103403034103520034046410701040349402400450007804200620080202d6a0700d0441a17180d103441c1c008009600741100c5101d8004590480c81e011103141c4116000d00c80c198131440400d08032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 698958363 1250 698957113 698957137
    0x90f021c060507030b0109091a0d150f0b0906010e0d0206040f0303080a052e0b031006030b030a03120e15010306090c0e071707110708010e190c03080703050f 69
    0x51410380350032010b441001e44004145800d00d50340107501e99102034100f0844100e440d0202d40154004422659081c55000d0990060001031488082c0a40a13800324444800150308010392018012100c0403a0f16101c446130744410081c002c41c240c1c2d0300c200b402e030004050080054101c0c0f904da9000841d10362040e400030802d100828010024140c100b2102a0702000001c0240058541840141e0451607011048840000e01d0303804490743c40c24141800001d41580703002e85949091850f10410801241e1150030002070816420030103a007004101920389030b0740340d1282c1c8422200d2095500241ca03078101000c01c43d2007102000c110303012941c441d95008500401c000205103050342805140c000e001c1d040801003207410001c0c480043e82c0643c920b18040f00d1920184c0b0b4540707810508440c540c111a02400092260400c0412410030660051241002c01021100280180c1c070629020f1590070750050b00002086008001191214000788030580c0f1901e00507142803000019812241c002110044d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 698959613 1250 698958363 698958409
    0x7030303110c07080705031902030a0206030405160602210a0801060e030c0406090c2003030a0b121e0f0f10090804150504030b0a110a030b040e07380d090f02 69
    0x41b0a05061000700c90b1454102e4003001590b010b500481d40c0c4001d6000001e0042d000000000d003408000d010304402d1120f17000000c10700c540c0c0c841d402591001ea40d940c51281e6071600c1c004021500c01001144c40402c1d40341c440040c40d81ca050000d840c00903240c0c20140d010b019203900000c8503a1240f04080280250304400103080040e520010201105582100c1541c06520354042840500105903076010941e8400450020200d201081c2c90320907601007130840d440382d5035111148a0500b052007202d03218031ba00300c50b062940030300c0310b80e900c0d1810200c6010f42e400c280c928099290b65a001101000d004800c414036166440d9904900300b803190030300c1c034001040802e0600420641e41c51494110b0300e02a0240600880e002d0380311640e105500c140014180da41001031003d88a07900001122418242036410321a91040c90b0301e07144506680715003e060314500d86002c12650303e078811000b00f031074800940c00c100d04007a03010002d0200440c20744680d0b01c01000e810061740c0311040310464228075880e0741c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 698960863 1250 698959613 698959619
    0xc0b07051b01020f0a11061603030905010f02041a09031c08090f010504122d120b03060403020304051e13020c100c140a110a12090e040507030303110c070807 69
    0x8180d50000503010b0442d04020300344440340d00000b8909602581102d420480d41074081c000411034440c8603001580f50340110076041c180b40c0c0680c003074207102d4003520080c400d40c0400702c1c01908910a0340034078001494003904150400180101408370718101400321107031103a02915000c002e22090710090000f85039a410000c010400f440300916100140c8000e0100381003d40e21180964a541100d8040103046444c402820016062040c41d010f4218864400030015503801049103c01c0c001000c0380380d0a20180d40ea2500340001e00074469038240d400303941894284402c00c44d040242c4140b40b2100003e07003112a5241c2c0d10b0390501224214918001a550340f84001c58a04240c4034100700300501d46050035001d415500481c8462440818810059071204a00f5003610100c0c4100080a450301c20240f0340010002021042d50609203903480715844107a4458241c2401c8400b1580282140c100c0f01003040002d0094000c4003901d4406010700c0c1c14410410111481c0c40a198031440701540082410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 698962113 1250 698960863 698960893
    0xf140a05100603090309060c05010207023007080a0609050f010e0d0f020609060412110102030a09020406050307150513180906050a0e120309070506030c09010e010e1c0c0b0705 77
    0x50004042d241000d00c80915152400b130081d1001d8802c00060200603031172041000404c0d4100d03060720f64000c4c080c05908140650300d5880c5103d03110303968a151401e100c50012090300141d01001c4078101c000900c24a4015034034a000b03402181001c6440c3d100b9000d00340710010080c0144003941894034000c00070f070714100c4c1008252207512105101590001000d100601c00302091543e4440e40108400d074400d00140c1c0d04aa140c11500c46034800d0b544040180210760300300c0c0e00102d071118000c88060000f90340702e108040c1c031500140700344030102d00480c01c5e03061094000c6001e01583c3c03198074068900959a00100390048100c1e004d4966a955250083d03c1084414400d89801029103071040041200307814400e581d40860004040140001000045c0013100410545024020180c440c7e5201c0c00d145803254030603080310f00031300e02042241c90414907a52280f26141124400142980b640c80303000020000c0b40740d208081514001c070803060104d0581e280b50010003c2500c00c0005003034452581c03103c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 698963363 1250 698962113 698962141
    0x20a11150c070b030f101401140c0304170c060306100c0213060608180106060c0206071b0b0a080c070b010e27161406040e090a0f0c090c0905130f140a05 67
    0x40c1006d45a030303903400d115000360b00c00b1807130080c039003803c150380c402c100c050582900303000d960340503c180e20000401040d1001c030109000d1052110320100d48010309018100700701804229440c9800903441c1c9082810507204400d103080d814006020300c41c030343c81c190400c20140d41d0240c01100100e40780c00140000d960141246100c012340250081080170305041c001000ba1144d40310107449990089540000c1c00b0100500034001b10107410003020355903840c0380202e569004100d100740441c3c19240000c5040e21030360100e603416503204501c0d003001cce801c2000034040088044c0c06203041e01d41c44040c82100402040c0c9a41c0000d000f88010803000302a0034003c001c8491a40003a0410b01404001030752549641d420349041d5500802100e150b965000d00710b0380390000c9240064058484c410302d070001d101c0b40300c3c14442951808501807040c10090034060340c281c101e921525400144003840079100d445240d00c800010142003401103840c00b00741d20a8a03000c20150341190400d07075107805008209420800c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 698964613 1250 698963363 698963371
    0x7031b0503040b10030809011805040501081e0706091205100906061e14100c050735070312091d0a0b1905010c1a09070510020a11150c070b030f 63
    0x400d240725181160b0b50030503e409011f9145040c004600300d0044041100c540300e0703025050241c4100429030703644070100c0d980d1580c1e44140c05044100030019004000c0401c000098519644540c05506c4c07411600f0f58042c004071a0075681070084170f0750300359007017030600910203e5030041c08081101c034241410300d036041400a0220618000ca035208110319032403600103c00c0c20740201c800192a2081c402d00395001c001060000f021409192004114138401001111040302d0300380840c00c044c1a0044e4000350101105d14200b0030340e00100040001031000f680c44e610004440c5081315040b651064224451114540f00c030702410950700c20000407100611604905003c101e501c0c1c403500d00302021540c4028224010f1038100601c2d0741500040c4040a548440c0079030003000740c104149801c801c4217441f9074160040600c03030b41c90a00c500781103074400200d045255800211101c4250148020018034036200122801c61a0040c0814618040107201000060610001a0f50340c0e04d0540c3c040d06001500034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 698965863 1250 698964613 698964631
    0x1031401140c0903120304120f08190f020903011e05060603010302010c060507020102070b180c150f0d060801020c0d0f030612030c0f08040602010b010801080d051207031b0503040b 79
    0xc40d80000141c04408101c1d00329a00c01c228aa0711100280860300b04800d0191007000c20400009200400050740881d4030154206e55800210801c00c0070201c030fa03d00b080e1100e0300381102100e40d0510552155005e4410740d100d0b8a001440c124109001c43d09452070040c180c00d0141030422850716101c0c0c68003425038042030440e211460740d070440d40003a01c807600c1d110011341503030717520400110054001d60490b228903070007011003c00c6290801e000d1441258440421480340101c10300f20031942048030406a41c41e0040340003508000c8e224000e4413036074000342c40300c908480c0ca0741b5000403821401c2c0300824141d582c24000d017003001162030004d4258002480714900b098038011040154844e40110740304610383c5441c003458141c0150510100c0c1c1416a20003504400002a0001d9007030b030154440b54043e84281c0b40c0d40300e85d030790f52500d00383c0302d040034294000422001c1180b50000010010660741c04181410005891902000c0d800411640000d421000c1503001041c8003c1c40302000744654890b242c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 698967113 1250 698965863 698965871
    0x16060e09011d0103081e040e0603240a0e120304050609120913090303200d1d060601080403021207110114070309090506130e0d0315060e060a050f030f01031401 70
    0x886802c800c0410511010f8038010000c242260702150020200004054001c8515103440d2116030b05406008240c514505c0f80c411300c1c6013292400d4240b840204083c0c0d80303080d40d000665885c103c202c0504298044441e03a03010300540000d65a0103500510300483c0130300c0040440b807402512581c0b920f003a0030988460310100340440320040e07541c130745910042d468201d000709240d40307189002d40c0580b01051a24941540300c66000d814594500003409204002403802d0003410032400100e2541c9610850181254101200082141d40107491003a04540b00344103c0e44800d03c00c00c40c04800d038200c0c250072215120004d180c80619070740311021410714001c0086071483c0020750740c0c01402500d95032142c110025110030002d01e0b11743d2500c0c1c00300c54841c280c06091083c0c0481c000000d03221074000c1c03920f20100340f610360100c0100b245035440109450a41d1104447d04292008101550700328901c14030411104110820404901d0405513000b0340380c9010000c05075045260207440b9002c44460300301960300d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 698968363 1250 698967113 698967149
    0x302150405060a0c17131b0302010c080c1906020301060201061d070305090c060a09030b010e0415090609081204030905010f12110705070308030a0506030304060c02090916060e0901 79
    0x318003240c111407110350004403165903070f1080d601d034826040d148000880c0c200400c00321b07404144c443d4480c2d0780f04900c2d0349548484280707126041500740c00081c0c002a211401000028000340080c01c4500d040c0080b03444000707030399000c0020b05100790400c480c019004001000b50310740901a00c4007038052403182030390034910f01000071203011006100a00b05516000030030840d043c20302a1108003a0080c02540e17640310b000da400341c46084903110465650501c0c0b000083d040d50b1101074280220f40c451034000e10101034030071440140048140559400d41d44e01c4241c800900c120b4010250341c40c008a10990500e454140a000c000e402e03030105040c8041106041da840c0c0c0d1101c0c1c00b111041e08120000fa10514150040c4002d0280b0b100003000e80c07040c010080300340001c0101851013045501d8050140e47d0703c200505440c0c2c040d40c803410021070180240d810041c42c1070b0040320383c010a400111910120314841c0c0000c55591a801400491002d1016000780e080c8486400d0150402450488102d11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 698969613 1250 698968363 698968373
    0x10303111207320609031b030a05120a110d06060f030504020f010c0c05130e06130f20130b010212040e01120f0605013201020d0e0a03081603021504 65
    0x101422100300719186410224510450f920035005056001c00d0860301140303041c0a14079960340c08006408141c2072981d145c0424058008121140c0540351f90742c04c0e0500141140004e00c1c5000903003581c010315140c04001c1000c020100143c08a003c00d00790105003989030180c0500181801c04541c42014107220421016840e4071a0f4040c501c03900b032805c8600d90915040c181c07524903103500a1544252829440d2128502e0f517004000668101c000b59115601c65403041d40b0303050031102c1c009001c0500341680401140c1c18221900551100c43ca901849454080000e1090404c00d40c0d0500c00c40d90f200011400c9582c104240803801701401d040d54540f0741400343c1c4038030050051088002c3c0e8001403807241c00f00f20990303111082e07031070303002000b070005585501c213020848846141820b01490444d049000c0d00c6810340c502c03400d416043e00a41101da0900c1401c031040d41c01120700503002060f078036000001440b0b440007804641074440076035501c00814a4002e09000000c0f00780e0403501815024000410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 698970863 1250 698969613 698969633
    0x30e0c090117010b0405040501090b061008010e06060f0c0a05070609050a05040e0c190515210a0e0a030513080313060507060f05040b09120a09180e0303010303111207 73
    0x942c80d09a107020040000c0c0b501d50240c11000e107205d41160500c0140020060150000407071940f0070340b010242641c6100070b020b80105d500382c0c2000050b00110040141d21400b0f10000d0304050302404842c07415092a035035800070f0b1302c40e1a55260383da00844500050080500201c0d01904081c41d01000c2a4a808002842d07225180a01032103566201d0410850b460104001d160321752014154a03000200c1c540104000a00e620603240914540814481e00c50300c01801c41d0b00c0300d01d00000c8807104000044070311202d800010005041507070b44640408400004100c10320a89102c1e91b01c02c0d594104d690baa0150005040e4002d1820b94407d00032030502101ca005404140e8056241c2192214014240000a00601071000380ba0a103468217100900140203107080c4600401740c2125184207c00c030080040e8817039402410009100084288880350f032110070890040c0842e000403e0701e07500140d0060035548280c0c03080300820206050f4141c02030081c000480c0141c90b00002a0070058140c650900207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 698972113 1250 698970863 698970869
    0x15010303051209030f0414030a0b01172509090c08060a0b0406140d170f0403080408011401051c080d0e1e0307150b03010e011e1503080d0507050c06130201030e0c0901 73
    0x1422104000c1039035403010409c0401981d000a602002c0f5656852105e04000f40d010018019005040340c000080b0392500d40c8401c0e9070081c0c4800480245401d20039002010495421104007190725000181c10100300111801440e12980000d40320b01c07a441040210b4080ba80224070f8101d0000003503006a80321145620a5030308210800040d0010b40c98056892058486544490002180100078450b089010308107446001000300500d504400c40d01055080c00d03c01c15074040c4150780750003868034040300740701001440b407491b02c0c0c00e1180c3c16042000307640e68040001071641c0101c0c1c40c100c08074840c4408504041d14000650714000f03042d1225445050b40341c0810000075110b90310f000854500354081400180784074001c1140719080300c0b190b06010291140511294200a54003540d03100c41002e20003101d0340880c2a500e88581310341080040d14004000d1024031206205090383d00c041031100d14414501458050040c811034400541154100220808254000c900000190b164000c8081c15 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 698973363 1250 698972113 698972129
    0x618010b07230a12120b0310020a112b081515040905040f230c0d02060c06070203190e0609010e0609030a0605010e06030606060a080915010303051209030f04 69
    0x400120300c04200005503242040185104810304881413041d85014010341080603500c1c1c0c00c1d03000001c00304005131203a0151459040c1c101520400151243d6802004420719908040b420a9a4040c1c0d16003010721030305d406e68a080d0b0407294102c0a1941503441503405643d130030300d01d0043c1400b08400c2c01110302c9d0b09007240612051130180410b080500c00741c03002000098000e10080c80c1914054210b0051104100e80c84807145440d50030250500039842c5080144d00010605d0318151410000111001c0009a8010804104040b1982c1c1e09200e20361060440b500250366911540e001c403549220124001130801c82c0b80c205180c0b03256100e20031200e00c1e2000340b81c414240850354000900601c14a402c07554148500c41c2040204a240e4100c14101e80c1181000790f00d541d140c105068580801301c6850360301420402010440301e010304802900182200c0490f5542001c243d81741101e401c0030380003a004034501003845070310130401c802c14944c4103a00d900510301740100003070504c906024900518003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 698974613 1250 698973363 698973383
    0xa1203090909081e0a020d1b06090c03020a150e0d020108060f19060f0207050f0d020d0501090501020703050c0d090602060109090809030601091509020906030f060f04050703050618010b07 82
    0x803c1c4040078003030301d014241034490080d0f1005080d60706038260340a80203000c05400b8000013408080c0c0514000b0011582804840c1c1d50051541d40340402403640d048111148107104101001685030510000050000207081240c00844200050001d20700c07a4046441800b42c03242c00700050740d1040d411508001e042e00c400c0e220700b07540c60014400030b0b140f003070902071140e0880c80080d1342d980c840340f03002080800da001d0716883ca40b03545c01e0260307404403a040560480900e8403501d005041440d18605101d02503c0006600c03087c84d602d0a0a81c1c1c0860001e40000f007000c80c00850701c00084c040d0aa50748641d080c0380c0a07141c176010001c1d45803281446815005039450401c10b003030281010840744c507050002e058421a684480700d90300180408000010b1140d180040420614054801c03500314190042c0601d055070350300d030140f4461600c010720b03058003d9004600c804c1207403524050341d03015609685001c1031501d80a001e0209401c208410602c1d004043d000420000c001e0204542d0620740001f403200d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 698975863 1250 698974613 698974631
    0xa0f050a0b0c010e0a06060518100608060a0e01080d0305011d0610121506030e070602190206090310050a1506080a0207170706020d0b040902061803070f090204050a12030909 76
    0x2500404540703164130030f41d00449600384104200e50f07002d0760584104072260a100234801c280720072201411141071410071444034080c809a8020a125507000c2c031300605108032541c0303480301c800d20401c00b0390203049160302c22003541442c203030140105805803600c2d500720030190308424452041350030090038240c02507580c11100d081162042d5901001104141e05c20b0024080c511040042c11010384150310000345483e800b906007440126101c011216554010860b82e0030110404000c000000c004a9001c1d0f070806c0400a80c1e1418030005c1c4d80341d0880d810000301d5190100003034040c0e078000c8150810080d2001303c240301c6540c20a08460b0440c050620040e00c5040c03904d0300007004900002c1c50f18010f034000c00c40008010b02d50f0000c1c451114000024800e11042c1c03411b0106a52405600940c488018854048003840039044001081c0c40181102c40707450390740e8032003146451581c000d00303070907030300000d0610460600703422190041100d021a0090801c061b01c008008400034002c035010a500d9030612 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 698977113 1250 698975863 698975887
    0x30e0a0b06041b0e03100608061b0d0e0615010203190809030408070b1c0b18070210020d060302010e0607032f1005010303020d020f0d0e040612060603020a0f050a0b 72
    0x308990f800400420f030780c400f0204401a210080250015200e84104003c80c9190f40c65405030008a132501030007400f40741c69014080310300c411a40841c03c21400148507060420101f800740c18084045034001d0302c2c00b41026000017910490310091a41036500401000003e80503805a581440d2403d1030541000e48801a40e40c0c1144280da114441342e208a12010a010341c00709d000f40f0070f80840c940113004000d102a000300c1981d01b82107045520160b803000004443d0704066105500c191203105440380b20320302e82e6002c002c9821010606030100e984035410310844d6000401e4103c91031048803000d003071661a036070080480d011403114201030300845800c40c841d40002c4185a0307201500b1070544040d8540c408855000b047c00744000d030010310450349007021050001c203201c0450403141c1c01030200805454001c0c1d41d100c98002c41079820956440000500208250144819500c20500490300c1803842c010041c164146401070358008044440c10420743d07469030a900116040300480d42c0d00d84410000c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 698978363 1250 698977113 698977121
    0x804050f040f020f030105090129070f02090403050c0d17040303110409050f041106070201020a060b1c14071a07021012050a2007111c0f03120c030e0a0b0604 69
    0xb601040d2400800c903100b50300080f0001c0c6040c1d0344180d40d14140c0d40e170b0342d80c400203215412003801034400c104000c054040e0584c80000b448086c0c002d28041120300843c0d80425140c80c4100c406a0024001190800a0340018001da12801c0fa1524014000702c040301509c81710280050402010b1555800d100380c0e0003803021003950000c02d0121004c002900c0d0040d02010464030442d411149000c4034046103a0341d103800819100e8054040c3d004280c00030941c0d41c3c810040544a10240d84540b9011208a07481c441a520b402c180c0d01c50340d24029440d0400d1b210502e45201c541241c0b451030f41100034105a000014292500715804580088072800d105005544600d0115007400d54981031400b00064070985802100c0c454402d600c2404a01001042d044654068154010141220600000428a41203180350b2101c0580c00746001e854105685110341340656180440100b0144030030803400450300e01c903a0044d400a0b04003406a203008130304d1140c072003104482c020403160805002c03c4035a259030740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 698979613 1250 698978363 698978381
    0x9010e0d2c0d080307090603060b04030807060e10090305090a0905010848010e06131403030c0d080a050f0106050a031a040c111b0306060d060b06030406090218040804050f04 76
    0x9030803956805d0030300303008205200d1800f602c0003090030300c0000030b00708041c80201c0b01160b411002c003078140f0502d603403454003134800c2506d0005180300d070880000c0704481d1886607840c00ea10a84600c0d42d21040302e02800228541540148500340c03411004001814000c01c0c6001241d01c03801c400c1d01880300ca0000028420b03c50401d0a0b02c62400107044101480c44a02c00c50381c502c1d00762107080740c00300d42e1030400045100c1c44a40d482c02050031036040040c40d40490202c440b000307000f025130707007030915a060040c940720030400a500041e40b4501800440340b007078841d00d80c00400f05180000c0703940c14540043c0a03031282400309810196200c007211b00b03145003c0030044d003c0b14010b10a0280380380c4400c00070310543d58800418030358007a10502c0340b2910040158504401ca028006d00702907a510810422504500c000c20b0b90b5941e16214056050b50743c4100075849144103c10010300e09185005001d05100384000c5041000d08820034400031038101410703941190307001c80310740031030040c040c011034042e01c0400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 698980863 1250 698979613 698979623
    0x30513120809041409030f0a03060b0a0309120302091e01030902180901240510120e030409060b030906040b070e060d201903090609020909010e0d2c0d 66
    0x614038104504000100801c0b04126000d00c01c1500101201c000b8100c240d5200906520421425014540500107480521114140090001d030f4802c540351103580b00d08141e000080e580d8610ba410032106020580905a040c41c046080c03940110100740480080078203401616004a40c8030116803281c0c11080ca42a40601304641311601c40003000603481c020b0ba6001c0c500e508041d50004400c500d1400129580f0480b607540c41c140340f4100900c68403030110440101001000000b20310680440e001f456005185000216a194a00800242111401e4214040050042061059002d400941c1e40d4019801001c00146034450b450190703441c80450280715003141c000b0825000c00354580d40100c0d40200c80c0f41d442000e040c4841481e045503c5011000c014091a030781100b50b41610a50011140d1846a034000032100003c1c1c0015050742c004466140b0281c2d15a001c0a014400034007c0a0802d030b62800c0ca0301f641d050784080002842c6c144030b480804420250b400d0340c5140d442403000c0749015000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 698982113 1250 698980863 698980889
    0x60c020d0204090b0f060d02090c0f0405031905060c18040b030f0d020309181003062712030b0406050d0209090a1208070206060108010f0b030a1407050706060e04080304030513 77
    0x3900e48000600c0b42214100c517201c42c0e00700001d0300742c00c0c081c0d24000311507802401e210181d600c0741019840e07074016000002d503d0a040c000880c1070b4030200b140070421a03100308a180c01c01018503009140c02c9000308180110130040c41460400d200c0b101000e02d00444c08c45010a013442000d001c0391804a42c0348103a00e40348100c10208030229000300c02008014030903034081c9200790400d0130107500a401600c40d03c443c04c000e11340070004605164461303a140c861b0080c481c80c004520280688103541150303800d690255040304840c4003540c051246030204101079400340304840c80c1c00005400d03600e0340e440c040e000e130f020070000803030306034041c000344142e0345e48101c4040e00800a50030082c5070b10001c90b440409403040b2000700e640c0d5805620400d040310340150040410394189080200d450b0409001101c02d65107a00481205482042006114045030707618aa12902d01c0d00701b0006440040d8400c6801004080c00c3c0f1002c2405ca03400c0b2941700c0c0c0c250812903600c4107078151040d40c801880d0311000b400c0303180d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 698983363 1250 698982113 698982131
    0x31103181c0908010e0601061e020a050a03030204090506010e03030406030e0c12010e06010b12011a123d0902090a080a0c15020d0f120608030d020a090816060c020d0204 74
    0xb02c0341d0710070754045000811500311071004903542c0d1482806050040b48010409090100da01122102050400d01c16a03c80301402c0c1c0c3c1c2c01e8a0411003084c1200429004601840000b00500c03a055200c030003440c2c40018424080046500ca100c0e5015010070582c5800455440d507a080010750b199080150003031052440916506000f030a048007c168180240f038000154034520340155480e0b1001d1414403445a43f07000c1180c1e43c0303404005040a2601000e01900c207074034442c40b1500d8450f1440356240c00d19801249011061051108001c4055005000040c441c1d0500c108840b03068444611005a4804090000905c4010994450031044c401d02044004225a1058010813288000079141703109a031920700317980318020703042e800e400261b81c5050070307181600c103240540062009080000303034161500c001608690101030720b14850341e0002014090310768403007080401040b095000d00104280c0303030000358804007544200e000704034003481494117640d0742842034561150f00910802403200c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 698984613 1250 698983363 698983367
    0xf051e03040f0b012c100b030a060801050c041a1605030a0216050d080306130b0d051f020319050a0b0607030c030e040b01020d050c010e06100312031103181c 69
    0xd2a01012a05440e0150002661503e03c80c01c200e40c240b040c11203170500801c0c0c0d001851452a0082860005c91241080015605d00b5070300114000c0304104000704665081000c0c460a580010f0b05038410b00c2c2c400c00c0b0400110341803102c0510901c0451350700300c0d82c03a284a210b507211045131b83c50150041c040040e14400b180c0d00060114580030304461458115a9140701304003005041a001600c0201e0404c001103181c6040c9007400703000000d00000150842c001c0001c40c1c500344120000315880c0c0c0c001c5007480064040d0312a100d08131480c490b025859403a02c05440500c2e07600d524480c090198841c40410000c10090b0050300200b0380103001c4680380e803a00d00340241013030041002640480c0039405008a40d003024040e5081c61b00c0c0c103070000c0890101008046409031f004030741e540340075507a95000a0843d103050001d00d001d03443c44003c205455040d420702a0380010320106201c2417504e40104821084443c00640b40d20105078030074480144603410342c0360304001ca0740b0100c500b54103202e034520038919 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 698985863 1250 698984613 698984633
    0x60903070e2406040f060516080c0705010207150c02100c080a031a0d0b4005060c03150d0501090c0f211a270303061305070f051e0304 59
    0x104411516801407104071042c00820300c10783c02400000185d096042c8080d43c0254002c210b02c0c8096803194110840c1a02e40000300c0c1c000c1c0c80c89002d0f9030880c0004100940e810001c4030080e129850b080c000c103003800b8001600f29217000d00001c0c011078500d009c5914450084600200f615002050241e030340d80c000d14020b004203501004660703200941500c0da1601d00700070310543c204680c800907070801511190500580610400201c00b240c0d441010640b0442906480080c800251040400821a258604a070a0040041074808490001d0080100c070300c01e48101d0209218040c1c0d040309855000341406409007105d80d4020b400004600d40004032204070345603a00484449404078140c120710b0a2041d00303c0e0b0002c4102405843c0c1d08506460030010351050700d90081000b0200c0d0300d1b81804e102c4240c0e0b107040c0051b60b045060304007001b041100d091a41b052403100e4100c0000700400d1500020107015154803039511003c01ca4082165045040708202120510704180c1e107550702e03031903e0301d0850252 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 698987113 1250 698985863 698985901
    0x30503070f140d08070e2205010f240e1309050d120e06010e071803050a0209010b030c071104150e270d0302210a02070203071a09060903070e 62
    0x9098444882d80341190100e00990910f110340e4411240340c6504108907030040300170804540c081c0303558102d041e03600d040c4404458240c000c01d501090a6162850030310107040c1d281d019408000c081c06610103200e1b03640840301c4005d8111f040034094001a132001c210341d1498032407403049151800076042e041c00307400200310092a41543e14568540c0c40c1c40003080940c3c0e00c00c1881c003003552144c00144840c0b0610400154050420700d814010044802c0e190340c0b4682079584141c80541054101205500348140708a0140006211861540c14210359000c4280b0035001c02421050703001c001c1c80907556503030700000365030310f200401006090b8880707c54010f001019181c00491840a1181c00e40340e445260f0448070159000d0041c0c8401d401026042d0080d5006040f0090351a03103500301d11440d906e4009103180142e240200058403100c0700d1050515180050b0001c01401c90840c00800329040100300721200760801740c40241d00c506005000c203291400981010b8400e00d1000c0400503002012402e103101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 698988363 1250 698987113 698987123
    0x1020409020403141c0914030a02180f01050f010c02040c030e0303010801021b0f0604020603100914061305040b0c07060f0204060c03021005070e0618030703081b070e130309030503070f 81
    0x503510000000e03100c95241c1561701001c20307060030342004800100c04868416a0018094521041e481d5001901011404412410110b051400e03c100b00d401d03031440a014060564400004901940c00a0078058408000070700c00c1d5240d000e14001e40c2d01c00d4006600011f5080b08694503541c5564140c0c0c041e402c00e490042c200c0700a84440841d11100050112003105404098202c0752156002e205999100600101502c00e602c1000110707504a88901c600c1d6900c094100082c40c00c14004001c01022400680c01c12903051805002c081500442042c0d00603808010595070b648091402c0c41c040c083c20819120014404180018242c0c0c02506445a0a120398290780707182508818250417030380c082c0c600e0750001e28030b414a03116604003203004180250211802c06480400c0e440042e103030420391f4108541c3c803800818808001c0903842d0511519985c3c0704050b103401400c0c0107545140b02001401c070080c0d0502008c0302c1040c140103c0b144005550400196a524066402c05031413482c1100300840e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 698989613 1250 698988363 698988373
    0x90a02031218060f040501201c0e1806060a0c0c0807170316020d031116051215150d0219030219031e0501110a020106090c0e0d060e0102040902040314 66
    0x850b52a0400880d082116035004850909003000011548240340c0c0324801c0c00800340380d0440901e180100181401c00e00e004084000903c042d81008080d030f04444d20300780c0941c003c0b4000180d80342080464942c48101600c41c1900e0f400c0110080307505111111010b44101c00c00c800110300e8a10119100c001c0e55880030300c1d40c0c2070408075801560350340714407013040c00c04600e00040344006180954820407114080d103042005d444010a50341c1c1012024214480305584e141d40400041c242481e603101d195950340c014180084a5114581e040a0018420028242d12040380035403a524641c0d0921810b4019200380459202c00d8941030401100d4002648240c50050380e140a03e002d0642020507661302501e0b1140b45840340024080d14690100b0031a0035540703400c0c40c0d200c004036480151080004960011640501d01050181114800444001000f001c05980d22445c2c072255040d48420307a01440008000058100a80c024000d0790040c8206c2400094008144000094003514986030101620 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 698990863 1250 698989613 698989657
    0x20703050c07081c0e0118080309043c02071a0403091418061201050a0b0a091b0c03020c1e0108070e0a0b090607021822050a0b090a020312 61
    0xda40d4503440000c07001c0c00d520b001441180341d111780b42d103510b500380604060080701c10184982003510101c3c0c100503495803020424491034038142c06074000030171904a081c00d007541c5401604554521281000344108000603460ba82e04141d070781203a800b1a0000074400c6680c04030740d200c400c6400140c0b0280d001032a520808604081100b009400041c00100b120b00130f4105410b20742c18038000145101d034030031160391f107104d21514280901e520803d4042400200341802038104540c000680c0c0126000d50301d010540010b801103d02d03100d84081490401c4c070048100d40c5000c0b40b400e00e21140c601e811060440c0380201024050449900e804000d80300d0300804d80d1003250480f2403e050265540c0c1c00103500604000c4c400707150005013003490014041038944030700e0307801042100d0358520440c10b480320b03218104160f4001c03102d030003858011880c00401d030055a60300e4985c0c1d184c0701504083d20f02c1901c04d000c1805501c00b00081082a940a420303110700340514101c06485401c20000c0110040100c6440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 698992113 1250 698990863 698990879
    0x6060f0504060e2206030302010209190503030909040f0611040312030213061b0c17120408060f220302060901060803090d080304020a0308040e012105100e0709020703050c07 76
    0x241e030076500306560b040c1c403805512003040901101300c0a820240c45840b640120403080724095140958042c0d000580d80300903290a1084043c000c040c4000000d00c500e1051060780d030040211019683d0849071402c0c4e544035828840381c0c98058120091481d481d1401c20380c100001d40c0098012a8040d5405800301c40e2040420780c2644103011003200d4084980ca0103106145c0242411030b00d100621070503402c3c03200c2990762101d01c00d1203504501400c1203510003000350b4440400a650007102006d51140c1003525041e45a81c1d5284094040c00c1203944107000581c460b0034803010440d4a131300c00d4110a980c0e003c01e050107501c070f85040d20b2846295082002c08111140d0010460700c000501070090794814005860b1069140c20151040364000d0311400008041007148000d04040d00c90788644400a5141c0040882d060744012240400d00c1112000000030640206582c4c000d040300d81c002081d103041c04020507041115030341101c0c20592002c200d45091580c84000b5017405160f41c0101d070026520340c100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 698993363 1250 698992113 698992117
    0x6050a0c052b021c020904060b09060f0d020913020a0807080112080d0f020a0f1119020f0102010f020a09050f030303042f04060e06131a1c0b04050106060f05 69
    0x305140b118031400800407100c889446078401000b48040141441101d401003000d40380c42800304840c3c6600071500e490f19140c5072080758014119442458681040040801d0b2103000f041080803000c079000c6a0680c921455404540c50a00b00170072481032602154031917030003074000d001c81c440011302100c0000c512501403000705040e90004640d811281c40f06980360340c1d650b403040c040b10814075110840c55905480c0340c0003030001858161910381c820203d4040041c055092400303600c24580c00740c00b002143c5d9403c0729950404c40e030141c03120503c034003c01700143c0c050b00922100004a030b10010343c48400c69030040307a080c16200111000d40c4003440340800c1603540d00090700e000c0c00041c0903256007540c00803080f680150050346841000c154800210010301200ca199002d1319016100b0000c000281c6098042c070920004a00001c11103241d4082e03c00401807940581c9501415000d0340000c0540403045e0850001584419821500d14081c80c10b180a00300500c55040400c22081e080f19142d401081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 698994613 1250 698993363 698993377
    0x60519031a060306190605040e0a0317060108060d020d1a10080a08160311060a05100501020a0c090b031011040e0105032a18040c080f030c030d2706050a0c05 69
    0x2c3c02c41d42c85069010109031744151a00c2521551104000317025115805101c04c4140054043c1404c2d21807420003602090700d000c60200c0802d02102041241e13a0040b15040e0000419140c22102071114400b040740c072404000c025000c400904141c050b41741c0700b90000b511030710801c20500b601d00d03554001141d44022405c03005042ea2024440648005050060144068024902040000d901030316003803c0a03000d54442034401c0c3c42d081044403000c2e84d0296440200828030040c44117402d140c0712846036110034040ea194141d01c41c40075034070360b950800c1011003030f428900c001c1108085218416540741d000d0b104d01840100482c00010f11032402203400301030000005044940f0580c460101c2d40085c410107400750740079000e5086070840d0300c94901214030661041d0200d003001ca050003009403909141400f00e20240c1c1c0308220066003c10302109440c01018062804a041d014410301300200001c001b251380011501c20301c424051081d0303030300864000c44500b881009400c2e1040012551849404c3d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 698995863 1250 698994613 698994619
    0x1605030c0411030114030c0607050604030801050a08060403030507021c09050a05040606140304080f0703020124230406050301020a1e08060603040b1503100903140c061603060519031a06 81
    0x48010003034410b2400340000b00700b2009055810b0070301c660300088c1031a000400103030f42c1580020100810075403c4154203014101c110341c05900180303001480fa036038050080c0300804043d10340340820520390003001141080d5511100c0700c54055800540100001e60034030442d4419602250f00051034107007071080100340c1d4141c4d0396031000a007038894102c800ea032014008595400041080b111103204c004094107070300c0d1281d8004500b6480d05110b0040e41c08010b0240d000c0c002c1c66550802c055442010b02030000052046420306610004000800925076135100d0303500344d4000114100103a510000d12450403c0c62041010b0305214040202c034020b43c00c407051790308030008002040c00303c1d81d54540d496009010150749507407a1041030111b4100a40050003510003034071050040205078100c40903060100c4200320710360408800c64151303030303039880083c6c002504000540090784d003aa02c2900300704042c00300600000d03540c0a180007000d140c500d4912054400005602035602c1c1042c040c141c0c503000f01001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 698997113 1250 698995863 698995867
    0x120f0815150a1107060806040c17061c0213020415080403020307021e0a0807050f060324130c0f03181106090f1f031817070804081605030c0411 63
    0x14107400001070b071040d1a041c0621005908000380701d07404002080c0a0480e6980d03229150903e42c0c02e105c00d84d40c0340142c0e0800c0c04119050050049280306e00943d0200c0100c0d0301c3c0e0b001010300d90106402501100c03010b5084807100084ca04105080c1e00104100ca01e042c0c0700c00c007516078108088035642c10540b40100160002c01c10131016140081200c0c004d201e0211500c0c031800c41c81c80004202030455840700d4119045404c01701714034030745683da0003070380300040e40e04500d1807800c900d00c2800760344807140c8100c414029038481069a2207000b41c1042490704c02e0001c102e800581c0d88040d00d000c440300e0401000a09191350a004100e10901400a03a0b030f1000002c00035881c1041008501e4100110990300400107441a030640d40d038a52402c1900c4411940340d000000a00c40c004040e215800441d4010200356141000000d400d88401d01946035184d0700e0b1a2a8140d629014605100310303841010940320345006882c80d00c807004030031011509e0840803078001c07041c0f0b00144400d446000203240d0030400c003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 698998363 1250 698997113 698997139
    0x323120f03040606080109060c0207091413060b090f090106050f100e12011109101704060b0d121e081e090102210f0906060a051c120f0815 61
    0x2a400590b4216204107008154141c880450034219020f10800390394a50310798000b2480c058052209001a01c60183d00780448541d4001441c0e142e90041c240b00c400065072500d810a11685900620f4003c10052003800c10b400c0886442407244026280c9802da946454400a05443c00c203414641e0b80d00080c1c00d8841c14510800161000700c00102d14640121490b03440e0500420203110743c0380c00031888072145850766802400e00107440c01d401d2501d001d0000102e5130100d0f4002c11a0006d034050b5120b1004100034681c0004a040348080040040c4040b142041ca41110342d0860700c440c85044108504034481c0640e81c4080341c28803010f0b204a10005082174528420308646800998001a003a002614094003510703c4e9040034980700c00030003003130850f130180f2046143c104141904040b44000811441c105200040e2018a052086500c1140f42c1101000708503c07042c041001e050308401c11210a0340a8034002c0e05801d6002107400005413404000b985c81d07504508208a080000781c2207405140c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 698999613 1250 698998363 698998387
    0x8012702040b030a17041a130e0a0b0d06020306030c0316140303120406240602070b07034103010305060c0c031c151d150406090501032312 61
    0x44402c0c0c841d0705401007a6030800451803007041c00705a14240801c180d0340360700c0d220442406c4a41ca8030503e009a1041000310411400100c80e101500d4202c0341061745900d4603841c01000308079440c503003600400c4003c6e1020500c203255025610aa1082e0252500002c00d1810580c683d1701007450b282080c14492010702180c9400c001080c02201c0c0501103c1c6805a03518800c0d0066130101c4041300c40325101c0d2506420003100342c00d0051402c4200740e495000c5810001c0181d21a055409030400f04040803c40600b80751045110202040c190f850800341031201c6114540c0c40071100c40074004170b10f81000701c40e91000d52401180c1c1220f80002c041d00c21a20b903501d08540c5907110b03001c291031034032082c001030710361a80240050240b03500102001490900f5070b01c001c08d050009500200d200201d9506014041c144034114079400b017142180358079103541d0000000c008040350b42051109614245c008010010007100c910310f07010066030700101d00041c0050075a504c419007042e482640d4000c0c403000c04070312 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 699000863 1250 698999613 698999621
    0xa090b072303090304050402030c0703020d050c0703081305061638070e13051e0c0a032d0203150913110102030d05070503060118060903080903010e160801270204 71
    0x2c41c0f00003580e00d0076030380303d0008003aa00152110f100362100080d00700100742e0100034070800c60000d82002420075040c0e0420b2511442c0314400600f0903070000420980c410b003111103100152500404041d240c00d44c0310100011140b10400480300c46262414054100d244005100c0e0403582140a4400c02040c4031405001034601804650900c042540c41c095165680000d0030100c001648000459190004010030105020007200d0fa420303d02a0511200750040811102d0400c02424085048846840da085020001102c40a040314410001081c800f034143c0085010b9031100b0b0300f00c14407000c49400c0009001c000c3c1c49107100d9072181c240e4100045c0c280d480c0c00d0580d000500590f4101001080000141c1f04210f41000000d0000800c111180da007180145a00e41300d02c0d04600b05090402d000948800640d00000e005040003155001c8969030035046036050082c2c4d402510381c4000c802061013510501402880c030a9400d00d451000d40720943e0100000e0008a03125034080e010313240d02884020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 699002113 1250 699000863 699000871
    0x8030307090933030c030b10050103020703080a0513020301050916080d02280b010f030311010506030c150706152301080403110102130608070e090105060a080c0c060a090b072303 78
    0x2480d540f840040454001503050700210b0054200032140c1ca002400d4071040c0801d500030350306040c0b040c4441c9012a0307006c454954007030b801c2030380051141c40c0c56140c2d200001350010001e50640c200000c01a03800c4000c21214404425403007000e003030544403070190380c0b60160f42141c000180e11803005c40240d5912081d0322080d103071952a00180d0304000344c41d65035406034260841c0d1082c01c0c069508004140d44851103000000601e0000c01c16410b081000030703100e03000e102d190340c4104024142d0030343c00e91000d001ca80100358403c01c01c2003040d0004001d514500d90034401d60301c070700e5500c0d9811418001402a520341c00340d816580c8906643d120307501914296407144400f440780d9801e100440d04040d80c0c91000000e42980d07190a11107243c2003100400c1c01d4a08030344180184440c40c0100071b82d4881e03006a443c1c49415043c4044141d031507094000c454000d21107240b81c240704520600c00782c152145d004006c224011035141c0f0060f0b855503403c0d680ea0313041d024166940b08022044074117000b607000286403c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 699003363 1250 699002113 699002201
    0x30c060405070512121e040b04030c140d11121f050601110d09060c080919170102040602120d0e15010806011703090103091b1403070e07140a0306030804080303070909 73
    0x240748e00c841c03c90005c3e406c2900111782d4548520410b10919401034100030300d2070011103544500036403e070385400c41c82e00680d5410740250105d0601e8204850240a082448011030040480341032011500030094075050350114081505042000212080458001001c801c03e45402c1301082ca0000304451580740c02000741c94418081c051000c0b40d0341c406190400f003140e00c81d40c0450a038203102c400714800c04199040d040350303881040100000c58001c59002c811000211609844114881e010000383c00b2000d1074a03603030f005107690000064041c1c0d2006041e609140101c591980c0c848030300c1711a1040d81013030032040717a000b40001d40d010341c0b090b042000207900c40c070184003400140c1841d101008d54039030440c3d0b0b1598800c00b13152000b8101000316200810075010826518200104098070004111245128112001418405860080d00f000000b10b030700540c1036544079a59100103032650425100720001a60101d00060419018002d12a0008441418041010b4950380e020520070000040041c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 699004613 1250 699003363 699003367
    0x20304121a07050c07090b030a170c0703050a06050906010e0f040212030a111c09030b0408090303191824120203131a01060c06020a02030c060405070512121e 69
    0x40350181c281003801a6a00c3d11195243c81c189004a1305120039900008580c47c80c2443c1c10105903000515070700c1260300034405001100a10381c00c10344c94401d584a4500a103e0300c0d2000040000000e0303481c07071f000d0203100108800d03101d00c0c0005454134000c0c4248500d2020540c04540d20081c81030100b90030510040c1a24039001c0c1e0040e0780c07421500300134108000300d80c00c00400120210244020400310000702c41240182541040180a0360410300000d0031000c82c0600250030000c60401b15450480010308a03902c8000f1a82d00808548180c022080010344803819960b00300c00c07000c840301c1503510540b2074007414000001c040c0700b00d6411110341c030100020b440c0c02004074105072004501507070541c8401607565040d41040c0f23140c5800c00f0300703e000100c0c2d800300410601c0c5e4058482d60045a01c10b10160b651002008200e1950080d80304002a5003c0c4c03009000070044000740c442d080300d0701507401c0e00300c80c0e0142240d117484150000355514051010000c1d0300c883c41c2c101c0141072480f00c110314154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 699005863 1250 699004613 699004643
    0x3121b020a08161706070c2301020711060304020306040b07030212010e1b13061206031208090709020c03030402060a03110d020301090609050c09040b21100e01020a02030412 76
    0x180740700826610a14050700180e100c0a1200c0e40600c3d076801801600003d0342c6072410140c4a02c2d501c4400a014104210b01f07a8048000c015001c0b5200700b0585041e12840881403012016038002d40c01180d086030142c0208e031081c200e40c1800c00c21390b4030a40d001006070100741d039581c40d114403250000b00b40d00d040660030080c8141d4001c0006445001e85550f21841c2141e1612894142c0c40072141038000c2582041446a002c0518039072500c42c00351100c5151101020b9420071168020780300c1034000618050542c244d815456a001d43c0700d07403040050340100e40380103940b142464100c1c8560f0500600301d41040002a0140c00c1803001400c810045180004504228a01480054100070303002038806030000300420103504140600070161482910400041c149256040c141d84519006076000d1601c81140700115500d074203890b08a204151a030314208800e0101058442d000882a0303000702e4940207240009150501c20380b00c9000468004600c1c03e804c1c0741e900598203403660021204015a84241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 699007113 1250 699005863 699005869
    0xb040204090209040e0307021e031002120a14010b09040e0309030a030c031205061c0606090c0c02030f120403081615020c0f0a08040b0a0509040c0e150403121b02 71
    0x20002040780420050300c2d140c440d02040700766110442c602e2803030342c41403040c8405a6581080310748000d000c02c41944034000007102180c2002140c4586102181c400710380010541c5085c24040d00c01d25680408000c0c0f40d46c060b01d2030000701d0080c00307441c1e042c100521030f04055051a41c01001103050100480741052a0b160000740b82001d4440b08800240583d04810101074000030000c1c10150104018403d030314026000c0707403642030304c41c1c0b419580011484040040c4a019882400544500320080c0961350640001402c0d00d12401400c034024445e4405424416101007055009400402d030b51506d007034515200d440d8030390000c2442444901000c0e1315400000d4030114a0800380300e07100405612000319146140c1031455030010300460360004207014000585e0fa034129000e445444d85100e880b110252000c60b19401004a50b0340c00919000602000d15006100100b8035202103410303035240c00316185c851f4050300692100501e00b240100158000c58000d61404440c04144205c1501c451429000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 699008363 1250 699007113 699007117
    0x23032b0311040f0e0a06030201020d0c081603180608152205010f090606050306030d11280507051005090603060103090f120905060702010905091008031b07150f120b0402 74
    0x10300a0302c070f9003082040703440c4203040d180d544881c0c106000c1111501d182c0000c1c0d140d481d00500340c400c0004644003241000481d80030740c0d0300c542902d4417000045d406c42c503001e087c840000407207080085031b010000481354800c050031841061000020001881d000043c40341d1100d6140104501e244000e11148a06a1340d10600d8000c289868100009518003101e03401162070581181c01004010000c120341610b000548200d21010341c5001401d896107000ca40742040d01490002d41c200c0305001705c0d42c01d01c0f1039907944e0740c210a01034810340c2d442690b60030410031a11450b03415140400c0d070074003404050b80b4020000e16070109041c100840c040030300c0d582d50b280021513044100e54812102c1e0a288007a54460f11500290000756500c0c0e1800e81c1a8002802507a502c2c4a207030f116441400008400b0441b200400c4001c00140040300c6e16000c2103003a41000050a030508001442006070001d0b14000c0c130311903080645156110402114007030324040341d01c41303080480e0105241d01c0307100c4842542c0391440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 699009613 1250 699008363 699008369
    0xe0a1409071406042303030c1506100201050919051504031d0f0f0d0f020306090601031b062021070c0b03040b070809120423032b031104 60
    0x303030510300d080207500c02007800e242c1500c0b4040c800902003445040000440c144100403140440020f803000e4400013480c40c89200c0c00322085020788000d8158080b400b10800c7d01810040f2210103071011080c0049003200c00c200d8801d031040c0d00850714945489994a032404003d4050016541d0740c0480000800c3d441100781d400b140000c2c46210800701c203050301c4003c10b5007040d040740c94903050b40b03454002401402c8007003051b502c240c0c414415030042001d914007407a40d0b10b9016043da001440c101d03514a072511024841591325903025803415071554004d03001c11084d100c00e9103a402464165525448200c0d04400e5046441c0c032070f0043c10025803551a25880311001ca039041b10381c1d038541c0e5113003150580700b9070390040484603424028400014108941994030507150b00d001300391030f51a064814541126a962402d50020020b00416440e924140d1000c800b50201c540c5c2400d0340c1c9400c241036580d4072030036800710350031814020080c01c0480c200103288108103600d8041005c00b01c0c0b0300c1856480c0d10640c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 699010863 1250 699009613 699009631
    0x108062409040f201b07030c0e090606150a1814091e0403031a0315010816030f02010e21030a030c050c0607030b060d05150109081603080306010504030605150f04060303090e0a14 78
    0x41002c106402d411410270781d220ba0400007030103d6041210106c1c107112000c000c4c401c1c2e5014082050046503104800010040304114800200c1d99510750b868070f4400d0100503c02e00505002c400035840000040e41035044e9440d03c3c200382c4e20780d602d50b1012401008100a1400c600c040c002c40180c40c0d44cbc0030407140705034102d050f2041c02c4a5150600083c80e0001402200c0008480000204007184042c2c03201064a902824207004c1e010001c400030f8001c072112010301c07404080a84060104080c002701034030044031603072030411080b100d94500b91100d0151006040c10390b40f100700040d41d980c1c440c2d0004000800050300c40e0303041c440901e51040c26560225186000755030840940c032038075a8842c046900070210003015100d03600342e461a00c00380d036074140000b62090400001041c0541d124000b22802950000c03410000780c100404107112119421082d40d10807004641c43d2400c80c503191140ca81200d0345a2a0111050b00e414107080d540c101c000c201e9a42e45540b104a4100d03c660441d1760b40c8a000700c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 699012113 1250 699010863 699010883
    0x31802040e0616020d02060c18030f01090309060302030f0414011b02010222050306010e07050415020309040605150706050c0c030a1808011401050108062409040f201b0703 75
    0x22045181180f1040500e003811540110719080a1540221300395810080c1d41c00044d40d00c6218407889041e0201841c0500d41500c42d0b05c000e0b101d00d031410752281c0800b80c46583d40080c81995140f0440680c041603501a482940c2d4002240009594807041d10070300d400d240005c90700d540000400d80400a44c5400c030030141c0d400054060365450404070001d0300c910303c2c68680703075880d081a000c60303900c031414000d4840c080e11480103e64610f0161081c5e400505d20003541400e10792809800946980054025502603403c00c207005c01d903860400004002e41d07010b215440e042c42e400d51154800707840090403418240404000030050444188020010465140c840001c1c0b009122883c0d03980e000c0301c0d40710711101d901d002c80d003981d15080d010042e41191000d180483c001c1d01e82c41d00040360025003405c0246904081c05408441c3d030340080140c61060360444042240d000c400c1984801c3d100070000c0303201444016070001301e00c00b9111002d4a0640c400008032710144d200c4070112498544190000d0744c04900e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 699013363 1250 699012113 699012121
    0x703090209060904110607050705090a020c0d0309170a050d0e0d0908010b060304200a0602010b13020f12130804092933120103060b010504030b0403031802040e06 71
    0x404909030080c000750784030788842c6132a403203404200548198840c40707400006240c6003400000c224a030040c1400402800c3c41d401c20114030402984030030940e0200d401001ca170300160724001d206414015400100d40e402c68503660b40611030382c0e840340c0c046405021040c0581c8000880901c5414000e8801d81e0041591106606000c1d242000c030781c1c0140e03110b0781090113034507503600e40500b941d0308030b81c1c000c1c1002c020040f00c4c41004580300d80000140d070050107265000030340c640d054214280041041d600d4003610080202c03040182c0c4648451071800e01c2081003581c00c21201d900850307500070604031002c1c00d000b10ba961450030f1680154404c0d8001c43d00c40600e10f07000c00b0294460800030a00500c100610760b84034010511a042510070030740c08019100b01c2c0100c00240006011000141d04441c0307580da0325002d00c4814a12081c041610200c0ca807161550042d4003c1c801c9905403900081c011410f80c1d51981c0860142002201d0b40006a80205900d40142c485010300c440000b441000b405a03494 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 699014613 1250 699013363 699013369
    0x40602120105061309091a07030f0507090305120c010902030a0c140a140f0f031009140601030c09021602040507020102090906030705130b0d021009080f011b0e031507030902 76
    0x101030300700910800f410415442c038a00c03000c0384003003142c0a061001c80d5a001c40d0500c0e580032884100c0c00c100c1c2070b0702e010420903d0795150b444041802500d580800154070780f10000c4904000c6404024003540c807140860249010080c00303040400070009c00400d10540c0ca0b404a803c01c0c0022030201c620848140c0b042c07022082107152900c03089020386200d40d849140c12074940004d040f0045035801196010118025511601c00d501079000740a41111018091280400000d001940050300d41c00144094500302c5d0300045036090480340c01100d041c0b41542000e0f034500c0254480c1c0da005680c21030098a000040e11940112803140c038294000503115080d8105011a0620080c0b41c14408c3e000742e04107020382d42d82c1c142c0008076003103420720008200d840352010070921b100510020b035003c0411205801c106901500b800182e030103450580d030381c030600b108000b401c0c0c03036000700c000001d20446000241583d00c540e06a580c0c505e4014202c2d0340c0407840710003904015100b5906100081c0d141c0b00c101c42541 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 699015863 1250 699014613 699014647
    0x50c0d08041508150d030c080c07050f060c0a1410110406080a060321031d010c0216050312030915150111161a0c030a2001050403020c0423040602 64
    0x940d0b81c00e100a044c504050440c2d0031610076680c151155100c4d64400e02410300c40c110702c00c44030b64400c0c85107954140c1030031180c0d51480d40b07114103031140301181c542c01c940d810084103441101031880e0091070f40c034003180d54072106000300d85001140391181e5032119113015082c2c05110b83c07551801d07806a60321810204024a00c210041800c0002410190100001201542d00c0300d0000b03518042240c002c00d034000c0440240881c1c1d035600b100140c240300c1310a03013442c041d48814282d0030160200c039204401284800400a514070819500d900148090602c0d659000021503102520005880110000c9000761006000944090381c000c0a00c2d43c84420a5802901c4071044541240060a08010401100900c4d06442c05088000603040c000c4000d002c022800381c8800c2d800020603262036459614005040311181c10b090310700305110791802103002c40184901d41c00789030540c1c0581922442c1105000203032000e24150800c3e030045502922200d100b240105003d24401d220140c0e8440303910000e02002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 699017113 1250 699015863 699015899
    0x2030c190c0618020904030e01121506020613080a0e0d0602030f1605130512030c0307060b2b021905030703030c12050405130b0604030804180e070501020c0d050c0d0804 74
    0x26403420f00250b503a501990740d01c1a030620301006030800200048402540c0f5103020001d2b40c0c1401019109842041d02c03450a0b9500765007101c0d410764074140d00300c02e940d034036000192a0001c200060760b4081d00c610503915201e44098401042502203580d01d0781240d00c200d07040d6090b04000814403020750160244d01c0c43c60741d02442c02905201c004c181d22203203410a81b00c1c0c1403044030072035440c0f006101d0510035980c070a0402c00559464800e14241031000d40791042d050f80c421001c03204205005000d2000801103103015071862417419440c1c0d0300344694441c15002c0801d10402d40440050680d40403c041b20286100750742e905030a00051a1580f0001160160700d010b0000900040c044c5031a002130307424a20003400400f10b040040c0d4000314010303204a800103800b0003800240800c440c03078100000c007250358a8920400081004810183c0c90b8071460080b039005820030803c0000c5807810700030b01e000240c0136405880e46143c4000014079071421691040711015000700d4100460b04070f4039003039100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 699018363 1250 699017113 699017141
    0x30d020303090d030504110603010e07090603110a0f1206170f07120b0403030f0615020c040b0108070513080106081f050c04122a140f1302030c190c06 66
    0x19402c2c40e10b1801e49803154800224205642c60002505104900280d1340c04808041e0405507256190300314050304040072503021001c64058800002c08510907c0f4409484520581240c101909070604a41da8040c0d010000b00300440428900b6003821984681c40013024000c03151080030700000c402e02c0c02c00d040201c0e015403980100c80c0c108903004649400c001004e5100c003200030356986928060b401401583c01400c1e2140ca0a04045070384505a6807190440c8400e03000c5a170400c4201c000c00065035407103184640058150004500b550f800380d005005c8800b03010507184801d83c0c851f24a00e00f102d0142c1d01400c2aa407100e01e0b8110403500d40f468201d01d4031900310042c070031444c006801c03043e44c0c070a91040c1442804015003120134018400703c105c0d1520840750340b000300c41d04920b610400800681c014600e0708403001d41241110320f4940b01c109600e5030301030303c4c80c0400d001d0302060800a42004040c1c1c032100e074040040c10700d020004840ca080c82c0c400c0c0d4541c0340c84c010a5081a208440c1c42d20103000c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 699019613 1250 699018363 699018367
    0x20c06071a09100501030b18031e030c0417010204060908070e0105060f37030213150219031701231e0324060102030a0f030504080f07050606030d0203 66
    0x450070224401201c803400544000060301c510402518184442c40710032103e5180400120400c00308030742150007180c1c1541d94440925a0301921603c4e803007440346e214000001c40030b04840510318034024641c0820184440740c105603940c40c09a824080c81c10300c218031039500150501c09070707401c1802d04028012030001410305a04003c1d0100c2c4240341070040d9842014041000c408260701c8070700316401e2002d107102d00c840c000100d4a2081c001000b4004400740905160748640c2c081d8402e2081e100002d001100c410200c03864060f616000c140b1203088501140203034150903038020540200c9003100c51195840100c441c00d440f41803541d519040e000501200e002c0300400005019103014103400d0441200c0c00703400c41e0200441207400c50540d40301d031a00341c00b8501a2a001042040c0303503443c0300705503028504440d0f131083d004907140d210720041c800200c0d900e0300c0354a04c807a04c41d5100ca03034007030322410276a03180c03141480a206845e0000707441106c89600140030400c050805004116051541d400294 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 699020863 1250 699019613 699019627
    0x80c0d110d0e0a0b150a030c1202030f011a0105130801022a06060a1707080d0e190b0403030c050111070c060f090b09100207180b0a06020601050105070b07032307020c06 74
    0x130400d0b0005401104015000e03400b60409a40740d594103001075901401581c6120b9844070086120010100260321a0191b084c60090903041805160481008850001d55500700b413401520150096030310302950b02c009000108854000f48020302c4a07030304030001c9074552001d607030b6015041c00b0000a04984c40e004041401076546518219905a5001a81000300b00e448000410310708040c0e94020314031449048025510300782c2090312008454010344514000406202034004104085d100e000384600c800c11081000c248506000951203104000100d80008030f0071814040d500082402d031100e01600000300442d5800c9140d43e4040013680c1040c803c5640740c16240c2005015011099000b08418074829001503c00d024800c042e004110080802030307802140d0344000e00000300325a02418040c100400c1007800022050304941c2d050b9100c0b4644100780c1c2d00e24a0855000e059407050503105c60012803105100c0c408001650031078038820341c062802180007440c0c440500850b5000e03c104100076 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 699022113 1250 699020863 699020873
    0x30c08071a09071d04030c02030604060b01090b0f0301030f05160f0f090b0f060c030408030f07022110180b04030f080129071b030c0e0c0c03030403080c0d110d0e0a 72
    0x11000c4e0180d51110400d03591103060a840116200c10003c0d4540241c1e010401006081d910008800000f81d84141141da100c0144c60b5440c0710b00580d00c030103681700340010070005402305001103865104006940008080105010840941d5003210500007101d14042c456500c4140800004000c02c43c014071a02503030b0710210304105611b0301640e0244000259000c46c19004104031030050111104603a925210440d1087c02504010001c03882406141102d284440305103026a04c2c48a0010285c0f0300c00045101e140300419104844102042440200002103002012840e2045002e9192480e55014080c4002c2c07c04105070490030212130748151115049500c44824000310000c00074640e66400d0310b040c0a0561243c1c80032010b0341d160306a5000c01000411500340e02194048144004183c48845c048207141c091041400709980c41800082d001c00d104101c04c91f04448081031035071400404092000c10b490355070518407400800000c1800383c1c2c0101e84102550002c000c0301802041009581d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 699023363 1250 699022113 699022139
    0x30e010f0806010e152a01111c0f140f060306010906061b080d020705071e0b030a0c14030703270b16030f0207030f021b06030a0207030c08071a0907 65
    0x9031400707441d4050001105030036040031142200907001801c106846d903030981e0007403202803038451082d5500b0507801200c0d01815000355806000414000d6000c080749091440081484400d00359000d41c4a14801c0c09001300140890700510180e007044c94140b82007001c0c907182180c107030700806a15140520802c003040e0320009205108100361036202e6401d002d41850314083c0100b20080215030b100040307103030400c0310004843c01190202e0380d4028600311002d0000900158910981d503812000708000346503400503501941403502c5604100500c072130702c0b00e194407007900200e5100f004260707a040e0310001c05a940001140c84a43c0e8032420341c0700c0c44255540c1284901c05840200300c28180c21030b09603018029000b5003103981c502c080c01c540b984424200140010030041e60340d40540540407046c0ca442001e410000440b17032014040302c2c5583c0b6458000d01c021342c07000009404026040781e000002031004401840320a0041142d4545030800c042c00c0602c8460180041085038481c000070045003964800f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 699024613 1250 699023363 699023387
    0x80f0103030806010c0c03060e030301082107020609131a150705120a0c050607090608090606100813060f090c17060402010c0f050f060702071406030112020409080403030e010f080601 80
    0x103801c03400500b81d840d11114101b45508001d103020f003450203220200c28004040e42c1250b40c07040131601c500120ba9100b20755081c051003ea1044035040000501500700003000f04400d0f6400760401280b0031300b025842c1c080301c10f00814486041882c488408003071030613241d0303071014200c0424030501c0e21415a80b01340e0754050350028805401000f00b64a0b030f040b8040c2d10300c51000c2c2e0304a4240d40691500c48002407010072240180404224210081007002000180d064030602002d8003020020400c03400588543c81300511001c0c0a05c0d48601750400a41035001da440301c1545600003080c6803107546848500701d041500643c2c1245000c040704030328580005260ba0301b1940a007003580344480c0303d0a280b2110300f03102c40702030440c0c80f82000794400701000140c400e2040342c055080d034004c070340c591128004240044c017540341d0140f424401031280c0310b0440010012184014030000b149041552240b826030801d5200390040780c0c40e2684a081c6580025085001481c546003646443c03800000181c41e03802c90315 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 699025863 1250 699024613 699024617
    0x90b070b0604021e0705100c1704170a0216050d0c03150f05041506080c10050f0408191a06090c0306190f03030e030109170328050106080f010303080601 67
    0x50201e00d064885070304940108007041c04c2591113001510700b2000e983d20401089440c0c0c440c420300c0348621602445000700030607203642c440703452021b801174042c4448800b40c015502103040003001801c84030200018003421381242c01403c4007c0c241c0c035066012450590046000f146400c04800c002075000d10000709aa5201c007844502c088410710340f400800300c00b1043c5403600e141c1001e01003804540c0f50205600c0e143d2406c103124454846030a15140c103686d8210a8102010901c3c81c4034042c0150003502c06545038001140c18641c0c0c0b040842c0c58030b10600e521404201e0702c001c0751410301070790a245c0110540c0194034035003a0300b85100412000c46004110f18140c0d200400850240e944907192540715501242e000ba03445500c07020702c5441440b4600c421804100401190345641c203060003000c48164101074803600e03c2e80ca90240c400650b000034182d10717608a11004c40600070281001c21010860103610004440d03041860182a0140241140e1042e58482c0010400268455285580b0400c28 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 699027113 1250 699025863 699025883
    0xd140406080c130801020307120c02010e030d1d0304090e0708031e0703051b030901030b01031406040b06121e010603200f070602120a0b0109030302060f060a030605090616090b07 78
    0xca520301d4001052078010707261303d500002c00e10003010f501c00c41600905440a03000c0082e5500c121059007201c2241000e8811500188040e00a000c0b05038010a00031040304a048980041024250304540c42034002c1c82ea41503441c8120130006400700500400341c02031400941c84e2400b030514240e110200340320303c85551000002c82c2c50030544502e0550304000e030500c16000b0f801b0750020086031a50014100c96002032f10700768030541ca40d8802d00810f9210120740c01d10310116110300d400e0102900303107010305642007001000060000400b10104900c90b41d10100c41c014255a0070750307904520b4506034070007001c040c28503165a102d1918074640c0d090b0032441d2a00a81c0d562100b011815660291203130141c881071010441c10390644405031103d00c980030044d000c12160000e800155000a41c0f40405401a40481c00113200503080040050b00040c009210300b21565495a50b001030b0f410487d0892051382003503041c801d20303500d4880c2941c210880c605141c00118103103d06410743d030265010145c81c1c2045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 699028363 1250 699027113 699027127
    0xe040c03020f0a020c030c0102150109020702030f100f110a021f0f0903090510090e0a0e0a080309010c0f110c040f091a040c1d010509070e0307080d140406080c 70
    0x181e412202c404a0881d58a40c0303c1d040c4050107515120106100d81c081c0c007a0315a1070802c0c0d803000c61a5203c400d140c440c2025507900705003492000f50440ea004076018812450303920802481006020034560320601c02040c0c03e01c90b50382c0801550302c692060702040d0300c240444140180c010030b110041034017816050b004001d5422045015085818901f151686010380d043d0030700d0341c0110000140c030000d032007810071000c4c0c0b00750458902e6000e100c0c0c4441c200240d0b011440104594006544000640c2d0494039000700c00c0d01d4101d1654415074100c48580e40d0b0311742c410032280d0441c8160422150303a0502d008070454000c40143c45400c9204194890769440486480e540001c0d4441401150409400e841c18500d20050507a07544041c1c1d8162410942c480c00010740d495060300c04c0c040050310394841500c40e440e20040c03005003076000c1c0082d0280400c2c100d6a40d0f0a4a0411182c1c00501002e40106a950b8085a014011400d44121a54125020030007404481d800440301a0001d2141c3c80385030361407007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 699029613 1250 699028363 699028367
    0x90f0d0f032c070e01080c06070f0609021905041406010816020a12020c1201021305062b0506010e01030501051f02120a0206060f1905210106081b0a060e040c 69
    0x6440403000b11404585a030880301a100284030380c151465610300e015266296651160f6038030b0840443c40d8400010401c1e00d000490240000c0e170400d102c2d1401241a40355640082d9040f007803040c081c402d100382080f04001c14a414015940d140011032039180031414081c00080c40c08600824458181c60480c54515546100b0070076a50700c290001501e1a18540b6048029140d0003060035003031051100c00d5090706036403010b03c2120100f600c00822600007500c1c0074140003280d081b5044130b1b406941101100c550721181c001e40611204542480042e181c9090340014101261411907203040525140c01400540c81d107000c0300080e40451800d65400b890310388c0d0200e02e0241c030790100042d02400400d50b12110f0343c000a005000300c1007200c65811801c07840c010b20001510440300d6800c0403030501001c1081d81090741075901c030039011080d10f4903020101c0d1042c2d400c0d00d03c03562000500d41c0c442d044400c206034010b00780100c8400100c59070b0341c0c204c0ca8804001c0c16906101850742c0b0440d502c0c2c80c0501c07054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 699030863 1250 699029613 699029651
    0x60904060509151f08031306210e01052e030b0a020c03040e100603020715110f0c0a0605010503010b130509010603020d110a0e01060f05070204090515090f0d0f03 71
    0xc0090f803000c4405241030480351074100da84da041c0c00803810741c1c4100440c8550002c020344007060080c13013150f070102d80b41150486684081110f02e407980004a0044009602a0702480003151034040000c00d880c1407040000d00041e01204d40a00304c5100309031182c000310342c80141282141d0b00710401115584460000c04020311a2200582c2c4506c0b00140001d0120308009400b8407941001900994080d9076590176016071041d604010311360001c8258000068046030301c141d80000c01005068181040107520b04180d510100031403105034049104502044050f000301409480c068000f80b0100c0d0b40140803a80160500d4440701c0b03041c2e11031000070180c034000d500a03001140c00824103001c0408a0034803028900200d100c0e64082e900440c00480c2d0400008200c5048500c031355151803040c850b00204440f980c02c80716040341d000d61285c0743e010100e00100300402d03600c4040744c06140b0302d042140f4000d02d009518809405503811200901c0c019541222801e4040d02041c20702180a20707241c070f1942184 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 699032113 1250 699030863 699030883
    0x220c320c011401120b010b0307121805031309060503010e0303060d2a03111905010c06060902030906100807060e04110c01060605090f0a1203050703090f060309060f05060904060509 79
    0xb00001000750305030034844c83c8980140c185a001d030341c860700502d08a01c0b0882d01c0001056903926000840480c0390711940c045541e61600c1b00400b006a038400341140d20031000a1003a100c41441400350400910034080205400c40c020840102d00d500307900d44030301008018038030920320001d0718000e00101500e05801744403024061b61404a03030350441c03554600140019200b201c030016042c031150811a1625014114080b070301070b081d030f152000450b00a1100304040b0f45564440e00d00150071a50383c0007a6003d5140c1101807d018901511400b107010140e41c492340700741c1d004450400106800060b001c4810500391004205a0055140c400c1c1500c2640344400d81c41d860400c0014029500401800c0b1011701120821088542c507000c0000c90452400360358080501080a600040d000d0002807242c0c92281c1403175080f007651442c1000d035200c01d640c4100082920b0780031a00402c4400c0c890300c4805500141c0c10807860070848003103414200c000300020000c40e99040070a090500820814004d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 699033363 1250 699032113 699032141
    0x80706030b0d08040b12060609031f02070b040f0b091c030209010c0b2403010c120f15060903021f0e0f0307050a03080702040501050105040b0f0306220c320c01 70
    0x180301c0d178402d0905c0140d405800030159440b200d0001c41e11600e0100110381c920507000b4000c0c0451624403e04c070b458003044030300c035040303ca13400c00404000800754800640b04038000c10f403030090710400342800d60342c0d2400180b604a05030080c0d5146140c0c20504070007095048075034500140c48401450040e90100b880c0c0c00041e01c0c51040342c0c204099081000c00c2c0f40d420101000b99080c802e0a010141426920038815140105444010114484045512041c3d22000c0c004000c00c40070326900c40800e07140140d42011001800c504400e00550800a200807480440c81c8242000b40600b0b890042102c80d881e09050f01c5400f0341104030075960381c200308460103400018503400220f42d40b45064899607010041c1240101d00340000040c556003c1d10542c0c044034140b003586c2e4034111a005004516910091581343d000b030708118140c4c1c41a030340c68010311030514941c034000340655107040090040142c20315403603015100c0c189480d07504410864201812454100d140fa02c4141100904c3e0240c0b03262092120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 699034613 1250 699033363 699033367
    0x905100b090114010509180a1d07060c0804090e060702010e0303041106030415020f07110f030c13060e040822180f02040530030403260c060c0d06060207080706030b0d08 74
    0x7c0858a0700f410140a20b840b41800c0040d0800074948124a40211001c2c03000c541090f00104559030094000d0b103e024403406c0040d00d0691110241d60031900c0e00664205564840e00402070b08a40900c221200e03080743d80300450451500e6a11044101009000380f0f01869010010074100f0120850022101e88a14802d549444c0c52100c10501504450320036035460007441c900a1080c1808442e06d015010080c0107059000d221030280121500d4031307004401c240d582d501c000500890408400b50286210f203e281e0358030101300b022201032014511494030380302c09e01c550802804210021007406a110090042071482002c41c6000080c0150703404203410030f0360144003103107041d031140040c03403003440b03007012000306580c200005d666902a5000040103101c000040804504182c20200640240c5251840c50034441d0201700f41062016545903214060215005820102502401c0c018229620090810380d242c020504e558800c070388140000d25a44910075881c50f25849101c8506503040342c01070f6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 699035863 1250 699034613 699034639
    0x21020f040f150e100e06030a0605070e0414070906030b04060801090b0a0e070605090d02060403020d03030506150702030a0209041e0807060510121403041205010905100b090114010509 80
    0x5445801419030a000d49071002148034184102c120780030b80d02002501c0480f40c10001c41030001d0b1740c040d05042c1e0501c00c4040c690002490340c0166403060b04c107036131144c000301d80204c2800181c071604900300c001c4982c02d9041001e029840034106088458900d00030030b9007614080402d00809a6801c50f088a509101411083c445602c40fa140a807020400c2086524100b25009031103045c64080e09000800801081c0d100780f070f061030552070313041c002003019241541e6580040d00c3c240241c0000c5011985a00030444145030403d4064254003098802601d0800950f000039124102d1a0001f0310952800300450188440310b409c01c030300760b10340c266215190b000c1c60408044507001104210345d95410800012210000d44262008840d011f40c9100a95802a9100b801d02011115182c45900c014400094008900380300c0844140c068000000c0c0b8100e0703418803a041100d02200e035643d1a0412010380a01d4aa450000d411600307680034107030028200c030300100d41c1c5200d2022102c2c2d204007040140c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 699037113 1250 699035863 699035891
    0x9092401031109063112030c0507090c02010515100203070f06140c0711030a0b011701110a030905010b060f12090109120f021506060a0e01050c071d07050421020f04 72
    0x91183e21030341742d004c00480d0080c0e6900d04c03004009010324108003082c040f0380400203002e052582c0702540b10390182c40900361929509411114242d43c1d02c030040c0e45500500242d014a5180c448803110301f9110300005448014020f0756074458100001c00b1044050f00201c28071070603034411003450440c1c14a55549040080c08600590046041540d804004410100b41f910b03002902051903079210503041056840d00696020b4494210913031080c5540324a40f440710b080c01c10b4001e041014181d28001681091401c00c0c9003110030fa0703080d80c0d002d0707003041200542080c4000240c81d0130000402d144c480a94844008a0142060050042050b11810b1211003000d8005a800210001c41d80c00c483c031540c62104030b41d01c50314065482e941c0050080200441e4a886400e40414964040c10102d10b840d2001e00c0a925120340c69229016446130307500350200210b940d540b05a0020700500e041d0703003400d08100340d9510889140c0079825280f00002404000c54443c006000040b4100030800c01800151901c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 699038363 1250 699037113 699037147
    0x204030b01031506030c030818030a24140c07020102070801090623040b060913020a03050d090e0709051e04021801110d02060a091a0405030909240103110906 69
    0x20444408400c001e8030a0302445500c138060403603800103a51a00540355480d001c04507800003006c0002404242c0c044507058900300104403000340f28281c24013400401c0744c0040108a014180100e01500300803a000006610122041c2c111902c1b10442c0d030350b5000e07840140e15154840e44090314550038400b9038814091590711095010503118808149070200444036050401e0460300201070000d054007140c0182005400b49038009003d0101090490b001c3d000603100203401c0d801114640d2101089825140d4000c191070024509003500410740d080003500a48940d0860051501502100c04105e0100074900510074070008007910440d520500c0b501c0b02d00c81c00d01c0911400e0b0114080224800c4131000000d2036034094103070b6034090085a122402c440b006090044025111a174a0943d56417981da040300a0754080ea120300000d540c0c1c0c0005000b40a10454001c004a1001c84a8a1000c060180c05400d441021000f40f80010710080c101408824074055550056003049001c51307a50305801c00014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 699039613 1250 699038363 699038369
    0x111070e0709150f090918030e311d07030b09030d0f0f060506031515040518040606051f0509010c0c0b0a0806060306210c180114120714040e010204030b01 68
    0x51754802c481d483d9884e100c29140024401007c000410380c00102091203925060b002c00001080040c5031800c2d25a03d20070440b1202841d41100e141c0400c507400e11800c0e00c501a0548118101514819800c40d2180d445403298800502060720034000246000018011102d890210442c00c00c00340d00000b241d0350040101104e010041464400301141030b107002002d8030b00c00c1700d0301c0c1c0c02c0c1e285140c0864240030980c00c264001a82040e800d200100d0144c0d40e540301403003200d000c031082099514003420410141d4110790300c4240039125000844aa260060040e110810070505005543ea45200012076031145054005000540007410108011241500601c3c02082d19618241103423220001c02809100070b55a00d580308440c07041d06444c080145503204081d083c1c000c1034070b46c281111800300d14000c00e5862142080180c20300144545080070099021401042e51118000f840c40c58410b0b55402c00b600401a05461a104604450703860380c000c80c00540d5130f04c00035501e9907035a00e03064907281c100780 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 699040863 1250 699039613 699039617
    0x140405100509100207030201020706050408121003050c0f0321030a15051008062b02040f150515040f08030c010b15030109020721120b0111070e0709150f 67
    0x400d2810091450280c18042c000705405007807000c0707043c0000002540400004c900b99502440700350089a598414103100b9030061401c0e594604180001910000c0700420305243c200580509002280000910303140610701031350440c2c0559645400603162401242a2103550912442d030b0030382d01c01c0d000b80554002c28150b83c00380041103c141d1076010710362132401a40d4001e4681d101c0f800c01244a014216040032010304492403001c0d021310a02e8850010841c4860501400c3d414a021401c040c45440003c00c8400030400048448141070360b4070300600c1c810f0314460b1300c84a00d400e1200741d01d002160000c080c681d94800d15680d9a5000d5601d0750024103005900b9441e044641c000c5040ca82c031030b40c0507000155005072950f030030540c0c107030005c5d00200e006071001c035004101c2d0445131101403401500f80020342c841c2044881e0425051007510545106039040042c02c41d2044442c1100041c058203036003442003124100c1d40c80d50310444d000c600961020b25005c40002410403c2500b105006501441c030b5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 699042113 1250 699040863 699040873
    0x1b0d21030612020f04050a1506020a110f180405100c2f06071803081c0606030b0f0f15210c0301030317040c0b040b0d0f1b050f0c01140405 61
    0xb142c4101d03090300c40000194000910140402d12443c00b5406268400420700c07000604042641d08000720004c1c5400800c05644542d525a0500c114105600e07e00201101c03101d6001400c140403034801070000315070420b0b00341840f0200301041814014030070703040140d540410840b080300800038519440d01c6498071017603003041182c0904100300740c0d40381e0642d609140105074589901804613200e4602100344489101d262070301000003868100103088003124030060146414281c0802d0045801c0780c1d00c550b007854a050542559900c80000e40103c29200701c905005450030000400c64400c0b054009040c2c19400042941c00f454070708100d204030004500062406603501c036690007442c40207000140126588425072082600d004035040c0c0c1c01031040304a252000d540d00146562600035400011040340301140384082c804442c031481509194603001402a014007903d0b610a054240c1c0583c01005000510200d0442031b50040301c40b010701c0980208840c4d082c003240d1701e584d110203407000c036154096 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 699043363 1250 699042113 699042119
    0x603020912061e090d0c021c020d0b071704030e0d06060504020f0a14090a12050309040914101506050901140a02010204050414150609120601080c01201b0d210306 71
    0xc1d411704210015202c2a1343d00c550b42c0c01308100b00f44400d98100d420300300c00c0304000040e110004045003041c4035070703c041203a081c0040003030001000604541b0904100f00308000200307074040921800382906440c03050100d40d0a0502da0003401030742e0481c0c0d07007007030001a01c001c0c0440520001c0441580b2562050142820114410a0f070311409948940c89101c14400f40440030300580c042c030406100364110391603d511000880d0942c1c4207600241c82d100e41641d40010440380500001c8a01545401c0400002c440e0180e0208188068008c51041000205018805074003c030908038000407291002600e9845210009003c2c0d4801c0c02554022030500302140c2550744451070090103200216036801102000000b4008560440e8065542c00301c804400807020000504c076407800b9182c03000181640e540e0400000d0480c00340d0121a5101010041104005040c0401c1c90720b01c00e02d0f10814008551218000255601d82010b030240652404159080d003442c01c0c180039849170035141c1c5043c446030ba5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 699044613 1250 699043363 699043381
    0xd0623011b03081f091d06090304032a1d0601030b06030603031903021306020106080c0a08060f070e120102071a15061b01180501240603020912061e 65
    0x41d06260040c04034503200003094000350b810440e0100c00c000a840c0c507445036601da100000f81c43d101100800845185c08101005003410700c401c1e07601c2804800154640313407071a42e0b06a030760201c05902c09009460742c0610200103100e20402401004c5001c80404107001c010310f808026002500c8150103c1e01e880303081f00b500c0c240501624801d0b50000c000c2c50500c0c502071440402e4085202d0751408040e801c004842554503800d080c1c002038802355000280c1749080c011043e140c600c00f83c2c11540715802c80035040200c0000010f00c20340c0641c04800303192042d11400d0b01920242d200c0c1001075402052008038405114055014010450055400507140740d5000709070b003542c0c00c5c207940c0f03500024991400051f8a082c598010009034240004a0ba003651071100190b08590384810380641164001d040601400030900a10506c0c084010b0807808071082042c7e02d40c98070782d01d44991001d0503004203c2c00920360b10380404400480d40d03542a516103103030542c6c0004010507100f1706142c000e0300200228500c0c3c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 699045863 1250 699044613 699044657
    0xc090103030c06020304060b0913020109140603062b11010e0f130b12060c031b0a0e131515110105060a03231506011209030804080d062301 61
    0x780c241e01d0380c1d8252070b0702d512001d010354002441035071440c2d1a2002d030f02d01c5848207804984a00034080394008444100c0c800104440565803041303e002c001d0501d40c4e4101e81c4d03010110382e0400b004031214007000d040c5941c0180300701d080e960344c0c000c840840c0f0079250501c0910b2070f25419144090b603400c1d103050380d24010044c00d103070000e8513141c010b20842c014020802c1c4540c003030956030000518078885003440341461403030140104c900407100607000c403d1120040680c5405140380f26401911820f20b500c0d0000202440d43e0440c03801d10130a5065510486080d90344d0002405c0b50a05540031041512a20007002d00340121000500091f04004a440c030245c06214580c0500402015400c030f00e491500c0d005640080d40154a99000c007069140756041010442031800d490010191002d52038450f0014000c0c50704002e020161608111a800019521065044e88560300041c59034445c3c4c1e6207030103032006094a4010403a0a00224001c07100341086042ca1200c4d10340076650f00300202e42c1180d90f81e0315a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 699047113 1250 699045863 699045869
    0x160215071217100306050711190201030501060809030f030c0c0a06140a06030503090d02010201060e04110901120201020d030c110712060608030405010909020c2a0f03010c0f0503040c0518090c0901 86
    0x10a035451040c03000400d942c04c9a038002c207251401c10b1062204192003403c2070327400d0321030030658102840c6540443d601401003600501d0b440c1080c1e0310910b406080b040d100e1017000e0340c0200360f00340040055454800f00042d10105060002201c10103003003840c015000300340070344414400c140303220001400703071940f1300500090382d600c98003950510046138207000910101c1e8a00b281955280e5101250b000310110540b48201d00901c101c2c1c0c81c0340848424000e100380d060300700076140c00200404c0030150f42c0000b40c2c144803c040c0c0c50005840224500101c80604160f43c5811090060700300c00901c00d202940e1160410340a040204640b5680b010740f65524803807840341030701156011504000c4800e003a8043c9c590394071010309032040c510b642501038561040c038840816024204045041c035508080c40c00d4009404150004c01054503281c1c0041c00c08140c01c40c44100b0042d0020016080000051b5010b00401020f802c0074002c00300b120382c11f0b114080c11100c11646100300c0e00c55891500d40300ca0010b0403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 699048363 1250 699047113 699047131
    0x403022a09090f07210f0309090f0c08010608041b0f1a03060108040b0a141617010e010b07050c061902190804030209040302031b1b060906160215071217 67
    0x80d2614101810440150743e8070142d0b501d80ea9401d17a100400d00b0b900f00007802501c00c4d41c0740b40748141001c0002080314158000c0391002450040454403064010798541e05444450074071668039912031070441154402c070400300300410010f0800080c040c841030701039429034024440080c003441001c280d410907800100d51090000d052200458081000e01e0b1180c2d0f0410b00044000c078000e000d444031454151414bc0d40161030b0646191880c3ca180e500403020307000044071480251955140200d0348803500d40c10300940340d01c45070000d0035400f0060100b2810701d494038090304850703c401e5044130138980e00504d0011480075008032048620214020710034104960380c460101420b06045409008090000a01c01c40c1980300c10052162400d017024402a0400a10f100406031051280d0b900b03c5030304103024459014040a000400c031960351202540c1e0074540d0025507031408501c50000403806444408010b80303080001405034180a4052000320402640e0b454805104544210b070f09402002201d002076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 699049613 1250 699048363 699048373
    0x406140c030a0e124914161a0105031207031b140a0309060905130c0306030c060c0b0105100c0b06010e0a061e14070b0403022a09090f 59
    0x210600070b05000f042040040c0011003203d44002e140f03890100060611140c1c3d00981c5150600351140105400c50165681d006510034099141500403944480c00654240a4103050045103038240340140c40c200c007604401c4202e5904d49080016184141d0034070041d840c0114000445c40b0b09000030380400c648109a84a4038040f031544080f25128078600314a90819548282040811001c0781e081d621410650040c086a064600e0003800301c003029407081003481f2100350100314655806581c40b640e1401000045412170b2280401c030024112500014a146d00c0900d011070500d48c4140d5061241d4828181071250f0b0740c07200108112268045451400a400b00c9031200000d0040d8415075041001814041d9010f80c50307000141d0801a2a008200000e07124600c01c44c4105001ea0466198007030303400c260510440605009000d032080c12006055402c00c02e000c507003010310804c10b00106d1507507039070400f4140e01700420005a01070b0071122288a088502c01041d413151000c642c1c548079844910081c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 699050863 1250 699049613 699049627
    0x15160b040c05060a0e040f0b030a080c0102040b161a06090705090d080a03090515040f03050a02030d0614040b01021b2e030b0a0806010b040e0606070c08030406140c03 73
    0x812004000300100d5400000d50000a00b9880d40000380c06a12410340312054100415010700080703c2c001c1032010881414000540803c0d14003080c1c1c166550b07040b41c06591740e901d800280700e019114030b030b01c034405808000480795a0061940d0244000e2441202030302c64002e614040710308440070591754941d2012240002c544240c0c080e10051000b10000741201483c51442e48440030340e604982d501d0404251150001c1042183c10b200c00141c00d007a1131140005030910f40c0314104504403480000342840320015204503014001c106440e80b02482e95000d100183c2c8606001848400ca881042d02841c1402c0c0740b80796075800070440d4142d641c0050300c59141c001c40d010400c101c8a25441c1030451180303038002c0740ca00d1384010703043d0380fa6640c9903620081902c9144005104403c0c0c0607500403401c0707400080041c409059008200d40031100c40540e600800e8984400042c0301d4803032038400030165040b03000000381403000803001e0002c0b500191520000036500b21041d090900c554480c50a00d40c00c20080f01c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 699052113 1250 699050863 699050873
    0x30d050c0d05030601021c052a070506070f0c14130506030d051305060f12130b060f0411120109050603030c0705151b010203011a070f060b060f0a0e1516 67
    0xa584d00c510144100c42c44c24081c41401070000004c41c5076600043c600080c2d145007449240864594005440c041c0550140080e00c029102c03082030013958851603001030904c050000d1140c107100450b1b041186003031400d40d604d0b100000d00516540c4c0e10300843c0341c0d65088002106070301c6528400c180240c064403071101003180032501d9610520307240d010b44900c008040340680f2027002074180802c0760845503548500044e803281c54503800030841040d80214078800400522074015a40d0043c0c2d041e40d15441d400040301c005009031400c01c1d40301c08020700c041aa40003107408207015074100c81102c1c10401032a01d40001745a102d1103049a1101242e00c182e004011030300300340c210b04802c50380248046040a4150b40098403c0303082c0d29030054203a40102c0103110985d004000245a00d003881041031500079555a03181d1140c0705d0610141c1060b5581d103031030803e5110348080720030b10b480c5c0c207181a5880910300380c00b500c0315039188100b60044e4000c2c594541e010f044241265080f00c1a420101080c191960351 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 699053363 1250 699052113 699052117
    0x1401140103050f04110f031e030306120f07060c290a0e06061c060213080d030e0c013e010c081b040e07020a0f0b060f090103150b0301150e0105030d050c0d05 69
    0x2000303805201e00781c0034101c15652300c0840990303580c0c100095650780c242042040207035148190b09001540080c3c110000101d000034254007245c80500b802041111a81001c0200400b1409040440e8184c402c0303095410307414221380c1e40309a0440c00701308000c011244140340d603424110b41c1c1580003c4006200c29118003500000d85265104d1078000d46448518035441d6400c080d0395008061950000b024503010a816020310300d44103045000808600340640002446405040080c21507501350203501000030075407a00c0040a4a15155004400c4c4045c04410b4020801580000002114140420031002e10980400040c1040c440e0360741c201070078400d2a400761200a803045040d407141006460019010006100c2c80c2802660a000740781740c520180107010f91500b115078403031040140107000069101c03140c0090080103900c0003420042843c00301c2d0040684103034030924038410150000741d00e14a00c00b164140c860940544410315090102a2003e0042480c1c0001981290b611900b019200e240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 699054613 1250 699053363 699053389
    0x501081e010e160302031e0613020418081905120412091707030308011e090b0a05150a0e010804110409030e040905011505180103080d1401140103050f0411 68
    0x1000094203810000c000c1d00d800c43d840100640704118480030400d5107000e00c075840784131041410406c094441404520703280ca00040c111400318140c95410380554440b0362109a0030020365140d84401c0d200b40c1401002034010b0100c0c040f5040300c05031201e09c13461080c81a243d69021041b107600040d02e455840c40150400394581204100c41200005181c0e004c4107074415000c0040800703000c0303660441c03d0040c01c0c41c005800c203108000001d043d02980040b44044a000c49601d50030000d00700000c100020f081081a40c082036012002d032600040b80e40c082d000400c04d10446495901c16001894019107600c1c608503806005800019219a0301d41040c0c2c025004051203440c3c0700080002c180c000804481e56918281c0300c9030354540c2d01c801204007500c0100c0c0681022030b1445148001d0303420303080e0f6808050100800e0300f0b0010949042840064100880c02e02c0030660b402019a10750f1a2401c6900da1340e00e4242c00a0b040c14045803074840302200c03c900960f0880310340030400c031040b424041c00615101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 699055863 1250 699054613 699054673
    0x60c020f040504081216170105010206040312060b0f09190605030406050406061a0306010f020303062805120d0305070c0f030305150a0f0e0604050907230303030c0a03050901050108 79
    0x404044e01d15213500b01c0600c03a40791082044030740b030703045000107241f8640010540200c00c2a00014005e40e07070000f9000b94081d0341868135108082c50303840144040d1003240d001c1c00302d481010a80c2c100c0743c0480d2019082c40c0b10290ba66881400032900d4404d80034205200351f0010070020400f2070003148180e08204e034001c0c021540858090b036250f00040d000d98010183d09503150001c42444030b15030b4807000d403040900c0288010741c110300300800001c11f0360720503030340c0c80780944c9e0034004131030b4280c58001e85a0020300004000006002464084a031502000c180400c0000d1070200000c2c1111b001d0110782d01250741056004003040da050b07600760001e1802030008043d00100c000441c58036510280d0f01c501a244030b40305400004e150294081c011800541144e11541c2840d0802110a0b07002a5880495130365200c0c03d00c08030f140000440c3c0842ea502c6019406020001c02c00c051880060001d001d025038660781003190750ba07041d40d51803c0740c0c0700380541225038000c2861881c54080c0d10f10044044407581d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 699057113 1250 699055863 699055867
    0x11090907120b03060703060806100e16020109080f12240907020c09010f080c090f070e130207061e020703020c040209040e030c06010312020f0a0f03050c06100807060c020f04050408 79
    0x610029141c20b500310341490010f03403982018044208c042c081c0a400000092100c80d2842c20311540140003540281005030100701104880340040c801d420101e80140c101c00c03030320380c2c80340e10b141c0b119150352204010380000c2d40c1c2e00002c0740c0c0d42c0c001024141603080300411598580080241000a5118094040401c51240422a07040d0341d5034082d07094020000086114101450401c803641031130083c0d801c003480344021208101740a101203900f1a4400c102d4a0300c401008034a1000404010b000b062a0015520104240e4200903580c0d00c05000f604882003242ca841080c000380506a118070f0300d0080044e0481740d200c1c42581010f8000e4504418004c001160003041c01c0a0903242d03821203034103841190300c041c0c01001404240c40348100071201c00e1000c2c24402d40b440003426564121164028000751104d8403000c1410701c5441070710303150342d038850941e115414181450311080f1014055201d150080600000f0198010040c00401c103902400c1c46520752902c3c0304200061200810039a864401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 699058363 1250 699057113 699057131
    0xc04050406020d42090f06080708010b0a03060504020604120f03081503030a120b031230010311210109170a0e01031e060605070b0c2b0b090106050403061109090712 72
    0x4600440c0e4000703886c9080019543d15003400c091030501ca982c0700105a9141051024084c0c036609100020303650004008038450300c641c8080f816520480d4040c1d40010100813044c010001d1441c580700c4414000e50328800c080c0c441c030068402c050200d8034282e515030700400c240112580505d4400f5a420b13440c01c000111112240042803c0502072200307105070400010780050b115422988940c4100d044000c00ca21400303811231401c80b9800c040c00045c104404080c4c3c0345c01c0c40d513960710a1035603c00408a048040c1c100d440c8406010382400003040750f20b81c210718100c106400101081d2140c00b00f2036904c5001d40c1d40c1c08001503006100541064500da20710803500054413181d4000c00005240e595180f60780d9031864103080e0520140078001a0715440100444203400c070810b1408003000c1081c6c0140340703084881c150070300003d004450540350080d50041c000598140c0000180081300c2c0580000c0c800800c8013148103030144140f10f0259488103200011a00091140040c0d581d1210141d0001540e400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 699059613 1250 699058363 699058379
    0x304030c021f11060a02070201050901110304030602040b0306030f0a05061314071d0c09131d0a24090c060c0503040924082d0c04050406020d42 63
    0x80150b00c69400b05100c83c219111044042041c1540310b10801d104500b031058a0303000038250b01c1000b843c40c1c104408104140c2c0024414421100150382c0300308119a1540e4904c3d0444007038108481e510700c2400350402600c0d1803000401c84801040d0710102800081e95401c440824040c1c02003401c0d502081401d62aa010580420424001e0460200d00c1d8803c914074000c001030508004010740e6070070f01e00f0b00203582c558039004007918035607202441c0484c403404000511080200303d4411000c80380300d0b409104041c4000d59950300b100d000c541624440011480c3c240c002582d0891100030310400c2100010086030384685c4000c20074030312500c2641d1415554503000000d8400c4040340100400e00c00d0781d660040e203a140307507401c02810b0710005800b0b10105101078050090880303151814441540c1e2080d4400c6c101030141c0403211380014420025801e16040142c003c1d00003190340c01c841854550948107420f085820b03007240e1031144155001c0d0700075003101e40c014000c40050a9032200141007022440381c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 699060863 1250 699059613 699059659
    0x2040c0e0613050301050622020f16060e1014010b031f0609081005011518092306040509100207020a0f060503102108091c0305180102120304030c02 65
    0x407800404000b07600d42020109400c4950280c8010710821181000000c1020350004080e0921001100161905042410305106109401c900002003601440903401c111166202a0401800c80122206043d0180046003110088207500070000260801001011081c00040d030744007050045a020514405c0c201100c0001d2540004000c1001070000303102c0c1d00307401c000a06108840c044140b09551502044000040031072940b030041120340c1000070718022040040d00014401604100f10710034980d150380c5840e81380005c1c856011690030f00032030321a1070310740200d40c00b5140c518041c0150321115100c030402075020716022604013282d03500c0080e0b140942414000244600e8580d40d941b40740c80220401c81602035000100201081071034420041143d4040d071100315401b01c050707565050440300040030300090f03110403000442414420010994040701400240901841b000c0000c030a40005985480312840403000081c003e02c00900840d100c2e03031a00c400300c0e001420081142c920540d1b111142 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 699062113 1250 699060863 699060877
    0x150603100612120e09150a17010c03050a060b0307081506120712060f0b0906040b0a0207030210030e06041112060108010515010e0a0611030c06041110020a0f02040c0e06 74
    0x569004441041403040703840020904603d03600d0030b030b410908850700140c0e03002000b401c1542d204080c3c0c01c1c130005680341c0c0341d640d4024000401296000808003110035019100d0940540c0002e8140808074809024038000c103019075206049503030459950050480301420001c0607020b200c4042841404141c8075500107002204400001d00c946180c580c202038140581c80120950320f0745445c904006180c003500c91402a110010035540c0d80d804103030b0008049005a0b08074101c0ba00c000034000701b101741c0002d143e0b0f04591080c0c0340c0ea400203417801e400342e00700d0f4101018002c030b54102c500000c0000f0b40c84c9070302180c0100000d0260384100303022641030740340280c260000c09090b0356400602810701041c3c02000d81145003403070441401c40c0141c0200b140c00c04148100301c280802e80542d929407041c1801070760011280081219800d1a09051002d42c2800c41c800c0c490103a00000400398405201107645084079400841503003455419a0031f00c402440c42e076201d0b81c10002c1c601c4071a60b40b0340d00c0c07100814013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 699063363 1250 699062113 699062129
    0xb0406090302090f15040b0301091b0e010e0f0f041e24020918060a031406071211030613060b04030c050a06030506011b031e0c030306090b031506031006 67
    0x4007415441841403028000c0c00f1108044150000c1000050312180d510b103902c8415a00032402c88080b44c082800343c5902c10005020740100d40031802c0d50700c44002080b003183c80003a15103c690366101420600c1c0403064418030188001c1c00e0004403005021000650064440e2191600304a040d59050303800300404841111100014820803005402400f24003501c00308020b011413406ca041400070340c128000d411038403810907034600000c03200d94a4500450045412844c8540542c80e4404980c2e1601c80071070301e400c04100003500c00001119548112403506212008403441d54440c4400c12041c101c1003821411110748501002c643c0911403c0038200451160303c03651589410102003100c580e04a4010b01c081615210030030681d03a900c01244e50104a003100048105e561700d040880d55107150803200720300850b16200305404154040040301e83c0c5402541c0401c900b540320ba0f42e540c103440c603101900f43d15900014441da8603201103d0540c2c2c0000c03004049814004206100f00140c42d02a13006602c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 699064613 1250 699063363 699063377
    0x41a0405240f07090803070b060a0b03010608011a0301270f0230060f0d080d2310030302210c0f0705100e010503010b030a0b0409110f060408120901090b0406 69
    0xd035a02075000154101e54141080c4c04014180010345569004140e00a401c5681c0c0c04045903c5031191405600030b801804407103603a079030f1a502c0107480b04000b071207519904000000b134000311038100c2040e00d05980e9003800d070001114254a1708117030b213410030246403001c1307a90b20b00c2c00496512038070040c10142101018200b2040c04964803d8201e82030000290b0240d541030108205960343d0503810700c0d0701d58100c500368516181c0c1d0078486040d00600d40154501c40c5400055001070030720101d54490070070101c4000b0540c1c0d4079a40f25159000342d500c03004000d81d102c1245020b1109411486c00325031000b545829091000201a451400b01444501155900200814042c0d4205003841c921302d15490708010540101c05070008000e444140f1801100c6c13040800498114a107940000f040c981d4014030520500b03210f0304280c6003030490112154454009074900380a40c2c10424203850403200000040d060100b84c0104490b0303981d1024000504010f9020004034009a141014002500855a400e5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 699065863 1250 699064613 699064621
    0x1403060c0f2109070608010b0f2104060b090c090f06160615090c140405040c0309120806042706090302010b131b030e0307060c0e130e0c0405041a040524 67
    0x1d41013140e0381d044842000b020030010310000c6801d000b2100c862020003582a80d601556510b100c40049080c11102600404028041440207a402c180032207035040700c030b4001035104e504a038042840f42d03c01460704880840c0c40b200892802c140a440f01402004183d02c0e11001d5a443c4000c440e038040381e40c228010b5041c8117021074040e521807050000218100300f1140420100106c22501130b138440c0c144a2500e9094404000d8440c0d0808242254004030802c12880710020161000c07000f02c800c80e024a00d002240b03e150380301403c441c0724228444a50403401403168440030f026180c40d00c429810b564892120751025150030070080e8440b00701c80d10009a4804560180c000f07040d03041c10685c100f42c240500107907071007000300c215070705c99a018000180c41c0300300040c2603a0810304c0110060340400b90020840715042c59402c54000c1440b440306850800d2000c5080104480e002d40300601842e0b41c0120b842e03900c0d00e54508694100e8050f004031100c0490781d1104002c51715440c42a000105140c02c144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 699067113 1250 699065863 699065881
    0x9020d050604020c0a0803060105040b0307030507020c100f030207020d080a0c060501050406140103020c16141c1e0f06050a0209010314040203060c090a0807090b03071403060c0f21 79
    0xd8104004640943c540f0806201c015505c606040c00500340f100004003169440e801201250001c080c80c0e08040c0d12490b2003007010b00101002c56041000d400b9130505c540707545ca065280700c40c0005094803146032203200e40c1c000710000c0d005040c08981008002c0500d0740440c90079005440c1c5089195280c0030f030b600c4240b034842c05907081a13104031b02860400e40c0c180b100000310f403143d28400100307180c0146c5030744044c0365162400c440c03018003501c0c1079401c290201d00110f80da0788100401200795003103030340d6445510058030b8000b01e0500142040000401c031a500544110184501c2ea00458000f6601c94090701d94038101c803c140d603824541540001d000d00303035503094018044030701c803030260724106481c09030086a154240200384100c10100010308540c156980911b1201820b45441150b031146d0b01d50075102c004018541c00c8520034030401d0400181400307044c0c2e881ca11120302801401c0c0d1922090b001e6541c0350004103004204140500c2404c040d4500d515024110703d000c20300440150a10504c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 699068363 1250 699067113 699067121
    0x20303030a051911070209070e10080117031305010f180b030115050711040507020123010f05031903050723151308031f12050303061f2c040609020d 65
    0x42d9042d180c03d100901e2a4804c800d01034a0800383c043c1c0c0c083c41c0c036a8540b2412240b500540c4441e81c1d102030342006030540c2e00e0f4480340e003074140c621160441d00c0c001b10040006030350340624800302c1c40e800c3c8149800c2c00381e54400c0301408028109810203004503003403541200d10102d01d0703401226105001100411060122000c909440405818400e2030b00d425a219400720078003081041340625110404262494800d520400b401c0c03250701950041800600d000b20140503082c03003003030600f0110601c0802c0903d8045400e2407481030427000c0301611300142c2d5007684c10384c201c0c101c290303817420601c112143d01c4601d0b04038100703081d03202c0405425800c42055000711090405414240100c10f9000400d0000d650401142d400c0a101c0c84c02c0300d01c1c1d00c01c01f5454001840e00d03801040d4403030820315401e2b0801000101a60141c00304550300d03560b004034403400100d03000100b514800061a00341e110340c1008460007040b081d821443d40f0040f4200c24800c04641a5901c47d441881281c1c0c0c0000d20040c0d035115882 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 699069613 1250 699068363 699068401
    0xc12030204032a12050a02030106080f032b0908070c06090501090504091403130905010e1003060b030c030d2a12081e040c08162103030207020303030a05 67
    0x18110308040c00c54860410845116400b081c40348901c400c003a0b180058030040b8030080c0070b040501d2098850b039190813070b22541c0e00c1c0c030203d0103582010130101d01c1103004075500054451200066040401c10301e000c1c8110714403a45010000c4611246004046480e030040e09200c501950719241d076880e1625107800d44c000c055000740100030030341806001382e82e440541d400455008a0340403174103078140d08159001c0300f9910102c099030701c0001a12000851441a924100e443c2810200f045a07a50303d00621441c9048400300d4074100450002d0000440d03903440088502c8000d003c0352444074254010078130b00000e504500010422100c0610359249510b5102454003518a115135000032050b50341304c07590f00c02d4883d40024020850700140c0300c0080000100412015002900ca03d828a81050307820340c2c0860141c00600e010342e44001c0151880c2c5030442d0111100d400c0d22418202440210b424918a605021010981c08100a070007603581080518003c59001c1c10005103420580b052140b6140c09072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 699070863 1250 699069613 699069617
    0x3020411120a0c05040b0c070b0a03140108070302030a02101b0b1812070308060d0f08070b070c0c0e1009050115030e07080316020406030209090c0114090d020d08040b0301060c12 78
    0x10384414505038081309542c00c8820520040e80c603044207070340c0305007852219000410301c9400480c116019540c182c005d1070f644002d424400b50182d803140a0035440e040c4601000c0c0d0183d108289010060404500c3c2044888151501050070400a03c01c00740c002080d46090f540f5018074014001c0e9007070034245000c4035441c0c1c0c000a10112425551402060094040280c244510540024040d488101c40045220360104508501e001c084c07802100300c1d00310080594803e0103841c00651214051003004140640041030168600d1804112036200a0014111f150030202d9410000300d400550040c68060309d84150340380d1110039604401800c0700e81a82c0300749800e0380304000400c0024004011034500d00c02801410300540614004100504580c0c1d1009400c50400c00c2003180103540415141e00f8180c0076a075002a003094120200200e0207101a41e80d03100c4042e00020300140b1700701903092020341c03048404504196030380c1204403081c0c00980c00000482c4160250030100a0030b6180b01c0303081e009034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 699072113 1250 699070863 699070871
    0x911040e0d0c1209050303070f06060501141c0b06070c03050d0206070f0822080909070e15070f0c06080f01050301090b010509040606051005120c0a171003020411120a 73
    0xa564010b1484442d68805004509544440000e03240b049090328003401c000740c01c0381da8032502444d0400d41600109015581d007440c1c072601162a42c8500c0b803581d440c6805a0302c0e1f908045991518141c00c034040f080b6040103d6031940d420344a42c6811024008440c02080c16007503a0349941400d42c201005100071004540000c01082040d82d00303c9980d0482404901d0000800d90f28820851054020a00c100c1d540f103014015003002c011000380105209032040c0c840454642324290203a40249600c1d42d030380e170700201c20200901d82d05c407039402074455140154100d411820b903035250356040301055008a0000780718031041200c450701c1c01021500401050b0020810080903440303031032080c1418003425200742c62030808202030140341d0304200040c0a00906041a89102400151855020075050260342d6070341c0002807564038900d07051b58814451615020b102c00c0c8080e01401020000030400d809020a4240c0803016131074501c0f41402200b031020300c0c240e640449142d03034070030710100a2202c0c4c1d40c6810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 699073363 1250 699072113 699072133
    0x1511010b090601081611031c0e01110405040e010209061303030206012132160603090203060c07210c0b0a02032509090e1b06130b09040905010911040e 66
    0x841134260390b124021140c00080d005260004a0302041d512070700e40c51501c408242e460500303100b4140c04900610010040128070401420b1500340c8000301c3e1368110f01c10b0184410002400e05411149411050200040c500002031000035010f0700300e0a09210f1404c0b0b0110140101501002114094042e84c409401d201e003549290030764881d640d05d4020308000b002c00524000c14100c8009412503031012500d140e205080074902a5036110115018224902c82400000d00328004d00c6042e9034036802401901403550340c040c81c03851a6000741021101e0400d0000c4500042c0501c42040e00141803540d03174041c00304c80c0c038106101d069002401c05c46510344104140510380e23908000d000c141c108113000d14503000340303801010340b00403200340c0c801d081003030a141c0110003813800415844480785000f80c80c4c100090703140060001078041e170b005240c5091800b000c00d0048900c0100508030b090700040000c40c6100c0b00e0f945940c203644833810b045030200300c1145620403520306401890b4103c2c0401b4024400080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 699074613 1250 699073363 699073367
    0x50303041406070311011a0301050c0a020604332414130e030c06010312030c0203030a0f0b15070215190c1112060712061406131511010b090601 63
    0x1070400422480341c100081e2010800d4042c021030000124404001c01c401c250a02c03801c10040f00d075000d158425440c00002480da03600d00030680b03000034a50703801040c599555a890029503038203400d00f440c0100c0c074107010059100c0d4820000680c4c42d800d81e4003189201c0b110048105008807513640c1059a071130f041c0280105d40c400d0306c1002540b0022035450120054000701e400041c4000344044413103000c0050091901b03200000c04a04a920464269000072400c02084048030015900d03a40141c01c00c0002c10f50310003650b004948000c6084c1e800203035030800480011400d141841e001c100440c030108490040d032402c050b481e040c600c400b41d000c902e040b400812002c030340440301c0b500a05101c440d141c0ca1341403110b070300307001c4004035800b810000068166031542c0743d940c01c0454000000410003c00c4a07649036080c0620b104860b12900c02100d02e07141d01e01081000c1c2c004140c6020030205c2100000340c0d8403810640500c42e9042525228010030781c080105d0309580d00c0d903114070b0003a40440213002144e6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 699075863 1250 699074613 699074639
    0xd020d020603101707060e040b03070e070e0607030914010311040b1e040b1c020732010c05031e090c0f030f0d0305152215080318040605030304 63
    0x159045880070b90b42d95030703181d0f0401401120381045109440004916100c001c2c002001e5082d104151582c54080113400d0030441901e404281d180d415411401c410040781340300c1c5583c2e03504541c0034244880c910169078086a581d42110700160300107503404608200810b110060100c041c4030a1038103201c10340d100e00380740e940c41c4914490380301551000202e05880b0ba09400c2c116102110904409907a01c0c2e075243c032444540c218495807984030120350100b0000700301d07520840c3c50285e403054108007200381810000d840704100d0798800c2400700c0792201080b00c000081c07054825840c4507448680d101d05201503001a60b041c005a1081c0c0041450305100016000068450070342004454803a071001244002c24140364514040510500c1560041444603070160001d070710a0030030143d125202030181c03080000b2601202207804012000a0701240e150750150804104c3c00d1048458002c001d50700c0210b21301d56802500c44a46071507010300c06041c0d80c40c4c140200320040200314000c500381424680c43c51101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 699077113 1250 699075863 699075889
    0x30310080f1f0e0a050105070201060509010e040204051e070809160305030910030917280804020d0305090d110405070819020c07031509140105070f030f0908031e01050d02 75
    0x901501d2480d111406142d40026000b0f0b1401d03002d4a06000492a0080c060035054400c4809942015404511070030042c1415040f00c00700650a020f9494a80a01005020190565891828000c0c1030b800c158640b80b402801100550307501d90051400d81c80c2d02e811300c0d154001d041c411140045013040851000004c1d544954400c072440c4561905450707060b0000d000c802001010311205a2200040060800280002001c00348807000310781e60021000005646100c82c0b2408100c0c09004100541000b4a10322441807180c1061460030113a840010340710700c0709100c11150300885403242501418a4007c09801030041c0c1000318003410840c05050200410401e0346152581c00300700c54603510420413070130004642100a9440b03075000c18a0a9015020007042a566030202401c0512401c50500c101d81c41040180d50759481c511040d802200a8440c0800c4001c03699201d480c914082541c9000460051134000e00040c0007094904100c44001e070142d011500c200708008501700507071503400b14040c070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 699078363 1250 699077113 699077143
    0x8011a0703031802100503091002040e0f040c0915080c0321030907030606060807030b03151b13080f07091b080405100c02102403060923030310080f 65
    0x201c140b02010070030140d0f070b0586010390701c5818080c00b228556040b00c010750051600398142c690280b2890340c0d5206070301c90740c4510101c280007907000603091036201038684d4005100d6800030f003a8503a50100f04060701c00803035950740c62180c00d417803c0080300c0c0100085006404142d01400d0210f600c00c4d2400c1445040c45604203802000000040301844140031950113107501080800959071180d0004041d20011120800480c0c46c4c0700c00c0c0341c0d00e0725000031001d03e10b10645030a500c540e500d011406083c50082c10342003120007411b010007494201c0c06094800901000300042c204001d00000b0103280980c0c40d40031703009030382c5084118040031006000d0107003c040c10303041c00211034072103107132607460701d840c04a4209020b490856100091540032030b01c140c500d50302ca2001d00a8420203280e0321741920920010a40a180c80d940400c00142e43d50000310b0340d18090300390180f640c004e03c80ca11010f10020640ca1103160000002c0005046006440c0800b811180c0018051103c49482140d40e80c0041030590007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 699079613 1250 699078363 699078371
    0x30b030c040c1215141e12070e0c070c1a0f0702010509032e020c1c02030702060301090e01110403080a030504051f0501030b0c07021f200d08011a070303 67
    0xb070400c3c0161007942c00007854003010012000000784007041503043d4000c80d091804112440d00307491510000d0308039500c41e440800044200e90800300541041644c078601c2050098071800070b0341e1540440500e03ca1021404000c0d910085032400e15418070507a044000d007031700c440711118943c40c0f202c0c0a07900c408042038102ca540e800b0134001a540c40c05a130700c2903a85841080c0c8204980c800c2200c0d610904807900d03420702000c10802c1100016402003012141056028003908060383d00d6607403410302a04100c0c01568503082c0c454020486c10340c005d070041c10206888900ba813400b41303009d01ca207160800351100d056040c40d040d5902e103020341c82904000010143c8500100302440000d2104135600607180161a40c0005060312030400b0300340910069500c0011304c0c0c0000c0b42c0c80d03140c40807650744580c0180304a00611401003810f1450320032020180c00c0107500314035408905156001c0c003207080301e60310041c080d03030010a5004151044c16007200341c9001b41400c0c03000c2032078004025034015a915060101d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699080863 1250 699079613 699079631
    0x5011802040f060e18150910051516060203010e04030e09010303170411061803160f0510020106091d1606120b0f030a0b07080c03060907030209010c170a020d030b030c04 74
    0x20300c120a0902e030720013480c505c41080c005400d00e0f441402c0031006060364110040d548804d000c1d8a2030100b4031401d03420201d00480d400103183c05c0d1703000340302040051148800d000d519450b00c0c401c0f42c009130859105195070b241030106044d001450352141441c211081c640c40d605581c1e00410035221a940075031000e80d2440414200901c200b040c10b60210050302d01600d650003004620050343c0c80e0b001890280c000c0c52004410f0300e6441c2d8800381521b0a5040d0b503001c481ca048140540702101032005800c655803900d0103d03100015001d0750407034201241d50300310070b43d03000c1030003d042000080008100c0d0314203004c1040080c0d00003940300b601c0c0c00204d000107940000040407a83e4442c00c1c5030b400d40c0c1400340f01b8441c0100034100c0d11042c021451030380c1c0c1c040c40da0f507014403410062105649566106103101c00042d000d170701c0f94008040444061521426841d060b0350ba0315064040240f41010302100491042012075040042624801c010710b0180901907d04000c40c1d03d4400707046403a0700070307600c41c00c0034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 699082113 1250 699080863 699080869
    0x1081b0f031e070f0504023a0e0c0a0905070909110405270705030c030a02070614040f110301061206050703020708030f01030b0f0c09041d0d020105011802040f060e 72
    0x1190010300c0b1100303a1410404102030243c07924041c1c0503201d10403825540200d11400c0903c01e0b2100780c145c440f9203860301070b001105c0b40c4e44d00c6003403e40102c4c41c040c1c40d00101e00c100e080340908406900c21900402400c103002013000001c1c88a40c012260071032405080181c25644030500030115885400000b4401c1c1001708030134490302c5a50081034200514050b00b00158040b00c0d07040200b000340c4844010380ba00c0c0c2c61000c0320b00e4031054036102031003402840801d500c00603a50091080034402ca80014200103201c10021044504840507101c070001c0c0c41c0000180310840c1d0044c8900407088008000c203504051411040196081000c0d01c442d0ba82c0b0300054196009a0444141c1c3e3307001809030361246000100700a40074800d000455060300041d020030664912420388038095581c0000c910300b04007106007400004d060400800490300c0d151016411542c4050205a017a03101d5035001040f03c1d8108908140d035212a8680c0702c6c14280f0400041041c05c0300700d014072082d01d03801c2c5480710100b0801400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 699083363 1250 699082113 699082123
    0x414060d170406180501030209032109041109042d02070510020f0705010e03120a090c151206050f0102030703050f0d0f06050f04050907050f01030e01061d01081b0f03 73
    0x10700d900c031035000900454000d4010f0342c101d1303a03081c2c0e0310301030008152208011011707800380f500c109415138050304001600b203100290b03c5400ca40e111103000c0c1814818000641599040f900050110000181040480c1498041c00743d401310540c0b004401500c8500911006000388400b80c4001c950119801c0f08104060102d44140581c0da1015034880c1c1400503509011762251104403003a44c038100e00d00b00715520120540d800c91140042208890761581244409008040c90440d9644000a40450b900230643c00c1325006001a40d205985990410844003c8845c0740c1c004520a41f50481e0313004107603034000100d54041d0307850724000d0385603280103c446a960148120340041141005224000364075030b0381c05101101c800320b50b40c440c81404c078010310040b20400c3d2120540c907007180c401030003581400d01600c25503810600d000035000c031010201e103085a080707410009088081855040a030141c2d6078443c0d000d8400c001c09480c500341c11149400e8944400c0401038040c1c5050300780c0d02403569080c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 699084613 1250 699083363 699083393
    0x3150509041a01090e0a080703030e0a06020d060b0301030809240d290a140a0b03090105040c0e0c2205040219030e03180904060e0f06150414060d 64
    0x28522103007800e00d05030380d502c140103a40d8844a02c80000005050140c0d005841c09800c40300b01400704481c003a110000c0d0703544005419070505886060011121208000440344e95005240068848000e01808025114964080341c001c0d44280014070224003040c04490320302d04d00319440541a900301140a108540c0300c20607095041001c2050b68820130380380c100481d10102241001048a941d070494810700c42d0085075581c00141d010020320260700b03018445a41248010301c0050490ba607502030b210558012070b2200c851340d4640c0240300420400284440c054111100c644207145072001c246902409080542c401c1c0c9a08140c40ea1040d502c902624005020082c4c0190b5841c0c00142d0a43c04006c548420000042c2c98166081d07100708021094405c3c8038070710b0007010740b010407070000c20610f00700141059407682d0f600c5001201d151030030090302e0000034500020340110b15040c18400f65010b00c02076424021410007100310300d9a0706001d00c241c0d00410440d09085242260300304032000c550460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 699085863 1250 699084613 699084619
    0x90f2a0415030602370c031803050c030705030a020d0f060605060f090f0910060e060c070609091109060708070f0206041e0906080715021f06140d0b07031505 69
    0x1c0c40100512140f9001400b081c0c101c044914001202c046480301c3c3c0141003000d40740c0d00441ca91051150314828007a03c1e00d500e000e440c1c60846c41d1035030038404074807101641c02105c0691001c6003002072030805105403401440101c0140140c241d41d500480c80318600c14000410019181d000c802c03c00c60300d54464006450b010308002d464808010b40c0854940c0001a194400c05c01d540c1d51030418a0185003051280c11050150740340e00d450040241c0d0141c1030390340d40325071019007400284003445081080100070705041e90388070b030b07950318140c1c0713032402c44600c0000300d800f84104214000440d101c2c3c40843e802581c1c00114141c1c1e40c42c4d0f900740781200310100300c0020340c0010001000100140440c10f1044001050090746c41e000c0d5881090400310f4125108541d0319070031002003000f1700314816004d107070221103500584504198901c7c1d14a401d14820a0020031199201d605002d100451403030618034900941b9a2036591a481d224841100390084c403e0341056214001040d00c481054071840c002d280103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 699087113 1250 699085863 699085901
    0x1407020a0f0303061802031f15180312050316030504020117041a090106080f0f0705010c0201050c0102040b040f05040213090b04140103050109061112271005090f2a04 73
    0x18021480185d4000d48a03000541d119106601000351040f1401040f50f5a40b27009000058160001750b514200700c1840940f020901040000441d01c41e060a0600080581d20130356a40352040b0301c3d0003605a0032082508040c0381c4010800180d80080d0341c0f4801d001c420440c83c8080d5518904090080c002e046030038000c0d4440c50910109010541000c000c0d504500c0581d80c0c0c0d4240824150b9451003070b0001c1d8600c50380724020401465005001b2007009600626100e840c01c503680e0a8a401c0e68083e5000c038200210001e401c00c40400c01059403000340808031070551030240e24140c0803081400901a071040c256650701d100c05c05a560b5444020341c0705036000450201d603524104280200b10512082d107950341009409180c05d0800d6045880b84104a98801141d44502c051000000ca1509842010b0010410b140d002d4103c1080321600c40c2000c030707601103410318040d0303900f030b0a000d002d0441c1d07002c03540311a000480359141148407a00c4582c4170500c40f0f01250300d140000d00a087c040031601200489 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 699088363 1250 699087113 699087149
    0xa1d01090c080a020112050c09120601032904140309031f0612020a0e04020f060304110a0905090c04180f080a030b0a0311060c070f181407020a0f030306 67
    0x19000105454001e19007505099510b041403a20b4048007503009000903002c0c0002043d04030307542d1105800101c103401e1241090b0000021640725411010300007166032040d001001003000c0140f070310300707000c480540e103562501e883d12280810f08030180000388028802c00200007040740c02c2054440c0000020300301c0700d6003005190b02c4401e07005043e2004480c14203010f0f0106080d14240e00010407a54041e04cc1e45042d49401a41905480081e1049a0100c01d4500c0e03142340b6a10900a540aa8040c600b8141c2c0c80c0c07069805c00582d0511940400b020340e040c6800c10191a4000c5018503810310191000f21b0f0b0449281c0507461000e88003900108200d280310004001e12450801400c1820659141004100315800400c5240411480014803142c0282c440d4219810202c0181c510702250b01c0c111819181c403491a00d48000d05a002109050b80ca80c024406441c158010104200880d08113260300c0e00f0103000082d00c614023100090b000816403010748041620940c030141c01401004072030b0030b41c100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 699089613 1250 699088363 699088421
    0x1031413110a060c050f010605151e18010f021513050307060903020618190215071a0a0b01030204080606060306131506113d02030103150e0f0706080a 66
    0x2200f4a080d5170398441c1600900d28564140b0405060311402048034a200c00e0300c01c00180709500290001c003400c40200160740165009001178109840d45601441c0e4000100000403d28503207000001c1c1151f001031800c070112212000300304c3c0c01401d55262001c2c00c0090f81005861440703140c8008080902e04900201070580c08110240511916a4141c2c81c0e40741c00f425582c0d442c8811940d141d050b280302c2080ea001480c05421000325609482007560401c0150b844a100006d40e041c1c03140c0070201c1c4a010401c120300705100783d00c1e000209003411810142040e00c403a64450006103103e010b0100000450000e0741c0d0390490361003556003e00180050109002c0b11311000100d84a6680170406c1c5010720343c50b080d00410050b03c1e80c01d0364043e414841900c943d08100c001100740c010038145424800300c900380e03202c6e40011806107000b0340c952080c05210071444c01c111022010401800d0b0054946101c42210104901c0203d4600d49060b441c6929100c10110081041711100300c46071a14080c00c429040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 699090863 1250 699089613 699089627
    0x140c0312101e03080f1305120a11060f04030f050c030303160806060a0f0309021c0b0618010810090503121801110c0316080702220b01031413110a06 65
    0xc4002d00c005500303100070750329408440d840740001003032400140102c81d183c0364840c003d00242c1215048040c0703040c5d502e0700410744d060500040e030100c0d508291030f12018041a0600c49440c45001d4440301c0c40c00390700c2e60100c0090300071400024a40300700080c42c401800340030005400805001419a0b503241800904032101c0d0074084010f0b80440c0070302c0700164851070000c068420000d1280c86030000024041000c4008080d041e000700d80c007088052840510000720102c4407402e03032040c0f52058050914008103c0c1e05030100b4005400754011200600540340301040c403907400b9040c450045258801440c2c40c5040d4084c00b50411800390208041040044803182d00b5144806d006008201c014400000c0e16064030070058151a103600400034143d4642d46111041019070240c4803080c1030903125400100e011800c003265101d0341d0442d0040d08120304040c81026112031090804201050391122403050400b401041e0000001c01000e12000740140b002e030000000c4001485030030095200e0741c0144c049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 699092113 1250 699090863 699090869
    0x140c0a0e070f0e0904030806030f12040e060d0825080f0702040c170c160512030915040302060f1306110a090501020a05100c230901120c140c031210 65
    0xd410160245180e03402a101690480c07000742070a441341c0d0303664500703036480300c8040c0c01c4a8040c803d00841c240001e0703040c484201202a44c004980ea16441c1081403805028003030b003813501c04c005030b84100c00000c14080440d14044003004085005907511140c90078400c03079005004d00b01850005240c440c801002c0001c20714248212020850321851881c200e9a070300c0702502e00750300c06490303c022459188581025018290002021448001880d80c2d01c90030712084209a40c0451004070901000340303810b0160780c6400342402c407618850718098400135500c10028042491300204400440c181e80145030802ca265a0846018085003071700038682c618a6114000000001c3e4048802203010361000c120300c1c030000c0e08907008140c05c0c0000c90b1524000c103c1e240c4001705120101030814001024104103482c42903200c22041d44079070010001511255008000314203a9241c940300081a0350401000080c0c540c42d611016200e050031101d207851071141c100348500c400f0403c0700700088240501005415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 699093363 1250 699092113 699092117
    0x503160608060d120c02090a051302011103070f1a0105010c030905010503250905010908030c1e150906070206011d040f0213111b0601060804080307091a07060e030f07140c0a0e07 78
    0x4235502c0d424070a04650007a60384440004405030300102641c2318443c6440959442740030340b89404c00b02d6840d040641201c2104030b03020003c2d007003203086000300c0d604050700402e001e08080010404580d4001c1c8060914066241408000302c0490444500d0944000f8000d0525184454400b070111002d00b52502501c21039001401300340380861889404000d41e040b0b100340f103008100d61148454042e03810854502000d605102e8052000c60300b0021802c140e000d8051710015000c607040c1544001d0901c64140c01c030440580c004035220308000c2095020360707801600011036280c1130500d440000d011907034003020401d6107410885446892701c0303800000e0200001d58044400c51081c00d003e6241c0b51002441400e010a600c100000e0104022600170740d4003421619200c0030f01a1940c900b822101c01c07501c016501c00038041582c0781001100e03c229651040404002e6040c16500b050421041c810100010b101005403c50018103150030040c1c20741d080f80060900c03607507a4a982d64810224411220070780 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 699094613 1250 699093363 699093379
    0x20903010e01020418110903030a0518090402010806011b0c260a021513091b02010509010605060301050d0302030405151201060806060906160605040804050a0503160608060d120c02 79
    0xe0900030500c00c8804566409040700700c3c0c0c5100c81701030b5005003950240004190f208000301202c507941400280200365040c1c40e01501d0340c5c3c800070314100c203207440d24466000702c2c880e00501000d0f03a0040035980e80000e003441d282500c4480501070b0350b503410410710001e201d40302c3d00130f000c5040701500440504004615030803404000f208045c49580b141550740203074200a545401c41901d001035070007001d0b501301c0b10920a05044e5569100c0b0100d803117901940343c030103d2080200f00c0603607080c0240c9400080000080c401c4a00b4100060720922040c80b03020321030002014080c0400d0300038810345000707100081901444014290140803543c1c4840c80048a40e4500d500209520b40950903082c00f450002d40180d08041100c802d200090f801440314149600025840200140590003814071581c4650040ca455030320303190074020404a19040144260015002000135800c031600c03007012100039140500c45616208c011440792922044083c004485072208104441d401c805680c0700c0a01c00d0b20940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 699095863 1250 699094613 699094631
    0x60609080c0102060c04050d080f0f030703230106080a180f020306070f050301050f0411070f020306060d021f1107240302040339030b04061b2c040606020102090301 72
    0x913104c0d5811a4130308440352042c0424072513402e003500c03410305062041d05910b1422a04508120040d0402d50344891504000010000c520340d050090694081c0811031001c1c18003007a040c01d40a05505000e81400c00c00c40c480041c11060b920f4008040c850a8500d01c1c0d0b01c03105580c106400f41680300300d8181e0207445401e000c62039076403140c6501c0d8440031140e0380d068150303400c00d020410000300364142030340d006032101011001007681c0b0300105285442130b404039101d902c00380305140c14a0801442d0f00d2054045500c901c0250301e60b140040515421441c0c9543e4482d22a2020354000c0300640302201d947c45201d10220f2440c0e00c20501904942d00000443e8014180c2034048059101d5400014000001d004203c2e182d810341840301e58a4034201c3d0030241c0081040d40c0111296a071540c020b407041002d032004e000911038140b05040f8030391a9040000000c40720548080e0010070840d03040d415010000e00d600c010700041c2200b6441c100c5008109005043d07030344d80028042d4106400240c807951030701050b5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 699097113 1250 699095863 699095867
    0x30b120c090c031006080a15080a02030c01110309010e060f0a050c061303120509071a0d0501050d0c030b041a07080406180309060f120609050f0703141810060609080c01 74
    0x3d41c0c40703691029040040320703003042e03021294100041d2041c18103d4440802003d0717041c440310400003802069004160410042c010189001205000e103414840c084689507a020707800300c200d4218807000e09042c0c00002250021400602c00c030191403c081d0701c08683c1008081d40301e00141248030402c002c0714402e0311041000c074048070119400401003080600880c425044c40d27004941d00040701c1056905203903403540400c02d051980e0b08502220900040d0800131b41c1c08030300c1150b0141c43c068407000048551340e90345101d4149c4a000c040d14940c00715001908000c1022681c62641d115008021440c0c102880041c01808080e40e04507817160a0885480748080d982c180494882c3d010340c0c9680b4841e1605400b52481e04401c0c14101c100030101104902c250b100d4010b000042c401c40c0400103462800c1c2c010f04451042c0504510300b05410010510801048c0c04c10644c0c001081000314041c11426012070340c540400042050382c1a420203000080a51b04003491104850361101a58a00981f02d001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 699098363 1250 699097113 699097117
    0x1509090c0c031e0c0d02030301050102251a0f0441040c030902090c031b071203020921060f010801020a0c0b060d0203030d0b01090504061d0403030b120c090c 69
    0x15280c240c1e80103000fa429410440840c81083d821203d01061400851200560500d00d0314070382007002d030b88008010455540d0400842c0d83d0403a07404072050700210801c00044000706248600c60020400f01c0248a2a040003403c54204215814542d039980b9a00d00b0304101c55486162120f000005049003a00100300c0c0f4940d000c0900c84c141c403800c040800900411006107120b18441e01050380d42c3c1038460041e2510580309000d400c901c00103079220300d008420014140d0f111601200418004e001789000241039440c680a480024100503841e00e0104001c02d0f0704107101150041201200400280c05a4000c0f807114040c002120140d00c50307a0b04d480d8464282c0c4900c0c401100001e41031000700001c680310003200d0303821034002007041c41c941d02d481e000285075400103d20344040550300c24002d01d09681000301a4010441070314248140d511740b035602030301c2540c0400d010710100c18900009042512950100d21441c400070001c40c903607900e0704c40455a0300d5808100e00d00405040021172901d600345da003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 699099613 1250 699098363 699098377
    0x7030c0b12040609140f0606030c040b03030a030e19080703020c01030b0604050909010921020705011b060b01090819020a0b070b0103030c15020a0e13110a0507020109051509090c 78
    0x215021501e9640c2c40c07000a00c0c4e05081641c43d500c60a00110760324505109402e0001c407503400600e0942088002c0505090035120208e1040345070800032701554a02100b55002e80c011800c0020b4001a118030581c200090124003d0a01852071a01c1c001c110100000c1d00c1c0c59806507084841c1c126032000150708176005100784c07550040040c08104034615166042d10741c0b282d42c03600042203441440c4d940d0f0419200e4207204c0420900c07490810707c03503285c1c100f0059004000034a4401d03c004c0202250341d4404c000903101411241e2513076651402640aa00c46000801c1280d00300c0e041040c465041c514000040c0400724414450440700043c44100300065503225134016024101c01e034a560340a07242c000000381c04540d100302213005107804051510143c41500c09584424030602031700070410a05810031501d8074a00c51901000b500c1a01c02541580d225110504090381c1d13030182ca000503a0850403540c0140d52010403120384010644a06015000300d00d0b050300c2c113003031030b4030342d018502c00300d010f5a5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 699100719 1106 699099613 699099637
    0xe070510050d2a020106051509041b02060712091709031203100f0509070c0b1506040305070e06063903030702010c260103020d02010207150207030c0b 66
    0x240054462464510080101e282401f00243e80c1641c00800743c1e0280c2c0e80460310f250306c1d0729698481c4100300000300c500d048001044030700039600c3c5c100b00c81c50310004046020032205114580034185055071f03c096203000300002c800c01703401e254000386610f80d4188180d045600324103501c1402103003c2d0440b9250b0111950603d20100344c11b0030250320503402429a0001c100085e6848051500030550080301ba000075110a000111568500d103502a4802c000080001c2007240000d400000c48040d0f03011482140d03100000c000303950150200c01009913208401e24100d00d400361300700d43e0f280150000d040b980220000015407858200321079800260399030300d0000d40030039000f07104900c2c000f0340d141ea500c904459501092000301d00c103100090003400c002107210704680c028400500a0000000220764980080d41c0080da0317500f080c4000e8030100050300c0c0114034814000c0407642508001c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 698920863 699100719 := by
  have h0 := BRFrame.cov_init 698920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 698920863 ≤ n) (h2 : n < 699100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
