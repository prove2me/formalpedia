-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4848
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:54.66971+00:00
-- url     : https://prove2.me/submissions/a071d042-5e15-4841-a6b2-a68df1a9bf7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 871762589 ≤ n < 871942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 871763839 1250 871762589 871762621
    0x301090b0703230c032d270606011d0a0b1603031b0f051b011e05060d051515030303011710020a0f031d010f0501030b06100215 56
    0x1610000d0403006220300107034140c0c80041c440712501ca0960480e5026503c03e008088241d034504180c92051010400519159140004640881b600c41002540c00e000c0d108220a085074680f04211451143c00d41c0200d14090a0780d001240002512991402d00000392810ba188010307001c10325420280c005064480c0281c0750064035146d071915480312110601c850404802000460019040c141c10103c2c0b070b0b02c1480505558440f6448a198070f091411048642e0340107814040c00540125480740203004080c0728024122885170840b41850140c00c0c001e500340d500260005006030341451248003c120f012600704511004200e0100304c0380c031660b000060014040750744aa060100200010354017800e03181c809801140c070b1080da03100d600c03d601c26070300700e000b890050004074440388080c00c12076110b60b11070708464056a001015000540c0b800d0780c2100c441070710541c2100c0c0c0c8ca01c018402d101c03817030070001d5100314100c5428000c0030210b10000e48800081e40c0d9445050b1600c0042210b90400030108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 871765089 1250 871763839 871763843
    0x30916080d0c2f1005040b070602031e0109051503030301050a05040207080f2a060609070c170c0717010b01090b1b2d01060e130303060e0a0c110703050a020d02030109 73
    0x18601803080503580c040c120304503c100510030000e124642400328017071010740e4112009154030741e041801c2521254081d41c0300500f14450760a00b9440340c02505410b1050070301034040914005a40d10301888003162420041c250584a54414401080030f030396002c1155056030425600981c49410038640352869003d060f0030203001038001701e40322074004084410748400c0c000700d1403145912040600070f02d85646080d41c40a41001407000061641d134051082503a91620500e54000b198030b101d405102560488d203501c200541012070100405541c24804600b0075010400807c001740549002808552440c4141040c403807002c2140300d1105081e0308400d800c00f40e40010713148541c81c3c0489407000c0d980064010466059046804100d101c1e0500c112801d840350420085640d494604e401c00c50500c49180c124200b64407618045502100301c05114041c900c00c50703000c036030020303c1600a491888003000c94580c60b0700041c1b007000812070000d505440c05805480c601442050350001c0389c007421103a000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 871766339 1250 871765089 871765133
    0x904020913050316060b0913031202070311010c05040815010803040e060a030c090b1e090415020f18010f0216210b09060402040617060a0b0102160308030916080d0c 72
    0x804014005150030036018404207c0d4039030a01d075924018006010ba1074240a00080c0540112055409065009020040c042d0610034142155281024250352140300c081d0002070340450708005030320b402c02956880200c0d10103580041d605082c5015a42d0095104031131031110450003046440e107400c0340100286401c61049411603844030719003409002da64665034001d01c0c002c40003004528081050441c16000180b00c180c580e00c1d2503d503440c0804c0003042008180c0d5007000642d07001c01042000301824038400c0302040030714850100140011100d03162070000d42d0080f0080c4409601810854020395000841c80c48404031104042a04600301d148000c0c403240b01c0030300f48075042c02c0c0011094411403003100c080c00040e454102d2000b07040da2411452a0503400480810066281c070b400c10380041c2810310445400c40302c040d40900c18480940d00c1994071040001c1842071606040c071030b0a144a0744094000c03070f0146403909490303481040881c00810845001c80010812040001d18101004442c0d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 871767589 1250 871766339 871766377
    0x903081804091505010312110a0209070327020f03030f030121080a1805030d0e0409080d0c110f06071d1f020106050a050915010804060906051e0609040209130503 71
    0x50f406000b060207000030b50300b4148441c1801c071000d10a000319a0081c602001030801c0040c1507090188501e005023251b405c1c0f41d128445503510810b6190540c40200100392410711200990041c49044444401d400b03000e5002000300402e40c006030000c9a0440d484c840407240e04400b0400d880480140e41d1500a00c14000000c9072052142d01c46071880e00c2c40000381303400351034681c3d0f8010180e640d031210115a002c1a01060503018074a41544440d1280340030300e0b20a031800c10114928230455101ca01c3c030701c0200c2c5000380844130710304003080741002a4048200804050901c2000034050038205501d181e140704c0480c0758010301d9150102e0b10301c001d08508070030a100d15990721000e8040c00d12405964001c01503000001500d01d4000802409103100c10410601815030100440d0170610040040c0d0b44152600314040001f42a031150901c84d480c07200b00011100901da490f404d200d800500854801d00e2846c2c00e1002603501d24200b80d40055500ca0b034650707240c081e407a140d815402541d24845900310300203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 871768839 1250 871767589 871767623
    0x15030703060e040c05120c090c09150a030c0207090203090a020d06090b2a03040b0105040203090f06010806070801080a050d1d1e010f020607050f0d06090f09060c090308180409 77
    0x12541300306481044a02c80d682000090740e45d540e44001c041c1c083e5004c1c00860105144a85e0000104a0b44034080d000080b081840c82e20721a09920885104001a03507a50341d00d440c036641804810041c1901d07034419455410009402541c5900f40000a4424165455600100555940050801e41d40070084140b41e141c06200140c646117542541c071852040c24001c1c55500840e601100c1c0b1940d840400c00c0031a17402c0105110007900010f10300d500324820004034002c42c200030072480e8020142000101031b1407800c1c0600609100040e405196a948444c15840003d4008546201705004901e00038629041c011080003040c0b0802002a800c80d000c100420642161208481d80a0354280c03190012441d24000c1244c0e00d00d4201c1c3e40100080060205ca401c48000f50014005130000c1c00c0080340c0350f0f40758a1120200e480180a0a506655a885000c00c002d07460040148803000da051040c00140b07152502642032240c80541115201c2028101c1c809079500c0c0e2090080070f400041e600700c0300f4400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 871770089 1250 871768839 871768853
    0x90f04030306050328050a15020d18110d0c090c09090513201809100f021305041d01020f030906061926060c13050f15030703060e04 58
    0x648095002900300350000ca01d904002900c480b07041c0c901c440414a552002da2440034094411300221040c0c020b0002e1207011130707010303c100c503440d4202c1500141e9420300c40340030030125100c01001d2f2107100b05203d106000306003050b41e210140030b0b05641407c1c0d01a882d1510900c0c481e00d5401000d034040c5010300e45003005601c041b0440c19546c0d0641c04012a441c0d02c0c101c4030038002e102000900c052449039004900d50380c036290091342c0060181103e10140580002c0302051481220104800e500c0b01c0c0c3c4a07d80486140108801c08a891000314500003203e61005401162070041d80d003d152030390844030010508004081080720200021915816094811030141e8000d0f92141c5c0d0740c3c8100d4001c40d46d6442d1a440c1402c1c2d140e10f00c0100760510745032207200202123810060190202110301b800c00c41410b828488684a15840c3c0c1190755582060525031080903219048140542c1c852852664076856080c0306191148411110300c0c5c682da1002e6044014054941110803281072005c140803c200380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 871771339 1250 871770089 871770091
    0x306020c0a0308150f13180f050c1e040b0105070501020403080714010209090412020f0a03020d09140f121908190c2001090522050112050a03030218090f 67
    0x200381d44000c4030380c403800b134041c4c12520b600108070b5101083d144004140e1414444110f0400200711003c100c06076031146801802090600642c0c0c00d112400018003041014031454158950407030308030805091000500356080b0513590300341e000e13030f0341c1c1c0c114040310368011420740d008940d01c00e00955940f03891349801c40550b04082c6003110203048003030b008480750304180280c4002d034101038080102075485032500318100d400d16a1010541c002c1c031018a108400500100309094040c4c0c00400c1c1c003805030a00200307020480d9001215500b41000642600e81d0790703800d04c0240003012181503401d04c044510b810305280b91100c25000c090060903020b810051814050403015081c44810704100c5c44400c01502d2004480800806059804d80203441420140203a0b032602841850b211401a40b03880c0840d0190400c44910405400c00020710013070f8560b94040c0380d015140400303081d0b0107400c0c2d650720070750b0720010201d00506042d004038044842c41198008032581100041c030344605400d00014006201d48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 871772589 1250 871771339 871771343
    0x332030108161d0a0506060d020a020d0807020a0b040f0302010e0303191103010305060402150f0c16060e1809010f09080c010b011407081b01050915010501020c21070306020c0a 77
    0x101c0c020002031507414090300f20103a443c00d44544070700c40d0740c1c0303503200001400001c000071b0f80044140014550400705201400d2540143c2d00201242012483c0240510400a04150031548801c01c5480018000301c14207420650052070000003030010300e0305030702411080c40b0628451201000300000764100341d0000c2c0703102130105000c020301103c25201c013400303200901008e4199480307030010038014109002e1306112020b03004941410a030744885841c105910a82940c0c813141d00603502426040c809c038403000c0040800e401e14013400c098100220f0100c0e00d40c0f2212041540855000840c13094007900000c0c030016005108100c559032034a0a1131564218250030445980390900580c1c2035400b85001c0b00781103010180903410702e4400d5603001d007a9444292071605a070356078444000d41c00024010136001d8020380c8040c00e5201d05801c4c00001c24901607211504551003e00000d6641d150030496500781d04e000c100d65007241032916891071800700c070369000400841c80003d03405407011012443d140700c58 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 871773839 1250 871772589 871772623
    0xc09020c1203091e3a0e0f06041203031b23090a06050c0d0201110301050d0c0f14091003080d020313020d050d033209071a071401090332030108 63
    0x1440c3d41140c001c800c1310528610a917a100020a41c52030043c19000c003140001801c018501ca040d00c081140c680203507001445130808102e60604154050107005540b000002003000901a0030300000c0514130085030480038103c81544420b2154840001c44580c0400905000c01969944500401d01d0388904815000c502a0010b0101660310602403625040001c100c07103400c40e400d1030b0130013440b59030b19001154040c5821100295100c0340740003103401404030311345a0321500c2014086c040300e0f0900030038041e0042d078205002c0c0000359010007901d0107200c00c0e44006072a03075503000d0b95445400c40140083d41c045000c3c85c00390200103001841840002540e40c0c2401613050040c5404420260b10135400041d02d101ca102c041d099928050351688440c02204554000d60303608200e860040259080503014200000c40400380641003030045002c6031288003c0100004503140100310f5480130f08600e0300841078000d400c5915024290345000e00c001c1300c0d1601c0e47c0b560b540b5003680c0d41d000390100320303440342c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 871775089 1250 871773839 871773883
    0x30b0f061905011110050108030a09050102150403030b0406031a0a06090905030712051603090503150118050c092e17040b0603160608040c09020c1203091e 68
    0x3824480c14000c900829440307141812820040151035500e00702440c040e60340b0440840300740c00d442ca8080e441c001d02400e009166101180c40f402001c02d2541d811550565000074011340c802c545003019190700030740500d00014480201c20004001d012682d00c0902000d901c110036805644024156601034401080d0802c0794682d280280400d0b6440108044c1080d000ae0101300b000c90b1002900c2c120442291a11318644101044d294010f80344061042d000105030360410310050501f005a5105042c049003020019031410f601d079442c0304800c040103010140c03a8000b00780106401c80a8503c0d40100800c444622a40c0c503040d0164440d049c048072810141d1000022209401240c0381881e84d41d00301c03a0f119156665484011540038007030841c1d074040c803400708200c2031424001ea0300e002904103a0364184450a19040845045c0182d820a540b6030b4810000750640c41800248a18000d800001594507603586d40d03034860914100d0903904c001148042a09034040d640421041d054919400c003460708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 871776339 1250 871775089 871775101
    0x30306130506030d0c08071a040c0905010b0304030c05010e071701060e070522120305070605071818090602070c05030f010506030c090919030806100e0f1005040f030b0f 74
    0x1501c00a55105805030040c42d0040c131803e200314649104140109035252804900390707519000400755103c0c0d041000340640c248410007000d001c0e890000c000d2654140415410304002980c0d501c03000e4402428040c0500c08501088000e41000c2e003160080350540c2c2da0300b96110030202c6c4500160304585001d51074a00082400c1881c100c50078000d44603652128184a460130001c0b40902d031829a09a401900c10b400160310381c076040d0003008561299443c1c68651260b40341c0300c2c0c00e42d00060403503014070609011400030150141c0021f011640c20340407165140080700c1d0309100400305880041c2c40c1e00e00000c0c10409004060a10104445c0181c0c1101c610351a107240b501c2c2280c1c0c05880f0325a25070040440c441d40d0b0f1802103503080d007200301d81d81035403811902d600c0b405600701d44200044020070303000780803c42180340c9412401e01c01c0b00d240c10506a485002000104078400302c1c583c40f0301c101c1001140c3c0e50794600c11020303500681200c41c0709500340c54603170074140c00b407010031200c02204034244800616 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 871777589 1250 871776339 871776341
    0x1f1e05180102070f060908041203020a0209090a03021011090312130b070804140f04140406050106051c05070c0f080c0c01050412030c021903032d050415030207060504030203030613 79
    0x80312900704201007903a04e4950740c0c1d50040e101d044802e1f142c2c3c020078000410b01b0101403144241c218440d400500c010750061050004007803008190100c00d802022240c000310b034001c03541505000c0b920400241150618200350242c1c0624059542c242c4200ca0181e41ca101452004080c200100c503410100540d855132410003511032000003e006000900c010400d22503400c10742c06116030020200080381b0784880c089011104010301e0716040c0040d80050200f8020140b06075030242c01d40c2c1c58030728030f80f0824681030070702000d40c10600310b92a9529000902c91078401c862001a080c1d10010900c0080454100200650444001a941c1d80104964402d1175809007003110111201da40440508200c15181900c170f107250100700781d82040c10181c0018040c80d00700303440070241d41710341c80e01204056207100c00e810581e55558142d0900d1901800a85941c0c1c122040e00d0485a0400408020381a036010440181c000c100000f4141405c0034280801c25030040051489100180e41c5c402e1400e0703108141710 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 871778839 1250 871777589 871777597
    0x302180702031804060b030a020d0f05090d121103011511010225030c02060c0f010e0c0f0907090302090103060606120b0108131a280e1f1e05180102 65
    0x300c00360384100a20310b2590607041e805480480002e0000810a07981e4020418543c070448640c2e011542c000340c0c148202d105403044c82800040328000b00a0742c03500c030800542d00c0480b03414013009d000210703c50200801d1242c021b50002c03a441842c0c0ca442c0e503500c440400d82a42c42c0800c01010a00ca0800500130760014030039612040400c0010700c0c00c0450444001d404000c0b01741040c0d04125a00e0008400b5845040c01400108400030003044079086555009003103841c2c04603807800c0360300845121011130ba42d00c0303403c1d20349071422100180c03a0f465140003520707000529400250003071900303030001040c44090350012044507407585a0030101d0f403038681c3c481c003182c800e8600300303011460800200d86a01480384040c40064411800c8a0b000e1240c001612076400003200c22050480c400701da2184031209810f260740851803800350074003036200500b01450701c4541e6410001d0791002d40c50b40c00e400c060342540081c99224051041c060342003855144090151030212194001c00074861560119101c05200711 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 871780089 1250 871778839 871778851
    0x108010b060702060a110106081b0103060b0702042307081611070605030709031b05100c0f0b06130f0b0102060601020f03040b0703030b0a0801020a032d1e06030507030218 75
    0x1649401d00b5982001040d811a10b505c0c002c126541480f404403120074800e2078081c0114200401c4858603040d9200000c45541d11102d040504182c010440e1440c000300741d819859040b600401c002c060300c040900c482d080b200303800000e41c1c0c0341814090000d4014081a0084612100752428000091000c2d070701450248640001c45d8480b403010841248600301a60b0000307164a002c884030b07580c03a01c50f080120203050a28242d424040410030880c0340100350740c0003181031410505204210740d19205225903448001406801c10130002541d56503c802e101c09110009403030401010111650540042183c200014058400d0301c001c280d4560002800c1da06002400005610385401c10324040c485420106045082c1600d030b10300c646140d80c500d804c080152402c00001602c980a543c002000c0d10070400c00c80c5441d00008584e40c00c50603248007500064140310a0124489011441204c900c1c01000c040a071151320303149000c402c010300802d0240482c0d0007101c2d92042e01399040e00031080c0b03450a0b644 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 871781339 1250 871780089 871780099
    0x25030e191d07120b1c060501080106060f050a0513121101020f190609140604140c060712031a0307080102040501020c040216171c0603140601030203030405060c19060b0102060108010b 80
    0x700c50b40d00c0a0540224040b15006001703201003590824aa11040001e00012909a40c0345e100602c00c0c14800d00c204070007407a00d4a0100b4606c0600c1c8005071141c4160b621000801c040003540001d041d000303c10100041c408030a0485000c9007504000001c00c0c0701c12049801800351600701c905100c0c001883c2e400d40303070b1059200580f036941079507044d0003040341c1e82e8215118901044030038024001409824416030041022007a4803041074003160030300001e0182c0c107125900074404900850036510004002c0c00c564140003a0711100c02070a06400c3c403880e261698948100725010032920010b401a00480e0b200780c08442c03040016504000a9000784034515500c000900708120208a01d82c1c6401552454009070f14503191404441c14010040e413a200000c20351169003c100b000924808543c4107a440300203481a0350455000130348034841e038400c15200e210302142501c02c2c01818070204110001d900309103650400c2501e40000540440074225002d40103d100004249106005441c650100241 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 871782589 1250 871781339 871781357
    0x120408010c0924030e061005100c0b1621020901090e0108120f19030606090504093809060403171005010c03120515041125030e191d07 59
    0x8507003481203804583e4101922400c0e54510034509204042c0560340c030000f11001d032820901031101e8044174180300d008110040341d03150040f480c0b20b00c086030003140b0b0901c11001c0c592001022203002090240008024203040c80c0c0d440800025402003001802c03e8941c0c00000e90f0f00c0c644054128000d2103400f0045d04503e4000c000000780038003c0c54045606800c0030b09001111043c0e1700359001f02112080840d64a40c400d006542c0c0205401c002410100c0c0c0901000d429640c41081c08001c02c0180000c44241d01d51a980c28907800748007030a44403030500c3c054003a14011003031950715803043d1000c0c1c02203100d800498411005642c42d45100e0080c1100c0700e18018913003001120076041e05402034041104105607035601c044580a0741d40145070f040402071840c1c041c0350804c000c5903134104e04021850000c1180d042c002d92140149154007a00b5810619420500e04040d160010030b64511a805404d80c1071400a26414586820a03545014ac0700807a0242c1c15052043d140401d581f4070001c592206 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 871783839 1250 871782589 871782629
    0x6081917030a0204030c0e0402212d010c1e020c030d081b040311030d0809070b03040510051006020d08271e0109110a14060714120408010c09 62
    0xa0011600b080072403600520300350752038a41450a1b00c680d00300781018520301040c442542352030020f0b200c146c0b1034074016140c20306030403000075034271558100340001c0b000c07802c1040c80c100414402da10488040d001e00a1008031010f2070018000044103250031414415a41035142e0b8038030000f4541c035010070140003809180741128003940c42d41c070010440442c03180030b201022640e80031600984020340c82110082c1d00041020201403d125440c0800d80400040c2070401c03800c10750008402c01100c01c1d00d55850703640e40741d500f0881e0030903a02012500141d030901007030091b40603459002404a03032050342652294042c1c1e0208a0302e4107400c0c3e848019804910300c00c03190000c00559560610b60382c0b58200ca0b078618000c3c5050002c4480c00020b014103942d104903407002d00c4000c055218240d901201d00f500401d04140001c000a13011010b641e00034480841c6c03480804c292110202d80071404901103a450183ca000900903940c8603000d844069424030405001c2c80340580c0c02c00065881c1c011032146854694 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 871785089 1250 871783839 871783883
    0x4062003040620070e060f04050c0313030c02100806011202031b1c06090b040b09011d190912030f022a240603070609081b01090e0901060819 62
    0xf000240380c801500101c42c010900c0100038400c01408081e121002c0c80c50302c03070100501005188034903030107a801e0008100500100e0b000b100d40c4401040e121484051040c00c0071580391079110b8009406c80f50100c094002c49400c1400280f040340c0999644d40c2880100c0d8001c0168001030700c00306032000d0350700c0450011902c000003625980030001046038128030b103802c0400c1900c40030360180d88056624024482039040c240200c410903030060701c0f146015450302c5000300c6030051100c0406a071482810104039909182c008020540c824101705000754400c82c106440100155413041c000b003440e1516040303120100c0e000b80c8281d04500c0e4584a001c41128140783d80204183c2d488922034080e5080901503c010240405592464440203809030300d8548140340c9011426007000342480a40320041051200000301e9540c100d55045407845041101030060303960380382ea6040750844102d602c0070001c0e40081588610106c90110741229084540c26030311080307207080c80c0805841d004002e00340c00c1c55075640f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 871786339 1250 871785089 871785107
    0x8150402100519110c011d040f020906041d130203060f07180e041106030121060b0603010602060a060e09030706200f07050f011820060f040620030406 66
    0x50b402d10600e04040b250115540f4461050303250007140501c0000d40c001001048030881a40e800c0c01c0000d0341c0031144a060b41544140d400c0c5074031468945040208044a58041e5034400318050002610342c0c0d2560b944072025030310b100380d0b504030a0078080042c40040b2401006202f03550003078080c00b00e94603030045501908030010844070500c00001103080b410324011602c1c20007803030002c101040c242807528001c28124103484500d44528000c0c801407040ca80302c090090300345003503440d09003003804541c5000c0c400340034a910002d500010100c000a0300036004680d40b032050300b048a041008944440524030001c0080d91180c005900a01075100081c80d03683c000e1203540500480000e01c01200070080420303502c014115a01e0385d80200d0b1080800600b042032615402856000b40071010400802c10325070080706401400303052031000d55810081c0050b442c42d0781c0b0007015001a0381c0b828039550180302c41d0701c10300c03410b00020301141e080c5800c054500c0c0c60010004400020b0b40c505840c2c80c400300c9a01803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 871787589 1250 871786339 871786369
    0xe0708010e072f15060607330606031a150d020904020c190b011502030906090f1005180a050d02102d120b01090302010809100203010e1008150402 64
    0xa25122001107005200c0c5020340185030400034850541c000f03403080441c260185c5454098001031194a00080c2c03034242052000714042e4100d40c1c06501c040035008d1503070540d030490852502d408408140700754503800ca01036010710a900b428083d0306000602c80168070480c8422851002406a0048500075400411480c100180054100040d9428460911501480501502141c0c60030102006281d9144a005003009160b42504001010020b5160b00c20030341c440344600c1c400600280340c0d0380c4244002c4400034000d40154034101200a02612980c09003c070300518155800141e0700510709103101c2c0c400d545003d45601d00a80082c0d0a200100f282c0300c200300284080240040603248003401c050094460700c1000d03000711078200b000540404111101401c035241821401f80d0780340d80110429084950a1806403074959481506a0522545030010380280d800000001610b010210310796016040d0300d990000e070683c0d103250055aa5044a40e06424440000001009483c00c4130b21000182 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 871788839 1250 871787589 871787627
    0x2060918010b09030c010f09031b08030c0703060b040c0c0b09120a1d1002030a080406021603020309120a021f170f180c01200106120b010e0708010e07 66
    0x100d4100c14100c0380140982207031009000108201c222403800f0008055982000e0803e4500c0d000507500c002d2605406000190100700c49075035106400008600701c00c0209020130603079846041480da4142c5a03a6980701c140c554504010104d40d0500e40ba00c50400044030585503014241a10341c3d4105140d10010900c450074000c0c1c08001e043c0410110051a401510b5590020225400c9512500c0304046062050040340d0001a100c0e1054001084a222040c0c2d800d082c9025a214604140a84512120394003040c010034004400c040d0000094802468207d070101d10290392582c90310341e2a03848400180d48000c41c00c04100501e40d04805c80c1d00b1502c4c980c60820340c0c00264110074060103a05075010460026400104200030981414800ca801c0325000a071400100540000313001d144c3c940c40ca510941d4015002c0880400254001c400034294450780c50048002400c0900d00705100f4030a0300075820144000520341d52107861191b041e0f038402106e480c0c15484400742203c903090309041e00300c412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 871790089 1250 871788839 871788859
    0x90b2d030f16120606240306080a0c091a0a29250606261902010f18050916080a0524180a05011a1c09020303070b1e0603150103020609 59
    0x2400d0b010910b103106c3c03000c4648110780b00e55601c400504aa509600039503032900840840d83c000b034504440d59040300d001c0c20003c1031030a400c1520349a010446035040d9401a14140c00203920240049071942c81d00441444022005008520200ea413003a13070f480c101003a042800e2007004a004030720b01000280161400078000e515880161400e242c0c0184d61504144034071040e84c03507020100405240c140120b4020b50064400340d0010b80414104100102480008036905e0074491204040400030700e0010003113449800c0440138115858081007050001aa80f040064000c2d03a003401406e00a001c200380e040340039030000780b140307556004c1d195911b98802400c200580301c0c5801c003242d03640106540798000485524214042c9000e0100001a9810140500c14920103150300410380e17141951414000c603490a0303d00c0024190300c82c170840140b503510182c06114414413585421101e601e11482a003405031118010195500d040c121001c034040c090400501c01810030002512001d83c001e008600c0c0e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 871791339 1250 871790089 871790099
    0xf0507060c0309021c030f03020c0f010908121b03010902030a02120a2f04030b180d02070618030f03030b01031b020610051207090b2d030f16120606 65
    0x1e48803554a000c000944944154040d8a0245541c010302000d80d08031003940300d2070350b901804205c0c08182203811315901042c480015030f000d008000101c54820020004205a450003040e80c0e00818404c40c00800100c00240d081d11182141502881c00c00c0c030204d056030f00e07040030307800a0b610040c40c90020940900401c1c400e410540c103418001c800a40e8081840e00e0510102802007034984003519804a01440c148610079070201290240d0340c000482003559a11041140d016440321954007006226418088205680c0400d84e501950780694408205000740c012004148015000282c155407802c288900040d020f64490b95544006041c00704070b445c1c496406410f907074034800800340513800c88404c000c1c032074610122400c0508011a06203000700d0100240e1036950050740203c01600d82da4017802038443d070b41c2078240749200c103c0d0458100c905025505240340b02c0c01d42d4806501a07c1440604640c0075408604071009407800300f02009698548000c4c103184403110750b02500c1c030554075400491 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 871792589 1250 871791339 871791341
    0xd080a1505091e070302090f0f0f090705121005060a110a020307060906030b03010219050309071e06080906090c0409020612150a060504030c0e04110a0f14090105100f050706 76
    0x110a0705900f01c04026443c0403807040c240303808001d0000003090300c1000340c0b5003d50364038004040c1c1a0800d940d05d00c900060180400c07c41d90071420260760200f00740041000840e400720040401e170f03803008101c54198641c91815820782d51140200341d8010014072a6000b480d11460301000c05070071080403610304400d1500440e0402e04260000740009402400c01d0058540500500c40c2c8248158000c5180c81442e10365494140c52080c00f110820500002060361100c2c01c100140c0603008880030700480712000740e001601c5038114810000805c0380580003070031000f00401c501d4454238228001e020b10449000801c0018a42c004080b03034400c4040c003001100c8211140c0071031140b540c01c1c50030081900c80e40b0400039840da032503001108110040005200050500d000b54044582d06d0b80e108034152524a001d480000c4440203058014090b02c00009024580d0b018003011208205c182040004000b024401e00a600f40901500302030182c18071284248503030a50b56400f043c0703191050804043c2e0b0341d408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 871793839 1250 871792589 871792591
    0x190e0703200d03050a030e070e0105010c150c020c0103050c071106030703020c0109050a031e02120310031e0b070309050c09040302150901093011011d06180d080a150509 74
    0x50001900170500307280c0e15801d81328550845407208010660546022200c20904105004490400144000080c1000201c14240100c80b90101082c070083c0c106840082d900c43c80101c2890010341080c02080c00c2406a00446040ca500400d000d602d5404210501c481c1d5400a400340c806c0503403c0000181c20002032103080741e0b0718818405402240c0050030300500c40174041803a60311110743c1c0303091703d0560ba40000707003c60010038051005440e40c0e030701d840003840b011040d8005018200a2040320602c1d41081c010b0407007251280d1805811621000d008404440c280c5200900e80e50014a140306030f803400051a0b0b910078820310480320818940072102501c2d050695508207181c0d16000f0501c200303d10402581c1100f9401c40740c1501e40410fa83c1007881c4880b42284c3c0a0511140d4038a040c0e2501e004e4021031181c481c03510120034a5080380303851a5a4000440e6402c17568010545442c40034040410300c09808003040da274828981d107821034a000184035001314040401482500060a900c50300149 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 871795089 1250 871793839 871793843
    0x102100c08011d060d0f02011407080705120c0304030807020d020d051f0b060304030c0f083c0304150f06170d09210201020f060a05190e0703200d 64
    0xa055241421460300c103410f440714040403664120400c40b44ea110020020080c90b084000700c1102a03141c00180c1c0c0d10348043c041ca40540b400081e114007801801401040075520030001c8604480004014405a002d81c030800c10180d0010001080402d2040d4041d0001500080401d00c011000fa40002c115148030030044545070003030800148000303102c50609044e6880810300707003c4d0a045000103103107031100810081c107000503510804103000103004d1601c2c1d00c1e0ba0029516a4030920014a2071440c800030142c2103c0051020b201d43c1580041c90b40500442001184a821a1074580d120300100c001c200d401c0040342d9a485071082d0842242c003441d0024194403504941c1a0b860301440c40c24024081044401d004a00404001c40c40e203803c82d810084100724003a42a130002d074030040b410410030002c8080f69201d60310512080c61107540c0700e140184c0c0c00154003001d0160303040c45030041d9444820410780d9034209440401c00304956030419000b0700481d84021540015480000c2c4c107070120043c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 871796339 1250 871795089 871795097
    0x180e010501120c06050307080609091f020903010c0507050a230d0512151e01020307210801150203040b090402040308070f02040515131d24150102100b0102100c 70
    0x20a01c260403e448010303107120301c0c03d1482c5240010001d012880058507050046458000252500000f0721048270030706000c0b030202162281240403070b0007a4014804140c4a0b520300100b1001e19409401100d6240307600a01500014045417100c40e524190300440404001000c1440100c151082c44115006a1181c0b5460303280c402c3c0c101c420003003800081440c429030a0344100303500e00744e031440292400300500b5800d000683c01c030540102c4c00c4d405a40380007803224021001203545042c40011182d020dd01c2a42c648085a0b6200c03203118242001c0c0c1c2460740581c00400042c000b0410884c0140618130011b44007524096490361845015130100c001a12041c1c0c250403900114a0706024054000d0004900c000c0b501c03000c41c0c00074004a40b00d0f0000032000e555030300c5040540385070b034036410720300b0760301303a040d03e8000f440340313107003010b40724002600710b032680031040006646440001081c0c150500c10390041c00400200c0590b00014a1001d03000c9040d03200d11201540081801c0c0281c10046244e03540e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 871797589 1250 871796339 871796369
    0x10050a0507030b0d0210050904060321030902060a0c1109150102070f050a050f040e01090302060406230718030b090f07080109050606011202070605042004090b01180e010501 76
    0x1014104036040600103908150912071810060390312481c9030783c09260102c032005940d5800210950300c074420100c1c1c213500141030100000c00e000082c50305141000000e07003401c0c8550040d200c110f084070400702000f540030206000d41c00e2104d104039011064603114404510704100c1140003c0c00d4074100722000750f11110b0311000345281d03507410f00054006221100c07030b0700c00c41810f1200041681038180034190040058400c6401c1b1542c940c0c02400e41190080002c11002825050003900c030f400403102952114101000080b0880c0a01c0c84049540d040141440700d0b5100e40c00115080d0000c1c1000c5c88a050514070084081070300c40c2051405200030000030b10714205904605030801c1000d9000034156450488103901040000c41c0355a800502441c00c80302030380c003151000c2e000b40140314002e0141c500d4030081000f04025843c91000800302c280b0b4040a4501c1c0e50100400d42e098900004c00e042e18a03c0100404005100c402c4210b6031928000708264004c0b0b84d6880c03c42e00300741d1152902c401c640f2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 871798839 1250 871797589 871797601
    0x10b030316110f010906300b0a0b040e0f07053a02070b0f040212010e1b0d120302030907051e0a1a22090207060e16140402070201020c031005 62
    0x5502000b01405a52090003020300c940003810154040c07140078180a0600420004d00f1680d9000c1d1525a44894546681d1900c081882c80109000d01f03426000380c10521010881d82902c0d0151000c48840e08140100b59880c60303c020b10300708001e810481800407d12242542003d50300044a81c0b0311000c0b990b445016000d20031040c081845040090344502c100480004602491b06065100c070241107040c225441d40d1000c6210040c81c0001c52540c0d503c0c0c103418545446020030141c0b03c68002c840388102800d80345d010002d210381800070080990b600f286c0462009400398000d0b42cdd10000b4030341a40e2009954802007400b030010906100e42c1c1d441d41c02c00c0c0a84602e40003221101800c01c80c4214003103401445840203452180c200f501300d200650682c045010382c40c05a48102403c0c5a180c2903407540001e260402c0a080010600d0b42c16004415800f0383d0004a070750400125040c10103080d241d9071042e000e000c001e620124060381140200d81860480c4d0711300700032a0921101052000900346818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 871800089 1250 871798839 871798853
    0x40609020f040207020a120f120201020a0206060a24030b1e090711060f091018061d0a140708060108100b0405060d02040c120c0f030509070303051902010b030316 71
    0x414440d9114601c140070007000b681ba450100401e03141d1210380300003916540c0c20146020710000800a01e03034892a52580400b0b0380c190003031b164451041d022a03039036480354001c003e0701103010301070340740111012580041f40c4a04d810030f001c1103250508000820b0f1400802140200d5181a05038001c90081280c0302018140740f44140d520850034a05400e03d880b0b450252512580e0143c07210100d030090b880440c0b000d15083c0941e4580f100018003c03c84d00d1000140b0032841c0f042c00d001034407000d03d0f1007558400103001074040240081c10038040d1100c3c10080d51440c0401c12441081c40e04e52149902c003141d01c070010060103001e41480802050002e001081c064160b40c00941103c0c043e504142c1880083d480f00c424240340c0640c1201e0109243e035004804032034a06c07880c1c0f1264499810480490142604800d8400c040c1d6a5568140b05982e580810f8603600e4046110080024030100311480107140c2d004541c081c1186940300105111107901c00180c9960413003460307581d072151041500700400c500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 871801339 1250 871800089 871800109
    0x708062e080a060b1c020c01060e060f1002120705010f230907050d0206070302151f060e06040306020f120424092f03070b030103110919111204060902 66
    0x40c22405102c0603003400f540310f001c3c1c05403145d00d402640780581a220b4040c00c40e0160f401006000303001700106503507150002c0300750200351038907400b0314100b1081c14081e041803605400201c0c0260000c2003910750303450321190310740d01c0001d0680380c5d03569543c0e669910400a00032803104002100c810440c94541c12204110305501400191039a880f00c0c904025030b89a01145945164040b90290b80f0380030541000d0b4104001c0d002014185000c010800c000900012011508455910f180c0702071a6110601078441d40e881c1802194410006d21040000800f150020039051041820080c1015905030900c510703940c06a030101d0388600c0b03141a1004112100002082d4038894071f9050000410544400c2c00c600006010b40140d4000408600c142a006681100d8807c1000c0e003111002950303038407001c81a400c01c2c0003c0341c415103005801c400c646801c2c0e01550041c8481c030480090610800d2044000344030100b01c01104030020700c0a40e0314021060340c4a4400d40c06000089404403040c4100502102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 871802589 1250 871801339 871801351
    0xf0b060102121603050307092402010c0e1e150a0f17041203090c05030714090604060608070503280e0f0732040203071d180708062e08 59
    0x280843c001c0d0300c0d0541203404440b81c06050190392900c4080d400c40d9442080d8100070101d161001c13010410590302c5110b0311144407540c1c000c012400d031280c001c903564003402840d980d01c00c0200e01c061203003424502c00000d940100910b203101c00e00a101c011030f000d8026541c403d0100d007401c4a01c42100d90002e190100c1030a0301e0720440003a01d4556100d441d1000341821780c0b410585d0342c54202d410840740501c120054500241284d130020350360044109a0007903804514042c288820204482d42094050301003a03c800381c58054140c0c0d00c000301250035401c01841e401030840d0110050f80489860117001280d107048200109500130203480341464192140d50460f00f41d8085181000001d0521200261551202c0b20566810781601c000708540c1104c6550325621a100006010105800002c0042010f886140e2140320400340c0003000313004240c040d510b0401e20700c060002100c403807180000701e0340100e004211800d02030f2503075541503040c01c1e0703a0121190b26800c0d04070444250b400c0001240e20075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 871803839 1250 871802589 871802623
    0x360b0405010e0f0a1e05040201030914070f090c0804031101022b15050a180b03150919080a0f17180c06030c071b031b05041a090708070207030f0b060102 67
    0x82d036994001c1c1d005c00c10702d442a12880c3d880002c1400c580c8207030800502c05400844682a049140365074036211002d0b0f02c110050001a400005080b0725140640851540980c03039100b510f5640740c505440103009007041150303a5600300241d540220380c8010f42e0354000c401078006004400e00100d06000c440160718080001e0001e40c10411442e668a20018107445280300c8403502410101d441c0d00180507a040895414042c00c405095090701c804401c510900c01d500442c0c21002c6003c0150b0080103003104007519144081281e0006c1d1401181460401e414a20348480365840d4042c42c0e50a5480581e81120f113100310040d0306240d81010420501a41c204440843c514101900414690b108454005011500c403805400000c1c14075104c513801503800040c2d012144140c51f010f64002e81050290034802d91401808122000b141c10240124200c080c2541d00d182d260b000c0c0a66070068014102000c51240000200000d0040307082e2140e018491000b1043c00d081c10000a801d115180180a01039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 871805089 1250 871803839 871803851
    0x3041104090506180709050a092609060f371106060405040606120606050109061704110f0d031722060c03091a060109360b0405010e0f0a 60
    0x7203207001c1030b4a40c0081c541040b00c13914010103403225040a034550311131440075280c101046656026a0003002a4512404251440d451020200e0514400c070007680c3c80036540a00c4004624207100e402010260a0070007101c4c1003450340750f4400045051210b0f0301c22010030515010345100680243c44c880d0740c2407401e0054047c04c01503005d40d03448000608bd28842c03519100400c080c0034150f401000500313031408a481c8a130205007400c4c80a820184206800211414000036a240c40303214401d0350107600d0701d03c4e40c143d52115203400071000131a4603115400500f08034011200e60f54038690980c1640300b0388401900710700381e2808034480c030002400b0122201c21891401088800c40d80d0341000f041e0300c9080010411101c0400b00c0c014450440002c0c44e50400c081100e5404091a1900744101001d903100b801d800c2d01c8442c1e4540042c0201324640641441111748952010312041440d9202e0850034001030000c1a00f0019042e100c083e406100d00139101414130030700c00300300c00f80309904c00c070710401c02c2c866 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 871806339 1250 871805089 871805093
    0xa09081c050a0b1e040209040603030f080901020316030f06270e0606090408071703070c0b1b18010e0a03080a021905070905060f0301050c03180721080714030304110409 74
    0x90036001c82034403104c100c02c50398000244d549507410344a403c1c2e005001007203480e8403842c0181045075448a040003042d803d100040550308d05000301ea10a013000c6140b60501c20390070301d068000d08414104a80c4150f09c5140c0440c481100212101c0b0006513000c141c0311580100c6240742c01c44e10301c04040300c2c0d41c0c0c2100040182940352402019041984030403456130b6800c041c1403035406020400140d0714050400014042d48551120700004158001c0100800d03c0d200c00c1e410300c8e20181405120141060103105040403102c1490102d02031542c1810040c24010200c2c1c002032100d020358000300d400c11b10220300307142c81580c100072200b0480180807801424203043e0716a00c0d80d5005600c82d2200054540c000140b5903103c20a0000044e2070190082c40301e4204940d44105682040383c032aa00210340b00d41070303041c40f0000070b02c1d80c0c221040001040b4400303420755000ba0720741080050544a111040000c400000c0b00d4100d05e1425001e9a0055034582c00c0c00e24009a40740030b40d00303150b48160306007910100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 871807589 1250 871806339 871806349
    0x3060509040b07050313060c0e0a050904050a02040c090e01260610090207020a03080c06091b2404050d0311160b120a0b0d0309141906080a09081c050a0b 67
    0x140126070f0303040a5840b91796007a076520305040c1c8480000d1045062903c490741d003e4000350369462990003100c0080c2d07001d449900340103101c40c00b101c0c040c0c510f6000007000070140c00c1903448414a50518580002c09030b0f1100140e146403102030f40130b086505100c6900240341d003c024a00d001c103402c0e007000340019051400c0c4c10302c1e190b11940a0b01c01c0c110341c0081e47e901191360305244500152750040100c2d1b1941c8146a810741c40c0c00080b51000c032640240300030322040030301c0351520680e0100c0080c6040d1044013007280c412003020030784460104180040101107229900c100a50040a00c01d50741e50500c60410300780385040480020198142800b0004180600c0d10b8600c1980c0b001d1087c180e404202c0c0d918103000c44040d140f0001415045044081c00506150303101c18048295100d41740c43d00e4442c01c070302c01401040803445100780c0100d814510180325551143c8856a0040b0881401251070700e4a61280340f41a40910410180d601c00311021a00310b5030a401015803002d0254001c002d6443d170400490 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 871808839 1250 871807589 871807591
    0x10506040b0903010b100507260706150b03101502120403021c1502041d04020315090705030d0504080118121b06020301080f46060e01060603060509040b 67
    0x40312a0000c1422101503c00b5031110303007160030007000c4035400c01090b140900545d110603416642c0c2e1a0010b04102c16510030408902e400c04170071443e500e40210340c1c0340c80d03000f071140390100440030750103510000e40521a80b014600440c40c549440c0e41d59490492803051201c0c044030808155004403008200340c4921600782d80850350103940002400c0c002c003803c1240c01c9500c1e0030050032800320301282380e0441402c2e40a00203481d0035031038040200b26640444003090b6801c98009603d540300b2035003c5545c1c2d2030381d04641d402c120842c044030441034503400043d04200c4040e03030103000070b00e002c2030400c2a024240107003007401000c00e00c5002d5040c0c0a84421300d03010340780c0303803440248101c90446050b1f80c400c210303040d100f2a400c114110740740d503160b0544603101d05090740001064420700380c100014002e81003000c0f00361b2014041c540e0716070840c55298040c84200380c040304e508803c1031086030007140890085414400082000007481424414040e04a410700c1d00002d009509400c20400000c41c0100e2072 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 871810089 1250 871808839 871808849
    0x20c09040b0702010209030d0306050a21110d0510020d0614010f140f0c0f012406030504060b030a0b070810060801050603040813030b0f06040c050d0b0102210d1401050604 75
    0x900c01d507540380030050340a41703c0c8141d41034040c400d030030381c003400203505600400030b43e40300315030410341c03d5641c00c0d11008100a4080c0410201d40c40001c48000806000020000720b9001d0001080300040e40c0780c0354100400561060101900001e203505c8401191040c0c50141405544e50003410390302d2400240000381c241c04210074400c0203100004800c40500540b41100851102603a1312440d0340709130742d2101e604d501a01b0701d46d070820404141140140c3c5640440d1501c2040b4214190725041d02107001d42405802a0380850791481c00701c007940c81c240320742c2807414001c0000c1c25030f034101a00014009640100560720100590f40c06200590f4802c148504440c001c442003034aa807282d00b01200c00748114109410321030341d41c5100104010800010510401041c071403410b0030b6072031401748026980052002400203808001ca02100080c99000755001903041c41200c580b0119a05803180164101144070040140490034480441082c0107044031905203030b1400c030255142c0b4011665a0045000e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 871811339 1250 871810089 871810103
    0x12040b0909070e0d0302100e0c030d5a050a0c0c080304080601090c02070f15031e14060f090601080405030d11030601020c0409050303130c03080414010f020c0904 71
    0x41142d880c0720b0303921100290001040e58000c4d50140c60701a69560048075032010403810040782c4120442c0100715400e151074064058604c80542807411114001c8080c03400b14145010415410408800800f0445081d80c416a20280342000201090420708000c000708a00304030403001c200700c5900006039071003960503046c0090743c03141368a05480c0000b01e50700004050700c800704000030740f0480001c2890417a003420208100903034000f0f10482e103d280318040d204c42c1580d00102003000c1203030708944a520f01614500001c680b00e1301c0421000d11442420190211900d459282c0342c02108500903035005802107500030120042c600106080340c200500c05d5040c001a500018140305c018011039803800c4840c1c2c0c04024440e901d0504407010b4100ba28014018070600e4030788019400d0500c120740c14a6085002581142d0301d00940070346401c850001114141c00120b80003000880703e2001e00050140141d00000c80b8112900040002011034007400842d40400c8901c0a141c0f100040581c120b42c00000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 871812589 1250 871811339 871811341
    0x60306031e320a060b090c130e0a230a0c030e0a03031113030b01061b0506060f0301090222050f01060c02010806010e0919060b0406020601150908060a0504020312040b0909 75
    0x6a295556502021000424081c0b00c0300c403c20042558000360710300c1c01c05c0341c18010700d858070807011104d800b907895490b4040d1041c1c8000e0180b1410008200e0748442c11060100d17000e0510020488404540c24011910900300c03014059800610300849500070f03054078040084d22103800031650b43c2e044004000c0d0615a0b221f844203103e10540d0b0480701401540721048003200c2d0b682c601184610000d106084c00a9801403581d0020764506005108245e001001444141c0320001001281c080801d4081da040d0750702c44ca00001030b20b40045066a1103072000c03485502c255803032400c100342e0b00c0040001132100321600050200c143c00c074244010300354081ca810301e000c0c1c3e03d4900680d01c000554206561040800040200c0d00780890348000c4000581181880401d90700d41c440e00190096000c0c00015802420061181412948002956091510b0280000343e0b90f12820341c01c102c4240d5044241d41d884a00304000e5040c104100600e034040f004482e46401e1030310104442e01d00501620714842c0140e40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 871813839 1250 871812589 871812653
    0x15100333031412041d06090702060a0b0307080d03050906010801021c1104180b12071505090303120f010602010b0a0f0506030618090109140c09060907031104060306031e 74
    0x440220006204919541c0310b884101d0258032281440ca0380710340c3c5d9808000180e040c20200682805806650000c00303d40c0c841018100160985c440000d8162003903040001d00d1a030704010007030b04c840703190b240000d503404d00c0940d0504100c4141c00c41d9034a40c0c010042a480040d5002d10003441d91904a400900400715141001c410700c0b490380b15841c0b820301440c0c0901514215031040e00d803280226140c1c0c010035444001c2c1ea849903420702c0364500c0c0c40041030294065500420040c000744c2e60040549242a1101171481c6500b441600da00748850800c1005100303840c0c09108481c1c052104031003890b08549421101214144c1c01c0c0130b00ca0040c0f07804400f007103083d114103240310088401c4802441c90b0b4030713094599078020004102c06440c039aa100401040044d00801e103007000039030142c207804d21a6198002d020541c10b0160041041580e100f0b0001a22000e001c043e1001e03056942c0c0102e051842c6042842120b004a00e81d079140448020303074480050184204d2041c02801039420500c02280781c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 871815089 1250 871813839 871813843
    0xd110a0e1e0d151b03020a020d0804200d02120a050709060b030a0c03090209240f09070807020a0c0b0d0e060f0a0f0908131a120708151003330314 64
    0x20100440039084c0ea0f6108000281e05a000b50008410715400c4036015200da074401c490b8004203031005000315038002c01000c610b6110590b104120207000d8201d00301c4181550105107143d031485d1107446540c21021841c020413900b44002c0380117210920043c094182131007000d548074030001d41000c50341c40e50380449008440c003d070400049150014102c075402d04e045507012030b0300a1640925080c000354001200001e00c1c01000003c031904015000c0380326039503081003d88030440d011380b007070040d4801e44c4103060008109480c0f40000c0d2607070201c0c407903c13950b0398403421040d00c004410741c00301500450100105940d0084180c6d40c004061100842c200707080c4e801e09002054404c2e00a40141c4002074500c0322018822001003c4420400c04441c019040c5040340f0b0a60103007200030310350000c0c0c81c0041802a4419038900d03801c4083c03104070302404e200420004500303c0c2e5040c40000400c0d1540089000700b9280726010300350010102c2c11560806e0703e09042c0c1240041c50000602c0340d8403101212420b1241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 871816339 1250 871815089 871815101
    0x2409130210090501090501020a1104020a0e0904061a040516180b0f040807050f090f28090308011e051306092405010504060c06020d110a0e1e0d15 64
    0x3905032040081c81e08401003000d020b6002d00d0303000ca0b440003000600740d48000342c1030320b44a80100580d0034007001c0c402040041e5105100100c104041c89d1803600f070503607030041403d014511821001860710a40368509170707645011100244194600010801d00030242084840117000c9031038001070780304956090245403012a00814200c00e004680003e10141242c000c200303407103120b004c80782328a0b80c4804220075500c08503400e642001074840417440c200901810f29801214400310400007a001c10112840700c00300008560390140c45250407424160019010380c05000d40009582500d01c41c2e0f00f80c2c148410f014131a440c01840300442e070300282410b6038007003006080ad00d40e052001c2c003c440c202209200200e160f896281c1b00c000400505076000d1021034007198100e486a0000e1030440d1180c000035006400500c001c1c0c3c1d2241405140034000030020125495141c49101d260309480043c0040050358109245006003d064940e403107a85840c40669480d601c14640005e0086540aa50260103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 871817589 1250 871816339 871816343
    0x3030b030f1b01020708012307121a131401060c050106050a0f060815010915110a08130b07020616241a0105070309030204200c0d08240913 61
    0xb41000001588458810344100e07241c0907421100d0194885545d10b089458502031100c1c00d81c580020145030380318a400d015400740041c02d1403100021801040b00039140740008040042c3c80380d00440381140b0707005000031102d01c14044100000c0d00f810080002181042c0aa0700030702c04090b105004000d4250885070141c034000c0c010814203a620354860310f88007024095240460100b100280422215103803040ea0ba82d0f059490710543e5203080350951001440030001c50030000c0c91507540500031020050038000600c1180700707035a1400e0b03203034a040c00417000ba002480350310b204010400140e9221010f07140e01581803100390b80140003c0c50306890b41440101070034070b1681100030380c1121094070f0f44040f00400c41d813101d0108401e210b1004403420f2007060300c010041200c040082c4050304165010003025020000080c3d000300d041e90b8104019009503051040380c0c0d0015110100306a0301c1409250000300c0a03c04400e004960911650b0802e444041070340a00d40400000d8026a1300360301d81c050460f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 871818839 1250 871817589 871817593
    0x40f0e030c010525080105010c0c170607030614030c040f0e07240f02031606150b130e0402090408030705070204110702010f0f0914060c01020c03130f0e010303030b030f 74
    0x84407886107001e010203e5101d80d44c800f0400d920005a2454019281d0140ca10f5407809503980c00c103401580d98501d140010703216a180000701041c1081d1041d03019150b5100d4200812441c601114000c0548007a80c0101000640280c2941d219480c001200340390311070202c0d004100b40c00024044001095048009074182c410b1400000381c1c01080070040c1c02809004e040c0725003001020005484400005903418010b901c10460040c280200c0e05404c0303d003c1c40307200045840070620031400c0280c0349075009942940e40c005441002d078200c5040d15001805480804c0324103103002e400151075540000c2c4041c0841c0030000024900d1407043c0111045030b81c1c000c00800c0f983d0b02030074501006400201089010500e031035038942917a0f006000b1321111f6001e55550701d1640d420510602184c294610f09150410400d0003030010100c0d003030000e44003000c900c500031078072108000a40e081c0114180d21403100306034507060500088413150031650640b501404c02007100750191022030718200d0840305a0390a8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 871820089 1250 871818839 871818847
    0x20403050a3003200f03150402090a090504140714040501091a0d0c050d030302030f0a09050c0d020a0e040803040b070306050a05040c05070f140c0306062b050102030a060906140f040f0e03 82
    0x117103000b0040c500801040c4418602c120f1408184002c030b1003040c1040e5030051081008004034211070300401d81c0a031003003400d40028014032003041c3c036100e100d40100c50420300d9822103400f28105441441e004100c054000c2c000d001494172100b15000c2403403107241c06048130171410000d1221324609803009050191102010780d501d1b0a00500070b40082c0c860010b040d0008010480c919040e020315020f8a0f0814042c000c0041d60a0030815112a500c0049800c02c01003840001c9980040419621883c0101d4016940c0e190a25103039005880051a2509052a0150501803074480288003410784034280c5000821094101003a00d8501403420010300929801e070322081004440324201e40032404139000c944018104004041c0c0301c2000722820740d08582034a40300c0141d510442c22910b207400111403c1c0b6000703203540e161507007039031700803144540c0054a400081007200001e1064400400c4020307410401040c1001c00112105010400319106c1e5890b010160200b040a510101c02104840d04680e52 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 871821339 1250 871820089 871820107
    0x60f150a030b0f07090e07080106201b010e1206070f051204050d020c03070b0d0b06040e07030b150307051b03091c0c05010306051021020403050a300320 67
    0x42d4441c01c130fa41100089440d0400240d540e941c1e500383e0700071000b9407901c140d543c0c00e1030701c00c42e04008100880d1900128060321420b10500031b0002c1c016003042d2042d0f400c0c01003250030002d0056100b52204501602101138003043c0e20101040441c2c00100c0c1d0314041c0b0b0306880700e110868041c010707020761824540440741444104080012143c418240c5902913440300705240c400c140c0ca4071078500c240b92810f1401c214545d0142016803003040700b140c006002d10300300b984030901101e071048110780e40c802107035440342e400c900c0c0e00e0044d040702c451b0344800301c220b0f1842c502107000030064050380111107443ca4502d40300444072641031064815800c07019280d40140e80e40c1485020138001c90b00000d4401c2c00b00e287d13002c240c0e94442c0c0652800d892001d46503801c007488403401211005880791295940e07048400241c9041482400107200950103940149420981c1d0b04001c858841115882145200203032065211030b43e01ca108011202802c0c180068003000b854a008510003004203c90740c500c40025000074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 871822589 1250 871821339 871821361
    0x806040603140307061113301a09030a0e10030e100f050f09150a02070c09020910030c0207210c0803120c0901050d0f02131511060f150a030b 62
    0x5045801040103200110070806426250b20a0030300002815030070150600c428642241c40707102070900740c1c8c08480401c0c3e460241c1d40b14040b54000482d644400c0d400d01c080e480101100b600d80090401d03000c2c41c40e0034071081c00944400f0307154503201d0150049a4500117868002e50100001424201c1540e21910002902030014000b1000c143d41403803500e0003003265079007080e0910f07200e02800401080c001d02c0c0e250010144100040110452a07001c2014000040c80c100d2428010300b00d450000d42c03220050303030800082d074811b408100700b018a041818840c0f80d9001482d402280c10a0b40a00700c001c91729105401809050a0050040d0106c4240000e0b2044000000c2010302010044a02103458200d45950203201d142d501a000541c1440b42d9078a01065030b00c0781002c0f035001600180f4100fa4800c1c01c414483c85070f800806c134800004c1100140e143c21139a00703011040500040c1a072840c209001603181c04000d030142d00180c101410b51681038544401c080059908440c2845d09031824140700b070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 871823839 1250 871822589 871822597
    0x6031c0816020606090c031b22051c080315030f0c0a1e060f0e130c0807170a020904020f0409060614071a101509050a0f0b0a08060406031403 62
    0x1c0c4540960640100c209201080c5240a05002414086280c65441036100b264101800581020190001820a5014640040135825110f0b110400c00c3c030507108803a02006030b41d030b0041b40101480d180513101d05043c0141d02c6505584640150748944a8041007850310142e03548680d0140315450030189a620001412425004100e030f10148094032002220b604e00660801ca042c0c14901c00000d1160a006d841406248041482c1007881d41c071708030000804802d200740e0300a010a54030186004940d60000c81303e544503407a41480c42007a4064400a4075400008200724841c5502065a4400c1c2d40c440d0102d4030070b00394039848035480b0780d00d640c001002400c4030320a0b040481c500d441e854030118235041c1510851a005011110b0f01e00d079100c28048002d000800203504107101030b0307010640c0102e007001c120741100e060303a40030695410700007888600c1c041900940305405240e00200840801e100c100c0e80050344900d0a440c103601c420000c18090600741d08001e0140303003a10380040c2d0407540000a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 871825089 1250 871823839 871823851
    0x304030c0302090106143c071401020406050a0311092d0301050c0d0b03070e0a0f0f0b061903180b06040513171623070f12030806031c08 60
    0x509040c0d07603c900a0314514403503c45c0060130300341402070030040d604000c100c03000810340c000c488410304c1001c00a860304020507c082c40030310502060700020b02507020181d10748004510000c6240c6400d00002800c2401210a050b003055100d00902c2c80710007068045c0c134102000603081c2036060010103098040347c8500c2c1c51114084a07000c101055500d414003645d07024001359400d03545090900d24240020303040b45010280c0620901c43e0004000715911a201c0c441d044282002078802480e1a540d81a00c0b12080b00d101d00c10305201c243c030324541e6010115209c0301551041c054614849490a801426130180f401540300c1c201500d500c10301242c0c01c11184a00c4003120108070ba90350704e2101c07a416402e040c20140a400e066240a00003a609100174204100c0c5000d628803a040a9aa221191401051135a65a0308201160390a4560401541020300003c50b09407100908001c0c0d960055807540101030100040a0089030746034400f446402c0c03008840c14152007001c2e41403103028001900a03185 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 871826339 1250 871825089 871825099
    0x1605040e0103032d0503060402030a2d150806150d0503040303080708010b03040b0c090d020405130302060c0f090415090c0e0f0f01090b031e04050f060c19120209030304030c0302 78
    0x1210540d610144c209000003035541750982140c0700d02007444003d40005201c42e0f01c0554400c0d0301520340301c4240c0744001d50a201e0252103a0400c40d030462106842144140f00040840000d0502c10540c0200390294048442e0000044113490b0000103a610a10503001400b070b4040003c01005060344440b405214400a4591a00699880c2450032480c4002c68000e0410140c200108200c81044801881c0c080c038001e140700c400c0380312900060200d4030290381c8104030b83c0038000284c00b0150144078a60b804060901107034181a100c82c003a0095100f10407255104541d1400c0903110844400c100d800905802c820030451012503100c01b82140b28107034600b600c00c9100c40951203092404a1208094003810780d607501070b4610b4198003132515000640145051601005980d942c0c01d440c8281500c903d010310000d1401d140865105810b0100c05008520107990070070000322401c2c0e0001110901c8107840c41e000d02c1e481032040c0d05100a00801d64400d80c540800580042400302c0d001041080e207000f112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 871827589 1250 871826339 871826387
    0x90a05090c0604030f030e010e0a0b0702120d020d08071205070206060910060e0603060d0f0c1d01120305070f140106080c09010501200a020d1a100503061605040e010303 74
    0x41001418050380c40001d1807417070705000c40d00c0020722a92001403e0340060401ca1402240100010f8500840350015000040040792038030075071500346008500c04611078040d004819180100a4540c0000d0003500e0a102d0071001180c1540d12038500c6490300509407408000303d09200c14000c0d100c0b80d0544580740300c3c800c0d1001081c1d000c40f48070310345011550551940300b200c3c00c2d4401480941e40005103d035611a00b40040480401c240c650b14249041c840c0307280e502110300302035182486c00d800720300310307200c95008000501441620200c5076007401d4240c24129280d0459280503500e12140900c028000050501d0301c040d0020150005000d80340040705031108100038006021041c2003d1145e2800181d03c041c10003000140b0050710104031505000340d0702e00381043d0b0042052203805600440e0040c0c017009583c1c00d040c824a400c00e800901003c144800e0b54130b4080060381d0f0300c4019141064034003000210345002c6015500304c40007815a81840d0034503607940c0c01c2c0039003580400707081c280180c1403101c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 871828839 1250 871827589 871827613
    0x13060b010215150f040906061805010e0703020d0906061e08030c0d0305060d0503121503030c0a080a0c0c08070617130602070305121003020406170a08031005090a0509 73
    0x860010b107500307142400c000c507a5441c4940801c403009625181a0864000d101d4505151141d0048032061401480c0c0415201c3c60140f034612a403000480084c010340c6004014401001e400402c140c0100e241d107405070b1600859807022006101c0e400e4028141d61800b070000800c010441302e8112800303e160312040f400d43da2081915200d2040c1e85016402da04140842c6d40d4803030080d40920740044015005891081c2996101451039110928214a00e0821410081d00954012184404201c02d4029605040c46012100d90321a000e6074020042400810030b0400d491280c100800b150341c106c004072009580d2940d030b454860000b4019800010f2401c0300c04101d54401c0c541890013900c400d45141746805154842400a4100d010120204207003002030b030402d40055891107006030f4218481d031030843e1861041108403a0a544000d4040e200c080a0401468010801c1c1040c00d40258207103589550701050612449419004150701040a409000102e00c0c1c55105034806e103c40c1045401510b514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 871830089 1250 871828839 871828843
    0xa0209120607020d110a0219030503040e0108070911120c19030203060f040c0f0f03060e01060e1323100504110c150411041508060c0a0311090a15021513060b0102 71
    0x880170822050344141107100060511568082c59007600042204069440340d0f140d40c00e56001d94800c8c0e1060580700018080e20780b0a101340001000855001c02c150864034084407103501540c0102cad501d0f805124001081c42c2c01a204030b4801010600e0050b0322040c1000014000750005d031080e50040d51801a00815800c1510410350440104d844851840701c0c2c50300304840c12101084460105601c030705000500700446100b00d8003810050f160203d94a90360018000420001e0030410410303418401240c2c039500402c52504c2a40c4040e50f00f81003d44d072908003a402c802841d030b1245411078070301103034107200c100d01001070720000a03200c040d00d00c1404408440b81c0040e8042e02c018155002000188071103103420390000d801d12080d4010210555611025541086000c803a8490303a42d00015080c1d401551610482c400a40031b80034079401c002e610f0005c9001c3d05618082c4003801207607a201464494002c1181c0c0d441020041c1c0512902d1401c04460148090b0b03141c022036820703090110002c655800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 871831339 1250 871830089 871830107
    0xf0105060616080d0b040501060c0b070c08040501140408070303080f0c0930060405060712050f160c0501020a03090c0501050c060402061b0f0715091406030a0209120607020d 76
    0x2c241004880c4803a501c428619520240d10031300c0c016602c0700d0340005516180182030007060b054172504000c14040c00d040d14007500c010291810040c0c030048000018a10b0310a80d42502e42c00c0c138200520540742d441c0d50003640f2550b0080605803103821703030000805a1203c141d07071003094950160303403040d2904540d2500c1d034061640c905034000c11030403c1e01da00822500c441458504850a85011429110807240c242101aa002c4d0740316007100040003541e680002c24110402000310040006260447d01c0e04a4242c0140c0401640882c1200ca0b41031644a410854045600308008650390184610043e0080451010440d140004000d0009156000b00f058454080501015003580d40c0e032079081103a1540b1005001a25030f170503012816080100700301100060341071600400703c1609094a40c602d81e084440c0c0701d0200f0101c200d050291100104601c00f1441c0243ca20f540c5a451b54403e100c0a801241901a04160403040740720b1b24480001d800303030107112a0780954825214294086030003c0e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 871832589 1250 871831339 871831357
    0x9031e070e130210020703020108060f09152101020904060b07021309061b031d010501030507061404151e031107021302070b041202070b0325140a020f01050606 70
    0xd201001440300040416501890705038030600701041d507034001046410740802080040c2e126120501c00c5580001c001908103004035142c0420346603000c0089d901c08401003498116064013107a90140d0380702c868500540c032007075207000d20709800c1c25039900d4000c0d00b090841038451030600800152010115089492141c0c02510794103039182d524450101505002c41d080754500d41d5140300c0b0f000d070101d400c2030400d004017595011415990680342d03528407445070000a1184d0345800c00400010780700143c1c0c1c0c000ca580504019500c030303002d40c1c00d403440d42c041c40c2d0101d0100468507103007000240e8072591800c45087e120354441190405234400314110f800029150b601135408010401c0540760850a05c400c10502c1400035280500e44e95460420407815507040702d001125001850b44142c051007010041c010703011186081d031030010303e0b5643e1000404072141034140d40544c44000d45100e5150620801904480c0540d24026800000d558190745240d0b038141d0752800004c2000c038541041180c40c441c0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 871833839 1250 871832589 871832593
    0x426031603050405101506180e071809051617090607051305060409140a020a0507060905010e0f0f120c120903280b0105091e060f130209031e 62
    0x551618400e03070080c40081c209481c01e20452032040140d41e450701480da18260b000e690f0790400b51401c44d0150482010042c036607a06280c4000074842c250b80d54085940c41101ca145c1341604150f0116540c9210940c0e801240c400d5040204102c4c98580001c5a940849155912000b5051200707990000c050400d56012066422240114254900c03504c05040000320351903603685110354a6000500383c2d07000e0f030701001c94980c843d2045400f4260700744c411544451201c909501c0d010f200340d4000c002d403040c032100500303d603076a00d80c030130600c0407d602c101030b10702e4644202c82d0f8880301749060a54070041d410601d0018031a400c02060a010004107441c1582e0a241c010040f9140f01d17000d41410381c001c4c008440e014400d807503208021000804c0c1c01030030104007040b07415003a07440c0e042c50001c2440c16080903000317540510502c401c0c0d000d000a5622681c5003181030383c40c6d9031180c200080c1c50300b6040c00d5140d840000c0109141381c001c1168001e004207038040b01280d200c0000071541c000039001201c1e412000f6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 871835089 1250 871833839 871833871
    0x2010c02071403070b0c0105150909030f07082502120c060f030403110a06020d0b0108011404090302101a121212101a031f12031b0b042603 61
    0x200c1207154400740c803984000c0070f965030b441d05d440990303140e0380000080054582d1180240f1103024004a04000e0480c02a41c4929840c80d081b100c079030f80d910071f051051000700c0e0300052035814001d40c141503a200c0d50700782c01091010002401e8600000307421020a03445034002e113201602014001500024082c005003005042c854002c2e125200c90700002c1080e0148a440242080c080000b4040c42c1c1c40f15120f82c070016243c42010040d04201c50421075020306204003180148206600c1d040e05518081c0c0845010139040c0d1180390032810000741841d0480c03c03d04141e0f440c130326010303042c241b210003010035100c08900020700c1044540c0c50302101d403101540a403c100d2030554800c0200303041d611141100003010002c1d81c1d120701e075180500400300c07145290350120501c1040701800013032801500300c500c40c1c96403090030310295401c5241c04610040034011115080201c03000bc1d0001c1940051300550108124034003402c000894440003903504002c4c0354899003641180c85101e040e01e010710000b580078502 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 871836339 1250 871835089 871835099
    0xb0c0d030605061828080616030b0a050402070525091104030f080a0e150301030303050f1501030b0102010b0414090609011a1203071704141e010810030c0801090201080702010c0207 79
    0x4540380344007039076501e03900810000d0011780282400e0005102a0004100c2482c010300800d00a442c40044801054100440808030369a4010710300d0684104a03401a5a01568540396141400380300228400076001007411b00707070102001c86101203c08254060241609040c0c43c105648928007000307100304500088007010603200000b0704010151410140400da06980024407030380302c2d0099020b03609a0000040c81015410301400e9008800c45031003498178100104104440308800342054105665285010650780c030075086455120070142c820092049000e9440c00b000000f246c201da0369200d22004070702890300502c00c13001d04010310b070825055080c129082180110200380c40c052148410702003000802e1803c0044503191640d01c0c00b09654619080d02c06021510105400b407050600402c0140c1c02e000d291400c60102000340b03001d54880d510862805500e4029400c041c1c01c8a00607040032515450540c0800013180c001d8a45002c00d5441c400700b01d0070b0798a88078001d00160809941002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 871837589 1250 871836339 871836349
    0xc010f200c10090b180c0a0b130f09021306170a0c09081009020a080d080a022d0c100218010c05030904090303060509070c1205130b0c0d0306050618 65
    0x2480d0080003030b68081084010110180c43e1007200c182e60388034800d0288001c904101903082c00c50000c0038040c4c0300d40e0340014001544e40095210344071800b580011032011400c03691203464080c001903da08140350b600c0715910030094000e8164076200002407040401c2d001e0041c3d842900e16204032580300b4442d03507080382e0703400a0300c100380c40d030b0043c4560784002042000041c4801001030118030000902804140100400b40406901000700e5400c012130280040f070740418010351101c612071002d0f07078409102104d42209544891454824000c808581e8000c1d2440b0005090942e446021107200c801c402d83d89004034803400d411252406041351000074070f035015000402495004c1c000707907400c100f09540490240d814441c0210006680c80348213100615181c0c580d5508401e02e4a040d8108646c00c0c2e56420f007580d11407032050148580440d2010607401089010b00240c00e40c212000c0d1210740700c03821103644404a149141c0403d0800001040c40c2c07c01200b6141e08900140282c0414680207003440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 871838839 1250 871837589 871837597
    0x5060403080d0219030e1e03070813080a050a0302010606030506010e0906040f02160b090c010504031b0503070e060907020d1d060c06010b090111010b21030706060b0c010f20 76
    0x10b4019000d0200704040c0011307030131032010b03c0100e460205185004100d45030810356421440156044100c00501c01300d41c00005807500f02e0b41c0862125aa500030585500360061564803401151145040c41410000e0200c2c0700035195100390001c0c030606441e404280c003511000c41e411030014030b61401d080090b14000084a81000d0f01a0000503d040c556410a081c0d034000000c0b2050034080b26000c50400c8044030038103600000c460080e100700c080503800207060340708500c00544803075049003040548140c070b800080001c04000741108ca030590390b150840041907080369500d2003100903c1c00151424008600009000410303900c01d000030340310752405403034103210120540d00400d06001074401e0b0002001340501070580240400c0c0c0b1544900001009000c089502803556418030740d01150540329000307049204135625500c003640300d50200c071451950046400140c03043e420050005045100c9100522008450781d00038000c100c08006002d05459983c51601001e0300c4030364000c685404048060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 871840089 1250 871838839 871838857
    0xa02060f0706182603040b0606091206090105010518060102100f06120804030506011a070b061203071a010512031b030c0d090914070804021203160302061f0506040308 73
    0x6040140085002000103400c1045400c03a800200116000f040e6802d8682d07008050340c0c04c1c07481c600d01035480310480a4098072460081c000810716503460341c1c842c2c1e40c40a000c100c1c10121581850f14440881c0a0002131103114020f03080000c0eaa1041078401405e01d00c40c4c201a002000700a40e486058001405800b0701d0a42d065500c09010643c064062040c900250082041c152601d0440c00c06c00d062131b1701a03010000c40304c400b8028101e00c1c3c1e0b0240540b102e0340c1e0021b102c90312664881001c1030361351000180f4180c1501000920310304000c0e01e0400c0d050152814000581e040ea210342c1071002c01c0011008200d4158001d204400407078419059010384010b440040d40d082582c802984d0f49080240e16041c00801c10415090150320650f2090208000c0e0401c042c004900b050100035102c00000b03031000c0d010380100c4641200e4000b08000300c440b4800341094070313840404281002500d5260a440505900c8045401c950244900707580c0300d016034100428942c68640344d45d44102d100d500c52400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 871841339 1250 871840089 871840091
    0x609060405150108150a0905041203020a0207030b0702030904060306141518130f0b070219020906010f031407020109051b030d080a060305010609020711150901030b0303091513080a02060f0706 84
    0x1902c01c060303c0f09248000200847d0b00003080500b00303441c18203000b4203e0110281018410308c040c0c030440d0790004044044903000f06590095868100040f800e5218030004079401a041040010400c44070394403480501030501c042207025120703144282c40c240a1102c07200da004040c42c2a04c1c0c1c11100744400c5d0f80c0c00241540b100403601000d955558182100a00c007980c0101c05001045080e0780c0602c0f003204015445c00d2444080c18155001944445001d001241048274184000c1c0d180c501a81c403101303101c00b11100e02c080314600544000d0203001c110138121414000c260228941d0744141d12040020100100078000b900034040040350b0b04040245201d141d030381c661070700001040003032080c1b1001e40311011000d45c2e00d0100f814441145450074130014010000d8100d050f40740201a0240ca04051092030003154921911000928500900043c1548080340106085210316020020445c1018071030304000320340e56540405032034075000000650480ca041120030580d58006004040840c49444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 871842589 1250 871841339 871841371
    0xf0506130b0f1002010603021c050a15020c1b10030506090a090302031605070e06010c0c0501050c0111031017030f0d090c17070501021623040e06040b0609060405150108 74
    0xc00103c0b842e802041c00310150b50f40d54800d00c1541001d14a010f01c89201151442c2d9602007903541c9681c603601030301c1c003402180c0e40750300c080c40d200c02680446420070060812904012603081ca015070700002d1034000c52040e1102d01054183c03500902a152180a006291140c82d41d00d1504c1c10000c0c16000700c049003107000402803500711491401039a0060b40c0120001c01d0300b68181014040106005003100f4103000c11980d104c000030710780410407410703990280303003d0b0744511107011110f0241000034100c10307612030081f08004c003c5030354118460495a101d0300f8444100000d400d2140c0300d00c2503000d146190b0404001d6504664119000001203a00c200802c010440e500d80600640c140081d00e030001d150001b1a04001a43e410001d500c0380c040140301034241e02d031810040c03400c0000000c20b04480c038444200c1d04011381daa01e50101d1700c514441000e45466180c6840c0c140e00420b0115201c5104002e00d00110305035060070300c030742c40c0304a42003503433000d031448030000544e00710744e00500c01050400856 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 871843839 1250 871842589 871842619
    0x20f060d0207140c01170c182709010c0f020a1b0506040e061002010e0d11010212250504060e01120603060f1a031519110f0c010f0506130b 61
    0x560702c40f5041c050340015086400081000402007040c5001010118403150140500e000c015400c44044c071968113100b955a050f16400b20f9642d1041c00c02e000070781c00320340f015450010441c02d415441104172000801800646550a80f9002c40c2d01c4100e03001039000242e84000242082481e007080c0b0b03d074941d42e28480c0c3c1d0710400690329070301a0b04004403101982d001d10050f0700f0b00070034556442800c1c0c002805103034242403200745c0d11180d40805000b0405025242141c850003035044642201c1600b00000541c0b500a82e86007840c02d031400c0b04d40c003401c01402400c0d50f4a200742c043d07405456195840c141942c034076000440344003090320f801c03100341d0350380b89070000004100d0b00c201c40d0940820f081c0401c0d44400c1640d42c00c450b941c0450502c0c001d401a4050440640200e01d09660010074800c40c41030400760b0343e14280c02007011f6000c248203c0c070700203060114800504007404554420000a01a0a2061000c4420348a0540300035400252064118803a980700d5000340c0034203603019001100d91aa00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 871845089 1250 871843839 871843853
    0xa05060f0a1514130b0f0f04020d090506040c0f14040903120c09050f0603090601030201031517030d0c021606030c030f020d1b0903050309100c0206070c080601090603020f060d0207 79
    0x381c1d0100d0030740450515400f44a080c1100c0c0c0c1c10000d81c6545081000040c802d001c1078581640381c034a00e00c07420310303d40000d9040e5160b80c1a60f02c160070700e003020082d502c1c01c0c2c64075580d520019901034407010b1254500003001c100e03c1a002082d910066541f031803030350030582480003401c0e40583c11414000c0848803001450349520588c5801c0c241030781c0e10010740c1c3c6004180280035210f401040d0045604004110b20403200049040c1140e5083ca0005001501248a41060f000030b400814400300010f03030f007110700c1c0e0f0000068450410303582800c20600c01c5aa0041c1d03600d0914a1100080a52066041054a001e5840300c0310781c40031400d011914a0002803078800b00d0740090070400303003103a61703044081c691815408030341150000b500780701321258116180d5507968021000c0041c0310321a113a010300c0b620391007040001c00346517000e89a10789806803407824002000d800d020305034035881000000205801180562421030b0f40190130741d00d440300803e060013030b1503000d225a942e01603001c01004c0c0c005610 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 871846339 1250 871845089 871845131
    0x11011202030907140301090b011a0f0c010204080c01050c0604030e030304151e090f030611040308040305010b03010f0506210111040308120604020307050d090204200a09080a05060f0a 80
    0x1205029002840c10180e4520484c0240020640260701d4180310b43c0000f0015840c0c0303410b666110710705190842c1541035003406403141e06507034005000003060103940540150003800543c0c0891045c2c03014407040b4001103c4030b02481104183c0d0354081030108010900941c100808060003400b620b141136103821100c06406454a1309000154080a410300c00b400038105e010102e0103146040c0d28518502803290b0749109442c040981046c1e51540c0380f040c00d11801c000c46000f5680303c1400c40d1141d55a041c1a030081c0300c030f103000602a500b01700941c4d00680c0c003441020301c65a001410760640e5201d14903400c01510310000e100c1015036031000445440a807410140c40198400d81003241d449051108010b2521006409140541c0c014003c0c40402900001034403064031f007040f4002800d04071400010090b0020407002ca04002d0615124043e400d49440100036680c010b031035151285075035142070350799404036440140c501d03041180401c82690f0081c804a41010020754042945802c00c42d08400e0602 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 871847589 1250 871846339 871846351
    0x10b0405010815010b21070903050a0c05091003080415020c030109050606100302041217210108010b03060f160c0506010b0703030b0603070c06050603070902160b060607050a1101120203 81
    0xc040a80c03c809154401c00d228054400344004a00381080d14144906000d50f4541460001c400c00300000d1200c2d07c9a8030701d00083d600401100e0300d004135410400205001400b80e580241584800103400300403036404c01d003c80340d111207602c0ca0180340c00751009009181d030000c1421401500503d1440b6a400d0184178000c50269001d4401800c018080001e4555500c41240078540140420454000d4128540c19070607045420160741d0441900100114890007400450010b01c0103160441864600c0d20141a42d0b00040200070100140d42007540d1050203ca40c1c8050304040800540c0f00e600080704907084c0b030f04605241000345019a692400e0520982004c0044040407401304280755042c062400b0800c000e84506103181000b14000f403004080c600098400b03038a44022903040c1d00e013044221b0003046524821501c80325480c03001d10350920540030540c0d00040303903804141546408022900000d41c40380003800d08071020360382ca00310641c645041c036040c450044800d01e0b0945070360004500c507003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 871848839 1250 871847589 871847593
    0x13111b0c09090d0e0112020c010c021f140402120a0807030f02010c0f0f1d0a060909110901120f090b040605070906050f120603070f08030406020c150d0509010b04050108 74
    0x2800801489081c82004105941a80c0300100c480c0c2600d80000101e0307a440000e103003500201e035003a185440a40704d6107881ca403044d0f107001402e00c616940440c600100f004000d0620b4802010340d0b000e40c059608903c0309910488145000c00c005180c550b034000300848002d42903415030800b0f61114081900114002d902082d40b481445101036820720130100c0d64070b1a81001c0140b0300c0501402400c0c1040300600380248400041c43c07400c490f2845150802a00000700303400709807a2207101c004e01001861044014160806e8032088286800d80142c0301d072680c040c2d40703c6848150708491a4040c115101c90f500e0a16502c5903c10003252400f0703030051013240100c20114190502c60b5005081c0360896010600b0003500780020043e120f0220122422a507141c0a1507000c6d48030b00b000281864510f40c812041c0000782c0000040e0f401c800f0003d002120140e0b02a00c46005120741800462900403403400e50114040050130541c680540c405030b04a06020000551074202c5030129085a20a8101000f25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 871850089 1250 871848839 871848853
    0xa0c060806040603030918270b090706050a0f050903010f020c1005010305030d200d140a180b0403031d06011505090307030303050c13090b100c0213111b 67
    0x550040c0303069400500584003080468556103008001040e680560622034140510903058144190426115182e5201440b07601480820031100b000c0c0010303030125680444c250000b50f040303901069003411204140c42c4c841c0350591400049074025041d02210703044c414140b1040d4000c0d01c0900c2112143d4002050060b622050104020720f00180c0064044030b517401d00005100064001c0107490030400e02c02d2001c9075400d44c0c400703400e020a0800f1180b0000a501080900300034189ea00310031424540b03006200c45c03a03150502d83c03205540080d16100425400d03982c0c00c8000070709a40700e142d03205000e07180001d50380524280c0c050b1b04e03128107510001c2c1c0e90b10407030062000c4c262400c40008903000c64207102d4580032141c0302082e111300c002d01c40035051565900c00078600d80d440f1022a02c40344a41c01d060766145884402d4080200030401070076014460540040d11128003481d850040990000c14020040e06400e529502501320309107608070702c0006000c3e00100c240b0342410007008202c104064188 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 871851339 1250 871850089 871850099
    0xb09060415090210140c0f06040b06010f050304150b0904140105011e0b030901091202010507021606120b01110a0308040501150b0d270b06130606020c040203060f030a0c 74
    0x20725034086031503440040c5440300d5800160303518502251004102d0602039011101403a02405034042c078042400140504244081c0e0140080380c03080c1b0462003811820404c4e00c0b90070044a1007060140f242c808100104080360108211080a80c40321105210101e070100d032040110714604001e0740c00f26000c0c0020712210003940307800e02544c1d0250045814145216000001203200f0400c207200b213030008107000011407566042904010310f103030f801641d50082008200b034000d0007010122000c900501076030442c3c1c0b403018014050341c42211080d0351403241450346410640c0040441f5800070b4140312600c5079180c1500d07410b0140c408400d0183d228415145072a092190a550b10645034000c00001204140060b0f42e0300030607160b00900080300040c003040c076510f21b000b02100444a42c02ca0900719402201000b1155200c00d12504c010303954403090b022407507800419900d55002d1680036800050501c01c19003455806103601c640000c100d02c004489123400310342400c00c42e02050350508100502440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 871852589 1250 871851339 871851353
    0x20d09060903180e0c04090902040f02040f0f06082809170d050a05060d0f26030106020c0904050606010e0f0a080309120c010f05070204090c080106080d030204121704030b090604 78
    0x130310b4420803421052900e000800382c180716600445030746030ba989500f4019500e03a42c0c002c0340c4054180c4011591551511039181c6094031078810701291030101140419201e1081c0280d9000d0038000002031003180c540b05480d600781d4008855100c550360f8448036440841c04175950500400141100e1070758800400b011001a140c00515440c515418941440511f0f2103101b48600040e070001000b1442c0a41450700b00c07005030142e9424000c640e20b00c940a403644d003a90b0001c604a0b9000e400b100c05c0504507109004503140d0840c0c000d4442e800249c0001c1c2030394026411006a51801810701040001c5500040c0240095030042c0800342c2c008555681c050070801d080c40b01440d6240b004082c10042040000d04032600784d60f4440400034003042280071521640c200701c038610760007204111040d4880398070a009080318460b900940c42100441d0b00814064400c440c16a0a030404070705600c0c50545840d29840c050000480c084c0d8000c010010110f00055892406181080041e200030300700307410248 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 871853839 1250 871852589 871852637
    0x11b02150310050913030c080f04230405060904120908010f0c3c030216060b0a0b0702090a020a05071b0f0911030f060406050a06080f09060613020d09060903 69
    0x500455204e001d00442001007a907100055070300d40380c010021542460850a18080e4501c2c0c0b80c15a940480c0c00302d580018442041c0100080000d1304000c0c0500c03000b0401910030a5135115040111680842d01182d008403080c90174200500740491160741d144000c0307003114540d130031680030140e644010343c3c80070364407200001c1a8886c5203038111f00e00c9400c402c001044102c80c0044492040e4054030140c0150081d01980e481500c0d46810810101c968140f540c094a09103160038030134034410300701042c0c4460750300640d0b49050300a0400c1e0303600cac3e40e07040c0306030001d41c040d9401c441031040c2808000300141000356003a0f0343c8520b0441c1031030084e1505124040b000d0305504201a40f0707007010f004400c08124402500d80c8020740b0400340c0303200d40b150b00204000300b01513000b060300f0036400070001c0740a54112540390702550007034080241c650349007812240c58036030031b4910796405404442000100950764010f003074038514403100011880039990b03500f401c0394000801180030941000021043d04005200c3d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 871855089 1250 871853839 871853849
    0x115030627021c1407170c03060a12060c020601060807120908070c180b09070f0e1518011404140108040c0803041d0a050f011505040305100203090f010b0f011b02150310 74
    0x1280710305505074014902d8450042c1f40010744a00400010704a950380550b00c0c00074044400107981606040c00c024018001200b10714016200740c0c40005915849107112030701c2202030780c0d28420825401d03036004015003190941900c10754018400324010501c6480644001d0280e03500007010005510031031415a813507140d00310b100350040e20810404607080140c0b22240102e82c6000980c1200c2e01001510f1644007a03482a80c0346001f2800c0c5400311522032002003501d800340c0700e001005e800840800140d20460080c03d2400711031807003000665001d90740264000b0b203c1c440341d076455502d07102034a145030032075403002101e4450341480141e40c440000340c5a82100b1051014805071405001c080790f005818031522901070314621040900f00e1084099401940d030103000d580000e074851400d40c010307410944040885001e015801410780702d051080c00200180135003840b10304c1c61141c0056902d0051200800c01c1c0c0c00e00610030381c006030758081d031920b2100440c0100c16100d040280000b142c3d0703400f44e008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 871856339 1250 871855089 871855097
    0x510030b1e090a0b030a1a10050603090304030b09030f13030b01240e01030e0712021207031104050403050d020a0906110115031103070807030b0115030627021c1407 72
    0x40c0300d059124080c40e02d501000c11140416813800c8840442e24000100384050421445501c0d00c0b503001c0c00482283c0e003c1c1104241e11141c00b6110020000740303100135244e084a41d4410030080000910002106500c81c240b0700540741816803040ca500e4155101d001d402100920b40c450600401040042e03603800350a0020440f81d0140495946800c4200340d011400b060207191460706106030b11a130417413090110b80106031002156501400c0c10a60114501240308a00184403141e010500181170340031280c200c904c0768500c40c40c401c00d10000b0040078009800300300d404c100070f444001080c0000d080c00101c070b64803c0569881c20400500020310102500e000b07074189a9898004d8502e600302100740c0f80c111000e200444e000c0400685000c0141d44820964065100d000003845030303080030207040b0390b1200603502140f5900030081702204c419001d4030340c00d100c0c5000e0016003484500e0042080003034140c1c0051138403d220304a410b480b4502580030400b5502c03207400081500414911175000071032414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 871857589 1250 871856339 871856389
    0x12210304111e0613080c060a0c0b0712020c0c04050711030702012f070317070b011502210a030e0c0607030c11060d090201111507030e070510030b 64
    0x40c030645020420706100b44542c070350301050994060520211000e008004048940da40760764014158148818841c00c0554040c0030340f1150b02c0d061000480d40031010f00d90783c0300b01d0755106070f5596650030704c0644580200002442948580180c074402480750310702a0008183c007000c4c1c48100420f50324010310580400409454880201400006403000e240c2d09082032410102507044400c004104510500c103c0780b120480d81000d08808200441924064401c400c14400d1101d07034038205208086008082104035001004010380050f1080641210b61069074003407480c5604120601c2403094400000b004002080c0d400746404d4450002e045c640350b40904076100c040e20010741c4071f024140e0041c0a1003090030342242000040661010290780c01007080ba103c407019a0014010200300384101d011803840700f4a04a031013400a03566440280301208422a59103882d8124050300c88194026000d104415000c600c584d10384140642080182d58006040c0c5281c03010021f1066403241c86100460200d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 871858839 1250 871857589 871857593
    0xc0518010801230a020f0d02070c030203100e06040201050d140901060807050d1a07140f070605060402070b1b0c0f030c060c030f0c070201210510151d010c0212210304 73
    0x3d1000d42e004054610050702d030810708200544c24070070000380400d4141300040040402580e06840020303030740241c0072154451807d440380c40c121060f1809250050f0b20000000700150b10550043c9010b608280f8041000e607240e5898010644084c0d8810025944a50061040b01400c102c3e07440140000c0703600e0400c0140e00d868220a08612501445d41200d001c000154028040c0d1100707403061840744c4880d42d4502c480d01c24a003540c2c10219086901c2030800c2c0204480e0b06c0c0500a0f50a0705410446829968803a0030a1400c00007035015045070329181440b0038641c8240a0025051f081c8081002d9a642e01c0b110b1030490030818002e201d480180b03020b10a10405004070310840ea80908040450740d560303030a81c00140c545000d0300070580d02405000c0100d030340a85d007a4002c14059840032006400050300c442c80e8601800941d58540001407c404120901206ca140c0d1800300b80818180460f10001c181c0101316a09000441401690f220004404e42005c424000500003001806d4207400d42c1029 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 871860089 1250 871858839 871858901
    0x503060c0d1e29060a081303020a02090a29030309010c29010e160c0f06020409020d0b010f05030114060d180b0f10030201140a030b0301020a0903050111040609050d0c0518010801 78
    0x6441c000303403047c120165908050003044054002d90700141002218501284100c3c05400c81c0c680b50384016400085003142d1302d101c0301d144542c00d20300402642c2007000000044031601c19400d0b05031703410141c8100b940f090f850307031140c2a00c5044043e1002482581440301364034011402804540b0381004c2d83c3c1c210005658001d40c40d00303150394404581c03d08400c46050180c003900450304010301c0c0500c0050004421596503002080c03070b40b030a8881c1ca00001c0c80010a50301404244142966004031008051041c50700c036000b001c40d0b0982c10340010f1025581e0f0007920114403e6041100e240880d101800300031080c2d01c030082d43c08240140d662850a0950740002d08401089a65907000c030307408540d9910490194101010140c1c01800854680d207001400400468551209444035443d142e00b40e0b2030009207004035000c1d01c1b026203079015461319081c1071003100c0c5200c00091302d481c42c2240c40410582d03681005031040c01c03004a00c03481c01d54140302d00503003110410100701d00c0901c0202001d026520320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 871861339 1250 871860089 871860091
    0x7152c030307021e0406092a02060c0f0c03030c450111010e060a1424190b1206010f0f1b051002070b010503060c0d1e29060a08 56
    0xc15158400f079216a00180c4c4180511a503543e079005040010225648204c0c0e480303001e044424224205011245003200001c80480c0d016140060700040700042d40c807000b8000800c00c0101c0c12031128949041d800c10207095400c19a41840d06020014039010b001400300fa014980801c25420400d00801e000100004c0d00e40c019091414000d034034201c444568042c802c187d0159001310000d025400c0c10400250b11400120344201485140012516945070b0384410184540c12880707000a0002d009a41528002040008198000c0014400c0c2140c1d2096280a00c0105056107280384c546031241030b40d11b00300900800c11410400c0410189140070340c006a00b071504d150504240030403100000040d201900d0b499809412846000702d001040c0c0d1b5158020312085005180c010804c1e600c403020141c54090541d29088582e0342030140b003500c40c403d2780c03040c1080f0b0610849032070200b1051a000058072a00c04c0c0b6441002079886551f6071222040f5034111a4881c1200c80700d15103644ca000180070820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 871862589 1250 871861339 871861343
    0x1403071e061b06090f06270b061f090315091a18010e1605040e060103030311191205070806240409050f09210a050c07152c030307 57
    0x2d0307a440358085a064090b02c2d4080e0003400034400503600342800b030340511455500f01ca43c00e18000103031820141d51407a01514007650102503881105a8484d419000405030040354007480010b0208c11450351a101121000c0712506c4075130f9034524506100700c00c1c3d4400142480c2c100c0c00d0500d14400a0740d00b41c3c90740030a00708120018502c0e182c0214030990248061142020343d807070120901640000080c940c0210340da80c0c5407034648a6201c80034401a6040b0803480c6030182e10030001400002e000390044041c00a40501060901c3e5403d201400300c084a0400800402c03c0d940940503480303054020030b03a0000590803c11043e052a0740461001803400c5e08100c0d0b030b54030161a84501c800602c044400400070744209102c20700307024082445040f020b566844441c442d0468181c183c130120380300c8815003002e0000c5141890014182501c0030340c0b0088269010307004090002c0348001889605c0d0340e150718288e541788654101c1c0ca200811402c03070303042080c8a000c42e0220052959a0010490340c0c003d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 871863839 1250 871862589 871862597
    0x40b0a0815030607030609050114220207021807030c020d020c100203040306020a031d010501051503061c03020105070212040305071217040b030a14060906040c050c01061403071e06 79
    0x1644000700684151800c0a010b58036018040074040400c0d41034001e0301c1580c2a1300c00c00c200301e9a03142d00ae20360000301074134240c0d041854a11041c4c1e01d411000c00c1003440e141c081030f01610b00ba5940d030004001601c0701040202c11004241444001c1d41d05214091408289000404481d64802c10180d550380d400301d9128400c2c4449505103100a100b4019030307004650081d4250b4544802d031201802070201000151160f0708044114000c080050003407604a44000d40401c00201d080004140c09500041070203420003034024824001e4520300c0d1071a0600d0f07010394000583ca0500070b40081c1070110b5404510700c844000d00c01800420303400f1402e9002c4030658030f0000d034900004c4c40e1200400d90030000b20f20070303143e02081c00520b425000c001507114114a40701084803080085484e4000002075840e42d402c680300c06d00050003408c05a101c4203481c0100d082050501043d01151825540c10340c100c24503000100310302c07409070300741000340704060a0f9040380c0c00c2c034580343c20016000c20300b0310b489490100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 871865089 1250 871863839 871863841
    0x51602150a0e010e0102031617150d0f030c1202010903050904020a0905060f09090708010b07060b120f030711090112120507060c050304030e010503011401031a0904030206040507050303040b0a08 85
    0x80302580c1c4050642d403070040090086104081e07001c4d00039081101c1c0d0460b12551040c150480754825445603040318140c0100400b1607e44000150729181c490103029049990950894041000b1441c00c12a091103691403400030f10003450a01e10303446890484078156814943c18400080d04001540c4843d42e041d83c006032206482d00c0201d480c0c045552045801400c001400c44400343c0550017400c0300c4206a03440002030b150a00d0845108800344074a4a21800621400700001c180750400d921007000104000d4542200c10510350809890740d0300382d41541d100248880403c0401c10f203c0f41c0508044030f030960300b985054043ca8501035850801043d0724050480c0448482c000e6003a035070b06540000081040500d9014042d02039441500c082d00414104e0720702e440c15600c0b801c1100d050720345e005410292192542c005402804c0d66000c200301149280504c0d2960352580035080c4d104034000c0c0c0c01022282080d090050400c043e0390080c501035041004107005480714181201d4003014189070013179035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 871866339 1250 871865089 871865101
    0x2d0609020a050d0e01020d09080d0e0303220203100f0e0c090610110106030b01150e030a0c06050936180a020d031b150b010309111903060204060503010905160215 71
    0x24841d180c0101e6807d4a80f803000703002d020540014004550068104205000c0c100c3c024030b83c1c03408115180c80001c001c60240c1c2c0000012403002d60000d5101070304903403280781200c0d8403c00303071400010881c0940342d4406d41301980e030104014005043d402610410f4290900320040f40140c0010941c2d0300034450010f00c5513040034000d40c07151000f150440300413203079943c440c80d0015402c00070b80080f000003546a40303555020301e0046583c00410741d105607056070035464407200b43c40d941c004082d51a07021303c80740000b1480c0b51030380500ca241e03901c4032100d6040001600020860301c1c1030250a40c04258102480812840000900c1c00c0351540c0407034081c0c0700c5407a98501204c24040c12022441c680c2d1681d2200010405403038404403c1c0c0d14181d000303001d01d10b00c0000440844100c66400f80c02c1c00c0c6001072400e0700d424600200c1800b45800384010b0600b40d265110072007031341d01030b50000002500c0040108040b81c1c1750701c941e54001105580e8948034035100d000095480f9005009030030304402e880040341d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 871867589 1250 871866339 871866341
    0xe0112020114190c030e0405161d030f0f0111030c0d1505030a0b1506070b010b0928060801051c0b0c0c0703030e0f0a06021504062d0609020a050d0e01 66
    0x100500e0b0f002a911000b4801004110003802c80301140410680414500645858006c2600c00e04402141d400e01000175401180c05610310362940c003880030f0801000305681c42c00d20500d408400400300030a0410810401c00703003121421551200e08072001e00901404101e00801c990500003031080105d0700500713611003003614152941c04181d240c441e4502d4a0200462008140c0c4190030800d0345441114a200c1400b40758460803000078210100e050051000082e8003001d8040e2640140400403016040ba0141e00c198040d000086a182e0940d0410000c403075000403041e016203804d5400900d03c401e0105000b40c542c096560042480026a0002c0c1c00d9106807403e80368207103d032108035207001d941d07828090b090201099049016585401c0f0312403480c103051140804682e900e50050884803581825411070f400c1c050000c071030b09519030350540c2501c05241c281c4d050380400c403017854208188420709a4110746044c0c1c40005028010300aa00c8119000001c0e10f514501851010681480380f2010038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 871868839 1250 871867589 871867597
    0x606140904140106030e0601090c0c080d06030507060c0c060201020406090b071a100503120903031905070b0c0406030e070803030a02071b0e010e090606030c01120f0c180e0112020114 80
    0x108a82e229100002550b44d4580c21440c401c0c0382c8181601c0c0c846c1d0b2108121801d440d20080c00f0008903403000b20050000d040b0400601e14800019000503403103031070340c1d1528200032865201e9000038480c14980c0052100c4899084014000d5000840c549440c102c005003101000d440740c030980003408201c4074180700d00e4041d0a9469041c4a00c403131510f15004001007400640e500803030703000307104160704c003004107180e10304407140e08000900650601c40d808030750480c039040c00e840740810082e090084600003805620719500032521202020344443c28040c00400300d1700c0b542d424880301d600c210b80030492118080200c0790402c007008409039440c5281d0400341840c1c14110383c2c4040702c01d0b40c16000501c08500410460580d01e1a40d00c0040907103c102c01d9aa48520a42c2e240382c0c9a007090520121541c001c042d0741ca001800ca0360007144000e02052500d04541311807402c103020503119009828440c2c82c42c8404c030b0181c08000c0c541e1640354101803100494103100304000303040c4846202142440c100e500152 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 871870089 1250 871868839 871868861
    0x8100b0a051c0e01061e0b0a1103070303050a05090a0b0a0b030705130504050c180114130c030c02120f122509061d0f130f060e04050607030606140904 66
    0x2ca00d10010030a690042000740d05140b22946013400110701d4054440040c1e4226081d043c8080011b8240444004268421060b0b41c0500900010003089004240050201702d4003035100050700349070a60403402528402448000c040c2c10000f001c00001c0e01c0408407a8100b880d02000241124185000c80c0c500440c68005591150520900c0c4126480d1608441d1240b4826000d84104440c1c40d8180100d1842d80c02c1841c10300c851010040c803000403000c1c1542040c0400502c0903544c24200030300b400031110b01c00002e0300082c0e20f600c200c0c000d030f9404004c040e084280001d40c8510f8207480200c40c004500540089080303a4a0100201d032083c0fa0904031401c00f808a259480c001b413000031005408140c00313104030b0002c121300c441444214604100c9413119800050030152404407441d041001c0f200111881aa5059407005040d40315040c84c440c8801805550003111070b2810241851894000020501000c0605014080c042c3d46c1e84810340341d030f140d8003001540d601d8110840001e0050000c1006d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 871871339 1250 871870089 871870117
    0x1b0504030b04480509061f02010b04020711040b01110a0b09030403060e03040e0108030f031306060b03090d0e2e021213061206031e0203210909010608100b0a05 70
    0xc08840c0000050000b0382d00c0042800100482e5520130030f000c01c2d9101241c0969101d0300e800c1e0901c2d40a011800c9160010200d80300000e10f136442000003030100d03080010b0945010803080d1010900d030a003440340c100342c1942402e00c059603100d8040215500c0130f90450081808040c18003081c1b000c1c20410a90b806541c0c864402d020303191603a446240c2e01d401c107106402e119110300000142d401230200071244554581024240740d40d444482491014451502c11501c080d40ca0900089002c144c0c4080e50040c06c490015049012040703074018100003030071581030310908080c3c90b800003c0c2a10090440d038003140b00390310010245001d0702030381000380c00c0c0118444480001003540100c03a000c4c501c8826100e203601e504118404006e201c004551441c04000c14208002c0c0c070310010107655030909440e4520060484194502c000c103a02040e411140d844602c03100041501c1c0490322f032540c64140034140741c2c0307000405854512010798001d00b0701c5c420340c0c0b1245070014600e0b008900c1503003103c030781c01c1c45015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 871872589 1250 871871339 871871423
    0xd0c0203040513021e0412060b031603060615140702220e01050f0f0403020606041109031c1106161805030f0a05100b030303040212031c1b0504030b04 66
    0x80740f00065403125140d001410356014404808102d00c05c151004c1c0d582442c00d5200c0c1e51059582d0100401d4603601c3e0f55407610885034100781e40c1c44442401005180309020108109140c680c00d07140b40102645c0c81c0051000e104404a02c02c3c0c461030641d02d0701c940407a94070780c00d9400c200d001c07a003102e0481200c204172800d0080404034100150000d030701030750103043c1150030795540d4201d1995540e810344000300140c00460105640345050781149854556000d20302d0300d440c00090001c1d02c0c1c10031582c3d290100000360f10b03099070f1240d0081d1050081000f0440038004c03a2804406ea00e40e984590248407060200e0000041c02e0704c440d0003540300c041d0201030100c0390180b201492080c0e50b4007840804950500c110102442110341320f01403201c1e240303070180045040d0340b9254208409144111060300f4107110902045026a00c41c100d03411554500c400001010003500110b060203123041d8110300d050002c2000f08000080c1c0c1d51003410b610580200c1d490803003001c842e00e03030188a0300000f50782c0c060291880c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 871873839 1250 871872589 871872619
    0x150902030601081303020d08040327090509070b0307141b010906050601021606051605070e070f051207051303020a090b03060a140106080a06080105041101080a050402060d0c02030405 80
    0x580290301903142602ca08115542d9025480000404200028016080074100c284594060218150014842e080c00003a4454500740c0030210b8850b04414244900b0b4003008010a610511400e80c2043c42a401740820504246044000f0b110103800e0004112200140404051040054446030402d603048002c0742144050410b02a100006083d10382c0c91514002c034000d98000a040001845950b0000000c00d1500300243c400350000403444104540600303221000840922441c2e000e07040f444800070090600600040c41041c182800300c05000c010046c4d04011082219100d9001d00749140035544c0d0902007000085a1031a540001d40184c0416804514000190082c1c1080e0006030100c03091940ca5001b1541034658004940800da2040c03c01440840e20071500f4580c05080d980c0080762807503030f445603103084800481d01980c003444604050422980c1c0415100e4100310950000e005906058002070307024454018409449956000141802070007802078900404008007900d00c0b0700402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 871875089 1250 871873839 871873841
    0x20706090c05130b091b0706061e170303010510021903030606181401260403121d061f120b0a0c110a061d1e06070c1e03031509 56
    0x14007840b80300710440300b08046940300740d10a03020700c20b50003094003449440701b82214900d1030000f1030070320042c1c200b0420710000c10400d01a0360010898146591030b842c440d02014801409540c100da1201100079182088061000007900d06641048440c00003c1f805030009038070703040d2000160603854110000702c609143d0142e1160048640b1034a9040d090b07807500102c01000c0850740224640d4040005046026500c2040000100003215801245a940b0b0640c110301c10030085404400050081a154a8608080c000d400c11150000140003440f400000d0064840c3c80051000c5405101515804030700b000c0100d622000744040c5c42000d0030000c0340e0070702c0c0208001c11a980d0f42018200360082d004c5034441c0d844042030b90320b008050301c0c10350120764030f80010f41055040d00250301c011210702c000014080c0008103004e070350b51340d00c80d50401d9403d081c642031140041c44c403402d016a9108000102e14011001000c0720224000c074410100d803468190001c0c140541210310004108030040f40542103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 871876339 1250 871875089 871875113
    0xa120b12060916091413080c07030c091103130f06020f04090605120f072c160f0e06121e090d030f0504170711060f04030b060603090d050d02070609 65
    0x3181e14001c4010303201c0c442d00d0160380a00d031005960741803110000d180642e902d0701580085100324502c7c0e107420704c0c0c0d980c80c1e803401d0030641050303960b000064001c00c484101c0388284c2c90315940704241c1c1401c0d803600d03050555a40d80c500c0d2014050b007a000360800100301d5a84d0480301d0f45045206c203640c0761a10382105200902c194020280500308100e0179211107040000da044080140740e005003280d03800d0003100080d00c6071802108204009442c07050201c0d10110381c120784503810b0800303404405506100014170060705c542104091240306100c40e41e41340c490340c0403900040c80d941c01d012000d84501030743d110140505c0404800f401c140c0c9061220135030340460b2003a40e080c140d5800b4048800d005e102d4200301d810560b40140160320920322120121601000f41ca0781e84d0003412020303420081c40000c12015817041030703000d100840004090040141040c002604140300b0745d10f45040d0318000301c900b5903455071030f0070007401e10101042e043c8003110207030101d6030b81550000c02845103403d1464204a8a15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 871877589 1250 871876339 871876363
    0x110105070e0f0a24050418090b1311010318021008041713090b03010b0d0c050a06021209062803020307110d09030620030103050f0d050a120b120609 65
    0xc441c20750300180307020040301003603800600a2201310b0600000e1303002050208601c820a1010034040000e405000c0c0c2108860745c040b044001c103070500a49060710008a006062150070345c842050722022401350b4414000c0c8074000c0c280080c0f80510340503104505001d07850000c0d80407200c0d9684d17805455000784964012807040103000d080340c0003802e00102e00c3c0100d060804071407003c0b00007001015129000301c12045006000040c441c061345012554807105074206849100c8010790070021410420b0b400002801e81d44060030008070154185612442091a241d128030004681d4410540320035102c4800c4000f40c41c0420f400e4800094050042e400131507150000c9a00e03205001480d00b004190311a50441d240e039020400f900355a1741d5401403076200c3d00d284c848041503030a044200c3e0740800550207940640000c0c00590f00001c02d01c0d02c1c2016044450007002010300103800008c0d0090407aa0386107980b0700010460aa409020400501d059113581c400c52281505110350075801040b05c0040341c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 871878839 1250 871877589 871877599
    0x6050301091419110f0604030501151503020a210b090711190f14190312060b070c0e0403050d09030f0e030601051305130804270b0a03080a110105070e 66
    0x441d5041540f00701810040c003440000002a070291034160300d6100c1d105001840641490f440b52a003908440f07584000701c00d4802d90100c00d01201c20500c0040400502a26042d440c1066215004000c0195025240b00200c1c5208002d0240011038110000d07400d80601944001e2401c140014403100000440c0590781c0145d540881c48815895240c03007603942c101c1423080c0700e10941d54880c0c21103410f01c81c60094a01490240c0000c43c81e241d241842d24034003a507110b2041d94807491080007110300903130003000345100801c0a03000181404c103d2004840240700c1e003401650362414103540d540304030f4100541c900c2c40c0a503060201030f08286080e601031000d40e01c1d40003540003070041c10754408080c016203a1191500c0500c082020340c54110944c801b048c804034003540b12283e5290755850b0080c0c0c01503082d072040c3d5061000714000e54400f4451809017070f00244201c4007a4004900f150b80d0f0350101078020480041c1b900d210901402d100300705650150000c01c110300d013007200103141090012180d8410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 871880089 1250 871878839 871878853
    0x6040b0a061406031305071202030f0c0901060c060605030d050315090f0c090312030108071d1509090a0b0a050a06051504151b060506010f051806030a060503010914 72
    0xc000612070202a02d144400308040c0203200b004000c3d40d83c00c000d198528801e081860392000560601201004200611110a03120000c0c410941050b1000d2941c02040d0701c04c10b80301c0c4c4a69640b00069044828034182000304007424100b04001d4040c640106806102d403800000d50f0039441002188542c941d4a0f03002d81d9210b164041201180c020354464180c41c0d251000705181444400003000903000043c12501d02d8420200040c01d6a0001d03030040c02e040c0c0003c0c000300103040082c0384004415044402d401c03024909002c040401d03030001e859040c0202540750008018003010050403100d5034001440341c640d807800c40038104c06071400b240e048105a06244001078682000d044604011000d8580035003000d041c0f045000611510320685c2c0104140b20038401144e08049540d980781c140520004582d41c41c08600240008084201400c200902041031103817041d1511a05408402c040b105d540d0340b915858000e501504042d00710a0f45035103040e61881c20010a0840005040d032610152416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 871881339 1250 871880089 871880101
    0x40e06040e060910320f07110a06110f16030207050a0e1603140f09060606040b07030315090c03020c07050109080a0807230a1a01151407060c0206040b 66
    0x20391200f9102c0c0c655035030100c0920483e180042c1c02c100c0311680311055094103508a4540f10500801c040b80d202c540c80400024480c00940051603d40d010041d810080c4049014080280d42c44d850030201620700d030355800b42c1065500404089840100300002d0311034542d0b010300c1107940c138012074100840240c0305400300083c0790b00340504a9411152840c4820045990380020125000b0180d400c2204050b92180040301011104c2592401840d48104070912860500d0145142402c007800c000c1c4240014001000782a079901d080380c1c502c50385403030081107010b0a80c0c4001803611098020710398003428040000d50050341a030241c00700308160360440d907030f150755100150343c0383c52079004059050f00100c0c0140e000c5120f40c001040554820b1405100010031884901c0c02008507a4000e100f603007242c40b0b08018803000c4c041c00d0b140c80c4c680f88015803140d490401c01401e01d0400040c00700a01c44805034807030001c03000200303a03448540c2000091250104030354000b5110034046070100c41110004000c100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 871882589 1250 871881339 871881343
    0x60d0501060f20031b0703051504120c0215070204090c15093c0b0d0f05060102060f0a090807020d032304050306010b09060c0706030f1a0904081e040e06040e 69
    0x502c20703086001552400442c48102c803511070429102905c81d108504000001500802c0031003107504142e10481814101490011080c08041c80781104010000c1c0c5000c1c0582d4400c440c44040d00a01c0c3c0c1d540e991a500c9101140c040c140f601000307002003101007000541400017180d440c8041501c1e17a5070000103500e40c4100c8e503602040c50b4030390300a85205c8030081920185940c0c142c0107002074548090550340d4910f20507d1903882105444c50072901c0c2d00e4080100c5915016440e00240d090001c0e000510304072a20281001c1c0013041d403401d080c1c89069070801c1c8181e0404646c503158010b4a94a4100303060704010b0007510007840b84c82c109021070b01c2980d091282d0b2a069905660b0000c01a18a80c0d207099103101e2150050f40105174400310410659507400d42c20440480100050346022440b0361480c207002d0b080702c1001e580d00481e10042c80c0030303c0483d03458003407a56005601111803501d5500707000000c1000814000b1054884000240120300340c840454807900ca0201141c040c041984260011340e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 871883839 1250 871882589 871882637
    0x4050309032a010810151d030c0f0405060411130e13123006051e0d080f0f030106021f090b061003150603020d060f0605030a02030402060d0501060f 65
    0x282c000b0707880c08540c20a541c411302c03103d50008402504100300e103840d401c40b103104034a415006070100f0074004c0b4004540b5039030a00060708501c1203028214402184010a60390148094186e104664400000c0c660f5512036104c400c6210007100241d031075000300d001e6150444501e0240c203807202c85480c0050244040c00d404030358019481803941c8440011070070141d802c0c442d02c00b60641c0180118600c00c2c051100c2204100340d82c070100801242003841e14050003143c00780b10101c1480140c560701500c00648601042500180d40702094950703a861010048016004000c28003900c58800000058195030010340717491214104104000284031285101040307a144040080070b0701000360000e9240e1601c40c9405030a03600c60308001ca049030b224030840354501c1060304900c000c40e0740030a68000d074480500c44c510140444441d008505401c0040c0507100f8040100450301460300040064215140c4c00c0c10b488850640400c00c1c0a01d5841e000c0141c820011400201e00149004108204203003804c0340d04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 871885089 1250 871883839 871883893
    0x100203070c0f0c1d040c1505090f06041d041101030209010903021009090509031201080f0a020607060f0c110c040b100f03090c090b0a0605122d0405030903 68
    0x5441c154160341c0d0b807601d001007410070a45500d0001e0000051a1045802010030142c0071140d4500314a09454503091440b82d5400c0140c0300d4004051f81c0d2003042e001800c0f1842d02000321000b004040d544000112944119048104044078550804000c0c690320007015005610a0f0b00c005000d40d1480011012406000359107800100d000f4002c1002d82031100841c400850325240100740c00d515501070905681094900c080c185e44001441031740c04103014070040c09004101d021703001d550701202c0d040741e990f00c89400c0648504400944142008000d5211403d001d21741001800305120002c0e008d800c5001d10b006507512400340701c00301c400c14a4039228080f6649402003400500c01c0e00c605040300e0107404220742c0f5040c156518a070b0000300da4818000c1000f010690400302e1002040c00920000001d5a03100700306100e01070100b880341340980490194000704201c42800441d401c4401c0c075403800410700e8149181032050341408107011000c00145000390081c0e08503a542e1011b0000310000408030010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 871886339 1250 871885089 871885097
    0xc03010306110c01090c06022119050c0f0c040c1704030305090c060d1d030f0a05181206010f080304050f131d030a1d0915040204150c0510020307 64
    0x600001c0c4103030b40600d102c10010035225040403440410607003101c5000c5010740e0a800142c008001c265810401110040c008015400111080306c0c020310f07080c0032b20340e01c407a031148901060b00310251160050703c1d19040c0f1102111000342ca20034540e610b9000e0840018060f6060100019034030303008001094440c0300b070070308815603595980c500310003d21000d44200c09034080d15500e02c0c82541d800b0040c0c0346482d620600050700070341e0544000d68410302c02d5a020110b0f041400042004035142c026109024200d08183d590b9844941e110054035268040103580720403182c1c1780341c40c400000100e85040c0da41781290b4000c07050b20360603100c3c0d0b0390066115455110760750415842c0c450800030340c021515940c009010940480903210310070490802c1a08100316880403450b8400c155100c6c2000c901840300d0354041d1081061803000c0341022000411080f03d0144041001e041030301c41e6811100241102c10002408081000009290340b08404050b20039205840c4106601c1c07665100b01d82c0200d0103519 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 871887589 1250 871886339 871886341
    0x9050c010c030912060b10020a080304030c080403020a0602160501020c060706180507060c0b24330409060f05010c03110a050307060b040c030b01080c1e0d0e0706080c03 74
    0x1004464181e5161400ca00b000181ca200003164401c40e600307541020311481000c1419000303541480780301d0301c0884142c42194410790b405804591880205c0360172540515003c0d0000701a401c201d511840b41c0c0d40000d422103071007500003d41d198007262a20300c45080100c594100e55071540126640c22201e40003580c8101c3c04c100000000b52141e011610b05c1d0645c11080c5000e00303003a01c1321410442c1380d134481008a00360901c50020007550710161907000d22244a446075a441802c40d80c2d110711201000301d4040c00c0301d204208100b0550280070060400c119495804c030b000d1581c9004c409070024800d0f006401d0a00c140813039942d0030340121106851041c0e40d4000440016201240c004115401504d0795010352030050000ca40140000c0c0f000600420001c01c0013900312040c0411640e0b24510340c01054600183c0c010310313a0703002109540098840c03c00b5a1250a20f4a888800d00d01580095070450300000da03548546580fa009280c1c200c1c0f00074160f03407040340d5925080c0c1c0c02640450300120b881600300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 871888839 1250 871887589 871887613
    0x102011808030c0a1b050319090f0b160c03050c010207080f0c012706030b090a02091008180a0b102301050a0e090f19020909180f0313180905 62
    0x3501500d040b0105150120815117140790354400120300c88030503206604000f07501c144c00341c0c1c220600c50074507845140c80103e142ca4010016012860f602030b000c001000000d14800381c8041e000b00c0d00f209074000e00400c520b540d50746440703079440c2055020540980030f0071000084282c004542240030b4003005020300400c400750b400440340d80e6101e00d04c0002d218000b480c05645841480b2000f00580304981b0009502106141003003c440e00080c001d04180b4010451134406407101c00c01c2c100b012580381032060300c0780c031400404000c1840280741020a0301c5040d0040b07003032046030f14105000d08080c1c3c54140ac402e440d43d440c0110310380e0852401c2c1121041c00200f1010754481e2006141c81c08a620340090701890030780005054903401d45142c0b024001c00e07411300010401c81050608942c0204808602c1d005c0c15101040601000800c41240d40d4401048041803c005005c05900940b46c402542d680305180b6181509418960203141052070014480c43c00510302d62142201741031b0400002c4c0344c515014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 871890089 1250 871888839 871888861
    0x1503062410020a2004050a020a210209041a0f0306010602060c0f07170a020106150c0f020f0901080a0b07081902071110030e10090b24031902010201180803 68
    0x4142001c0440c4540c3c205800800c4040c045015010550182025115090310410041d18800741041c0f681d01c0c41000b44180d0250050080450013520000f008001e07403801031070400a0046e503000c0e6802038242107030381d000300c1144103201c1d04081d011140c04007840907800500da5950400d001b00310140e44080c01258203504044098800b001d118860300e49415190744e10f10a2800c00300d16012100c1c4404560440015028001d1401424a0881d40c041c140007d0310020641940f1901c050310302460300074048250744800d03044129003103000c1c1103c641560f4078613102d65503183e4108156042d55000c0003080078140b1400f8a680140050a00c0404035150050400006e601015080303501da50705450b40e4185031104001462a020940c03000900140c4505070182000b03404504596036a180248201c00182078820070741e000000e0ba0040c6910312168801d0640a961200f1100d81c144644002c50b001c0c4405c00d11010802c074400e03402401130041480501a080403010700080c45840d003400000c0d82140700d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 871891339 1250 871890089 871890109
    0x151207050c0c030a0609050d030c020c010e010c1e0318050a0501080a021b0f010c02030910050903030f181e03060a020d180b100b0403030215060109090515030624 71
    0x101e20580d25203800c0000043d14012440208031034440d1a9111601401001e00a4080c0b0503213904040c0200f40d03142d64000cbd15020600749807030601100d40150341450340324011084c520342e80240e56121100f80d000034102e00104803d403c034001004480311840300c0484961010456102804c0704075401d08100055811030001401071213140d50900c039003003002e03401d84c2c0d40425844032000a0b00d001100c114010307080d9800d40d01c0716020b55104001020340303910f80000c1500740090350300d0201d88500c2200d00103411840b4180440a0210380407440515820508038556414581100c2100065100341d01980000d42e207460075540c160007c1d00007400750040c0d60010030742903410a9000403100d40213054038544202204080d81e184038a8810810014078801d002406071107440555030a0500d1a42c00a542c2d1a40c0c407819005090303608042111640107001c444041c00710380b80c2c02d018903d03000d5150340b20fa504102030380703110f80319850224464541d121078850740c6441c0c4042c5d4650010044050007103140d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 871892589 1250 871891339 871891357
    0x3071e0e180c0a2411010c0804200315040c0f08032a03120c191806140706020a02071503020d1a1315080d11060f01230103270215120705 60
    0x5c0360070140088218284905540e4200030f403140030752400c2504140c49007019401d900c840c00300555401c0386c40b81c2d8000498071300514858000443d035580c0d615008156a61171b85c0481c006240303401021921181c0800a0204030304062000e2081c110f0640b00340b08010599004260306070070400c09822507058070007116610650303500c0380603e81611500750072284140c2e006c0c41e0000494440382240c924100d140c00100070a803d1400081345120650403005900c95101d00500080d4009000c02d032403802844408000c2050001e603c000144070700e0083c020354481285504000d141058004400400c4424544440d00181800e24400c010490f11002070151484c0c9980210310844000341680080112403154401595541c02103901502a903152040182c13449000628210045c0084c0e203000b24078a211034005011040003030400300050b001086100c803030602d40e8820b40344d100d45032440030801070302652080e03402c520300c0178611100415602800800c00c503803016580c0030a2119103c0d1000d029245 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 871893839 1250 871892589 871892597
    0x3e040e070e0106030b01030e010c1b03020703060606080603061b09060703030e01020d0b03480a03120f030b0d0f0c090e0615030a0203071e0e180c0a24 66
    0x5034032850844501c003401d90060b0002501d0f084404195617050050102c10310300900248481252400b010f80300a003054010184a041c0055030400d140c4200300c90002140c010008000042c1c448000800007030048800e140288110404941d0f81d0020014103400601450034a900386100701003001010781c0301c04010b60405403a188440300081080c030090440400c4550000781c288030b0f80c4249820f10b0080300c0f0045080c2c80d51844c03400c2d820841030380c000c0d104230b01003410320b60800c4a042941c81c000300032040c2d5400503484c4001108204901c080c11040d2a05031f2501e126900e0f00c1d01080303090340e09108009401603004e0001c10009104490306105d1548910789134003400e51240c441d441151640810852150311070002d010800300c642c800c2e9410140241c2c06880101d003542c0200341e90344001d21628003081040300030700c9002000b030f200000103840f484d6000c45440c1019010342d0f00d007045091620659000d01c4403240403502e0501e82413001c5542d086003199055082903205800c0c00720180540c400d01c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 871895089 1250 871893839 871893853
    0xe01080703020f040906060e030d080f04020d050d0201090b01150903231605010e0103020405010c241a03120a12110f0408060f01061103040504050c0d02073e040e 71
    0x40c01040f01501c0509100e030740008080d4503103180100070510f0341d07065074080e40000e2694a070307590f8400c1503668041c03d1085000e0749900e80d480802c140d582ca400000e440c2d03000720049a0406541900700c1d208150164059038004e980703c182c9485a00c50200504002c290365210800000c3e001d840400001c2e5904c0051080e411000f404140c10f010a039100c9402a494a40080c8829038000501d4203040070b0230b01c3c1c118100341c00c0c9000a01000d040d0300e005000000040036449000164a0841c242550b01c50000c0c401a451031794840c40e4070101c088a984680250f50f48610729030410800d03981100a00e03940ea441500940141d00700501440c02e00c400c00d03010800841800d050544010002448914010f10359468418180c80c5000c07810b811003020080b1000c0e072008281000030959084c5c91044500180d1a00c0c1d110320f0b140c1e50f10410742c0905006d23001080e56014890340c01d110b280e10810001c6820709441202211a054070009030151081d05c00001000110b424140c0c003d0820034a1841180d0308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 871896339 1250 871895089 871895107
    0x203070201120902100f1d01082a0f130e04110607030e062107030605060d1109190302120a03080721060306020a180305070b220308091503070e0108070302 68
    0x5d5590126400300403d00c04600300411a5004550b060b05041350f9a20013040a6090002003542d01d000e40313600c0000415141c001107005030307121602844080103440d0780d95451021150641c0da00007035080c454444d01c0036400910012141205442981d109000f10b003c0ea9490040143c80e03009450f06904101400030103459684030b100040405601b0484039051031030114040d9241003030001c015a003003500b040d001b080340740c0300d5209450400d066400080f80c420b10b4038908488034040c0043d03003035211502c207400d04d07000020036080405890080d102e003c0003003008031010781e5035508050000e00195156000070f600a02c504801c05104042c0640c103000c1d228140760500580d56150016204140d00242c0c4106068000c080000d0140c0b540c520210700900c0c6485d00360f1149071074401e00c04000400148441404903d400400200141f007561345150b80d100e0400500da0741005624502a0000c084003521200000c0c1c107880c412a450350f2401506403c45d0011151418050094014140c09000f80c00d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 871897589 1250 871896339 871896349
    0x91a130501020f03041e150c030e0105040813060512010527090f070f060c060f150b030405010c030218100509040e06040209010f060516020d1a070e03010204060203070201120902 78
    0x1040c000500f90716821306041c1102c1c8a804102443e00000c0f120b17001300300107800242800440811410005483e2204e003c060b0068485540140050f519080c2000200072015000c0d03d96100100201981152200c03001d4030a80b1524a013159049080001040545400101402c83c28000c4000c028a8038580a042c00c4805040c1e4200b4201d130420002a50701a404020b404001d050814101400900c0d0943c0a80050000380000e00f03000d8850203000070a0610b0780108d48108441c01104880c1070b60b030081c4441c2d0390001e940880d015400e280b02500c0940c0b0900a640600ca0034802201c084c02038503080000d4448503003000024010f09001860031907940d441404016515100900700c203190910412917019016080745400322401442408500e5100050740c110059401d901008003240d8000500700010100300100080341000c0707041036143c4c0b07000380c15000c0c8107981c44141c00b040340c4004140c05d030302650003800c0043e8014045c0a001d98454a89007001b02d140c440c0c0000d000d1000d40100d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 871898839 1250 871897589 871897597
    0x17060903091c0c1a180f0d020904050a0c0806010602160b0901030c020703140102180631151716141e0d1e020703080106110321070f03091a13050102 65
    0x5420440041424010b014609842c4082d01c0320891340e101c00d03154403100003000c1801490000c0d012720000ca00040c1040410440044942e0300b10400301d4a640d80c45c94802c1e0380c0d40c024000c00b00180225040e102c51000c0b446008025629000645400c0000341d070011030081a40c4804807086120768000003010509402c04202802c030000d0015aa48694041200018464652250160408100c81c00c0c0180c803108080d0181c4a00c2c0c107015010a1000c0b45c0d0500c1302c02146c02015080b4202c02202a4540e0400040200c03880c06820714511aa141d045181402950890f2103010074a18040c96201e440b5400c000d01c1e903404d503110180c0349800c4402c06190a41c02c0f031905410142c0d40c070b421111004030b40041d1001000d00c0d80106600e80685690024040f00701849000c00740989074514500404083c070a0703840a46418442c00546802c00742c1210002364250780e42004202e02e8890748100e54428081d0300010303034200000f01d101c1102482c0084083c00300424203484589100050000a02c082c0010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 871900089 1250 871898839 871898879
    0x70f050a051609050f04200d060c09050d0b0115110d092303061f090e0a050601050a03110108071e0e090907061409040902030f010902150c0c121617060903091c0c 71
    0x1c1ca84cac2000d0015003114055000b40d803064241b02c150b480040c0c0134114082c190350202c60b5800030038818030f8080d0303040c400080c0c106d2001d004441c1c1d99941c50303a0140829013201e1034803503104004c416101c00354618405d4a13040f01d4041d046280080d41580340c10012042035004050380d507003925507840d000f90454072428544a6142c005104c02e10501400b00280780c05080d00b00d480412640c55591841411611031000f00d06100340c6000242540d802001020030100102c10241310001c800c50300240344180440c1003c3c4585103a6000c10a03200700000e590042d0b4805884891001407103a0102400d500492400c43e80191140300d0040142c0702440500c206000202c008a6104194810000c94411a08801c006d0001c288107948003400d0000f08240034503010b981040f42e43d82c91050150070141540615452282c40d0800007401464003c10301e0710a900754403d40d030250b2607074020242c0301e1040c0c2000ca07034040d003071400704080318401020b180d07882d61080c1c20f1a04070a60704c1400c2e0f941a00e030001e103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 871901339 1250 871900089 871900091
    0xe030f0f0601080606030d2111030114040f0e031204150912090b0f0406180306060b0a030e0303130b0a0f1a120a0c0605070f050a051609050f04200d06 66
    0x403c0000340401020750052400ca004d0181080c0ea0a03000700550700710088440c02a400c64100d200ba001503500440384941d0690308503540e036840d004078003023440f40c1c03000756409140340081030010344156204104681000c05c025625002e500b1245c0c0c5080c900203401a54011400d0900310407100b21446101b00e503921a040803641040300c40c0001d0204003050384042207014007082184400c030f040701c044800b0f454480c10440b00203c510700c801014130115800041403580b030f081002c07403002101805007060300031955080c8050360103a0a10342d141d00040d540296034103040c441a40c000341d41210529030241300e003440040c84002c0d452a00058030010682540300406401c0429980d08201c0703035004040e0344202c0201012490380d0b403440c07046011841713032500f004404501d6900f040341000301c24501d60340182c100d94150106050860311000020b5110300000c8038120b00140c5c4907558043caa1003040a4500d03000259169210303031925071030407071000744400301e0800e05600035070b5030498a50380396004240c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 871902589 1250 871901339 871901341
    0x201020c010203040b0628180b040e061b041203050903101518021305090603210307110f0705010513120c08010e010e0307290c1201050d02030a030e030f0f06 69
    0x181f103007194072080301161007408401c1c3c21039103200c2d48858108403040c80d01c04440d103c410b15940e000900d604840c02c0d1b070003401c102190161600005409020b020b00c0c1008d0b01e080702c00002d613040b0a202e58410f540c959240c1d00f82c80c0b404240140c02038104544058152104007642c50859400c80d2800500c0d04c1ca01000e900c801d100348084888800e0400000003800c51030403542c1003240c05000b2851041c148500d916000155654070240310800b2101001080c07003d05030a403c507015003e07002200c140740050341c80d05a4a05610000469404030408600602262801c02d001103c0c2e0383e0000d03c8042c1c1507013804000280c00a80242e0050005010b281c0342030340c05051140c12030940314441c1007040640e0400500d100c012201200702c0c0c00c6168800d107090752503512010210441040b00680c44034000f101001c0100e101070b6203000b040d40c0001c40b600f0014683e01d0394200104605400030107501a403012400d4000280200403841020000808455011100802003880d282485000c013006412201c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 871903839 1250 871902589 871902601
    0xe04051507050c150601050408010f0227060a0e041427241003080c07030501200a2304180b1c03080c0910091403060705190201020c010203040b 63
    0x129115080350741442c1981c0762a2410b21895a1100c400144100b010b21410100d03102d81c0c0580126002402132100900405038003002c900002d420003002415490b0f04180180000c000d1104141c040c2c04008100500704240c0aa049461300c800d0b0300003680065443c0030520301700c481d0040562260b0070500d0207034804a090300d044c03506001590880c410a61281e5403080b810364111241040c400001c0624540b1555142ca01e1040089560300c003520f070140014401940e1100825508180c0b8000c500900c00310001000303110503d841158034012581d03040c040c0002c100d01c9031120641c0c1003542c48480b010090705d107100800641c01a808000440484280000d1090460250004450081b036072605d0b2080c10b0404001a034030b200303a00030200013510b00090f2107516100181d500c001800b0340001074032422035202400d542c100f0700a003038003036041c4880c184c03c52800040e501c0c81800650303502401d05040032140d42c543c0da0b8042d1070100795502400181d07820002403029620540c06a0300421841c1828 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 871905089 1250 871903839 871903873
    0x80f0f1204150603020a06031e05041101080115050412030c1218090b09060d0507080610170f0c011b0203010f14060d0302301204030f030e150901060e0405 68
    0x181c502d80c258200901000076a85012000e4100d64440c10040b6103800202c00c6041303595120313405514220726000500c428000300302c1c82035602d01003c0c1c0300c00345981d0b2107a141c6070603c62900d0082c00018010402800920b140c011310141d658801d0401c40c01f01da4050f902c5208c140300054580303000501001c04065041100c1070702200130002c0c4d1400300010a03813600440c2209900070404e6014152002e00c00301048001c01c01d9000030034a00713040e100706041c00c0c100c4a900c20700742d20580c111525220030918840030040f9210700a038040600403c8071915001c01902c500303805207103480e051b161140d070280168500b806220f180c11150f40001804a05a95030004d01d543c01400c0d582c005c9a03580003040c00a0740001d140003000d442d01c40e0342c0c00d940602544954040211203010345900001052030b800c90301c08007a042c0e004501c02d4541c04030102c9040400c500b1114001e984405d40e41c011504482181111125582c00c14480360001c01d141c0d480d400000e03000e5009076001c98071a881101a82800d400d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 871906339 1250 871905089 871905113
    0x906100b0f03010b0307050c150106020c09060117060105040b040e090f061003080f1c0f0f051b0f0904060303120501080304180b0a0509090109030305090f0a080f0f1204 74
    0x20300d221403424801801c1c0e002840380014010b5060001c000000710303d05e80e01840c195500004214221280c00462004800c0122428420310016101b102c040511600e0030f104940d103c1c3c0d2046e0b4500740a03400d00441008c03548000341ca00707410720404000c080b030110812001000589401d5924600c0c5080400e50580b0301101e00484074a590030032014001404100d040007000c81e5081180240c0f1030440f880e1a0700d6910904d0600c10f03818200c0c0b5a0300741040d55940050003147c48901e405c00900c0b003c1013602064074400c03039071100511202030b0141e002120b9030000d8450214232095503402c1c40251030105040702c02030f800070380c00716911f441c41244000050140301e000d40f8981000d035080502c1c10401d11607401c6000c0001f0705641d102c01c2d0040c1c498032040804e800408000303040c0d8906003400708030f844c02050040d200ba0002814400003610041e000a110b10a502513980107000b0101d41e07803034205145d00201c0c400d074403815041000017042d0a02401034140080f803d005502c160406181a54038000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 871907589 1250 871906339 871906349
    0x3090c0f080d0c05030f03040c170a1e0f1407150306080304090b060702030d0908010c080609040605070207030515181b101205010b07050721030c020a0806090610 71
    0x8040380040c028641c0c082003110b25820781e4148900c00f020707a45840303421401075080e07101c1901000301c10081440404800281124028143c0804000043d100075450741610070010b04680e610206d159007800104d1602c4100f80d006009601c4032074165039941040c0d990f582d001c50203a601486044c84690020001220001c40038102001034a140200c2c594581c0100d04c10900e2050741c54820300702c2511000229071130340364007d081d580460024040504404003501442c40990b01c1c04000b0144d607030280300701034040c110051000303041c0e54079962814084c1400400890442c00b502c2c07000000a2000c102130303205c0d038030380f603523110f5440c5843c5010319960302040030b10808943c003190065400386922001281d4180c003c0d91583c1d030b01702700c0707100c05d440440c4060003084142c0d24120000902d410b080340949811031241d425500b42c0d9035605c030240d07043c45a03611107400104d0455000c90000c0c4c012900404814405000c100956598200081c00d005040394400e1075a04813102b0024500318510701c0c180948 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 871908839 1250 871907589 871907609
    0x40c06110a050c0904020607061b020d0e01170603070b0d0207260904050a1e0608070f030b130521030601080c0c0307200a030f03020c01091802031e0703090c 69
    0x700030361101c0c0d80c2d4004400ca91402440c0600101d015512030300211011140c12030800e10070450a0055240c0f0551060321010042c09450326007181c0520a5100d4101824141e49010300e81c0340120244c0c601c2c180203003010703900d441181c5001940b44410f401800444030200c0006071608828101107440c4c50581d1021074002c0c0ba8600101c48a46501094844035a23050720000303140e0791000711020051040c2404200c117483d440174030f20540d00c080d803c1042654004000d980082c0e68075076504119203521700005200040d0240000d2804010510740302101d4000d804403400714001010410010b8040d900e1103055800000400c0460350b0007410789500f012094400601e07100c55481119203d0164000c02417400380114020b251401d6410408100604000c1100101c80d9507850103510380280460114090300030300342d0322a055809a8804004c5807141c2541040a070203901030400207510041c0343c00c3c0120080c3d000d0300c0320500150f1026105201644000a0145c058202002c0756038a030f501c404151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 871910089 1250 871908839 871908853
    0x4020301060507080310031416080c01020705130b04090b01030b0f0412030911030708060708150d030f0203120117010b0d0f030e0619050a03240308160209040c0611 72
    0x700e0380041103a1080e908030740f2040e20781d203035078058a5281c411a4800782c2840c44400403030394011000705002942c40010b240040c1440c0c4c0d180805901c4a54140390240541c2055000300700d1802c2050a82c08224400200004c00d03045030310000e03044400210013a21007031000710050080006c0d0071441070b0041683e196414840c5066a00c01c0310345080400d5050030507480702400410803000e1a45a158081e0081c20b4480458071880c070180d45100441342d44000810341d4001c40c0d0b521f08034a0003401c0690014000896800e06520190b450403000350305041180b0040200d0302401d910b640d0154003034416202c0b40d000640e0308500203401d54031202556845252180d16480008203028080303542254181002e03034505000100080e02e074002c100c0090310642d004444103091583c071200504641c07900d0f480c00c000c0000c1e2a00d01e0310101490112448283da07000200307001040c00d070f5019200d031060303030004001c00350f040703a002c02c100300410741d01181e440030524018800c07103401000b0b018034400244020100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 871911339 1250 871910089 871910099
    0x201091e03021e040e030c15010308040605031504021603020f121605010204030506091c110d0e0307050301020d0912032315041b090e2406070c060512010504020301 72
    0x40030038a1000a100f40301110308651010500503201034840f100403c100100341da0a20030a80320b40c040300303110001d0300070703c1800c5414568010142e8140d07500005404c1c1400d050240a4030320f980043c1031880e030001c6a4012090b5603aa40c002001140d0112013080810b180301e19001e4030b000d490038015011a00010000243c082c0e01e8010b4490f05070003c5005000420796081c80f900a120b590030141441c011803041020350000081c40c51f003019010030202840c2d0350030003421510010035228114140d00304402e000035151003400744008051004065802041c0d58600107400c903802200c1e642c1680ba169080d0806004c82c440d1840c01004150500b440074103400011140200e140302c5050303640500500c00f168591000c4240300c007d8690150080042c0f0401000802c00740180480710f034002075040c10081060744001250b02c0c018030b603814800d41140f5005400b01d0100080907075594200c04180141c502191000b2640001000e054481d242e40e42a4464507002901050300041d001304c1c010401081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 871912589 1250 871911339 871911389
    0x20f0703030b12070b04080c0901060f05030411190f0909021f02030715050628050d1a0f010806101406030a09020a08010b1009081c0210020c0604020109 67
    0x80155162a0010744120740c0400501c02c48207070303c4208010311030b030705000c5601d0004d44010020b403001d12040300c1140314100100101c16a09000c2c00002079400343c00c030001140a000950f8000344101e40100d02c4a03940070101d01c054140d110099135242c0c000204018031003001d009180501032300c80c005e00203031074603802150402034140380c58107801c480c500300301081901c2841603607001a03200d1132540d8150381041000002c2d02c8150340741489030003540c456040d20341c6415090650800b81922480906207080204458080c3e20403050340c00e480b4801c1d038601e109400e030607104d12440d0504411121541440802c914201000b0295901342c1ca1041c0c052040204501019210050490f015030303880d5200351147c1c000e0103403500c00030b4114240000200f0b83d0740040d00710b5104008161002c00800310080c07401c882c8100c1c1c0d07120741c00d07064210348402c0304d035541e10b83c0780601c04d0861801201c0d004d03400504d03040c2c120b81c051008080c0b01c1d04443c00340320856a01150354002040b022202107014080564550 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 871913839 1250 871912589 871912597
    0x5062409060108090f0303070507030806030313030b0912030a060e0f0403090b13150f0f0e0d060906021c200315040504020f0a0b040306050a090b07030c030612050c040f020f 76
    0x340c14040741c0030025015413810007008030a0044c2c40e050301d4883c00c0000019151781c000480c200c01056440000810a00b40001580e0030075041051101166207035455000341410054030310009400b0b06402d501340390504d03500442c0103601c1318000041c118641050703802d0404000e00701c45210704059090101081c0d21004c1c110550341c81c41c4096a4520b50300140115803130996000e1031220188000c550304a9400c60f078030003482100c2d902e481e004180d0340442100c0020401082c1d030390220280c0758400100c0d001d03901a507034140c4507440051510341c10309840c201054107613004031030360754603a90707134181c02054207a00e4654900200c1d03001d4154144058040184c0c10b02c0b0b20280d0159a51304005415541c0c3c031300c620314207082e02404006805454821194141d842408180e550a0a00002c00c1350034a240c1f040c0c2840300d4114044c0e800a45552400318003a10130380002d4020151101004030700d440010040581c090700c103070000c140e080d41c20000e11098650614109034501e01c1440f0424001800074225 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871915089 1250 871913839 871913851
    0xe2212050307020715120507230d091b090b010806010906030e07240207050f010e330409140906070e0a0f080706020f03040308120405031605062409 65
    0xa40365500d9502c124a0f06000c2d07130240c8101954091a44520350700b00300180743c200440c15060002c0c0c2c0d00c02130181c414401c8010b0700710010b140114200040500e01000d0f0000070f001e00341c0490818000e0b00c802c411104055119501c183d200d54040240740744174810303442d40910a003404c1d003040c0742407000600402c3c5036104003014142c0300c42a00300c295070213003e008040d21705c004003500600107084190903801c1c02441e81c0c102603c503410021800e46064505101480416511100400c0e850400e0014095440180044800140d280451409006000b03441c0c0c541c1040b02c0c007500d551814148405468040c2d42c000d030100103250038801400004140c03032390700144a007826050035041a001c070301c07501115400317500100040a030205034244007081035000c03503146508580300b6150b41c129003926072280f0f1100070700300300781000300050300603a03200e844c3e43c80f900a00075641007001180a0500e04401e503801214960480410040c20800e01e0040b40d0320704c640300c0114400c3c180e02c503000c07c001c80030103048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 871916339 1250 871915089 871915097
    0x91801060903062a0e040c08010f0306110714060601080a02070c05010521090705011103120106030f1d06100f1202060702030307021008040627021003020f040e2212 72
    0x185258120704071409966244c00448070084204200380020020500c0c060200d21070740c101a03074900c40d144034928840c180c030441c41c1c82240c03403459035503504010070840341038040741402803103150085000444046009c1c140315000e07101a00c1c00200042008400401b8800040c0c8180599400b08240c010558103480003030030000d6444202d40d4080c000100380b004000031075064482048005200880e041044550a0300e41d210326003041c41c0f03102d480703004080c0d0704102081500010046280719402901d15840501c20004940c00c903400da0b1815a0401315015200d90f00000a002a010000a4200052580c54280c01d901800d1004000c5810b0702c0300360191080700046000015990f05104a452490307000300f001040d40d903404030150038080211003c1c5e070032602d410f104c900700d00800e100301c402010030b41c600050440e03003da00300310078000419481800c0641c284901480c2031101d500078006040205801040d5113001913544445402c107054036480030010400c91400213002150321940031400e820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 871917589 1250 871916339 871916351
    0x6021b0a09090f060e1f1e050403020d120b030d08060f09040b010303020f06130b090f0105190f0c1b1b06050a020c0307060e010c06180302010209180106090306 70
    0x8002031400c401600942071080ca0200c61008002c107840507950300621a00d001d11000c00300001395929030380101c205090800c801c00440780d8001301a440304190307448642c400404034002140c050211882110f080380543c0c03020a0082c10650416a01c0300350003c891001c1c00300303030071410201e6103c10100080ca800c0c0942e140100d590340da5080f410f0214010013a1046069140034185400c11000c00e01c810b80c058041c4045000c0945000b040c15441081c4203910310700200210741e40c5410582d401495101503000c0d09500315100079080c05010301a40008000301101c01e41000004111031150b00b8402055140a20081c03c80390084c03040c4404104000c0d455108140b2811704031003400b100f1504294605c0003903c04100e0b1a04140035002800c4240c0c21206074442e6072051607560943c40c000c0e140490204c0192500c1503110b05400700d8500d02c158030118203101a5030144a648021038000c03000344c1d40206110b505824801250345110b00c442110380740c25494610040d00d079540c0c43c04060311141d1103030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 871918839 1250 871917589 871917643
    0x604060302160210051317061504150311030c0301060e0a0b010908010f0c1e08060405090304030b1e09060721240509060111060c0c07050613080c06040602 68
    0x15141442e15000f400101c0401d001d032000400f50b500c20a2042c501001808011403640340310340c40500070080c2540248142d440d8602102806041040526406600c40a40191070307130048280e64000c51140101402d05211041058140a03640a000780640c1c5030440411101e81001ca4054020341c030307100c1c002035000c000c1c3c0040303c4802082c0c01010140d802d0a404000b58500c9a01c00d5000d82c0e540d9039010500c00101c10307148105110850b8032400506403201242191520740d01480c1c0000c1c40c0000c0342d10b0541c4d281d45046031088115800d807030500c070b42a0880f0349124038107030040c0c1c0040064060070842c5002e14016140040c1c407141c1e002c014544040d4600588519031003a03141b84600b40080c0c0c03110805002d4a80c152406000e0107000b8041500401e00d594060341190f02098694800380100b5500d0910034a010303049042101103a1180702c0700000c02d516494002c10800c009101c540c5d01030360812041502e41446100100e0003100208000c0151581c046a035400c0c04440d1030030140c0280e001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 871920089 1250 871918839 871918867
    0x2090705090d150501050f09042319050c01021903051c0e010506030114010b090906031c0f09060c030503040b1e0c0405130504030512070210091406060d020604060302 73
    0x808400d580100b0040c010301c0601005000d0031002c201c1c41e8005105030380c1c071101030000c0780c0c00c4031015580080b680004034000924522080c49202c10714040ea1100a10900405140110001030414030740e500c0b501ca042841020311140040c1300080c001000041c171040d0071078201601d245d0002e0708009011134104200880001c2840e009124a50140b102010072008030b4000c000964503144258a080203030b000c0c120311041a141240c039000700c40e5045c088400e013803000001c0000c0c501e503071601502400103144000140b2107110000d0556032060790305030004000e400c590070340e0060000d028240100c41c4c00240c0c48002c4960140e0300c01d21038000c940711840510101e00e43c0448002a82018108102140540d84080c00850324202d545004030b1020210907030407504143c4018000078401c1000541c1804000031756a04845244116000644c401d100003003201d948050848810b01003c003012070300c020030450300d508100100c0700d0b400b01b1034031076000561500c96445044245500811410083c0d954 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 871921339 1250 871920089 871920097
    0xa03050a030212010e010e060103050903030106030c030207081201210b07030b0402091e0a0b04080d0f0c0b07031406030d08071101060513090b01080706020322170f1e0a02090705 78
    0x41d0380f10101155850301d01104021100f40111500098413030005503030780d80f01e806014081c030031a50103546142d0038880c1c218041d10800d01d003002070540800108000400071780080c408400040c554615030750600401351080c0d0f41c0b0810701c1e524114911000c0010988170b0890a410582a09001416111031008079010b40191610326034800503011801031701c1000385504401d54017089031070806d1a40c850b41724000718000d0b8007070104a64491409418a10b0141e0030290050391203081007800d000c035075540c40c1d41521046460000081d1125a1300310708040384118650040411001b8002208100708003d110300e000800c500d040014180115000300130030742c440405007078040e22a200c4010300f913003158050041120112a20903480c000094190b40105a003801d490301c40c0d010314a04000c070000700d04294030301c841c3c0315580c0d07150000c005842c080000400030f901118001420314100ca241c511400c6c941400c0c11060b1088405010080c40b400128032008001c1c2c3c1100d905400d510b07450012905805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 871922589 1250 871921339 871921357
    0x80d0b0a120b04110a12110102010e0d0504051c0201050724020705240c0d0207030912051c21020c0a0b0712050105031f0203060102120f090414090a03050a0302 70
    0x140c512210390900010542d07141c851130103004091002c10241090000100701d52003214404140450300790002508070001c850034100520001ca2107900010140b4105076021210501188000400b041b460402d03100d45801c1c01c2600c100100080d0550300040c209118426006001071100e10f2140100541801840582031160500719103891140c5055a6261001000303140f42c5000d255001c0342c0301c0401c3c20b20601c07c40749601190304142c0c0114041d00a5000356801b2030a1250b402004152280c8203a40015010300400051100c40d40c0700030000b00a0340400715020400607038651802074120b90040c0501d01c14606000140d45c0c100c0e403104281454201034005240408400502c0120380e40051040024040b0324010020350340c0c3d070410075031340300d686040030500040c1109030118a1032075039011b10b43c41081030050711407040e01c40d20160301551001d094100004400b10f4448502d0400f80b003060380d072400d0011000042d00300704900340e40c2e0301800302c001810003100013180f505240c403d8041c1d07600b00e2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 871923839 1250 871922589 871922609
    0x4050d051c0c0204140603070b0c032107030f060614070c03060f48020a02210d1809020c030d0612111c063207110a080d0b0a 55
    0x54404000409a0b030310004141e2140341011500d400a84d0b94200075801120020010315000f46824049011908404401c2c480b50100b030007514401d0501001c11441c0f02400560aa0b4078070b411000a400c49103801040c00c003880c81c01205015964000407069a20505c840748207032500c040b443d0101c00e01403180c1009013924109100400c400096801c180f107584030211400400750002550322031007407002c1d0240b441002d185c4032001141c80002611408480d0341c2d00c1510a1140580c010451031040101030346100140401d500e035914034184075507882c01c04145020851200c02d0303034020359107050600425050560000b40c42111301e00400850340c0403007036010705000181c3c0ea518040c580120302c0200342c80b0010004040c2889250030260ba40e81c02c042c0400070390000c9000d0b07d0350f10051840340700c40048070360b0140415008045008a14041ea400306278800c9091400e01001400003030420407004540e031040c0000b00c002181c0c038041d101200c100b40d2002600030601e03800a04102c400d0750008241d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 871925089 1250 871923839 871923883
    0xd0e0f01020d14070509010302090604030203030c0a050f0a0308011509051201020c1504080d0b2d12030306031e030f0a0c020117100e04110a0608180102070804050d05 73
    0x4107401030070359030034030780070400400c0c81c945443e03801007100b102c041000070310070000016958001d601403c0d00d148013078100350034284c0700d074040381c90b543c8401c0c071642c0c450f44400742030302c10020100f0150121044d40c501600c60648a9a80a050448180103200070038180c200140302c428072940c0040d00800c401404143e40f030403001d1002d1b000b5401307000d8a20650103410303a80b06600d80c05801450045074405d914903e4070903900d180c41d0007040152a115803090842c11820f0044401d1340d420380c1c1c0c0c030001160114000c0ac0038401c0004003048504270703241940051040202c6954046035a020214100d1100007008618501c12421842030070031022201c00003044110761513a105440c481c1e2a4400c0c1c80b004204101141040e02d01003040b10b0407012611131300001c1c08085005041e20340c0003482018401540d2700c0d240c00184a10005802650009100000f04019007030007805101e0114083c030000c5150100a4480c0c0d10644100e000b0607000e003515049040401c00c003001100c3d00d00c90070588031844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 871926339 1250 871925089 871925113
    0x30a0e060c240702060f06011407030c0507350312090109081306080f060325030b0f160c08070b06010e0307060203040501020708011119050c014d0d0e 66
    0x5200043d28a0001403141000042002c00188040b87c0181416154507032400364482c0340c407100303600c01e000032000c101d038403031814000450030001e0a0141000c01d01002000c00300c1c8403a40004c0c0e4290a10340944480300c103188000d1030010007101c4a0b220781d208412025903a409115000d400380c4d4070010320510000032106207650210070303a541079403074540c0d0b0349110382c070f980034000300035141550340a51641140b032035000d010390703503882861507141c4117400c80e00080c0c0d8a860780898446c04481d01d120301c000300003c002c2404020308050503840528103240041308000d465444043c09007080040820400c00041006030b070003002103030b4175604020b0031500400d032584002903c83d000f40c400c0501500c13940002042181c07040c0160319480000c00202401d102ca40d49548801880090502040c07003c10131041c065800d00307000b500050600031084000032240c505140d041052040001c01e03645c50160b0010490440c40824880d0000d440ccd0241070301d03100c40f00f002c90000d10303a007800c145c1603121b40d502d80c1035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 871927589 1250 871926339 871926403
    0x21501030f05240609151f140d060807080d0c12210e06010b041d1b0406020c13020408100902030309040609240b1b030405060f09040e030a0e060c 64
    0x4c0708540950300386100d0348035403010301c0b05030b050749111540c8880641d91003101c0c0ca01604034070400d04203502d482000081c50030007644a03544071b204e1102200b5100c0344144005641007201c5070003414400300030f028600300755000a0406070700481c002c101d400c41e480700c010300794468115104002d19103074404000804850a440043c0340148400140780151000050661501d409603001c17104d005004224402d03a000b588907020310001c03e00203000948070300d81d000420300c550191002d40000d03002032001c606240c0030000354000c0307007584038615030042006120401020801900d001280030b00480d0b051200d100181c21406038000182d003007427628400081d410116000184004850310496107001001885d2402d840d03501c0c0a201d2400ca020801e10024501c00c503616130007544084145c1e4109030b11040001c1240c2d0100c0124004900c0c085a040150f280030f01c104081c14000b44d004618151b410140030741907011951103140702d141e0103d011181520140100c114135070040d03510074007190006103d0340c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 871928839 1250 871927589 871927591
    0x317010e0412030e1002030907080f060403180303050409020c0705060f1c0e07030b25090915210201030b060a02011407230d1b080106030b01021501030f0524 69
    0xc0c81910300070400b2900203009101e142e801d58081409400c0186100359440060340c809403046180e842a2900040d904105112426400644c83c0190a580c00d250800610141d149442000740041c41036003000000d070000304903800c0368035550001d42c40d000d5901c907507030400b0904e41c8040d41000f00020290b0000344100c00030540e01d08035a1100000d0b5511001560450f1640b01a0003000c1c0d000e01e00c2030000c0b92400c008242e00c28070850002410225401405107807541d100d1480c0046113a002c000d010602c514050704541001c00b040c0003501a14085000c2e00d4004e6080000b25000c240070f12460030b692190b004021b2442000e0045035482c50b16680090080101e0134400508402c40303000300307a60900c10743c018846151400f605240c10b203074204010002d50b02007a0280c01023a520044a4060f03100078190f01161419502c0780701e01036241c408043c064480540c00141150003552400035851840845181540d0300041c030004080e06910b413041c07807d02c5101c4024048540c98a9200324a21003403802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 871930089 1250 871928839 871928843
    0x10509121005010605270a0506160813061b05280512190c0b07050913090b01050316030519260315270c04170c031b01050d090317010e04 60
    0x1c0410306510b4061b00ca106661a00143d40001100800c1040c1d2505c07a0140501841030182c1d4821910695100310155000040c11034407540d143c4002c000390303608000540f0250110308210341604070340380c0d03465031241403499003070b52035400e2010ba07035078040f2650a000c80101c2d848801c40321804500708400344d050300500c00034230f24650031064942d02d8521681c030380140294804c00740d241380c0d120a10159550b80150491940003031902c1b020100c4251140907042e89940030715840142541094180350619192100f092035400da51501007000850003c0c051200c2130020302e8010103507c0928100740740d90020a151078064080d4610301d0700d95a0f000c00294001c04103126007000c2070003c041800b5002d440c030001000d40d0004d030000c6c0c15201d1a10f00403154004000c046043c07409e0740b1303995144100750f10004030340b040b980700072401c00c001d0504001400d09450102c0100c0e440ca050400000c005101c0c0707001104455403507020143c02c250003a013a040c1c10320502c0c20650340700d684030f5243c540300040407242 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 871931339 1250 871930089 871930117
    0x320040f030b0a15060c02010c020d0b10060206060303040302091506070c0806092b170a0606030e0616050a09090f0209011e02030301060309021309030806030d0e010509121005010605 80
    0x410103d807143e224214049055101c2d541442d89810380030ba81500c4581d50aa0611182c06070440042e9200c9511103100d0f071040c5015100c5d401e00f5507000c14004150341007102990b01c54018448242e400009480441c3d6045650b108150303200036840408013a440103441d0084004601a0300f0000c3c9040c0e0041500c2c60181182d40c035540b204401a52000076802140800071411081d40010355035040b40b83e0f0041540c00c107170b428064132961000048608603040f50499a0340d40d828480654180940741d6000d4031800105002d052240c424036082600415a0701070081c0012002da405000d984414014030440d0820407800d445074058001960000c07a100d0f0010b54410409040d18a10025002c43c00c44141d0003541541e08001c41540100031801007603900c103c0b42024400c0c0481d050190f4060f480c4a5a074039115420410305148c588425603044200b4040c1e000005034031640d009098031281d82c0210307188821280c0e625205802e00c1c1c5d000d070340d80c00007504060001c146560080c009200e11583e26807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 871932589 1250 871931339 871931341
    0x509030702031903140c1e060603150105100503130602072102010219030b01020c0a090f0b180f0406020910021c030e060a0902040b0a0f031b080a030320040f030b 71
    0x49403c041015440c401004600030000e002844d140c481c001d002c4445a03001140c5d500041601448158640f010700356525501c55010080981800d105621006040b8102c0340b0155060000040d1400002081c00040000c044002a0310b4003100e404505003d400c11011540c81170641008285800314000120a040210320508803862052080f6010400100001c1c03c950460030011000307002003109a40c114402c810642c0c1081d55022000ca0080c80c6070403001507000c00b8100c600c0c0a070344950104d035114400503da1100c8002c05810f800b80c0c82080e200540340150b541d890400d0080c0aa0700c03900e074114070511072541009070002030424001c5480d1907101e9031179803848012030035603020348850310b41c0d9001240854402030040c0c00202c0b580d48010b00c04120b500f45c036800709078805d00640c03103050b55039480e00c03040050221350802c400b07965502c440a00d4007030307003418012590b0f1444082e00904043d40d03034000e00d24480c54515402c10501e9010308442d039403a680c1345c103010181414001581c0c10700c8070700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 871933839 1250 871932589 871932613
    0x140105210f06010e1c0c090204140f010509060307180e01081516021b0303040b0c1014041109252601060c020108071101050c0c0c010314010b0d0609050903070203 71
    0x25031500301d00f2001018010044070034440803040d206004030803101030100b100c000c580c48031f01d03001800180c80da8240c03a90032800d010040040382c20100300018140039003001425081c2d00c4160449601c0255810024040412904014542c14450340b10001180f1810f00105400e2000f242900c02002401007541c2140c403101003449404825003601d03409a444250680e0b0b1441e40034499244204009059a00f02a0389001c5100903a01c82c24400459801880309003480c0741c40d52080c0943c240c159000300003145040da40300000881031040c3d480c464181080080c00301c0c15030380803507003010f044140c2c1e000d8032149043c0302814602480f40b008401e8420101c000c40e0174800c010465048442070b0340d030f01440503140e07001942d6000d0007500f42401c100000040384032035002401500d01907100c2409d21680c804415928a01b021002c1c14064101401c0c95003070784503600c142d4200f505492041082d25581d0f010b5400f41c400400c526400f4038540c40c00c140400c0800305002c40500300043c003c0d010b6600800c0300c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 871935089 1250 871933839 871933847
    0xb04150801050a170f03030421020303041e05190b01140d050a06050c041a04060f080708060f220e0c061908130f050d030b040e07140105210f0601 64
    0x240251070304103446160410104c140041c010120f000b1200c00d48100624407883c1d1070840c0c1c8216800d442c160313142c05503024020100e455954162034603101a504500b01640c801c2c1b02ea03920580d5490300314540c80c07802c0302400014403045030080064045254090300c030f86022021941d0034410240c1020140c0e12000850420240a2403001e9000c405071100032116510a4010400504449071104d0148030104050344844070b007945008480210310345a5142000050040000304e21400c204806041400a40f0740c0000e0030541007201104e1404040303a440c40801e20f0a5203010843c180398074501c501921969107a44030940b9006158241c840500350b5006100c2248181c0c0140c02d401d0ba060400762141d503100c1d40020b40c0250201c0a00300081d07000b91244c54000c42214011740e00f41d04000b09014100340c2512892166a030155418407107820079803000b0b6142d41c00343c0b00348103501d00d0118072008268800c0b41121505032803194034074040c5408079140c107803c50040b00d041c3d2405007100007007480366001e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 871936339 1250 871935089 871935091
    0x307021c05070b0121020607050f0c01090e3c010f0602010b0108040f06021303080d0f0b1012020c0105090304030606080601050d0f0222020a09050603010305070b03130602040b041508 80
    0x2140d01c8094991900e42c007085c1002c281c1d25084407500c8154804030060351070400030301c0402d000d00f00514002c85004841400c01d019072007110b06001c0781610401801122003842544110f51650b100b0095038421000c040c000c0d007809610300341c254070301c151f104001109894541607a5840d4085580142c039080140e0880300041101130114510400080008035050410303800c5600ca900c0140c10030380101400011144180c104a17071030440030880058407804d501c07880c018108210004d01001400001080355200403140b20810044155101c0c800030303507248c04903481120700c64020481842c003c90b015440303810600003140e4160601c400050b84480c0010f0081c10307104c2c010547d50b04000903645802e03960b80702c2d2a0485c1c00c4130070120a441411030010140d800520700c5031016a42d114101c900910301c0082c0e8101904c55602480107202246000030201e040d90816405282d80f0307102c40c6120783d44d5503e0800020111800000d0116401624402501c100c4484507850000800a208240c602e000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 871937589 1250 871936339 871936343
    0x1206280f03050601052e0c060920030a02060406260f010302090108030a050a0f11060c090a0801050903250c0914060f031c0309022e0507030c110a09020307021c0507 72
    0xc00385551b00321075a4900e10184040c020b042c00c07902aa8180e450501381c40780900c003903c100c040700c0301000311807000340d100c0340c00d01604030050071410301c280c0e0009071180201d0155004010000012202e201000090044521044d1172041c915282401c1d0724211a402400101e00600b401400020705407000420346901480c0d0740c4450341080c00d001e804842508000d02944100085085000c2d41240705200c1c0c54040d12806c408582d03109004410310004012592203075010760301d82002c100741c20748040309450002168280c0605100d400c204a00784805a280340502252051440002c030445aa4054900c408030440c00000ba0f0b075900e01000f010314100541e10b0b070035801619034406402079001101c01032021a080015940074982c0110355114852031903410000c0b02d405012804420300d806031070502d4100d1410616100c00c999000780211a207c1004109040020301030026503500311460300900603444d0115100d10746440d000350b64010b400d0742e0808901c2c4d090006003040f8400c004840f0304ea9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 871938839 1250 871937589 871937629
    0xb0d201207031707150e0a05011113090e030f03070c03030c08070e041d010c0302071122050405010f090f02040e0304082d03070c0810021206280f0305060105 69
    0x484030414030740c041c4e2003120100c407101035225140c080e0541601c15041603281200080007500114540302c1d00f10303105480c1c8061280b40a03c420b141080208050805072003c1c9080402c3c0c020400f44034620b540185501401e59107030100402244c2c5900c8031b811a0703d180640c0c3c00740598a10302c0c10a60702c21005940a800041c0030400900041c20190031a044032031824015030603007100c8540c0103003103c40e21100f0b41e0001b41c0004014090200590b0201f0415104484a00d1840040b00c1c1161412254612210b4070a444800080510000798400d0710b1400e20040103005201552504090544d034080040b80315518080344d00752040b80000542e800e0302c800d00c008011500d0118007011074190a8029040f148101c41803108104030b0500150902c03030720920414200c5802c00c0d05003420002e18009500b81244144414100074040044c4150006015280c00c1038000d80c5203110500042c0d503881100f8602c5440c0000654901656506011680110150b03151a62244108006025000c1958540d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 871940089 1250 871938839 871938863
    0x30106022b0806010e0d0c060210060e010f05130212070804201c060608120a0206010e090a031209020a18200a0e131e0c18090b0d20120703 61
    0x3d94001d180360b200c00c3d41c006160040440d020b94905203c0da8586d0821070041c0c00082314210544840d005650161a00404070301f8190b041c9080c8410b584954814640b207001401305880307003107107507a04036901d440ba02c00c604c4040c1d02e800c0801501c0a08140c80440d103c0c03050601c007001e102c10555144100800040103a2442004030384087c850318075545043d901c0c99914030002654803410006090000c62041c0c681d51100840711003c5c3c20b2181c160301c40f00c0103030900810004604400300d901c07000305a0500b09041e024141d203c050008014000f00250880c00949c0c002c92400703450703134400704c6682452800b03024a0401000303408a00c03080c108a50400141803214180260003003441e054001c8010f0001c5403009030707030600d55041e00c5103500f034110707000c0103448080401c41b03d5014003a401e450505000c5050441000c01091080b0544248034590345d440320b4000d216903c4c2d0f61405c80b55500885688042d941000c0b09201919500c41528032402c508001402d0441010591b001280d03084100d031003107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 871941339 1250 871940089 871940101
    0x3030e061305120330010515091504170f0f070b09060f2a011505090f07031805010b0a0e13030318020a060c050607030218010c0c030206030106022b08 66
    0x308110034400702c01c3d50005000c60340c0b40c031201d29401c0210030250450030b10820005810b10f58010011782265001e41c074500d1b95540703050443c04c116a9028010764000750101e203561801c113000c0c010782d000100400000107280520103000207400505d08600c0007911000c1c0160058180e40d40c0c994812226401e0040c40040300510f0610f020b003140440e52201285401154440400040768510780704542c1903621410b017403901000d2051003451081410a81211400c05000600050000f01140d403246e0380306c5c00158035544a41c000c0e00e03046022018110089007a40380c002d018205411355503003c3d03055800001120030300c00a485003d140400a0300c40ca43e8440c0d10101c0262220414003010300007031104080058940340107500040c10b00703a8600c000600103241140c1400e0303000d00300404243c01030245124010302041d00c00c080303c0d42401d00355442010307842c0c65004004c107544060350026000c0000602541c0108440c40c0754000b03101c4108000104072403001c990810446590002000c1c5000121 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 871942446 1107 871941339 871941349
    0x1005030c060906070215130306140c1606151d09010b01052a010207032307030f030506010e030601032901080613020105120a050103030e061305 63
    0x8400315456000035100d0045402c1d440c4500380001e0303d50215600d99008a00700725071640d9040d150030443e8643c0c50686441d2005440d00341c2080c554107144070780d205005115030b800011050501d00c124041444445510301d080b82d1455a5207d11a041020f0700303680402404082418800f4522441c04854844000703040d1804c1030f0b040c030103003445582e0058103480506030281280002000a048107100c4080030702d885003c19440082c0300000d1561180d541c0712244d003c14400042012555051105d501c11420054000340c040c6860042c003d119030025600300c1c40515241c20208484800a401c1134020307481283c503084a500401d1004030001c1282c403000030001c4000429615081d44691907400041c8810354a0300405e0600b0304585c019070903201c0000124510424a24000c030155004003800e020a40102d6003440480409140030421101c944115080b1640c00070b15040500c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 871762589 871942446 := by
  have h0 := BRFrame.cov_init 871762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 871762589 ≤ n) (h2 : n < 871942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
