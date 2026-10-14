-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2279
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:38.098848+00:00
-- url     : https://prove2.me/submissions/4f9d043f-4f96-4397-8a09-c99fbbd4758d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 409712230 ≤ n < 409892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 409713480 1250 409712230 409712293
    0x606060a050c030f04060314150306011203030e061e070206040c090203090312010b040f08071802130e1501120506010c11040207061e060503030703211b02010c0201050702 75
    0x210b403890b000900b140300c1d680340700e010398000107030000d9415095002014150303c85210240079a9445201c04401d0140c2c91049071325411160043c00009408407072200010b000380340004030b042241e0301035407512100b550803020f90182500094041d05110768001da00000301c0c0301601c1d050800359201d0b08a940b1070300503156070540200000f40304401c00c109884100d0603123a810b002559440b581100f00d80d005024901c40e8400840000c40ca4603000078884084a4515a960100b0010b001d100340081d0004003001100c15103020000804d081d001c4401c0f4050b410b45a0880000c01020001400789511419a503824a04160802c480d40e81c000070b0b04d01419400000e0403a42110703800004009102e1107000812081c501200f91550745158032043c14000020041004482d445404069880c01510001000036003c06200c8019501c9050366000d500115200861845400026850120b0141e048000145e41d5100180500e99090040075001034007400900100110a0780e40558040070000c8060300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 409714730 1250 409713480 409713487
    0x31806011508074b0903030507020f2205070807030504111908031b0d050f270604090c09090507050a0809070509040804030611030c030412090512010204170606060a05 73
    0x10460030400c6201c40c290103c0d24441d542d5190503504c0034840c03440c0541d40241415110020070305015000c801700350307a01a03c40303d060640603400c000b03207040d2414200ba00301524202e141d100c00c3c004440c1005001c403501c004140b078541983d0085c840ca000501c81000c040c208028403011130b548860740160584262109011010009034200b481d11140e48001e42600c00080c9000124003080003003102000c0d150241d070030780140d101c01100c1d1805480c45107004101c007003042c2c1004024280e089010201044803c03804062a18000342070740c3c0044e4041101c8585406180c0c5400b5404513000c4003030011441c0421036800c096a0042650045040c143c041c410b016000c502a02d0081020382c00408000b80300c270085107010b28102845400510089450781d083c5048071542d02c44540c1517a21030308ad01c00c405030840e603e035101d44060080e9103d410f0180540e00b000400e135501c6422026021503040c0c0300169880d803511070743e002a00c06400304104150004801c1c040030b66070702d408550031541d01c0d01d459501c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 409715980 1250 409714730 409714757
    0x20a06030b120f070303110625110307080a26010b1602040c0e010801230607141b030d020a050c01052817062403100b03180601150807 59
    0xd440d1210030700701e10b2030300c2003500303000c20300200240034801d8a100e40d5884d14080c103044000d40c4c1d1620b0a540300d403d00b6020400110035503023400e500e00034111741c52420f2500000e04000349401e5a0244806441e55080003032400750b290381204048980f41c84080c01d145801c110094440c24149040c01118050b00c0e0018141172812084446030103c0381d00184108045641c0100142c1030300920600140030903c040000141c203c0101d401038404c407140440008842c0066040092551150384102d131001202d03101c0003600c480c204140d0101e156240c0040e28174102c84c40400d46090312943c916405c542c04000940001100443c0a4a2150b001e00300740b901c441484100342140e03460708a180344411030038064bd02030b296000c09000ca803a2606100040345499103000d004420707002c1c5200c0c3c204012000241c3c0e20030b1040000075580300306180100360718241c403030303000c580c460f807007a00c040d01c4d080c0c0c0032440455800b0041c0200ba0040c941d81d00311001150300d8020190050000074003220500c4440ca40072107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 409717230 1250 409715980 409715989
    0x3020f04080304080a060e0a03021c03020f0327010b01021b031203070302071208060607170d0c0507060c0206010608011503090f12020601080303090a14030c120a0318020a06030b 78
    0x40180c045802030b25262501c1c0c00510341d44018a410980f1018149074031226400000702c0c5050344690198080e01d944094407c0c0800c8108641c0d0240e010541e00700064107622203540d000d540602e000d03948621044502940080d02e5540a042c1c50120b64540004442c0c00d81e0001500001c1d460034003071440e195032912000070300302901d204000c0402c41d000800c006409030305500924400303100f56800303410004200340864150004440c4070fa00103004020b240702241e102050304031022003040c000c515299001c80308070181e0b01079044000102c1d001280820400080e40142c4d04000d56510050481c0e40c900741000b050b5910600c1074481c071400001d1440507080c0b2a410030460139070090b0071020740d00c1040c40c0c80a68110140700c01030040c01184008102c0c40d001108a90081102c24002d02c00200b580e00c030510400100d20707000303090348001c0014004002d01849465100302c0c5a036142600c0c0e800c0402c0103400d6442c0d42d0f10011074142e8003035079100144c0e981c003c103405980032480c0004018a00c9008036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 409718480 1250 409717230 409717237
    0x10b13050f0d0c0e19090201080a2a090905010905270109062310030b0c0a03060e040b1f03030c0b0a090212010b1806030c1203160506010e0c1903020f 66
    0x1811420142a0100e14482130090807800b5580303002848075000694100340c0d04071030400b0700003400141c0c01d13400f0626850050f0000700031214403c19089460741c0b2417003080b1803103400621181c042250340b002046203c0240c0700b114010200000c0030301c207610780440800c00141142d6000720340003c5900c10600c2c8141c00b540b1508019034401003c21081d5030a500340c1407501c40d85031241ca14100c6000014151b0450413100e02c085035403240d0592001d84070341403840160340100c48803004150342c0381b00000e0794280510005024600640400c262800c0100130300c00c026009061070f0036002c5140c2c50800010382d00c00342d0581001d070440f0315038580d03844102d1510090042200c0103940000104d049000000c010342c801d0030b45100841d14003003010100489030306d0ba11411a103c81e4590402e03480c0d0901d44c20304a040b061000e80c1d1500b40c81c90407d0f82d0009240088500b4401c0c0c41d580c0c40800140b1511640b844840d401075105c8103604d0030314121121000340b00d0b03000740d560402c064011484585130300e8070200740c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 409719730 1250 409718480 409718483
    0x9010b0c070e010b030105120d0c1104150e04140d08070c030314040c05041a0f090a0e100207020a06092301050903070909020f0409050706050c0319030b0306010b13050f0d 75
    0xe0707265079030344043c408981003130203194421a41c23502411203906000640c400d01a0f920380303c13900000d4490320fa544421807981030f0950402d440301924994200e4003080d1002401000d05c104200b401c040c144001c503000e0380c000410060b4030400e24030071780300c4e0003801c215030000d81490a144190283d180c100c01410040e03068100404100c020301c42040780c00e132112000c0e220259070400500c4003e03146a1580040c5d0b0800c2d40d0810ba0221940c202420000d001c5503005082c8840410038820040c40c640c54a07510703e044d8865540d0100d074510851408580d1700300204002c0c0ba0030348416081034201c0c50000c403034070451030000200c038810f2807680c1d010318180c071031890b001420348109950310400d920140103880d030100e101d9100780c0c2039201c280c509882603c01c8140c000000f0b1040341d00384502991190300a03083e00c6690322060001e400c009203070722004005021f040c0d50104010440c071052500c1c1801c1a007100080010500c000c40b03101910500d84000c4440c1150003008100080000c5004035400344030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 409720980 1250 409719730 409719749
    0x3030b040519150b070602070218040804031506180b0114030c070b0f0424020706021b19120f09030c060f090b0a0f0302070201050c060a0608010e0c09010b0c07 70
    0x401140e151403161080301e84010b0031042c80201d0300c1404050310100c0320b01800403526810710161011800980c040c040d0301d840500360f442945801645403040c110121811180790304000390034020004038203520307024246443c505200c41030070105d5005c0c0403800c032503018883c9580e8010b0010903a100b1509190018516601c01c0d1303403401c10821191950b0310403101905d0580c1e00c1008140c8aa81c6040064480c41c1c000800c4640d2406040f40880e10300c0d00c1d07001d4403007102d80a00004000c603441d403008190001d00b24030031040214a40d824542860403990f0042d4550b00d100f00600041140e01c42806100045403822140b84107044109484a940e00c0d00040c194a144410100d5215006414400044d80c6c6071205031f61580c2e0b84103802e0592041c009800c0c0050881c21407402f03c18040d40140903042c1c41414a98106131b64090340901d05801140d82040564440c0400c0086000078070403112607002c190080e0080c1c0c2c18400110360140d0045c0302d1070030828000119911407400c10701c4004042c106060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 409722230 1250 409720980 409720991
    0x1030303180f030302090f010e10030e071a04060801061b020906010207031403040515071205090d050f061f05150d110705010504021309050c191206150b030402150703030b04 76
    0x1c00400035040b07000725900481443c40d68103030549c01078a055a1030b800080006015180d41e010880c00707042080030140341481801c00224101200d00101d00080f00c5a40146132903d1500500406d9000182d00110078001e1381290000e00e00d070001e0000f8140c03034041c1c500c121540c6076140100d20788a0154030107852140e50300b007a01b1400401200400844004071920070000d9080941240e240c4900003004054000100701e46030300c43e001c1c00240c04012402820543ca48415494103814030700c00643c0c00c0356507000981081104004030040e1440c0d513081c0044049075509160116910112100541200041c027188100388510705812000d00d1540c02d10078562116540d1404070b01802e0241e0303040f8440c144407218842038a00b07a00c6641e2f5070a80080c0100f80390000c61060154201e0940c1c00e00700b200c03180710404103100a05807040d0118031300c120800601c5013103c041003142a60190000d801d012420014800907998119403881e00c4018410b0302c44d92001c0074a016801812302040c1c00d43c1060401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 409723480 1250 409722230 409722233
    0xf140403060516171f120609060e03091509030c0a29070b0f1806070203040f0f05280306090807030206100e011202120f030901121401030303180f 64
    0x90300168043c168000101960642e9000c0c2680d005510312110304000f400200060203011107a002e240e030341d0120098120b40301341c03203105c0103058820065054420136141d4122101b00841c40c45892a50010030000e0350070304c01000000303050000500a60303c6102000700300c0d072111707a50034000040540300082c1501d5402d50740781da41c190555001560320150000c503105e01030740d44440b1811205c58a81c041c40ea224242c1e1121038290003680040c00200340508982e10f410000507041003600d0040c06550010342e01d40d0301e4544405181086900400031404c010601040a5110b0488180e082c00d401038100020031071b10390441803021030390350002c0c04460030050aa01071010440050038503a029a081d03070005e5680355086645c40e1200c0c42007220007040e060040028840a1580250840c0700601c2c9403501c01d0306901c401e00d00715010341801e203640c0002170030641542e00710720300b880d520752002c800f84a0103045a00c0a05508070510014082c19103820b01d110101d0b0100d40071100d9141e2010555802280c0e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 409724730 1250 409723480 409723493
    0x20c042c07080d03090201120e030d090302030d0e03040302031506220c20070303030c030b04021b0601050102060f0a18050a0605060f180a020a030b030703210e030a030f140403 77
    0x9449490660f0058010b00c0040c94400d01a0500090701a11212040d000682c1d42c3c1004020030b9000c2e10007400b0512540c034001c402c0d4002d1440c024061f5004648550a058050342112a442c614503640c2d40104010030041c1c8010a0605e80c540c60701d005110650b80f98808101203030706281d0701d0156840c1252800f80003054552155000c2403066992600310035030440d0346401c241e40d085100c00142d100301c0e0b040000034401d400c00000e00070079107408190181440d004c82d060342c000000c0c0c81c08000900c42c80c001121410007049005000900c000c003098240240f1381e005000c805401025426104c00da03100008a5090101055503030050495048003030340e0418000030401650102d11908100d40c1840b540d10303000264100112581c89150941c0e101c40030003900941c0110002024140c03261b0b0980702d959014852900290f0040880c0d0400050b40030a800c52090032268030401c0c003140d031b404000f550b140082c8036038510f40e050070029050008000c00313940d500070380d0448018844000502004000c0f1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 409725980 1250 409724730 409724743
    0xc05180402060a0c3003060605091306090905060114010201020f030f092410050102070f05130e010501170c0105070b010308090406030501051f080304080a02060d1407200d020c042c 79
    0x400807a400012175204401c80640e0013502c251f00000c0c205100790106071030314512880018018400015106659004030401c0d15411001580c1030780091004206d0441540201c001c005030900c021840c0204140b1101060701001d49584c004002000000300030240c10800f0094540c56421b081c04030428000c2c542e40c029808270b410001c0206410000681940001003490949821284000c0c20a041100307100c11084c09408003a0002d44a10410341c0f440c0080c813446000c3d001103440b05442c58040c03c64545851019103a45041140403c120b80118503100340d0541560f50140d90700b5914040c03000064050300f0260800b0341294644824030481c3c51400c91030140904104041502141c0c1d10760015840307024911038100680c10607038041c07005141010040c6880c6200ad440061000540ca400000554040720340300003040c06011180a644181031051140c0c81030480101100d4081d804001e4032070010652660142d0b450b58450b8084001400c194881524600e10300095000c442c04a0340d41c845 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 409727230 1250 409725980 409726043
    0x203130210170703020f310b07080306040504050c100801150908120c0f0a0302010902090906040f0b0c07060e071a0f190c1208040c05180402060a0c 65
    0x12800e034040c0011809800d410454200e0440700c0c440030f82d500b0340280c020b50b0000860480c00e0400300f14a950b05808683d41c003800d08040c10182000d02181d501c61507034011144c00504440710103000c29400070350740e10101da602c100e0030f03034000c9410b49483c80d10070304e00307040021490707400b1400702c43d0200220345c08a4a64100c0b80146072204003020707900c60699a10440780034040c1241c0001c1c1642c84c02c0d8909400070203110500100b10b4254065112006040120b8628120010303512000c02c4400d500d41207942c1c82d040402280030341690300300fa5076240240003a001009018000c0100040c900008070419151501d800401c00e100b0000d800440a45540c00f5002c0d415803400d6038041c07140c2400d0b081066801c1103400000c04c82c03800b404040040e54100d2403007031003070402c400304550000161071441d181c406d030003ca444901040c10145005442d02c002d580029014a955041d8504076100f01030302282c00a4058911654850150000300c41c40d1026030b801508024035808001030f50380c0a40c001010340f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 409728480 1250 409727230 409727239
    0x2120f01140105090f060f0d05070e01030606020c0904110406030b040218070c0b09030403140c01090902030601021f02040906060c0b061e0103151a040504060801090f12020a0602031302 81
    0x26a00c8500c0c0c4080541410340790342c0003c00c01c0c070003d807103414110703400c00380085e009258505040365440250b00310b5003e121101006070b180c2c030a000c903864000e090f0b0300e00c0a6090a0030310299081c850f00a603624080a907807403107003030040e02103001e203c0710520000841d0009842403040365200e040051074081c080d1001c81c002c02407140400268040d6000a80c0034901d6550340ca8008101511075400b1064080d02d6203003180400c101c0000015609411004102035000260420080310f00000d0283d600580c4512415401001000042c0c1e9000ca42c410b101584207022400e810300d2403c0f102c00a0040782c10446465161030004500030b90800c0070844624851304ca0303400b5035600c0c1c0302400140904c040324902c001c040e0802c28505513000e50483c3c01e030310300540c0081107100d6803100c00010f80340c1101180711083c3e030001000c1c411401c150044102400e1910001c0c469040940d03100341c020b400600000d409040c551100442a0388281f01c0500320a411100654030303403d04590b1000119005201207105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 409729730 1250 409728480 409728511
    0x6081605040e06040210020309100822050c1c060c091a0717090d0606031b061b020d030210050f0a0605040e1209030a02061309180f0f02130212 63
    0xd03498a8000e500c9000300c0c1d44040d142548580d400d01600107807003030469040d0300050141840d03548501d001c0c860540b203540d541c483e80d030426591b5200c07071422680b80d6120005046010303a001c90000114002440300c00e81e08112104285042c20ce004a8103000091410f07042c140344110746a4071407042019a900034102580542803184010094800d40d070307006001d080c07000240a000c0c1168400740c0352844002c0d1000c54801c200b175075014110b65090708101c5406581c5d0020801c080002e0103000b0140c1040c0c14030915101d001d64010f40c00c0d801c1803c0003031041c584420745c032003014402c2c07000f21418001c0003014007050030108a41668094100c0f18120201c3c80c2010024144c60240681035505a041e4060a1204032401c1c21304800d03405610007a0705485800000d40040e02c1d5440180420301c200b01c180c0500314109503002c070550b01c0340003201c450184051703590745c042503131501d4000d41c565100d090f00c015038905101060256154048840f0300d98408284030204c0d0280c0d40420b0710407822411013080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 409730980 1250 409729730 409729739
    0x71208191406040533060d020c011b0203040602120d06030516032009060d02061912060807061202130e0a150f0f0512010f0c020304080705090f070509040b04060816 72
    0x810010785003d50301d80d503926411300d17000701c038001c41c07418001034000e058185001100d0394800e0584e4031001d44018282e6581203400e00003030382200d4000b0741c1c0381184060740c5403900c1c11000940c3c8400310b19018101080000d0f5040c8986001d42c8010019a0302c801655a0000c142c0a402d403040e4040c4002e4800d50000100b80f508545407004c0520038800080440500e500c655080c0700000344140300c22600048100002c0d404c22010b03030950982007150390355108100c1c0b2031501800c1518260b52041805601600003404601d4000e0160407000d0020700005031220901c040807500d1442c242d00404441d0522410311950f050b154000462011840c20301c1300c0e40340ea403454038000d110f0310780c40343e48c0c400c0c00500b405000c1c0d803078804000003079408c030031002190903405222800c0407aa410407074000913030700000b81080b40c41c0707040c014400149000c50b00002c0a190040c5002c1d03207604010f102c541084000141c0340d49558950f4480d03642140081c3c0200700071510349100c0e59613658115120407a22520410001c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 409732230 1250 409730980 409731001
    0x50d170717150301090c091e050103022d040c05041706060102060a0f020405060f070c0801051b030604330f0f03020f010c060e01050f09030712081914060405 69
    0x1e0101a0314141c00240d65109080003241120b0188016815501e51000c3d501180c038081c81070014180c0342000144001c40c00908071000c00044c01c94805c81400d0000400140c1d50740c0000d81d2081096804100040c0c500080c80844040c0402c00594040c2c54540004c0b040b9038404058000e94402e001501880341e40030300e00a42d602c000701d690070b0059001000080d0341481c641c001d24501d103040e030005410191202c0000301c41c1e40205080c8102d00d0408100c03001801035030030a071030081903041c00812080c03c0c0706110040c40000d600c102d2421400c0003010079090303251f1ba4480c49a0014116228502c100c814020306134811000c074440c52290702158012540041080c0d2060440302c1c19030032211500e2441c0e0a000c0c2d00d1081d0015641403000600503480070401600805800004110000400f4600300c03c1c84a6040e01c044c00c5140ea9600078000c11001441c800f6004855426a0500d00c12903550207101d9641501350380c0200c80d4407410284000e0641401e500b403140140001c031030510203545c0301601c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 409733480 1250 409732230 409732247
    0x2061c0603060e190318170a05010b010f0c110a0302030f0a120e03070515160804060306090c0e090a1b05070c1502060a1e0903050702040501090218040506040207050d1707 75
    0x1c40d40c80c48644c071281c002405a00c0c40b4918400c02022050000e680b501c29a410b0b460702e13184902d1a402005444007040360030310910b036404109081038401c2507480d0074000c0c000e11402100070268601c1c0c940c502c0c0650b6940300c801c001181e000301260303840905499000d450b902d02e100102c454080c20090103031704500071045500c401002400070045640342404010032000a41e0b0302072113a09081000c2c1208109400c2d00e44041806080d00755074903841c1c42d400400300e803810b40c82140400c0c0303402542d890320790740f088214182080403a50300019460b84040ea1009009400048146001c1204400790300f680001c01342880b42d00488043c10040d9a41d403144010041c00d5100c400180c01c01800520803004650000b00c000b1840c14160b008801d04880c01070882e6030200040c2c011070404140b13502146464010640986402e0b0740540c20642000d00d40d80610300403544180c070682c0c8840008030213888a90555814680103802c48600781d03003c0201601d0f00408801d45c42d01c0380d0002c4000707004079000d29101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 409734730 1250 409733480 409733503
    0x1701050303070609060e1e0d021f0b18131103010c02030703230417061b180d02091003120c0f0311150703050a0606110c0105030402061c0603060e 64
    0x3851908545aa40b0001009a0002185e0440c2d80b9003400760760400422010749500e924014584040451404091a00e000d40d9021401c41d4085074888103515506488251401c42012002c08c0280c00440080c208101114004074001d449508204507441d03101c410309407042c0510141c4281401c540141400d8031001e01180c0d016a00c20424440043d22580120380e00d1012248240c005003c10400e254107644558840e20707004505029621428406018417501f051200503111140441c500605805e80150781003100140441003211801e9201c0440d0705c2e11281e402030800d079031490030420548200043d80415a14505000030210307409001c1c000c60034615400c061006000366082d44d00300c0700413141c40125400f50140410a0820a68005901c0d00803010350314041014541140c210003140c44651065040040b80141079071084404a0f402858441c02e18180f5a29038071070001c100c1c64455900c80c0384201841054841012203182d00141c25248104001d0000c4c4003c1040c866403034a07007114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 409735980 1250 409734730 409734733
    0x801140114030714070c030b07081e0601050a02460803040204020f0403020301020a030605360c0702060403050a05010b06120a05071115040b06010305040b15060d0606050a17010503 79
    0x41000b590164a040c2c408410030342c0010b05d8988240c1d81c51904404903031045610304031a00c01e10001c5904200150341c0050b80ca40b403000c1c0c008110b841c58114090180c003540c10300c24001080c0f00b10a101381b00b00c4c8082d8a03104007a41c1c41600508020b624900c416a1982e103555205031405072003407269600b04034081d0402002801c44d1115020440254413004054108410420001005031400e001a000b1040d0b80d403400586a468482802145685207900003194100104a018142400700407075500490f003000b000c03c3c40c0d480361107500551240f214081c1d07002c000413030b00004202c00042d1000069100310006d10042d1020402d004541c05500e00007032922094200284049207035600c2107620940c81c6c0740103045804c43d0f150041c102070900c101d030071500402c4000c2000307000030350300c0c15900a04203203010420b601d40340d01c41010191024241898840c62985280d00a940308000d85964001840313003007229036954803015043d5402a00c80601240310750252914580e02e458109048610140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 409737230 1250 409735980 409735987
    0xc1b04110412081606050a02070c240e1c0804080d020303070c060e0c12030d0b100e2806120e0c060d020a1809020301080f0601031a07050d0c0801140114 67
    0x2655120340c1e03003090013100300c29920101c080d00802c040e409510702034003c407000182d0302c00a50401401126807600043d559080400100c810302703a0302c10040d400c01d00c2c5072601c400c1680d0440002591001c51510030f20001c9440c41050b8140400000103000700d0742644d048613038480080000383d031039001c22100f410220b2051001c220104265800004c42d5169003004c0d100751240f280002400d5843c0344804124075800890800083c000501c56010224401c40d44440160314074100100852507441c01ca41c06440412350440b420043c549000b000b4007a2101603140c0c050321904000d01004245c02c80004070f40c1880c2c01007440540105484801c02406407026143c00d1030001100042d6004251020400450513200c4404a8098050502601e00904096600d514000c1441d2912100c1b000050080d0018070041001464028040c20b40400c2c0203c3d031001c83d41e41c000150345d64010312840200300790070110104595640201110b05880c070703a80c01914031406010045515007000b4110140e031a4040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 409738480 1250 409737230 409737233
    0x90e070512030c10021c14180f061e071b11150c0313060801180906110d060f060309030914040605100512130302030912030c1b04110412 60
    0x140c1044020340c070310450b4900a00d41880c6898aa005000c0540c001d81c042481c0d403403201081c0720412200d00700341050000c0c130b40c003541d80086504090030066401001e0502c104074001c0900200710b10440d550180c820a00d00002c5004018000016229507a4514400217050030700624414070320f00714040690500c800141e8807501c41524050840e50301c070345002004184040c1810040814407025000f8584031328204d13041c5040c070481d0f41c001c0c0f0140010710300103010030644913503482503074007040c100881d103030341e05003498030040480f43e1100094910005151501807925040034040303036082140c0c0011160f940c40110100e90185a0050004520000402c540c1300c0c030702c0f413107050104002c0000030314683d00d0000912072041c0d01484404502c0110b40d00b03240e195100011548020485000030b2001080e58000f510b0707106000b45113214402c817a0075404580801c0013920310090700e00342112540000800202e83d55109010102d101718204034401c031601c4554010344003103403211003650404135040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 409739730 1250 409738480 409738489
    0x3060a06060f270303023a0f090504050411010f0e0f0f132d020403020612040303140106200705150f19110c030604020102060a15030f0516090e0705 65
    0x140404004401c2d0f102e5400500050b10018840044d40b29400500c680441c200100d1581c0610900710180c01e25121000281d0410f8184107000e05400351030709034100c2807400011b4079980c0c3d140e080b861b00b03d803814040000304440382c09a440110000d8a9900c0d20180c401000c0781c840703070111040d81c1c0100040c03010040c64149050301c2c030f2906200500184d07000120040c902d007101d0780f20b1742100c0740321034801c481da810041c20b01c03d42003141210781042d494542107801044980c41404560a100b0100e0030008007810303c0307035002104080d00050000700c6940c0d541401010340925840f4029156102807460000740000101907084590140404074005000559041c00b60010404941448400c11240000032140104074481008980f2108010205074107c6440d249010502c5402644a1000d100160384c0000d80d041c0d0090f031035400030940021810700f410106000f03a10042c8010045001c600c1041000309003420302070f44010700543d9152395061000c042e5418100ca410351034220000074011401e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 409740980 1250 409739730 409739747
    0x40903050c0d05270d141014100b0306090604090f081612022a060418060915030c030b101e051f0909150f09020903060a06060f 56
    0x2414003a0404038000161400c000c02442800300240c000079941c0c1120720400c0c044003c0c440d0000105031340080040c0070503a512151200a45111100344609880140c02c00080b000c0b41c2d11600305105214900240189040041c0c507150907025240c007011406840c0441528403c1e0b00040c2030b00019124841440700030806500207890500c201d025660210f00c00341d0007004100084168101c80d043c05040503403450866070718403000c5411020f05503004541d11140c0e03600c04800c40f6484200b02c9103000000d0024440c075802080201e5080098072501c1071103070b10403811503401c0007046c00b4075800f6a648802549440c00300505200c0022001e0010500c0351225a03030000d191800d07900030580755030024801070040003042c0b4041101407410f0000f801d2614a0406081105c40e441041c240e9944c0003900504050013201e01103907a80082c840c0b01082d160182d802044d40404407103159441718002d1010b980660141130080c03083c80040b401e80c102e9032003039104803251684e40e5001461b1401c0304441411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 409742230 1250 409740980 409740983
    0x10915020a03090b04050c0a0e0f06010e1306080f0c010207050306040308100302150d0f180b0415110408070e01050a090e0106030c080c01030e011107030804080c030304080c060916050409 82
    0x143d40780900b0000400c1c8000315405207000d44000c01c0c010818071b0401c804400640c10110098131003a00f40408c880308840b0880e0408000d003030505035044008041102d003007482c4002c0000f2810000002601400443d000075803a03040c005071424603840350700590b610f41c0d5522489801d68028000500820320135095550032960750945680c0b20b6a80f50005801d02050241703002c82d601c00001c00003003100e07a510600c190900b88030300901a10410441c484010006c0100252103403d41c1c000240c1000780d00b40d45001401d407002400c0041c1c4030340a5103003045802c50302620300f5901c9120404900e0b1116090002e0481c1c10041c151201d0300d0030712030b01c50094840c212401c0510340d203c560200000f801e0710720300700c050200d040080440c41038500004065a1100d0035080042c1d00d00800d0403004a109021a90b01c0c90305410024000d48580c649030100c0e1080c00900318041c0004000d001c00c001d4404001c01196241d082201c003c0e48a10b00c225403143c0b526841c441d40b174201100100650708198024070b2806 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 409743480 1250 409742230 409742237
    0xf050c131503060b0403031116030c1404020c03180a0f0f120203010f05090d0306091b050a0c050105010305152202041508010216050f030a051c0905150a060602010915020a 75
    0x255903044922050381046d08110085510190407220b000780070007601c09085113200c07100410b40d01c0e58580d00c90000b014020156040c01f002c0843c0c0c80364669804a07203001c04900d0849549400b90065100703106a0100b50b1849010070110018414114082401c10b5560248581d51041d00d0900c0d602c0300a10700c420204d0b010754840c0340e0030360580103a1217001c0c800c1410030050040c00d030300d65500800300c0720f240d0081c11340c0510b0f29242844800100382107040490380d030300f8040d50b610000d480a41e40030241580c000d0182d802c0100102c1000000b240c070250341000d00c194144282c480302048034940c645000c826003040e512002c2d0401501e0190022000410150840342001d503d803201c050076a840f0b0b920311100d801503c0b03800410030904200d506108030a00300598280114400d0040c0180325002004054250b401524540c2040c0c59002e5000c01d6405411600c0310350a040e49a0100b02d0102c0e06070620340c0c642a00042d0260041c09203100d001d80c41030312101c0000900a00a00035048440c900041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 409744730 1250 409743480 409743491
    0x109030206030f0109050a06030c0e0414060c0a0e09280f0e1e030a0906030902190e061f090308031906030c08190804120501110d0f050c131503 63
    0x25071075110055010f075484004650b0550b041213800000d66038054161001546001002c00104056065107130035500110300c1064135440c4c5080c03070144401304101c0c200d4180294004c1c4020882c440700141401003c0f900c8980030322000f00100540c6076402c42d00c04189a14410440d05107600410b01d000081c103d80f90700281400e00380004908035491000340840c03c0d445a0701c0c52080c40c8185940790f0306507002c040154500782c0103943c0101f09900a00c100300c103040d190b032618421517482c141582588507000d816524090755400d00e00300c1c6c00b0b0080c0c541501501e80036100c0e403500041540307044c1c20141d10b61200640d4074503641d902d003e2075000802e00c0b06843c00c02c400100758598a402000300650080e2040c40d245820b003a02a4180095401241001032603030700c5a030001b4480b20161001c5900300c0311066541c0c540d0b400c7c070718007500001401c981c21020000d50011501c4180d88449402c600f070310b0302000300d40e68032184002584140d904800c40a4080d180421100d0020740d402425076041c0d20700030a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 409745980 1250 409744730 409744733
    0x61605070f050109090c020d05070f0b0f0601030e0f031b0f0d02030c0d03020301080c010311120f09010b0604030f0b1315060603050609070f0509010512090d031b1d010903 75
    0x10803190750003036040008020001c00442d0380c80301404000c2e0070a4130080008450303002c0040d60300e207103500d08141880030106481051002c000403000801341c10809105841c5000049840b02510840b140d501292a1003014180b140c1c0016884040740031000041d440d101d069591007007034088418015840b4824024804001c08080c4070038403000d10250001c544450b01081c86608022140015108162040c40104003003200001d00c280d20380e0003802c000036000916842202103228400080310214106e03820312010020351b000c5144521105e034000c2100041070f008100c9903115038407001d0901c144034403032400490030454200da003101c01d251500080740419568046402542482c0948c0300740c0d00e82c01041415050702410b0352049044031015518a0819030260107c201409040f00700400807400103410390080c3c048034680050740c1d9103124240752015a5a41c0e44900c0c806220002e41040e460303a801c203c05810303c62047d051038480303a003010090b100025045050034603890401c03656240000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 409747230 1250 409745980 409745983
    0x20d1b02150c22081c0e06130e13120903020f0609030f0609030304110406050d03030e010213030606080f06010b160f020405040f03030c0e06070b151002031306031a061605 75
    0x3c00e600c1c01c0c20036080303200d403600d80800e060150b041070340500d0449214103890060313480550140060320494043e610b980204000c000f4100e8541c22140c4840d5400d020301000b01006030745051054030408100b01048040c1e1030880c0c0409941c0320094021005d05001543d82c58a1405004aa5406000c0720954038484207114039000b0141d0b175000e829040082840140a4404200c1442010035502070260320703d40400f18141d08a5800d015040550300d00c4031100d140030030340450703a0340034006c00200d00080d128180800201441d10030b04140748204104035100d1140417800038100c58581d020700b414444c100c65a0500000503a9080783e980a55a50311001a0344a01c2030500503806800c404001030310710701d0b001c0c01301d0303400918034024406400360290159540404403010300c1d50100c042c0469855200500f81f400b4000c490b0940c0c40080740c903049102e140d00001416504103a06a5440840d50724032007902103400c80001e00035064450041c1150a041800081100300c404021171107074010f054440f107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 409748480 1250 409747230 409747267
    0xb0714031210090b01090902090a08011b1205131709060412050c010e100c0f0c0923042118030501020306040c021501050108060a1503020d1b02150c 65
    0x300752529000c000c1c804070100101021002d0440c0e86810060724a600300040c2510304144120841241c0009000038240c59030b000840c020030203480240041caa1000e000800c0984210000700010b403600b4094000c25411301501d805860541030580e0064850346849164074000c404141c444a010040720140307480b000014001800c0b908409003a042040c0703801c0e401d00b081e00329018100f00035034003031003000e0782c0780c61000e001040c1c1e034100021441280c1c54003994101692902410207400190700148507885908041e0070308985440040013000340c0312056000c04402e9401504003818001417401080914009001c002c1c0035081903107040f20001220262400035800c2202d41d65004030034001d82e07051074000c4810b49a0b80c3d00117030002a1255105a1052405120391030400c005100461440c3d1a00040c42000d01048030701c40d42c1e60680808068041d501c4040980030742491302c142c650302c1d91451035006001c0900c65018105040b10320008070419080640123681614040121215208400311503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 409749730 1250 409748480 409748497
    0xf1911010c1703070e1002120c12030114040c1d3a11010201091e0201051e0406080106050f0703080a063602030903042102210601090e03040b071403 65
    0xc01d6813464460001042c6141a10300300d4069180c4402c1043e5044c3c0108200f00300130410100d082e00d03060300e05901c5140c140c074a08040844503002001151185d080120400740d66400e0b142484001d071141c00031200b01c8042042040460031140f0031401a03c5c04201c4d04610b81c46080780402411500c0da0342c0301640d0343c400c0703107940d2a480304050001000341e180007442c0d45080c240000c012940d05a1140341c2102982800c842844801c0300211085a004406646039404585d00301030740000300360b50a0031160700c540900800b080c48080005540c038465011a0307611404015500e040012554095902c01d90151003144100d403580b002082c0402c41c00782c44000407072803000d5500f00000d00c00f420305402480041d00024a40100700f0007403031481c0041290215614403650301017090080d00b1001c2940e039950300095003c0d1580d40c039206012000800c0d000d19030700f80004d980b49640d03101100000c544c41800500c3c0550421f000801c80000d0700c42c09410750178001e500701801d4520122296086600c030220 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 409750980 1250 409749730 409749773
    0x603070906120605240d020d08040618090204140405060406031403070b061005120a020702040603060f18020a051e0d1406010b0c030702060304030e1e01020f1911010c 73
    0xc0660034001c882c000c1c250800d000d100b40c24400707414860f001c0b04014114002d140a84085c1b910034085440b20003002101036000340e10b16880b1515584002e00d80d0548440c06281c100c01003001040c1160144211422989010852043d0303120030010301018040044c40564095035a05000010981d03400076103070031f0016080030710307a1106149041008000301500b41030240300902c010744416604201107510710324901c4500706055a55101d10400703407041180c000d4010f41080400410018660003e800400c91400d040c08605481404040c41c1d0340c1c15000654031031104002007009040c0440b452290400c15441c0041c4466120081030441d40c8880044600180d41076181c40d1078001441010302508804403918034101c0b010030043d81c0ca00506402910035180080840d00b01030151000c0790342c6140180820108000401610038040100401c0e0344c050300400c40340050f00c1d1030100c0d407151100c01f801140ca0b09084140c071a80072030111508401d060210000f000e03000303d10000420b10400c2c4107200c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 409752230 1250 409750980 409751009
    0x180706210501150809070f0303030609050105090f0a15120b060108060607030507030e0604150903030e0609130207140a0f02130c0e0907031d03030f100f0e0603070906 73
    0x20020003010080d0180c0016501d08001403108000f10922a10302d81030341e2604030501e844041c04c1500700341e12940080389600d80d400c8004205900341c0c02c402c00300e1741ea0400800550380e891b400c1c440003030011507100c07048000c000c0000d58001001d6000140000d07181ca5480403040d12001d8802c80750b00c02800c2a591180c945003048880d40c0c0c010341d95a40040c1c103442450409032150f0f005440b40c001d9490003024415805030b0341c2001d0300d0300e1050324000d00c00c0b4000171500e200c0750704002d00710803107030300068002450307000c4c075032a45040030811a801180050700050244504c01c0700a40250091402103403110344d00003450145590800254505a00078010b110141c641c40c8100100c090051020420007030402c180c3c1924030750080b20702c0001c0366040d01d80802558034948210020308105480d01d0070040d415844599585001000d03510809803034813101c1c865120450100c2014041d4070070b03140e5280c183c0c00c1c2070295848a400403500300002408540546859040c400103546c03860300903601504001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 409753480 1250 409752230 409752257
    0x90305091003021611010c08070605070f0203030601090501051c05010308280503040204051305060108100b040e0307020d11040f02030a0506090108072c0c071a1509180706 75
    0x101c01090048218102141342a0340c81d0043c10701c0705a461006030103000d2010024809034041d02080c081ca80e030291803030b40c0e0b66043c0d01c2d240d00286019181d200004081381d844000244c000000c42c0e000d840305844001310940b50000455442c0c1c441080403282d901c8100c0b034060f984000b030240b180a903110f040c045440c0c0380a200394600542c000100d0f462000d13101e8503c58804d40d004422680c000d6010f842c0850f0076a5041c3c802d106072540e41c4001052807003894000640c08001290100c00824240010f00c42d05205400f04819034110440c1c8141d03e030410004540180f4000c4140e19032180300721281103010503402c0000d82112000304025041640000400030001da842c0301d841d501803000c50f003514155061401032503407442a4011090448000b9018805400c45490140c0f0380703080141c1451a140b415000800480d04114421159000c1206059000d45200390134103200d0103008014030650000041041866900a00b900d0240c49801c0c10b500c1c4d01c0501801604050b10306a02c4d1401c41000302c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 409754730 1250 409753480 409753489
    0xc18030f1f05130605090319020717070e01090513080a08012c0c0309010e06100e0615090108040c030b0703090c1d1b04170d23070318080109030509 65
    0x1903400718907a4500d000b04102c0b01040c401009103803160042c40c00a6140c0c0c843c0c0030140340d44114440c105045080d0051011300f941e001036041c05480309003c090b411250044030190b43c0b8800ea0048600030004140180034540665010b01d6102c6420010b034400b419054a1f000780c264802403e040000d0000c0e8010302c0140e540c00c0404c1071800301c1c0d004040064a41031400340c034004c0b003d01610540344001001c44d0594078250801c98280d111181a07802d00e040c035050350017401e16244521a00400c0000000d03002c1d1070480f0b0714504405c0303441c2d0107600d8030040d10011a511a002002150084442080403004c103040080e11031207003a054800055408103818611030b0b03008140d2103960045100100154001842020f041d00006012520804030020102c03008040c0595040000c1c401c40c40071041c00e540f000024206000c90050311034050350403101e001410102c2c110114030014040420249000074851421001c40e0f076541c07115100102d464105050944072040c600703400080004c04c81c030805107170 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 409755980 1250 409754730 409754773
    0x120406060f051c03140d14060f280b030403030506040501210b040f241104150c170408010209010e0d0b060d1505010e0403020f01050705030c18030f 65
    0x200a01d200e1006207000b0025240c02255039103025690408042a4209070040b90349aa10045c11024541c8a180f2105c49030700030017010784c01a0f400740c0ba80e00804c1d4103003003081600300c03002c8001d002d6214613800101e15203444205084507900d005680c5500040e04000e020286000d80d200390f50220b00b90a0480800040d1281a00010003014903c0c903200202d030700ea4508020780d15071080c40c0044941e914100824150540c1d000a04034814810395144410513038020070100a201c580200416101001951864000c6014442c0b814004a06400c515409680204035240c80f40304d000941c10744500742d25041d43c225030700506c2680e401080368100c075a088000e22000c40c2c41070318920204840390719403a40400d4050941c5000d4501c00d41000c0c14099041c14080c1402c003030510901255070340d2003564040030001c85c1c05400500403201c0d050784146c810b0260714000c01300c69444a0554031038400400e559440400c940c4002c10800704c0344039003500c05106c001902d202070303405801148038000f083d031a09603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 409757230 1250 409755980 409755989
    0x2010c08070f110109050706020102030403080c04180906020705070f080c12070e040c0b070c03020f0907080f0702010212090304030b1f1214011e0e01060608060d030e0612040606 78
    0x1200204000c0050b500040d5990201c031070303103041e210510140d036509004009150b000383c064014190042a400d40540085002d188640d54081490359500743e0750069019500445160030b0054040d03400d00785d4a03802114040707020b6200185000c05640e41e0515000e120343c801c0c141e009601d0390130440480d0503c4102d195a41c15605010000d00d00c40045454809601800000391203003004203041c4040000740c100074240803c4019035491311420b04101188052000701e06c01c16070b14540420600f408500140281003548505510b62580c040001c02013800403d01800c643d0300b400010001045c816103580a007800002035a5039604604100c41d8041000b01a091b054000000c40142811405003081c21500040c0f49844e9854036032410746290078540d00048403540c20b20303000b401901e084411800c03403c1400b9204201004071118080d003038400031f12540000c103019800003002800d0102031030400f01c1c031a15026206061044c00550035410601004050342d5040c0100710800000344a07010140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 409758480 1250 409757230 409757237
    0x90218090f010501210b070509030f060a06062a08160b040218091902040f02030a0b10030c230f0a180608270c0603011202130504080417070e07080702010c 68
    0x12104005c03100180c0da03035541d00a10260001c0000307000c807841102990b10f0124000c003910080044450800c7d1f582d003065650400f168600344c00051058003400c8589170418042201409402807000c3c6d40360010303080801650b043c5010800359600080801108038058403d640c14007250a150062000f00c120600c08240701003600024000d85580000c1c00720181e400d960350031821440e07144007040282c2111800988100e00103c140700740e41910b0b0308804002c10080c0c0380225900d802213400c50036038003030451400c0450403a049400c0c40009000c0703500510301900440074074090710171401d001154803075404180001c5900f0b108540c60141e002c0000002d0440c0d250800c901c0c140b11a8080100800d5221440d0709009040d441c2100b0720148035040300c10784000d110070748960303550445400102407040704034030070745c605150801d003262107121303041c000c90300b000d44281440e04140303072078038403c51200001009200d01070b00083c00784072030503031213210700c0d050740d618072880c20100800fa0949070248900b0091 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 409759730 1250 409758480 409758509
    0x606020709090b2403030a0e010206061f23070f170421141c021e061501021f021209030a0c03030b01090803040305011b02030406020709090218090f010501 68
    0x2c1580e00c1000f5812001c40440442403150402c0c0c007208010204030141e030503002c0070070418851a00180c840b20040003c1c0c00341c5a075561201c1c1005544a00326815021420341500700d80070311403261090301403162042070b00c04d400d9185001c085600f41c01c40181110045040c4942c1020000b200d0314800d0f82400c03454030641011308000d5406403102c1030b0303282c8504805030214880240055030f40d44491004d000c8065074004644041428036200c0e1001a91001d4800c0707226040d44080d820410039424046040900a1500c86082c011700c20b0859041150440c4210210706440a5940f10b0310132852400140060ba43d112406104101c100020810502d42e04180112481c2d02e401031103801013250306250000340e0940d0000103036001001e5800003103251101090103c20000c05500800c03030140701c0200b4561401c3c1c03069040340d80340315078019500145c000c40301c2040003809135081494000d20042c120140003c07140490f4203198401c40d041d90880d40a01802c888085007031041c1405041e503008607254 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 409760980 1250 409759730 409759733
    0x8011b02070b13090e0c030111042d0312080601030b06031e06040e0f0609011b050f0a0318050c0f030106052107030b040803100501020601050a27020d060602070909 72
    0x40340d424600c2000032182c2c000407110780b43c4442c50060000341c495184100500c01c03019070704c1c1e6514070003400864060341c640406d030600d094029040c2c034211010f40c2c008031810200d400341c6030b407450400b580750003111825020210002e03c82d0740140b01c03c0811951003007800d29180000609079a03c0800107405003404000b4880000281419800d080005a4030b221043c0c840401280041c02e00440361160380c024a0384403001d5003404a182c40c000e030284e0009102c41100b03082034640e49203c45200501040c000c20030004550762801c003804002d0818200003030860f103408501d00721051022022221072308a8407084a10340703000307141560300d0b4500364002c0155500303050104004020380d4010803682d00d280111031020f20820004030010303592210514500d0304052511001d1354100351500d000200880d400804c16510000b040d604031f540042684601c146446aa922040060b00348840221405403841c51007804600080c02100749620000501e5032400707400030305004041c2c00042c0300d2414450b0020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409762230 1250 409760980 409760983
    0xb01050603010e06010f0c1205070b100518070207080706050406030507110c0f03100f05190203151309140714060903070e19150e07210b12120408011b02 67
    0xc0c4d2009013800c1960800d120303e181074400302e1070080b00901d900075407654a0b8041e030741300000d003a800e071081e0810111521480c40381029507005000d01500314106194070a1204800c19200c1c0e000095401a030703040a8641035414180aa140c1000005c1440000c0801c840c0c0c0e403605c0b496078400c1c5075142041e03075000220074142d1580603819903144100c0303508542903416942401101c24100c242c4400f000021104404400942812503109030b801d2003a0010340400009802103a2241b04181824074011501004111050607050703002c0b607010707950306824800a82c00d074480c1c85c482c6020707900030185607190104e006140e0740e00018081c050078084c802405280c03400550003042c2d40308103090110a0703484d81d449282842141c10481a0103003800c4503901c0000800d007090301a80c807140c8018040d13a44440082d10304c5001032420004545503420f42a03c0e4a4003030303220003c1642e0042401c400c0381300c0005944d1826410420409403110700141c03c0210403001d114a2034240075141a0b010340450410019 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 409763480 1250 409762230 409762259
    0x4030b070c0c14130510090c0207080c090c07050a0614070c1112010b130e0c0f011205070912060510050d030c060216150209041103060604060e1302070b040b0105060301 74
    0x1840e0207003030340203043d40c55600e1480c2807140c0084504200709602d06010002c20075000d622503140c26529150104c1c0c13000c0d10209422040c0c4610400802d05841c44400307000502c1c9004081d0740c030084090000100040c800c0c0700381010203019000200d40c15204c0840414200d0b03000d400c40b0b0a100c9003450100c0054500c02ea80d611203201260000c1c420f40400701054003400c03041e5800341d40001301c4036426a1480450780701610401188007113603203055801c02400011150b145c003090129a140d02ca401e0381401c15003000d64418140d18005003d1556500171203110405104c0031241c0ca0307113a004004005075081d504800070300c0c0454004440c21400d0b100a80060000712014004e07070780005241580f4507400e0400c009151b844a844a0030740720203d0030760000d42025008a2080b4144844200c132804110181c9010310402042c030b40c03801d840c00c102030b50b40180090307005802c507189110740b2140c14014405050f5003800707003201032564038051408a00c1c0010580096100c0c01c400e0006111200040100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 409764730 1250 409763480 409763489
    0xb0109090504020a050d030503010e011509090e12030106050405040f020304080304151104060305091501052b02062a15160c02040c020d02010b040e0a02011808011104030b070c0c 78
    0x1ca540395400411036950564100d0340d000940e840e01300041503070040c0294100d410350426040d40f41d80300e80702807054820a19905002464548042c4422286a809103800781008005c5070b4664802c860f00303072035a070001d84c004e1010038070209080045003000e002e0301c503c0c050780d203c0840c50340c43c180d900e0800b10702002d40050002c100311468510542415401080341c800c8400241b0b4449968000060140408503620700c118003451183c4010000744214160607260024070400244482d158140400180c83c0380022030910032030b8010b0091b0700c4900040040010410404200d404002c42114110303100c0300d400245684074200280d03803080c4c5040070580040c400b400075000d0703001c1c2a00c02c5a000ca40020b02962003440e08402d6116550001a010754588042c1c009110f1003006104000c100c0f6120512400140c0003400c3c9040150311030000404c810412000c0014540d84a030000d40c01c503005650b8051103290006018402d1000b080314540e8095507900d8444240c052569070b080881d1414800c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 409765980 1250 409764730 409764749
    0xa0c0e0619080414100f0606111c031509020a020105090a03050405060912030c0703120c03090e091606030609051012260c0615060a0801140d06061511010b0109 70
    0x1040c10444003260f8404d1030125601104c0750305080790180340c000c0100e01c1c1b020140510b08000090700d107005503200d04108a6650103810042c104441c140604d40c10b918803a0105a51114184103215010f0026009040240310050319200c203042c000c0e007102c102402004150b4009140031000903484070498058510544a103919580040e012800742c00b01031400d508240804a1102060390000403002c2c102ca000b03555610b01c80004c1e10069a800850740703805400183c580e2810b1100415030a1620b4004000c5412540e5403142c51086144080c0d07a81c00440c00030340c803000d0806c0352074164010282c10010810311512058540998005c02840c01e1900500140e4105045083d00201d24000004e843d03801110030b94642e400144151108000c44044144c51034060400710142009425034100000d5901c03144426400c0c0f500c030300c1e003030080003165aa0244854076114000740090144070b0040c20410301e42c40f040070030108003600b10691403031480c117680c6c50300c400401d080e80d102e1080411101d00e0711 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 409767230 1250 409765980 409765997
    0x180303020901021018060c03020f09010c020d0c06020d020606040506011b02030a2102060a021201060c150207060c11010b060d0f0e0a0506010e0f1515120a0c0e0619 72
    0xc1c0181c3c101002d01e440c1d901c009144c02070140d00c0c541a00fa0020381c084c13103141c040041d09a10750040e1704170b018a9a179038454000c18400d00c0d6155000f24601040c9a0000744031500b500525a41d006100c11140c200d9401a004650003060841c2c04110160700148103e40502a611708200000c0480110b0211007425100350050102592418404a0101c61300000c0308031900c803084015104009044204100502c500e070300041801299100317490f046c000034420410981d10f0204100d40c80a4244015180020300d8062184202c40134402001f8042c4280030105022541e01c0000d490304400707051100099062003c2c250441d0303100d0044803810000d0000000c2d0103500081d2241c01070040c2c602c14065889074034842c2d018001c0008185040740d000042d0f07032143e903840440d15035244e001a1140300e000700403d00c0c80d442d42c0c940350110000d60410490440d0030150b907249007204014060302d8440405580c0e007072450160380d200352001810042500d1301450456007020281c081602480d1080821004d00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 409768480 1250 409767230 409767247
    0xf0807030e0604050304170105010315020306060c030703022b02070306021c0f05060411070b040b040f06053d090b0f1306051c0201170408090411040302031018030302 73
    0x240c0c803211080e0342440440d403143c5001d02e03206607030b82e129015112803031041000811212005000d600d050ba9484504880060402d494400181d040908002e5000f4424004494240b0080000d030024a00a5000386200e02000e00c1640343c80c3ca003c104140540a00d164a0700c031290005800401c60303a02200042c0d40c0c102e40000f01080800794140c3c144454103081c0c208500910503040319024075001c540411848030140c070f00320010304c1050070040180300e0b100c0014012134a819005a071040c0602d01d0b450814445664100031603500301c41c104080e401d80c9001c0700e00400311803030610070b80ca240440a100007000b8a282d9101c02400d116a2209a8032458105403944941d1403030201c000c03015180d4030000400300700301e0380500041d02400b8002d481912004803801c540c141000030350760701a11004049a01407121480307000f0010015140d0a50800101016032914459100c001000c0743c80c0b60307212421881014201040c3c410700d901200d040a00514184101c2c03500356016540c503040060791003416 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 409769730 1250 409768480 409768487
    0x7030e0606190506040b0301031a07090e04050c0603090303091b0307090e0a060606020601060e031b060325030c030e03030f010608040311010501090615080f01050f040b060d02070c060903030f0807 86
    0x243c2c1c1145402c5200403900189908040001c2c3d8180d03849074040071101c010040700c911000b40c04840d01c000260340340b4020402070600e4182240c0190052090f22074a07064500440c510398801e5a114445900000400c0401d401c188a1b0003000c2284184900800818000180d5603c455010321581113950791420242150304010a180039980f0900070b00415070342e00310180d143c880034403600c1c0201c1c04640304407a0320326010504840e1401c14080914110f4141d0090040c1c50300005e00412004810010f1030b15488030603030130712422401d50369001c114040b07461001000c1d200e1191101101d98003e000388406602142400b6040d0f034618909102d507595982000c40300111f50040303042142d4039180012030740c0030580d0031840540707620201040e041e4140301c60807281c2c80f5040b101c240c0d06a500328014041890180403001807654000d0001c252080740c100019295070041d000162000e5001074004100008507543c440101061b08000ca081c5295850281090b90b21807241300c1000000000203213010b01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 409770980 1250 409769730 409769779
    0xf0b1f0c0f1109070e0d08030601020a0501090b10120804140d0b16090503030712110a060203090a0c0506030906010612093e03030403110d02090a1407030e0606 70
    0x400842050424031542014440b141071014060300409003080040d10070350050f0742c0001511009420108540e005481c0d000140c3c01c0a060303181180aa0800d200c0410000d000303039035500d40078003100d10301c600b0800c0741801074291540c441d0911502207810310300452040c00680d011203e42942421000c52410001007004140d144008c2c803600941040c0501402d800050703000d94242c60300c070000c0c002d48501c1015540d01507588001c0c40164183c88156416220705410b410100110044504000da166144405d0303030000c8900c1c0b10703641d22280310002445007103c20440100415a0207038903500b820907005440740c1e030501612003844412101e050050000e603002c01c43d81c81c6c004811a924201e44007841c5d00743c01200c142401010200f40c3d6084c8100c0b074401e0b0518840e64020019450f140c81c2d9511815540ca801c3e1440b80c2c4138450380207400140c1c541031001d0703114000c810000900304201a001004c1a003015040c0c40800d850081050505040012800d8014404440c203403118048512030000e0446c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 409772230 1250 409770980 409770983
    0x15070b0c130e07090b0c060718230a05010e090403050f070f08030a1a030d120608030c100c0f05030403081503030a050d050a050402031903050f03010f03060f0b1f0c 72
    0xc0074000080c2c4000003800040c058807031542c400840d941e64101c00d51450181c2081040c440d00308201044035540900c040301c0b40c0080304007030080b810b40d43d165080010305850044282c20040050503108503d801e0034090b014010900707054a03459982804544c26110041001307042c0840004e00d030009894080540e10f0741e6901c00d5071101c20020724908903c070354000f0380350701e0714090a20034103458904410030403001c442c0b0098001c1800d003195205c100d17002c07040c10051700f198544d508c42c0030840001c00d1004145e84c180240040100c0303540c8035000001ca5080c1051107081002544403002000c1c1d0080c212500f007601490451140d40300c69002c2d51107040e00d005070ba90302d407000051480455400c0009001c1e903600e1107000300040d0396900c52107010341e041106e0080d4503030030020042d4952011504071a61070340c041d02d000b80c100159542403100300d900a80151800c8000b1100400c100400383c010b050041000204c2405504040030100e1600f10107030030712052039443d42c100400717058410a210038131117 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 409773480 1250 409772230 409772257
    0x702060d0e011808180118060c0308070305070f03020a11010903081b031015050c011109040e03121512010f050105040b0901060509010e0a1212030b15070b0c 69
    0x10405400010001c25090035485920750800704014003029903210500e1255401040440c07a01c54041a44184404503415450501560360310088074000700c030020402a00f1645c88501005440d401d0140c0382940c02004101050309102c20010081d0340900382210b140c6407401d02588035121031030b09a4204074020307600c11196292948903424160b00c400020f001c1c0584220320002054008000826488102c51040d0fa25640f20343c100b00c0d0480e1950184081c0c1d0302d80c0752450815004011003425126904684500c10601040c008142c8c5014443d5050109581004503e020340d11000040c0708540140010075140c242584c941c081e480d003080c44d041041c0018002c1120560908980380100001e005590140340740902e88500303810610041411388a903a166682002a03400046440303610401c8400d41001041600140c0351440c0100c05403600d201e00c81001c0c045101000080072030b00d40380c45440c8a0f00c800601c010149401008681a10750052401155a0754100f007030f40c00c034400c016070312009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 409774730 1250 409773480 409773487
    0x20d050a1b1202030303010506030c1e090405100312200f01090c05030111070609170406020105040501050907150c0c0503060c070c06021209040c0e040e0706020106080d0503011a070206 81
    0x40001c0c41c8601d0303608500c0e1240d08a0425200c00082001d080400002074041c0d2080005105ca444c250004c0c0d0350140c502d080041c03810705016840b00541d601c010318100082000704000340f091815000f4142d2015204c400c03e0042c44c40c548824a1000038210001c0910800900217800b20042183e48000150850200c4042d03d4490203224000c012659060310090300041000c0381d07500d0f0601a038104410701c0d050f0142030840c0f907141d00c4002d02810354100d440441c81c2c11401020b07000100944014003039500009a1403505040a5080d2440141480c40d00e402c00c400600c2207141000e11503401e01c2c02460250340351080d51814401480341a004070364144030304010810b501041d54000c0400600c0344060605041d80c8401c1a69a0040d81d8410140128180324200e614100343e440f06101200302e107400d8124010400100f070032201207800c0d07500a5084254248a210780900a0308001c01110000b40b0352440e04040c01001c034001809168605071110003e02c04102012060b41c1011382c00801003583d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 409775980 1250 409774730 409774733
    0xf06070e090c070c170a06060e0106030f060303050f0f0c12040f062c180a0203160c02131d03030a0606090605090307062f010504050c100516020d050a 66
    0x50121101001d2251080100250940d400e500c180c480c3c0e01d512018141046051255000c0e925003c0302001007140303c1c0c2d2030450082903850080100600071148145280d504005006054418410140481d80d05191007000060352207401c482c8514000f4180d60f449400851182c481131083d8804041d2a111341c400351042c10050100501c2110120014101e039a41d03111001e41e0ba00741c1308180c0c88601501c80e03a0485084071406641c1c1060760300101440c541070280e0740b4866625a080c1c07904004143e020080001c1c0040040c9515200c1d40c0500780700260b21403130350004298003060404000460340390440f1a1401c2c020b404a01d42140303460080e0380d102d00d0041038000051100e8800d03640002c0750018009022800b880c00c40d4150314001c0c014045140c10b280e001d0352008505d000301c03c01e0300f00c070601c29500c200c5082000349550400000100b0641050f0500b03518124241d20054402e600060304070b28142c0d0844200c42c442d024119640f14542141d000041c180e0316080c0d03025282e0b000f2042c0000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 409777230 1250 409775980 409775987
    0x60403150b010215011d0403030e0d02011a010c050a1e020303030a0c02070609140409030905060c01020403170a1b0203010216030e040509060712110714031c05040b07030c020f0607 79
    0x401d012070a03800c64000307600c941e814200100c000e101e41120240e980300300800f81d40c0c3d040d80f07080d80103029060101c0c800c50420403051404080d80c8000005035941c40c91481840034090026080000918164481c90034030380b0307000c1d240d9103041d0008142d0b40782603424058000506243c04030ba00d40007010340341c0f2031170034510120141c44101c401c01c005000d008000b00e1494003c8206c2c0040c1c426011070380d11101c070984c042c0301c0200319082e420340611070704440c00034003a074071040200a24920b43d0009070711280b55240018a80c00561044541c984052003001c003c29444101d403a5190750b44501c002c0c00c07071118008240240f06561228101d5a006502070060682104070249007540651701000503903200d00c0401d4441c001a1210400100000340f8813a059210340c100b011506c0c440010302d440c08032180e03501030786c200b84000840d603980c00101e0103500041e0480100f03091081e0b03040c01408a850156554802100002c0448050556900303031582464801c00203184030141120480c1c41c242000840035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 409778480 1250 409777230 409777241
    0x605042306030622110a0f05010908030c0d0c030302070c120b060406050f0d0c0e090a120e0d02040c03150e010f060c20060d02030406021e091e06040315 67
    0x580350400c50004100941400034005114802110b440e00340e03100001130406400c040250140c850080000c0d031000c159480d41c8000b00206200090005240e180c03030000340c00d1762841c0d4040703480c40e001401108840350707000c1800142c000381c91415005446040c901075000740201d50000e84a444c0840e0041014a2180b04007021315004102d0420030fa0f03100c10400041c1c034180c4c040c01d90000b04d01503188240c1e04141c0c07000c488980c07098006041a44d129031107071010320021102d2801d10f43c000000750092040e407042d0700c0350801c2540b0380095003c500e2401f00b1050010041300a014a540c0c0342900012071281c1e110094021040c10035080143d9105411007201c2400c0c011504130003854140040c40c00d0050723039200380007903102141105041c0b04001ca0012415207541464028070b040180902070740b40d034402984030700e100718001030304e40c86c040209801494507400e107007804030300401a400c4540c3d01c00c4080b05004510481080382a4006808035409010310743c0001c0c80c008a106980007580000c0c1c101c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 409779730 1250 409778480 409778531
    0xa08060f030a030c02210109080702040e0f0303040206070c15031e0b01120f02040b07201203030f06030118051c032313120e030d030c140d060504 64
    0xe4035604011004140e119950b1401c02804110b00c4400c0c000142082424008003506124800d4821190744414a00750b46030182c0403100400000745040861900344211142543c4000c024905d12490034411b941d40d2002400c040d00c100404200c400820511f15000307800780110303818074040d0400d844009009400c140c1c1241d01d40d020444103030842903c2ca0702c05c030000004140c0d95100c1c031044041c40368009019a01ea11000d840c2c00708408549042c2203402081610b00c6070100c1c444c5040010f103c4404400300f0a0707194030980905a103400000000010307640c01484050030150503450b0b050000303006000000b5204411841900c0420902c41c7c08240308405a1086051054400304100100c080311195240c40100d240501c0140e0303c0f095884a42d680d1085d034082203900030340d00c1c94071121820038407020b1200000e10b00241c800c456050a210844160405050510680c00c03804d8000d0008082e400d003104d04550041602c0410b03041540024000b0310000d0b004110b4150186a641210042d5410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 409780980 1250 409779730 409779739
    0xc02030316020c0a03150b0a0f180204050d080307110d02100f0c05040614130e070f0c03022a040f0213080c0108040602030c07020406090204080c0604031a04020607080a0806 76
    0x82901c0c040c008114000d05610040c62400e5050541d0b560702c4050750b0090304105841e42d00c0184003126100c81100101800c00300c4910602c461501101c04860300342c10000110440c0180002c0145803104401c40340c02d554001c0000713841e65150107044591403400d004031030043c420701d240001031540110345400b00c1c004003c3d00b030040340303d5a0f41c80000d84204004d19000118108030070803102e485000248810500c1c0c0c20342c2e40c5440c00341c0c118610b030070b64141c01c10460089030005002c000340d0032041000c000e00e8035081c928440500c07601c01039107070211002c5c2d442111200100021591004140c516078080004004001c2d03080904800402500089160000d145081d880032640c00d9002601070f6020105179145c4d4580d65550ba2058040e42010340010660340041c01a200169500e02030840500410840180c885140070300c05868001806928ec0c014102008148049112000030070000c40c1598425400d036100d17440810001e20030100c020300310341c0000c80c102440545c082d10580c01084100e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 409782230 1250 409780980 409781011
    0x10020310090911190b071a0901151e08011113050109180c030f020715230f060105090a091e050118110d0c1709010603050604140a060c020303 62
    0x100100407220080302c0504090100c444280ba41e140204008000418807030907091180d5581d034020780b06400a000403500b107040b551b030070110700004035003641e40309085000911150a200420b480110440e00030550094207480101d00c0310054080b4200003003880c0d0700200140c10f90315601a0450b0040c2048d020000303440c0030006000e610445100d010b5030f244c40e8152031000f503112110002824030a04107130074152500080042e51002e0310180c0b403102d02507813a0002400d40d85c9103120480701d5820318107680103901b8140c481c214520b11050396008035900c00806d41d80d10b5890060310103001b03c40c2d0300c60f80b00d602d200c00030a0301c0e001030704000c14501a5403101d80016003004948000c0c0d400c240038650071524017000c004024107140e00010004014849024900140302c6110801d0b2000300000342c000c5841414408040c400c540741c0d040d40148114001c001c01810344d40ca413510340e403001c0d1019254600c591840c800c3c540c42802110354503a4000010012000c0140c0b0107510381c0c1040301c1200d00324030b061 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 409783480 1250 409782230 409782239
    0x30f04180b0315131e151b14130f030503040806070f0e010c020a09050a0e06060d030906140f070605040b0a060e010515070503040602010204080709022508090310020310 74
    0x2850550250286200d600a940313403034200c40901c00303038902038a100381e0f0482c00c0b2031075112940040c0c411501031a8841d0118000c0d07188441554401280c44070401d0308071550005e02070740040004942d042c8165900d40e104c0e0500e00040258003590001c48101c026040c0000c100100003005004440e0080c00f42c07081c2c0d5503803c800b942d5800d043c503034100104050032a11022584601203508546200400b00b60480d40c40340f9201044407070417a0344100343d80e581c0c183d02c550f01c481000019405001195950580f807041c1c4d40c000d02c00462449804144100c41d20004191903410040d01c10015000b0500c40d1540000d0804c03001a100c10344082c2d480640200c0411403466542c000e1a0940d1040d0b0708280403a440d04060142c01c101450702c0049505080c031a0100180052005000425055001507201d80c1040240750410503d948405030803031041000d40f4102020b11740801082d4016202882c41e0380e4141080c8189201d5010b4450745401a403185000d0b0040b181e003d1170080071240414080e0540b20b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 409784730 1250 409783480 409783483
    0x9050f0c0d140a1202210f0703050307050409020f04090f02031e0c0c070807050102070b03190209010c15140112151505030f03090301290d05030f04180b03 68
    0x80ca035008912a42480045076070300c80700c1188001c6810456503c0001525400c12610200b2818001600840f000c05481c60350100b5018090014882c0c06242c036140c000c440000344a171490060601c60302000050703200b8002c0d41910020440c491b000e540d2903a14540d42002035100d0300405800d1890907203481a008024400d40388900c800003460784d444026906800308102009120404840081000c080c00c40f6040c04054020007400d8002c007091810840068102072035a0411f0300392031400d0042020820409010070a0412429030040c4c0c2c4d1120f001c0103c42d1543c64110203014420407001041c01540c03140d00c48142c001c410b81d5505401e1341c0791000301401800358000a0b003400b6a6003608054407806030300c0f03105148400499080c0996540b4042428406501481001d540011030f51038950700307080c0101c45000052100c0c4050440c218541080003030a121901c80c01440028003610070007038104121107895001c441e281d03864580e210000400c1010a600305103120381445080da140c0c0c10f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 409785980 1250 409784730 409784743
    0x103031206061d0d0204021e04090c080c03130201021507180603020406020703110406080a150f02130b03100b0c28030c0f080702040f1b140307030c020c030102030a09050f 75
    0x29800c0c54a6207582155080201013800014140e07407141d82005062819900e1469003044071141071041c0351158584004202218a0451250140001c0604000f41e800059046a0b4406d0441166110005c0a400101d281c502000401c0c0c2c40d14034002d05009413603400c100200d40b03d884840c0300300461512800220242d00492144901592082c3ca0034000150f844070307155050300002d480040d03456580c501440c50001d0703440040c1d6070007045000701080c1c076009004440348014400750a515080da051400300720411a44281c008880011010031160002c03900107600502070a9600c1c0d40b02e01c410104a5190446420114040c4003060840510000c03c05803032955250141c40300001da100c207071545900d2001841003112440790030443d000059445200c0c0e00400c0c03907150400515141c0030541c0d11900100840282e0500c0750400c03140b5052514030084aa0080d202d2502199011080c10280d2600b044142410340c503500101c1048a216020380c4060700540c0520211610030808140d50f80c1c0307822 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 409787230 1250 409785980 409786007
    0x2403071d2b110603070503090f0a1203110708160203060109060509060603070c0237210503040801050906010e0a05151201090f050a02010306171b010c0b070e0909070803070f05070509010303120606 86
    0x2c4601c42e81035522f078000e030b000600b50944c4007200740c81c0000c0350303803891515402040c1500c001c515044801d03040d801c00b00009030150040c12000c01510741404000307446a4401003180e07228040000000d9400c600c69004004059805072030609008102d102182c203c12814450820401e0b140c0b503c444c14010250b9014100c8a2075a00390300c00200000c0d036014080c0030700c0170030b5850344810080050024000d101e01c0c3c2c842c1d330040c809032960354184401c5c20361041700a80024600c0742004107204030500049001c0364409400c80e00b0400c14000645281c2c05403058031405814200d5094140e400e10402044d180c000920036a410040c2a84031418814082245000e4141c1c2e42d00a0b000b00f01c0300141070070600500b000504050140803070070740e81c2c03001c003078011101d0400140341c080895805080c0003c81e02d8001c40c000d400307050701904091620b550ba005440c400b4000d0003011131001c040c4041400080d002e04000b0740008090360710303410080c1108500000d0072021520308000084c030b00b071180280301c1e880e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 409788480 1250 409787230 409787243
    0xe0705040f0911190e07090807090b060306040b01030b060a030605090c03041205090406030c060c110603070c060b0f0d12080f06010c022403071d2b110603070503090f0a 74
    0x20542441405841e50b144d062010074480800c0c4041040340c05c2d404001c0c400c13041c56075550881c23820020030368141022988107410b21410603ca0150541d241c0050382d920140580d0001044050500128060b24507604104e40104d000180080401c2d490f801035000c0d00d009440403540c40d2211004240c0350b10013100c0150580b400e2141800215114200902885200500104042d1744070f40781c2e259140125071180001c00c104d42a5141000246c024050000303a00301c0302070741107150031140603049000400008010990301d001c1e071059951400d4030303506500c2c03028105001807403041ca04410220340d18000d0501280c01030001038250078200d580c442c4640f4040e510156881c1082d800e214101d902014035030a4a8100b03038110b0a03205420000d107215105607917850f050240685000550200300404450249041100081c3d441d11121001c603502d5462074001022030b4414180303080050351000040344e00031400003d1002859010014600a03c2c0e024161081c0c1c058107040556503007100d82d4000c210 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 409789730 1250 409788480 409788503
    0x6020c03061e06011b08180f0103050c031b0c010c02030423011709010f0e100e0105061507020a0e0703062303060f070201090f08040303091a27040e0705040f09 70
    0x25510584c0d451500102d48200520490240c0d59038888030740056032243c58034951f80e0708446c000d26060042301202c0b00c00b030804001a081403440101710b480020091114007c1a000c0c01420449200441d0403003c0030030000c010303058148a0003500d903800351103010040b0390080070011011209101c1d041c1c4845d0140c48031100042104100e83e0f81030f20041103042c0ea9566002c0745c0310b03040c1032405014081118000500314064083c241031040314502102590140c1c0360202f0409141c99802c1c1c05e810047c01020040e844c2c1915100284030444160415405180d140381842001754042e0000703030544901c6002c1c0c150701c4150890050080aa8003031541e459031200010801c020700d0180f180b90000c83c503200100d9881581d40300c1d4207040029000845904100140800626500010340c001034501c1c40a1200b80c000c1c444c801d0b500b6406400c550486622008960414804130211a868078000c05007041c40245107003201036840710031600c1028001c40c00c20b0340d0968444140d20584070b0490380028144803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 409790980 1250 409789730 409789741
    0x605100f051603090806160315060c0b06030a050304060f0215060d020d080d090f060c0207030f03030c050910020c0103050c0405060f07170309061503071508070c0c06020c03061e 78
    0x810070b140d8074040e0103120104d0302c0070503d10018491a8031a20601101d1101c8045140c1c4c000d04030740d141002c103542100c0c1910140816580075800600d06500a400804140c0311500042d0900e603c1c9900200944030000c0c000845a0b00314200e9224a24150203580c560b5209100300c04440500f100c060358040d07540b150340001403810940d0407405c0f5004036022820b101d03170864480200c505503403040c0c0c1d4001d0004e500030704200107401550f40040242c406440704038079695403e03103181921380300182031540b924908401c0c50700c240151901100024030901800f01c022201030b4852000106290000381800c0004401c94100c2c01110115400901010300d09901340803039108035000030004490303651443c225005402c0e000c80280d40900d241d500500030b40d040c5045200b100348810400c1600907000614100a08140b100c00c942c0b09021900f4002d441e540d800c0402c860f50b844404005209421000c0040341170740e40064201541d64090b0200d0300726403614281c551000020101c5814110180350014070b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 409792230 1250 409790980 409791007
    0x408030f0702010e010e03090f10080c0c0c04110c15060108070e030307171b0109110f0102010e060c0c010e01050613020a05040b0d0c1205070801031e050106090605100f05 75
    0x198010701c0d9100010702011030322201806e5503031886804502e42d0020602c0070b92481e00c060821905031040b03c1c440e102c00c82c105406850b8000040c40c0c3e5410302c2e004107500b50111400d00080d034020600a10030040d10701c8203150308281d60401541c01c011441a21040100180c80f0702c5994016030381615001c40d1380e51285000c030742900f00b880506405000c00d112a80000e03860780f020405210a80040588626040c06042c1d0381c040d400b1038031500c90f0f040c2100800450300c44c0516449440c07050340c503402d90f0816400182c2c0500340d5040c0d00aa02e00c100001c01c40c13405012406040a0700c5840000e001d400da040c404142078600c19141300794481099500340c4d0300300056900618041880d410407a0805035180c620b1b00c00d603000313030310404401c68072000d03606060b40d440340c585840445502410415820035880c02000000c0501000303140803881c80742081d01120310550f0a018581c000024007000ba100c00f03c0101610691140034024a120b0403c0d2101c07034080d11506602120076511141000f007000c800c203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 409793480 1250 409792230 409792261
    0x3051b0a0515090f030f041706040818150307021b0109140402070c0f030515010b210603011b03020c07051519030b120a0203070501031a01050d0e06040515010608040803 74
    0x40704684a004c2110920700024405814000919840280c40341e1904501010020382030085214076003200c41003100065014059490310042c103200100c4103020a80824407580e180301000c9401940030041049080d80018000d6056030010a1180ca900080c4015a030000046c06841401024520410f1071401c080d4040c104c42801307285034503078043e0345403803841900d01d0507003003543d55810200c00e000c40400026012401004460740092500b5000b0440b0701d5451a404041501e50040c4c00c0845d4442c0d03000d4001c04c660000ca02c0b81130049544c0514080e0080d403180680c2c00c140d000c0d801d400507140c54001d40c0e0711000c1222201041c54491682c00c0d580040c06162281000e0666507004400305d42c0302c2d02072021413040c180d0b0003404406d03014010140740c0210b681c00141014200740b1001d80c241d007c11a030103110741c001c2c2450b645400c0c0304106c81018202c240b80c00086841414100720a005000034210b090003c2202d1450807030741c07943e10485000c201254050b085d0729041010681014100505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 409794730 1250 409793480 409793491
    0x207020d1e44040e01030308010305070b04061b020a08061302030105090d083c040b0a090201090902161a0106170408120408070b0106030608010f1a01030b060d060303051b0a0515 78
    0x2030600e0980c0f40c012810300d00304c081e00160300017500d0400500810104000080c007800c05007184a080a1810000070520980503101e90300c032500100291046446200d401c0b00038052550541302c1c58500000ca454901441a509074403e6081c0004105039035800b0810300e2400c002c95075025203541d82ca040d00d090241c07512041680c098101060600805110000703001003008004142c42c40703052a00304042000805400c80000c18a45122040181e800c18510022103243d240d0150300c03400c10000460112040100141904007191100082d04208488241c140c03144d644882c0303051600380400801e658000c450042040d50300700004050120400346207a0300600c260740c1c051030005c4955485119a40030391108020030344400c001e0200070300a004070000400001010804040c125200360b50444000100606160f5034142c4c8852580325070089a00680b49150140201550381ca00184640c1c4100c03609050780c00e0f410340e1807926290218100c030825802a0081c03040c6a04c3c0d003030010355018003406 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 409795980 1250 409794730 409794863
    0xe010506130b0f040e12040e060f030c0123160809120703080706090204270c0512060f100503190512070f020108071b110901050a15030207020d1e 64
    0x5034600c40b604146c3c010310252224036042180c9041c032605000e03440c82511007551080e003020f42c0700b09003641c1c0841080106901c08040d0342480c048401661740d140304481c2d6000f6002040000141030000660041c82c4400003900c450403000d6510240a455141c50b0000172300941d03040010340b01040781d0f5013003c0640c07400100001a00410f10300c1d4402c15002a0710030044001d80603003200140010280100020b10301903420200203814a54603076220a8001c0089a0108008020441d99200c440a0f000640809400c07a0050f60b081c1020681200e10f40000710781c2ea104111881318440454001c1d01c040d07651000c0929a06d0302181d00641c3c20f076030014030342e1f41003000030040c0d900720700403ea070552a071902601030410b00d140c17030b0b009103c1c0019050708443c0c01020090030400001c1004403000300b0395001c501e001a1100464130010b42450800440134100a0b1682c2164800380d09480c010706d01c11744140100341c00061140490801000603011004202400400041e048820032030f0752000050380c3c00303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 409797230 1250 409795980 409795993
    0x3032706031e0a06140108090f0607020304140a030206042d1205100c0203090d051504030302030129041e0f06080708070903050c0f0d060e010506130b0f040e 69
    0x40108034a9003003207030031041003000b05995060140d9181d48594004002000a03c54a0b06000c00c80f4005180300c0c400604020b0098000b1f09000000d10a04902c0502c07101528481d06080d00020340d290800d0080d00320021400c03e5007417044c42d0040461045990281c1420304181c50a0352003100c9550003001d01d46002c0d60710104001c80f103940c000f0500502200c000544c10070405040507841c08040c00401d0322507030710b00102d03100d07503075000002d42c0c030b640a08031502c54070f9041e58607115040c00d400f03803203038030382400c021040c80701301500354004c3c41c103803942502d0504010f210b00802c27000000c1d900c5005d41c03c1c008208003d0008001f42c1001042230703984620040c207800d0740c8240300380310f90040707920020004101000340241c00758440203258001686180556145085032035954940324003180720b0748184540c1c06080e04580f82c85803280d41c240d4001408111042042809a010780811250036108042030b10090a080e411442242110180544208007118865003440001c01102c00a0000d038442c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 409798480 1250 409797230 409797307
    0xe01080703061a10030e0d0503060a051c170706140415020c01060b04080c040501050d0b0f060f04020c0a030801050315060409020102031b0c0405240d020a120b0105030f0105060303 79
    0x1241d440c080c1115036170300010100e00100c039540c1031030249900d0b0820818100140a03035a41e500803610141c440840d142145290700d81c450b0701005648080c0202480031180e45480c0d07070707080708020701a0356010f144240150700c8040d900c01ca401108890003462106019000740034080c02d540600380311400316000186098850544000c5900250f0007000190300c240d004240600341801014010135090311206010086661741c046803103401032001480145c42d50018140d41da401d40982e8120034080c1045580708050402c0b55110244030301e00350040b40701c40d000061130b405d0003d142c44cc2480311590445041c2c480004100181c95040d1050b411440180002c1c1340000540038055030b40100e03100141242c20040c8140402c0c4c542c0142603404400158140060a000c0081c603072410020480300f911301c0c40700c43c0c800910418603c2d000032030244542080301082281e0080c860f4141c450440849660400202d000c038240c0c0c808880d40d5400d9082400510b041c4021081c000580b007002194011782d00100d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 409799730 1250 409798480 409798489
    0x3032c06040b1b010506130207050705060f09030111090f0d0f02120304060909020703050403030c0f08041518150f02070806070305070f03060e07180909080c06010e01080703061a 78
    0x1030703040310103034200003c0d00b04448009100300e142403002c03d0000f07200324980440040c225441045a011701d1940016402c01004014400300d405040010304180e298201c845151010341c20006280e03020b586415000e0f41d070180c000054031f4074020000c140011000043c4180285070080c11001c0b0384035450b090080300140d0f01c1e50015089050346200071a129403030100000c140000a91204a045204120440100354448215030640307416040c407403001c15441c50003040d40803448001030712000c004600800e03907c88401c0c1d02c28015074550360307546500c1080c100103080d11429204642181414040e4144818014444400248650700665005070f9455040d10f04201085500300006551a0100503005400031010300c0444054501004030306e0070801c6c29407803004050306010078807100c10b4401a1003011141090082c10b00c020382880b80818924142400b034000c1d80109009016020002c0362152402c040d0504903080d00004080040c61a1240002452a01058450601b40f602d00d002a07458 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 409800980 1250 409799730 409799737
    0x403030212070809060a0513060e0105060103061a0405240a0c03120e100f060305030705340e04020a091506030501060f08010b09040603021c150603032c06 68
    0x98901580c0c40034200400400320200600c14000d100040c81400101c18002480682c0043ca000e03001490303848c0d10217000c40b40c043c6002c2c000c009034105080d0000703090042d040140691020f8809010468962842c0403a400034404803442014013400100300c0c600d44480745140303103403a01004001000300b0381c08483c07459003c2814100070405072100d0317404042d4429080b5250b0103c06404100c00c9003910361080c0c440c05200803c040850300e40107142c101500715400f03200195880703000c07682d80c2c0605161840e1910140f020700303500c9130740140c0e40c01000344901100e0501d00761a4851814000c0c01c2100a01e94808040d106a800031812480410300d864a4810742240440c01e00c24a105685041802800d032030050b0051310820040b6070340c183c2503e8101440314190f80d1000fa80d240c4440403100482c00402c105d17407019510000c0211003c20514180308000c01050061440200d9410341c0b04418056a0303003480020001482c07503044240002d20b03441245443e0710000b41442003d1071a1002614941 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 409802230 1250 409800980 409800983
    0x70f1e050109031d030a031808070306060e06030f0a1704030204050c0c010c0e360c1b0d1709010e060a140a0516050d020409020d06030303181509020a05030604 70
    0x2e5545000106168118103151400803610a8600002050001094443c0c00c00c0c00c00400344400c41840408444421800002400314901150f65585d901c0c10560003a107513622551071a4031124000c26020b01380403500c0007400a050005000c0000e05503201152028441c1c09140b101505200100c0140c1e0b07079000703281c080e20501d0740c0706403511014940c0e1421a00f10a03c69814040b082400905a464048d10620120100514a58503190603400c0c14200d02c90749901040024803442000300c040445406400b2440c010b400d031010072105c5a1a099440c10742c01c3c4140d003c11034900d039100b0202004403416520524440000c1100c280820f191858400c050342c081c1122612806411501d034500c12040d680042924414003d600703050809001040356640341c04200030300003038481d0250781d9540495006103803c10301190b90b04a2071400d41c000f000b40c2e000c12400030307041038103801d02d00c0d8030910801c0105030000e000c0e60b400c1084054100081c01714003000c0ba0041ca1048000403250360038030030207100d103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 409803480 1250 409802230 409802233
    0x32703010911010206130b19020c0105010806090d02070b09040e010b0306090601090e0307120c030215010e16051201150c06060e0f0f090c011d121e0c06070f1e05 71
    0x440ba000a07003000b200800500c075540210f5190340c00300b00c8462440e5080360001100000042e113100e41c10029216040d0b20607400d40c03c04000181a40001072003600c50300b071401c260790a0640320001207841355041c0c461206400401d01404d401d41c68194000ca40124040c400011940b00b918082400c000040711440516084203004104207610741c00790b0359905110030301035417400700956140c050b0150500407141c200a01120f40c48200b5000b04001e6400456070301c0031450030360707580c107400700f9000d0115044034010301c10018919405d40101d0507a0f100301010303100c11840c1da00304400a040c5168454040c410005e61031400d00c041070191103601e0180807480000652803800c00402d034a900d1000d0440c145901418081084425022511900e54130091805140304141c000c9802400b040c2c505e000c0e40d0080c00008000c3c4034100c00034905031804515000d0000c0d2010540c11903488a8201000c150060010050140010750300a440c0029a10421400d055200c405101d503500c40004181111039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 409804730 1250 409803480 409803503
    0x108072001060801062106020a0905090c0c011107110f0a2310090303090314100f0b090f13020105031801060308070c05060301050a120f0215040e010b0703020327030109 74
    0x24040207003d014042c0607034885503a00111883c02c1c86d406030038500406060345a0106200008a1180f01100001d02000b461804a4101b00d2004003040d4071030b9240001079031916601d2140d2040c00425284030607000901c0c4140c043d8110180840165042c01d4254018100366010546100600e0b40b00d0780705030344203a07030820501c14405001d00c00c9920b40100c0b0038030074401d000b0030009501181020581c0e41c4a000e415068411032452072130500e80620503d045400c02e03050811392021a4400751020404032017011541d2100000000c3d8004156010440290182400c50165015400441e003114825038400c104030f039261022401c407400d540040703411000005000c400d020b0048100c40140c0f008941c05072555241c00c0001e482c01609100d05c41d10b44003c41403034424070a400d0704a500342c6801905503a0640d032418010407540d400b070b000b0030410000c1c0300d001203100341d4400c003515091907140d00110700d400700d1142d50f0780580f095811042020b18034030710802055102800350070240391080510081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 409805980 1250 409804730 409804739
    0x160302100501030507051201020405100314100501021b03191a1e06010c0f0204050f01050307083408030d060e070809070501030e0321070e0d03050702010807200106 72
    0xc000300103036040002410040140301007800801c0b080700312481151440c1c0c4681c10300810f140a4080c40e07220741c0d845020910300403100c9415801080c0304500390310003105c2d03658900311004101c40d414091180141e10549101c02007000304985140e0001004003143c100020441c03e9003405481358104540414103225840d5952510080072500311400c102c0b80710380c1c3c10994a488840050062056040081d00d50301c5500340402802c02103e2280c0152050001c4c1c940325040c0f296208080c03013440c2c00ba100358800022100c00103d19562428a0103c01030340021541540d6560021082c0c070b0f11201d043d24000005410104000800c3c40b511032440200b4802d01d04460044c545000402e40d00c24030080758100008d407100841c0240c10f42d038003402c0004804107515803242c518028048141e500840a43e42c00c4103089010084c6403040003595510303046034004405100510004800080c082182442803800542c042e09000740e100403145844d024550440d46800306045401045141c0c59541d10410720 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 409807230 1250 409805980 409805983
    0x3130803270601060806130617010c180e0a0b040e0f0c010e18060d110a060203040f14150c10020f0d0c1b170c030408070e010504050c120417160302 65
    0x11030007410041c0c6180c2d80b50410240c56244000d00b40c074402e4926001500000713129a0040019004d40110340c0110030701030900034001c0584090b4140415400c00311052071401c01c100c1441525621044503a941d21880403140c007901d11545500d41c00b9850704110b80c808035041040c41d80510061004100940d00b0710300150180c6815010356000b162140403603600c40c1140382e10f40307402c200103940301e100c80100c9007816802c20314400140340e40100c0c12140080c0d010340c0080a0001d40740354804140007da615000907203a100c2c0c3c00c00c0280c00c0b106500c0c01d2604d116800000e00200b031650b03015945850b502d50512000c0b41c0c03042ca10340340c4000e80800c0c01c500c2118203110b20350300c180361810080c080e00030104001c01503141c200b50060146003003040d13400c401c0d5031100a0301c840804a4080744d44558403482030b00d8454a0900480c9011210785000058502e081e0003103901032241c0752003803850300000b100b1910302890000d2065964400400340c041c4494101d0f002465695519510414154841e2900a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 409808480 1250 409807230 409807291
    0x50d05041e050d0201080613060b0705100e06040f0305070507030c0e06030d02060c090a050a030b0103050607020106030c03080f160c061d0f040902010909090605190903021203130803 80
    0x20680c0000c01002400315885083e07003000b100d902400c0c60b030482da8940e40084c1c40c4252050300201c400b81018000034103401c400000e403420b00d1141c4203a5410024030590f02084810940b000301d00d65021402081c0490000d42074514a036020b454468500886920350600d4507445910031603c10581d80020425841110429038010300104c015000c0501c5051000b55903440c081c142070b409400005969083c3d41e2100040001004094445403580b90349040c20314010500344002d40b09070084100103560184103100d0f03032081e40c2d0711100280758107083d40c5030382c03031075402c072480b034041d0440d0402c0b07103040d04602c041d45401014410b03d91084117600b800d20050035910800284e090000e0003015070b00e607070f40c0e68952400d5116002e44001482c0441d90004070b036589071503401201064903081842d005e01031250401413203030740b0400740f002c000f40341d007060041110035100019005070082e01c0c11004a52003c1c0040d90803204100b10a000c64800e5112981d850f4001c0d41c10400e08048501d00380140f46055258 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 409809730 1250 409808480 409808519
    0x203030711010c021b0409020409050c090906010e1303050f131502161e150e0f0d080a08060303090a0603060f060c0203070611101802121c050d09050d0504 68
    0xa02c00e20800d038002070366600c260f85d1001c0010310100d421a425850f00e60042d060150024806c2c454820780d820550303245c0381580c3d1020f02803103040001801156002941904030b4a103903864030006d80e039041040d6004d81210340102c0c10014100040340154001c00040c2690a0f021800d80400c0c91410b108840340c2c0c04068a000d083d50404a1840610211070011108503010340c3c00c0900301e4584008035061854041d0440140380d0254000c050301d0a83c03010340420000c03400da81c0b52449101e00020045181c4026070024113101c030810008034500d1241700d5264101401a003124141100d040005400d5440c5030010b80000c0d6032150304202041002e11010000c2030746060080070202940c010070707107500b40d070300422052111413034541414140c1003210900c0c0c0711240e1010840d403155070034480109269001c060f131055514450700000140c01244507080c07010600c10f40e035113060300100e0507115038004107030702800240d41e1500c08001c83c1042c01814640055075440b035540780d060880061180546818 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 409810980 1250 409809730 409809733
    0x1d0402130c051303050c1f120f060522050c161e080c0a1106090d0b040f021507261b1e15010803070f080f0c0f100e03030603060c0903100c0203030711 66
    0x10210410390043d07400f2095004007180807503004a002c0c03504010b01080c1d44600d801c00306150031010414cd00740001811451070070b600380420b49801c607100c0464007401100b191500c4654080f0f00000d9101200c941c113620301c496030307258001c2958a588549801004a10619401c02c404001c10060007450814495030102d41142c00c003c2c4080204d0004403401c00010004a070500100d024082c08901e0800380540c01880807038589814500da100c20b07008000102c6e45e00340000918680d400c0e80b40c0d800d0070001994441181060500a80c1c40b29014144c008082c40c1d004502d100c02e503110301558103400c400030b014010b03c1000c0415000e1004940141c0c00b4117150703003051110740c001413118040e084017141c0098000392200595640254584180410898244a00c810942481c600880c22034070400b08030310100a20500b1108960b243d120444541e68941c000d440011110305442002e0044950081e0880d0703500d448140854045540e000340400259101000700010b081d03100503e40310b406013490 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 409812230 1250 409810980 409811029
    0x50108250f050405091006061d0904020d020609010306080102120402030d020d0f030c050903100606122c030f04060801140d03172802041d0402130c051303050c 70
    0x82034003989030182d0090520481e1120046410858200010150345040c1e15081080c2c030342d96134028000c406280c1503802d0350100580b410f2141c0c54051009481180c01920070300744080b041e820010b95500c841e5101d0705041e651500400c20603403d01c05400c0034010a02e2f08034441c1060300405240540300d10240045610206c02d090b18a944000c0c02a6201e80ca82030100368010724800540d01405110030f4146c0501c910904800c3d9000c8541041c011903985440703150240c0045080714056035480c01200c50500fa0b640c0300703c109a0080480c410002c4206402c2d00d04140c00c1d94101d05855019034840c40025406900601c43c0b000020700c02c0b00001c804881e0b003013401059a80150a081c0300300030800d01c07400c3c41c40010b1203c40742c003090711991801711001c0003440f107030708a1071400035003281c040c98030584030b000383c07500519812285440c002ca400804030800048a10340d0800a400c10200240410509204035680c1e400c9400d060006913100790301501e2488101024007907203d00121a990b0041080d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 409813480 1250 409812230 409812239
    0x123e07050319170705120105040501050d0212070e1608060319021e03100f110a080f070e06070605010302010e1e0d0c0806070c0c121709040f05010825 66
    0x10484040d1290321a02c00111403000e41c054440901021140046a040710200300f00ca030380c098000c00b04004000d0b010502641c0f40c40c144001c4940074011550000e031006002c0f009882c115030340c6508503c00c44104d50143c0d485452481c004041074030709864001491200e0065103400044440c0c3c080c10690007840506982c141030031a0000c07562019004040031900c041541144043c40b0340e601c1000b41c03c651110031000707600c10003000003502c0003914a2030401d111180345450341c100e80c900902a40c13a00459119500308117800d100103400d0505100118043c20a81e484d0200a0643d0782e0003140c0c0003071a503241d400050070a402100d030b12885200085401944d681c1810880500c115049d52100c1968000b0715005000404a0300410018407031082000103183d070220341c2d001585e10802c1110f103110381d10a00541ca9801d0410001e080013004c050f5041c40c400003c0c0605058800208080703480603442c481032044500a8001c0c400039001401d9020300304100540040044828001c902007482c0340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 409814730 1250 409813480 409813483
    0x15090b0906060703030b19051008010b040e19060617010603021303110f04470904030e0904030917030408060a0213170c18070e01123e0705 61
    0x700224480c803008503100013451300c00c0d80300c060041005488450312008191418540c2209446160702c40c0200148088006108900981c100e40d00720055608250925420344001d0100405151404441e216450044d0a290150030000c1085131503c2c007101d40780d6080034040f0340e4140c100105041c0100510403003070351050180401c80b50880c0401d01c00b03a813128000f41191034101c801c0b80d403183c20000340444400110020004400074030a14060303220204114100d5000e0020056040481805c021900f5003048002243d10038442d00c2e080c2c1c048960240043c0c41342c0c8040e2016800a84000020300c18440e01121068100a2200042d0b00f450b00d0300d00402e584102c0101a40003c0303401080c0001e10703141d035501040c00340c0050800e002403091104251035656114400d150301c2039008582c0091074200c0710344514014039850781c0329400d460500d00192403844143c8451411556164a04002200c1072404042d95010400084500b01e0a007015041307054800016119469810054540011030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 409815980 1250 409814730 409814749
    0x9050109020702130902061314120c130921020d02010b041104031106040b0a021b04270c0e0a020c0f01020c0717031c09060c0e090601050c0118050115090b 68
    0x11248010501a28520101f00103004104c200d0007120501030f00410310310680790040c080f140e0159001080400034003003159603020032410094101800100091055850b50004081e55004015030791200c80000f00c07980c07030b010000d50943d0040c1c01c00c000d1502d45a0b8203024120380804101e80500c020b1130039100d05c0100d8812488014800e940c0e042e011071450b100d8405030340c0101500c22015880c0d8a2105000e9241d082110010706601611502c14107280b4041c451361180051070300300d00a040600c0d402541004441c0b2a0aa03000328074100d0020382e00610ba2442c40c82100d03406d0002d612203e00340400c5141002100c200d45d026401404440290040010f180c0d0450301001010b000b000c81c60305416086204926400305910080706080e160205507400c81c030700c000d11950003045410112141210201d90340c030a082c2c0e00554400103e15a0b40c0718101800c80c1c01d454000020700d14089182050001d485020121244d9442e02c10b100c050380659021030008010f40e038000d04c40d440311440080c09010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 409817230 1250 409815980 409816009
    0x1e010f0509010212070b06101107030201030b0d120906020c0102030309030d05041401111b191202100e070e010b0c03030705160b07080103120c03140d0e07060909050109020702 77
    0x1408980d030707460340e8800c102400c11441040720740d507912900b6041ca043e004504540d880d00680b4595800301d041031258140102404d28440941030b6a41154011005025048216580f001b0301c0310500c00400c031503003180c0251003070301e0300c5c0e20010358600440a400c095200d500c080c1590070a0042022488002c42125280c40b1420400180d51ba00d61400300d0703020040313801100c8507601c0c002403258280394050013000c841c1c21049079000801c030031880c21a0b50b00e250100c502c0c2e00100d801d00fa140014908808407650001900644403000d4501040d50f080301c0031142c0c2c4100319400000100031841c90700342e110b40036010703845d00c45281c82c02040005540c0d10020b0034240c200140059280b4601d4010a0030001040d8800d00201160800c40350042a01c41c0c2800291031100107202d032016074501a10000c035100b80d0607164038400b5000c0b0003040c9000c2e0411004040001d4442c40d04100990044c09000054051074903580c450700d007841002811900160003180c0f0180c410003044c800341c0d07a0a42080d42d0300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 409818480 1250 409817230 409817237
    0x61b0b060f0d050604030f020715120504021c051c051318020f040902191d010804060e070b0703020c0a0509040609061506030902180f060d0c1d0103021e010f 69
    0x12894400401d02d02c07040d11001520601902c0240000c1640c840b40803540303e031442c1e00301c4070700329165008540c0c441d101c01030310740100b843c4070000030700000070350800c0f41d20600080114000c140c0c19000d401100b071040d20211607a070040082e100400c00c6150b01c200c540c4c0700614140c1c0c01c5c110001c000506590403809a460072015850701200403903e25011149440000b007281034071103a0724800d5070301035000329103014103814110385580c110034865000640704007a03e49104444a03110b600542d18040c0141040d110a80c4502001e0851402045201d000b822421941359484d829030034001d007452840f00c0414403814522100f0030169680d00f0403640c0090304032500241c407610f5841c0c420020400055203000d580e034403050004280d80c05500400502e4000d80300707507c48168400c084500f00404403481e0a0728548040461280c0c107201d4180d0420603c24000040b02a0310703441f070300c14403a04189580517021030b048018021030420704207100b10642c00d80b20b4640003901c0306002900700b440c8050b108041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 409819730 1250 409818480 409818499
    0x50a0816140a0e090f060d03051b030d050402030606100f050f041e050a0e13060c2007290a0509030a0501060306020403110d050d050c1608060f0c071203090c1d01061b0b06 75
    0x324a070342c028079602c52b2003200c200d9694400c0106124040c15003281d0076031181c021440052680c0c2000ba846482c058419514490340c01035020099513170f0341240c1e020300c80c0d080e01400046144404440d13820201e00703403e219070000d01d1810f030800c000300c1c0c0c07140c0110211904417010b20241007041c6405a03842035208101041f80148040100c4075518a4144441190f60b60106080c50140200c0e02101707a8481fa00c000c12810078411360700e03258441e2910656210700e01007100c414420312660140c0074401d8014190b44640075140c03101801e41c4c03040d0b00203950340c031ba0000d41003013001410203171040c080c501660a001c0700740351500c500751031b40b000b000c90304d062150014804041c9001408203080e64a070819800700040c0d1111b070135694a0344100c500c00c41c1241400c003c10030700c2c1840382c01d031402c0580c0880c0c40c3c00c00c2c00008400b28041c1003484e8040b43c1204000300b01040020860510003000290003140415a624101c002412400103607140a0610707525400c5002007075580d01419408281610301000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 409820980 1250 409819730 409819747
    0x207050904060f050709081612020904061515170705033603071b030206160303060b03130501060506090a031707050d090e07050a0816140a0e090f060d0305 68
    0x141444005400c0c0c007500c2c00313041000b901d42000700e2100343d400711400c4500e2071400c000a5910b60703003240034210f0009450030121005160541000d40d101e40700d840b01003040c81c03404089145022554006d604941d41d0900d4006c070150b40015001043c124000b0142c400d410258030140052201a002e42c02e0128180040ea4030f1045c0c800f00740442108409400700950f41c41344d2019129048090100d5414440003000c0040c00c081c0072100003500d07002070a0078a4800720030549100000001030407014940c40d0340c000101120001d01640c4208410644107007409040d180050844259402c01e85c4140c60a00c0804e80948890000500782ca034460020541780c0202e0148030030500a0400040c958403451840103400d5602814401c00c6070058007030700c016600d0301201907805004044400300003c00e042d000031300c840602e2148450300015410102c5102c41c030084c00d01416440401218007050b0103040040306070502c1070401d0b52000380c039010b1042c641400b00004001e4070180364042d041100104600b030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 409822230 1250 409820980 409820993
    0x30206091203180115120201081506030115020a0c15180e13060207080f04050a0f0303021002090f0a030506190e0c01080603121c0b0f0a0905100b0c0609010b100207050904 75
    0x11181c181ca020705105c150b840c00a1402c001060000328000781008000c500e4504110118182c0b005000b050345045030b003400082d500302c03140c690500d4218441c0c0c24010b0049a13280c08103c000d03103440004244c02d99103180010700600014a0791080a0701030302010441c400c0d41007a9147c0000302c1c1d0400c8000040c003800c101010f406004d5024051160025190320000c12000c01802294010348058003541c2d036400d1848018540c0384400f6000d40c01c0081c502d1003a03011580149400c1038014400d131007010101001c5024054035030011070b0a640444117100000c1c3c074902c00c04500c002840700510007003036074542050702d508a10719842e060186250110701256070501c82d50205039581c000c081d44030b442c024005000a00d00000c00c107070700d510341421000c9604201581d030740c204001070b096180c801d28103407040000b003100804d04844c0071211140410350300060002002e032a46881c0080101c1d0038500036040c00c640d80c20240358072420400c1a4003403810380104e9068100c800840304000c030742d56641400d6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 409823480 1250 409822230 409822241
    0x52b1d21070302011407050705091918061d10050a0b060c010b040b0607031d1c05030c0f06010515031009090803190e0307020d0203100e0a0302060912031801 69
    0x540c00c0400305541400c920100141d0302088034001d0340d400054801303000400555205a000c0600250054101408039040000040d5001a44503c0600310a01803110480450b80d601020a10314a1042c958109000740d41c090080210b00c000701d40c40e26201c81c0c2819a9542600e108142451030b150300000348800120b071300488103164040c00007540c1b4800c105900c3d0007440710003c0a48264900010b00446040840c1a285241c0c3c0c1a241c80c2081075010103100d00d00300402018a030f2000c10740040d03810343c1c055007914488192198000710340310000241e00500704036141c5c82d68900740d4001001000582d840c04241c0842001d1070201c01d559854401c000d08190900d0382100350300c2c9040204141c200086103000310302c14000c0b2281942000c0010040ca02540d6101480b0120b075401072000c4070140c50020b800740201c5100a084510218030035850505807100480007100700d4000005c03180502d50107011084d4049500300c050400d2040d004022442400007803c1802c018050b1120307010441000d5110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 409824730 1250 409823480 409823509
    0x60902040e072702120c070501200711060307080f04050a0512040e06150f09040b130e060a022a03091e030106060c0f030804030516052b1d 61
    0x140c0d1082c54640715144100300c0212800344101c40c60340b002a01c40340c0b2600c00d407145c042002d400d601294450003520aa6600b1001050381c26550798120307407180002a40c840401c0c0d2810410740354442d0003a00f044c0598140310112540102410020081b650b9808000d05510102403410555652541d0406030320301920300100030b082e8030039480d080502c42c0304e1304040c20465041c0d2035421142c0e0b481e032052003044541503d0702c1d0500780041c094003246108240187c49079100c00303040091006104c100140000c410103201e81292030759403030200c1480340700344101c0d5480b449030b660039481c240c903c202c0e40c0c10245034568030481c0140703402e240a98003803090040707801c12000209903241902e042685010780550011105100758038281000803418010b070615188240c007c1414600e28010b502c050710781c61f00040c4103c04120b0100a000b51142281e039090040d540182c00803c59400d5454400d803003188000d021003030f451200b8a0748500c0d158024000c07441c00c1481d20301c3d0b14540d1684008101d201000380d07103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 409825980 1250 409824730 409824733
    0x90f021c0b09010519200c12040b04141c060510120c0503060912040e101203050403110f130e0c0d1103060c0a0503131a0403030218030c010c060902040e 67
    0x40c4080c0c40015000031740540c1580070410300c00802d5078409401c4a845142e03c50060210b40d10311982014000003805108401e40c05a07041c04009005501d607030360140d040000c00860100d02440160211403a01c140f03c0c200351002c0100700302035541e2001820365010000d0100b900c0f07000040c001ca40040d0410001c1c00030400b149900b2400c0c0c502000d00903581d000c2e0314064401e51000441c20400020030007505800f1080b41454581022041c00c6580c2c00101030881501e0f00c6c1d00c000441c1182c1d8658509030324001c1e5201a141c0b8150316001c40301550200f8418420078030101010b2090b0317240e4190b0007801100740000110030101e82c540a003031818106e585580900482500300500100034007030351080703204a05850b0540e4580c10000d407540104208940015001c0c400907001c8294440b4080c03019018665405085140c5045400b514030100d03800c60010381c004c21082d00950690700030000130312040380504603100030000001c0403040e030644c1c080e107000d4880e80d0102c1552a0769000500c000705640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 409827230 1250 409825980 409826003
    0x7031a19020a050d0603140f1c0c02030c090f0708010503010b061207230d0509030a051b030903031b06070905030d120902130b0102060c040e0601080c131401030c03090f021c 76
    0x18a0030000320f82c087d1181c40341c040c150309602d50000119511340840203411811414201a00c01103450b00c1181000301c0c0c16101380000045141e890790340b114032408500c0080c0d1114a403804008041c020113900a43c02a8101144141165140d40079101071400000c08000690740b020811104007624141c282103104603a0a0a03d030118210010a442c5039200b806000030744034104583c1d5a44158450140000d41c1440000d01ca68480c1c102c200e05440482e044a0501a0000002c0c5c21075211a840c0194000f501c820750b103c2071414050b01d43d200a560900310340317540c0340c07001190b140c03128040e4600c100480803141030144106940b0201c65240c01030a52001e002180410304c008025400ca12805885003600003011a0300c003000b05c03000d413040c802d00050345448810040d81ca101c03000d080003c001105121000c810322029140e1001042c0c9600840044012100054115a050141e4000300760610b512540403a54284400310060742c1910a00c601c21440125000000d00041000340260f5125 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 409828480 1250 409827230 409827233
    0x60705030403050a2d0f1407020d080c0105090c0406060509150d0e1606090f12020405060103020d09061d0a080f07080906040602061f0303021b0102010b0d030207031a19020a050d0603 80
    0x450300b8200e11009840c0c07906d042c1403030041611060040145101118802c010700801070501c4021008003c2c851103450307040c00c1ea1118000c6c02d4410840b0011071640c8250810341e154a840d0083c0d000408290810925128156003c1a041002d00c421403d4600c00028020034003012079000441f501c20384010345039606081d00300640348240d18807540001400c03c3c44049203400c1d021008202b211403110700d6207410303141c07a42804046d02d00184542d040c140d09103e00c1e8110021401000040707407181c200000e00850158924020400c2801501d035076038442900f810002c0c5500003214481ca1f00c0c04002c13500c030600380c50704440c40d1003508403080c2c000c100480e00050b45600024680e0080040c180701c609105088a15801620f0140c40080c0059204039407140034400d804520400700c2e44117100209000e05030307402040400750541310840041e03010407020014043e42c0000b201d0b04d1400c4048800e0542007995200005000341d0810300c440781e600103000806503020740204c1d881c68040c1c40b0306100c4542d42c2d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 409829730 1250 409828480 409828547
    0x7111e01060f080601120b07020c180402010807020102130e060f0a270b0a030602090a170a1509050703080a0c0506012c09061b0d0204031112060705030403050a 70
    0x491280b881e03001a80c40c0007041c89000801d50324140c45001d022111440d2198a40302d5002034040e00080070360080032014011074640e4000c0349100b5042d0a10418203040c1440010704000d0000c1035102164414842500c03a44240c503006030454a014003c0003142d142c9800103800106c1c0c100c0440d81c040c00c0c01c0c00008012014080c0090040240417a0011410b10b86181100341c40c510008103070720031000ea400348001405903020340b07103601001d04a00022520f40549240c1440700072403900030350740302c07076001c804010444e4100e2041c0940c042050142114a40e83c1a0355154140801849041c02007110700403648a14107510341030380c001c400c0380c4041d6590848642820354140c0040c443c41c6555903031950100d540703100f1a01820100f0010b00e950750f12001d54082107400e0092810f80e040c0c00f003001c1000300704240042c002a60050703035400001b40c02d9004200c100c2824540402250b00300d0000c04c2411504171060301d1b07005400d4102070303580d01d000d41000c40300d402c0610703040e2820310f602e80c520340100700300d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 409830980 1250 409829730 409829741
    0x60504060f0f09091e1d071421030903100218040b0a03080306060c0316020a09140121051606030e0a03050702040b1206040b010e24241b01060b03010e07111e01 70
    0x81184c141d41002351210044040703c80d035003000940083d080700c940e840040d000154469000a10410781c2d041c00c1c6030038002420301a03121900e81e0b825802080090b03083e0400c2100504030f0324122010004500302401040e0110000d10002d00450400300004480b622400c0840700429041d0003520340d12400c88548034000c11074200285d0150391054008a1858180e2141d81003030b01c6008140115a80703414801641004100100c104903403000e201200000d40821648000c0505c6070005400182030080040071200102c1d06083d483d80708482040109400104880003d601a03c0200c1c114520502041700b07400900c264141600c0740c1400c210a110340759011178140c0e1000e01c80b251090301d41321b05814a030a96043c0107207081c0310b0068400c4182c070b81032200014071942000c1403122040d280032201c40d41d03000410b5070700a001000e50f1007018105c00b0701c80c0034090051b10b02ca850031541881803e480108000f410f0744280304508220040f024001c1090b842c2c540009a20740c0130400d2142c50890107040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 409832230 1250 409830980 409831031
    0xb0301060f0503060102060f0414030c100b0307060915050403020618030d0305011a1e040803130f060e131d010f06050d0b0402010507080c07060504060f0f09091e 71
    0x1252a04007099091180084078081c201c142c2c02000c031a00c1d2082d0081d04820003a004603088800701030142180c03501030005d4a10381c0301c1c4c0400341c020116640d030801d040e0340740694054800c3d000168240031054110780c1c11802d03141312079070904503c110701e40103450500c40c070782001e5800840800d840e1084c3c1030b40b0303110101c010b40a0b804c1e14104044540141c056600070301a50340c44c10300c8070892002c00ca1403807000d020501c91810390b01c00c5a21621140c1c118030f61003900b00c802181c00014070500c1450032503003010002d0000d90110850340d40b402c51300400a403840c4006501c22200e1540800405001d60000140388094903601707084034650300360080c004c3c2100410780c8d00c1c5a00304100044c05103070210611648517017081407503e06076103030340c0110358503400f2500845051009120205580008024880140519480366540d070341c00c11401500724000384c5003c0d070401c4290616041c42c40d501a01d0b04040b5100f030700c80410306008070031040980240c82c40c0003d00789031402d081500f20b401d0611821500c0b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 409833480 1250 409832230 409832237
    0x121e1f0504060b0a030804050105220602010b10080106020c1e040f0b01030f050907120807060501080303041419020f010c05060a1b23030703091202010603110609240f03010b030106 79
    0x8203e10b00130300454003814440540304100a01040107954017800003001d8142074421031103031512141c140c04001901c281c2040c80141c0d500c0c8442110f41c1411140b8100e0b0398254248080190314000c0020b44e1004980c00341c90050345646410700b4803100001030502c484200401c1881010042c001010060100c9802e0b82e00103402c10003480b8002007a4814a402800498040c10a850900d84103221801c055501240c243d0800c002c0000850410321a0034060403d407000b640d501d05182c01d12000d180b041014100e220307000701c40284010340781c0c066900003c1d50306407441e081c0140c0c102c0043e980546104006070540c00342100700800c1c400264042e580c901103020012203208e4003120202c68100640c0e140c110f12080f0780c06100c5120306580080c66110707641d4507010860303008980d904602d41d6005c01001e00540c0d103a0800380200a00380d02c08001200341942c0c0740303040c4030012001402c020f1070048401005440104560a152181c8088401244c02401010ba680d40c2d24002d88400d0b50003481011b000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 409834730 1250 409833480 409833491
    0x4051c02090f1009090f1106190203070201021b0907110f1b130e060103060f09150507030c231b030412060b091306050a0605041d0606121e1f050406 65
    0x1e551241c42000311603608410f504c946d5151a5945180a205040354154050020302080074685010740f102204412190f001e103441c1c1c81d40740b00192405210001501114850050207030302c0d5141c0d02c0c24154840380d02c0c075140c20004088207540d800c041c542e25211141c0c0c0a038007400b650521520089101c540c03010740300040321b4aa8088040304403801c8085a01c01e54010340d004002154040e04908405410100c00168490f140c0e41d400030801c82000f60745050b2910382e00bc1084480d010300c40c5c4403e019081c10300c403a0f0b0b00b000155210841100c0394040c05106400f150381c3c11000b0f04440c040c1c0b44a00303010112540d03644c403840d041c000c9130182101211031900707219000c1c2c3c0c1030a14040c0d40b0b000d0303101c0c1c100001c0c800d07542d40d603810082d100041451181c15503c0000107000e540d41d01501824004041020411a20315040b041c04c0c41c01c02004070740140d11004002c200300c440060180220038121036540b500d20075000415041140c4e60b044005240380360340c21b28201c10b0143e40010301551148404104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 409835980 1250 409834730 409834739
    0x11206080718022a01020c0a060c1e05040b0a0c17030f010b0903060606210103060501080f0105060603071b1a01090e0109050d031a06040e0a05071404051c02090f10 72
    0x2644114079110444c04480544080344489801d45690596822000981802420064a0300d404415007007030760a5910380d482d03110699002025020506a12002c0740c1e41102500b6028103184039074413171103c0550340011020b45441c410b06000d0006a88a2248003040010074103031511500706480144007224500c000086031030342070040b03800d001c20107000307050b603617a60108022090700120080d0305114142e500c020300000c03065040ca030285100d800c00045550400765000d00d0b00032079504c4807000340e140c1000d001a0382d0f90f40c1c0660387d01c060940750405905c0fa010545401140b500303140181556022684140d44240c0c021496041e51009503081044214481d91b250984d500050702a1094000445e400c1e140c9100e40c210340029114240820b072004054400f09807a90301c254001816905031205008440c8142d00440e40c02000900d4003c40003642c4e00140750306481070f441620b00c244810300c1d507c01e107120301c422500072040d001840d01c2c03841e01d0210b50240100380200c94450401400c00300224 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 409837230 1250 409835980 409836029
    0x90d0501090210080108120a120c031e1103040602071106040303050c0c100c02090408160c090c03051905101203020a050c010906020706080c07080403030c050709060b0f090112060807 80
    0xf4102c6e0300900050900b200c01c000c0c0501c8542c0300a410108008540c28141c079007851034043c0b261180c1d650b0754001541c04030400300441d240d80c1d400250b90f51504119480c0008000342c01074940003504000e005a540c6104d1401e00540102c28190741d030015000f080000078103800c0005000450315180070384034840305d507208000170525116600fa010807507841044000d41441c00b61203602038070507810b05160400300104c1c10344031605200103c501d020080c4003072060903030500031016a50f1131414240402c1c00d001d1805000c03e011122103001240d600e40c0082c80a04000400c0001000b688822014810032030800035220301a02c60140c841c0d204425884e0102e51042c10b2a00854400d40d0291114500b400e5048541a50103070403070b81040c3c000d215860100b0510f03001080194425181c0c005000d0b01460164200a450b41c030603c80c070f61a0002c1001240103e200311501002d11078081c030b642d0b083d0340300161034041020709c4102180745441d201160008000503800196820011b9104420129103140e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 409838480 1250 409837230 409837247
    0x106080c040605040b130e01150908010203070c0f0f0f0f0605060102120d0c021203091f0b211501081608010e0c092802030f07030c0e06030606090d0501090210 70
    0x40c2c0002e00100b208200e41580071010f409080301000004007071aa80300003188862400b07030082c2900c0e00240d02503042240d04400394400500c41500254250b203418400a01102600c07040507020208603070b00c00c010840c8440034480c400303522101c0c0c010f5500c1c5600b001e0604040c2241d08542071460310000ca8520360001483d58030307001001c3e07c002d00d0801804c03000000b51202c11a0307501503100b640007807208240202d010718803c1c00131070300400c00d0398210a680010b91254100e00808140f4110704d94580382c490300b2403862861a010716034030074a88450782ca90728080d203140150041500c00e80c00418003150100f44100030009545901a10a413102e000031b080301c0488504030f916500005507013495003010021594042a82100302e10110a4a560301500035003002d00d00780328a5001081003503004100c0301d416005401846c0c1005090000000501440c0c0255515407040c000070002901ca42c2e102d20880700300410103020504403403000c3c81d006001e40344030341d000c0303220303241c0c440c00e00300420f1003001403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 409839730 1250 409838480 409838489
    0x80601090602151f0803030901020c010b1903080a050d050a0b0301060b0f0403120e1302030a0515060715110d06030c090e1c03021201060804020a090204140909031b060106080c04 78
    0x620582c2c0b03610740d285a590a0203c10000011107044c40010f0140052014600c0380c0007450001da50f4074501d070762007400c41d02c103086800d2184038005184514284400ca009056a5201151030f42c2d4440900d81031f0350b47e01450400602c1b05080000f00301c03480d642904107941c80d980640090003403c1c1c4031889004d0307d01542800341e40580040c0010804906161010ac0306440103041c140800e4201d200815503002c40a0800c40358a600001030100f5a8854800c8ac0e5201d1041079096910891101c0040d01034417030b111000d403205913410040412662558440d2078903126241e41c084da9050070901d03480280007184000d4a10107810803000580480601400f05d01d00c0c90b500281c4640c5001c2403110009075400c0031080d0030144d0038000381c03600000b440c50443c0600865100d0140ca0f1401d0701c10411500c5e51a0008510350380180401c210007801d001a0302c540000844000196503541c081452031401203040310708168504800048003040041403450581c0e60980e607280c2581e4a203850701c1a83d1049125 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 409840980 1250 409839730 409839763
    0x60b010315030f03031d1b0a080d0c0b0105030a030e060d0e030309160b03060105090123070807060f0e0705040b1804030e0915061204080702120d020c0a080d110703060c080601090602 80
    0x24110b21039203281c9180f0144008c1c0400301060b1035941162038200c1886800b0080340e4090a110f05210500c52410300400703003140100520182503030021f0085121444080c081e140c04a071080d9104a1500202e10428459084a4803071410740340e120350300c403c40b2118900e036548680e40032810401030380c2100c2c410f41040c0c64003850f101c0b45000468490050700840c0c40c80045240f1000b01c1111042c0c000c050041c00340d0010703506c4203443d04108003104c4c060311051035650324051010040c10000708850003283c01c21100040c50038001008039440800c204288414000100c0401c01019040b60300710030440429582d005182e9500c10701207944c0ca10500350580c3c001070510a006103d900e49195035030181c455520542031201e19400318115168240850843c0c2c0c002454620350264100070380c0c1c040c020100d580600c042e2031f2440351500c0e21a400ba001d41045014100f829451004000c248010352b40600c0402088840d035200034103004080e142c240c0004c03000040015000e10001e42e00504a8142c2c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 409842230 1250 409840980 409840993
    0x4051018021809030d020c03070b060105030402090103140a0203030c060103030f08100e0c25020102011a0f2e0f080c0309061609120b011404020c030403060b010315030f03031d 77
    0x1c00b9a845020007818001031348410081d00d45503188500180207100d000000179600c466061815041c1084000c024078100941030040001503a102041d850440c0c1e0045040140d00b4002554a400c1818608029405102c00518840d02130000120070381203a0090b680c01d10900d0826a00f02d420502c2030340c1039070500c11194801c0c000314034014102e5802c0a2044406480d200240400c00c2c5000c1c800c2e0480039035000b000500c0e07010b55070280584621401d0007190340c40240c644c000080c00040d0084e00e00380c0983c421104248500d444000440d00c14021080107902d108448107000b8410f08a80f0340c2c400002e42e0000c040340d040100c0c0d000341c030700a1028101503e0a030340c0f031551060748500d02140d95400c20905020000b01c1858401d410305550f406800c091041e90306080c1e10742c8041000c4409203008900c100208411042c0220503141600c1d8003c44c08503212881d803004038003420040940c60301d180190f23080042041030040801e110103200b514180300740a6840020741d0345502582c02c41280b84c0003c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 409843480 1250 409842230 409842259
    0x90e030901080a230106020105040309270b04060909150f09020f010318060203010f0603050c180121051501080a0c0e10170115090812040b0c010e060405101802 70
    0x281c0040e155000c40c1400d00203c11101c602d01300d00782d00c083c0e000b90f0250355510f05000030300d075001a0320390107000b4600c0543c0305031501500c1504134035900141219415603903880d003101940c450300188000c00104409100100d901e05203c4085140e100546e60343d42d00d04600243c03681070174019048807580040c040c030200760b203080c0154007815102452620024001c1c81520000c3c54a10166018012820b0002007890134490045d0880703002400100441d1402d01400382ca42c051400010309204003881c000314006042c0c1640c0d070301400c21400651146007070501308469032042100c07682000f10242c0c2c418000351503118610003119042041c035000115025419403080c2004031103030488a00320b01d85032500b10b072000c1036000000c04c280c0008000c40010070300900213550003640300d400340200c007003d011464a04525400307280f003280300c1d503c075650300816000c00c00c0e5000e60020000301c800409441003440c0901d0856180c3c10351040050501d8907050b004018180c00d9089510855800782a50b40d240c2d581 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 409844730 1250 409843480 409843501
    0x2010c020f03010e0a03110c030313151103160309060c050715110312070801152a0203030a080105043e210a0f050705030403030b0a050613090e03090108 67
    0x200710003103406648403a0040d02d000000c00510750424040d07616a0f4241d640d1140003030603c10343d81d42c4644a540b06001d18040115070038071b0001190781201d9a151015805e00c001d880f071039548041004540008980308800e104012108174160f4400e0351200c80180c0c6400b420f80d802c0c00840030190413a07101800c18000003403108500c440707450207414040030040c690700001d8a1540855030b00c2031070340300e030348288500d25820450f42809040c040114a61900320b80768010b001103950700984003000b58107505540b10b900200c070700d01d907101d0f0040c0c1a207985165152016004c05820312071303d4000c6203841d84003802002c1c001914041452080000102c08080081000b1240b0496007521901601040303100710a450030031102c007400781080754409491904a80b6041183d0030308400004031400c0604120400e039000b070880340d0055260400040070490200490314003620b81c0c00540d0080c1c800518a8052204e6055107802c07180a08824803004070310340d40654490141185090102e1031401c081000140f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 409845980 1250 409844730 409844749
    0x1203120a020f070c08070b030610030902060403080f0a0e010914040f0615080109150311090720010b0406080c0630150102150106021009030e0a0602010c02061302010c02 74
    0x2000001d030504a042044032025481648210b880c04036a960802240c2c500388004030040050964150030b514040000c20100381ca41102c800400d03541d141e40c0c50846d0703100410366000e5074001e540c407900c4410081600003168440d400c10008210000c2c440750143d8452811582074441006070310418030000d1062101600c0e0380452211450384841006c543d48800c58001c0c10b548055a40d03c8a180d413514807680200c1d286a407002140214104050000c905c0c0400040c0c04d80505032608400c56440c10001c40c2d0030300700313070300a082d4200708814a6940d9900541005100d00401c450804c62030782d840c007005507a003801621845d00500180800c80301c00a1081c0295660340c08400d00c50300d20b200c2607031198122542140c005160414603141c080055904000a48800c0450131003030340726505001c0302075500c08840c50005940382c2c9446a090816110f0302c07050308000405810b14042030b03100c09029010303001445408005105500025490403143c0801c004120b030103031100e825089840c4c090051100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 409847230 1250 409845980 409845991
    0xc0307060e0406170304210206030610031d07180e0c0105031306050f1b12060f030a0c030c2c070513050904061a0a0506091e06040b030a0605120312 65
    0x5036a2000041c010701120b00014003040014055980d4508042c0a80c080c00d04141d4500c5e804c5c070b1031301c91410060709c9040440b0f41060003101c0e680c4607580961411409416050700c9113024450700c00503088000c600050001c00d64104114948015244010810840d1240c1440042c0741d80048030030246540688011a0010644d11210761008880c2c0c84200c1a035034203072200d200d00b0400904015000c51a105120f40202050540700c0c0b0345641061000240000680107a1241001003c00c0d0038913a41001f035001c0b003940c0030b000b2441d216aa030070152850207452040c1800301c2c8d401c15113600c00c441c1040507070100d0312048440c2031080e1108001140d280d04107000801408030040c4010400390349200b03405228170700c0340c0c9001c40c0502c070305640c01d00003203041c650950044143c22000e012a036258130556000782c900b519545901040c0320600031291011901560704001e000501041d1801c00310010b601c14000d504090049994400500560741d244000c1030b0881e810512401003010842c80c0d003180c105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 409848480 1250 409847230 409847239
    0x412090302180723030718080a081206060304030c1101052a0f07120312090602030f0f150603070807020705150c070506070c0b0f0d0c1106090c0307060e 67
    0x551250701003000118101001100068880d00300200d044e4400e040c2e19443e40c590344021a8003003040b4400d00c031070002071b04803400e11003000b00b041040008100c0c00c800034504a0115094000d0600f85160070354000c60900004002e044001ba1a81c04c00c00c1c1100c0c003690745680c40092a581d035407603100d945460003d1b5541080010005112801900744004581c6600b2201d100b117440c0c003299245203409054009000b05400035001040940740d00f030781461409806003412405440e00240c004010300301b018005201714808000d1000700c00d1040d089900c112441c2c602d9110325115020150401e200c10440b2542c030110401c0003c8825100f00507550b00800c6d1f0b070044a40f4151541c00241c00c00000c0f0000c80e40c501404a510410080100030503402030101f51460b502d00034441d2101c0281c6045030080140c0000d0020700510ae0984150488150b0314405030100071241a403200209030709420704882229115480c00309058080200b42c00c0360030f15000707008142ca64644041034500c0e003208420603501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 409849730 1250 409848480 409848497
    0x40b04060b0301030b130b0a061401020706020c1c06020301150909060311010c080c060f06180c040b0a020f01020307031a04231b0715150b04030f02040b040e0a17090102060412 77
    0x4403411f00c0c45006140e030f0300d80440c0d803506262000c21609a4246014115846098100200780c4c0100b0500d500aa098409074400001d20b0650b07440c00b140f10030005c00701c83c40000000b40ea00340d003564900800c4480e940c0d0202031680c0b1500f5105550303103400083c08186184021401640c00b84101c41505032003824824185008400c480c0c1c00d1107001c5401e070b203031000030300c0c208400303841e0102c0032903800a4a80000002428100c903030010901a5000b5000002000610b03038000c240200403542403016010000c2d582c07450445402400750034442d61584006038440c0282c107651900303006141c1002d6048488012603000c450360014003000140c5000001d88400c4420902c1c42c40f120010907d60f40074140103849034151500040845003405151840c101c0e08107020710210074103208440403250402c51000c0c42004074000074009150f0700008075480751805131440f500740000b207482c00703e13540900c542d0000406240000d0aa40c440c1503517590041c1c0001002400007403500c02d1f110345e004041c0c6021103a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 409850980 1250 409849730 409849733
    0xb0a02071e170a2102070b0c150a020c010c031103040209180709020702090f04171c020a0c020405070306181802041119020d090312021c0c02040b04060b0301030b13 72
    0x50042d8580c1c03550007034111411030014803500400800368a0340d6000901800c002001000391a07840c5030003031201032036000500f07440003401000510321071007234440820f00d1402c00d40d01000080d030118100005075402e043d01001c41e00e029110b00442074661200d070519503501c40d0300700507104a00034505002607002603036002d1000e0307003009100d01030845a01d0040c1c0d16080303801044446240103007882c0f00111501d040000094280c100b941c0c0d801601c13038416440310b40e18080d5100089103140200907a920105a481290380e12280400020780251420486619203c008a050b140340303015a600c2546c0d409038115080c2d0311607020342c02d0444610004e00d0308a0040c2d0000b4140d659044164100050104a64034280c1c1c00c2501904000d100e80001c0041d10300513403020300724a03410300c409803245d0216000250450300a0002d0801d84140b01e4807040c2d408260a4081c082500842d0140d0155161403180b02c428109885884195140401030608603840d56a820081210041c5a40380100140000d0030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 409852230 1250 409850980 409850999
    0x105040b3601090b06040b070f050a030e131a0f0d080f03040c090501120f2103200309190314030108031c0218041a0a08030406090b0a02071e 62
    0x140c04450445001400c2401c460038a10401041e000000120b1802d0009901981c99008880031144040324450702d45180b03040c500840000c40300090701901420100d0b0f020103500c05502c0c4c8401100b1940454280d9038080380008031455085900c990841c2885141040d2402d404c11000d000c1c001004800050215502e045407034100000500405001105110800020307035115030180041a0b800c100360741c0340110f841c00d4003c035460301520000d030320090403050080e6903410034524190901d080131500c0342035400400410422210f03100600310031450380745051000d400c032806100c081c0c004044501100d848a510b043d4864001ca0500510550340b82d84101c040c00514020162600170715219003000c0d51203410020744403480c024580c410003908080000d102c640000c1c0c1c540a03500001c0201e0903c46518080407908090341d401140c0d810006501100007000348180d40d01340e42e641140c165500000e040c04d02881ca0b0300809600511403d01004080d00d2007185201d4005c0450440180d4501002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 409853480 1250 409852230 409852279
    0x17090a11240f07060e06090705060706060b1b0c220f15060908121c090c0b0f1803030f0a030f090c080f0d050301210f050d17011a030105040b 62
    0x40c042c010020645105102c0c461142461035a400c40c0034009601e0450107903038941c8414051380d0300c10280032a030581030003031550000700500070820b0140d86e940410180e0b00c0c1d00506009001000b0300c128048400b45080110243c289044d46258100070802d6030481c69001d003410146e410000c69840300e9900892407803800310002840e05445015001c0e0400c03542506044002c0d1007011448000c009803400254030b150215515150640b000a150103245004d281d030080f1540300e10900140031a40d5007450b0614801005510650700141e040840c0d024149500c80c0200c81c0e28401b490003e006669003580240c100768511940680000703480c081682d2500c42c15030f0079802c80003195201259a010f000c0040000c40c56511340c40c20000c0c2190b1408003248091944c2c81d10020340b051a104603a01044024480588001e61040a503001d8458100000700391052805041138000c0c0d82c0c500006461200070384007400545801c981620b10703800c00303041c40094410b10000301c0d048030035090721083c0c41c01c940450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 409854730 1250 409853480 409853497
    0x9020d05070308030412092303070302130b030c1c080c070b0d06090c0e2412010b090112050f0a050405030705060a02040807170309010e06120717090a1124 68
    0x1015140e00309400d000751b040001d42d50440c00d200303030b8010911030b1855600c441c01c0009150880b84000c040c518000c281800001e500083d0050ba010100000c407907031503003003804403113019400c54030180d0b40d820800200900a40982c1e05811a8140d24004200032800908404022104403a00565910204559940441c2844e0441035a9100600c00a981d90141c00701d91003881c1350500780416120001503100944004c2c9c4050003082c828422070703403411030301660070f001140071605480e1369450065031002d6012a02c15400110142d6002a042c0d180d4814140548901041a4800d03030b50300ca059801040c001e0020350704c42c030007400103a00081c01007080a01c94521202d0141c2c54070b04e4209034600d0103680f504120006881c002080c0c0b034000c030000545981d4007007440c00044400d40040802c2c5144103600100e29443ca01d001008001600104600960840c42c060685956964a0825203c0305040c074010842c1034465100041807906e01c142c186012816801c01c40f020088003910480766011485 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 409855980 1250 409854730 409854743
    0xc0e04020607080f0d0f051e07020106050306150405010e0c0403081806070f030816021218060a0503060102060109022b0b0d05060f01080a0302070e0702010b0901030506060f04020a0905010309020d050703 89
    0x40701c0304517102c0750007004c3c40800b12000910603810301c020a520141d00000401441004100015003024400d41108005145c040c0c10303140a41004003c05e00752f00b20508055002c1d0341010300000c1c100300a01d22092003540c2c103140190074141150b940071840d5201d0410450124071100b19103c6540d610310003014443e02c81c1b00d034000956590b150151004100404058142c0a104030010300e164010450000d40706000c5000b550310081c400c070059a44101c0d240e00b03500208007241002ca401c0e0044000c40c001e1500740c003100c3d5a603a903803c50038141d118010002050b500100d0b12080040e80185000d4040c000c00d1001185141100b40840c085041714203041c1c55903407108007030220b005504a500c0340074004400141c00b6030085500c01955a00c0740348240c1e16005841320008010034800c5d44000030804005040d06d44650f946c2c102940d440e0000c5d6140c510a1081c002000d81c6031038144201e410013121511231a039400c1c41e00c0015002440300c1e120a0343c00c08800c0f041240080c00910000024510400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 409857230 1250 409855980 409855987
    0x10050301260309040507121401080c06160507062a0305070f241d030a050a080907030503030114010f031e320118060812090105190801210c0e04020607080f 68
    0x54045c000e0fa400101e413076442e88c9444006005003603000c41d545000b00001e0b9800c680d16000492a003808403031150300580513025002c07012568662188152000c040c07203d01a56107020742000303404020881581c014081041002032070000b640f040c07501840355024450b0a0241d00e0841910380802c440010303969940d43c0d94083c0100112030221a00c0041201c600040d0b0070040c0701003015010748611500340003840303007550015540560400c2294061580300b82520384a507500c04c002499510614074242c081b500c00000c1042c810f10920801c0050019600c14500e092240242140244811441d410b00600840040084855990024984a4040030702e8a086606d0041d40390300140d900000800840c0c1820b804000012000070400344e4500c40d80d800c56951b075084c00058a40e0b204002020703001c0c0400c190f05225045d04000c40138101e440d0b15601840514190301044000603c03588020203010b4156014030441c180340141700d50107440034181f50f1a10429032209030150b04441c1d9161180300001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 409858480 1250 409857230 409857257
    0x12040302010b03070e1308070807060c03021e03070f0e0d050708030d0506090103050c041a10200304030506010e090a0b0a05010f05040902060319020409110910050301260309040507 79
    0x1001044c0050459142400550502c9000509072042e00078001d0301003500400c045040c0240f00b012964a02d03449403040110101c031280c050003a4003c85001c2003128402c4a015039008000f9044030b1260555654500d069990340310103842d00290106101d8000d0200010f200000d10100002c00103003162000464032002d13008541002d942c2d000700501d0290ba20080100000740b0000f4a840e0040300840e00859101c0064500c002c0e1031025030701040d071180021b25042425504140300f0101170088810040c01400320111859507031240e84001406603100d071004011105600c04e4407604005000281c82c015a859102c081032580141e600e9101f80e0759071001003007000101c2c003010000f00000e56007806050760540004505002c010041c200717010800c43d142c210403405604440c090f201081c020008001e1404101115400000f800c5005041226a034812140201700740c07070417109070010003203801e8400403000040d6440c40358017010b140f1050144d06080e9a03a40512481004542c0d51201c039040d10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 409859730 1250 409858480 409858483
    0x513031d270c0903030d09030c06090b06030c0301020c03070311070801091505070e01050307081503101e050906011502010e06130302160f090207081308011407080115031112040302010b03 82
    0x2d05240d000490801680041d5240801965007034440d112002070050000e05040d03490181c0410001d08043c5041d800d0020440c1c590f2059002b00c20070b4044509035900841494200d01c11100c1d50489544140040c3c00040d106000f01b1241100103016240c0103070782e80070b016094440c0c0520440b1550004204450304403018852036620402d01e180c6001010500c0c40040d255100c0600340d03400304000350001640480540b40c201c3d030942406412143e50941590f6400f0080013045000d07080e00d080c08600881d4440c07036010b00c90007043c2c0e01d00030f00710a900e0000b44001d08025049000c00350754a40b11183e0505c00c042c44103071b2046000c480113a85103602480d00a0804122600031982041c4600c018400c89507101014402d86140c04c42c010380e10001c5081c4001c00307001c1e90f41c0c5222a06180200441c0c1c169040d001682480c8a1085043c41500d42c1042030711040024010400301e86c418070000f20602c1e100c1e4100c40c00e07100c0c0c00500c10740b13441040e01004c9400c00c8201c4080d809030b915096491280d090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 409860980 1250 409859730 409859809
    0x10902121c0c02010c060e0c03070b030709170c1212160c0b0c100203060a0e0a06060e06040e0f04080c0a050d1806052703071d0a0513031d 61
    0x141403402080710b07009580080d241300101000948140d03561785d20700d00e1041c0c0c20030010504040041c110340c1010345d51079648085034801c86040c00040c007a4080000c2e0f20007000d40c5c5503424080075000c2c0080020800900614080344500c05d41c0d144a0080485080328141c40180071021894205021070f00c082d013401800740c2c0707160317010132480d99040041c100a50808074510160300a070782d0025959071a40400200001c0c05600018000048401801807201c0d9580c42441150040d03158136070f04201501c00c204150181e841101c00c014200000034003082210948185d12501c0741d5240d909041140c540c05161000c0481d00f1525903100c444a82c04140c2c000c100700000c3c0b1105040c051629080a000030418010007a0f511540103d110624040c0400d030510141803a0004d021611401c1c1d03188468042c860803200030a4101c4010004104c85030a140189842505c000c1c1c0803440c2c4001036507048800c5007880c01300e1080c80f4420f4032541c8540d901c544404818012080b4802680c685003021a64941c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 409862230 1250 409860980 409861033
    0x301050606271203041412070f0e1b04030302061902040f0e040203071a0a030c0c1707020a050402030702011505040c080412030e10021801080709090c0201090212 71
    0x3001030281c84601c0002c11002015452000d6860300880d841d5008100d40ba042c103940c0640340d0101080c003182039510700c8503491200c0d0040343d030404c258000f202c0598403a8521b01a03420600012103087c0001c1103180c1120740c0000752190b001d1403440c0400c0d111009030b0010781048005810100500c00c400b001a003107100c1c40010f0210852405207080805801e0224a204000c030812014001500359a030504c41c0340000c0101c0c4549e000c944004207400300003a8001c044000c042072074814080e103072500c100c040c4000ea80c0d209181d20138a50036004021240d40020300100d0748040d54a03004a140e807243c0c00514016201c0d0f40001ca4410402c102800388840d0940245005a00e8420030300c030340c280c2c03003402e403a0080d400559408000c0c8c00b080c4214041c1c0700c2049480c9c00c0d80300c0d01c1258144150150b0003000c4404401602503400310880e8011030303052105941002c0011100714003400a1801075002c0d4074815003500000031001e90f15030208804200500821400c0c0d00134594001000ca2180c0c41c000307a08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 409863480 1250 409862230 409862239
    0x30606030201031d06130314030a0e06010b071505040f0611133c09050408091f090b090a0806011403060f0c070609020103091e11010912060509010b060409020903010506 74
    0x810304c6400280c3d81c0c04000c21401c03c40f904100c010f42414041c40450742200c5400c040075540c0d2800b65140e00140070ba03400c0703000300e9116000000980030030110544201d10761005480d001076884100c0c2e04d0161002801c2500c154001d91000c01c0090b545120b8102003070600d00b059a100e101c040b6015a00314425031012134607170310080c0d40c1200015029680780c031495040180c003041d407001c011040b10b0300f0b4498010b1046285060b040c4810f01610001428602c20708513650311841e84408032052103480c030000c518001c18100741007400a000320002900d0311540c06030400400d10f6941c4405881c1503803e07803000c82502c01900e410512824113000300303944215107500e10f202c41d00301665039080e28803170003078040e00d00c80e0b80308544011a81f09420540c0b090380c0241166903583c4003000e181039401c00301002145c02c030125080b140c403154022881513040b07407480765420402469940b80c2e080a850300414201c015517079004c1310302040c1d842c03c0141000c1e0220000041e10380c00d251082c50300310b0303d0150845224 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 409864730 1250 409863480 409863521
    0x1d030a02010c1d011e0504050d0c08120a020c0f1f09050a0f0509070c0501180308090105160210020f0d0c050a0212041a0703020c040c12051b0a051c0603060603020103 73
    0xda44c01259800350021544008442100b178058100d84a00031a04419440300c08a0700311011320101c00c0c1140142c0f0203e8045d2034001a00c040048068410051f2b480096000008070390000d01d44003020040d00344024080b403040150382e68540b00701000c0348001c8808100c03165400e0211741405060500500000042000418200320000f0010385008040300100000440c521041110a41100c420780c20030000f41051024207280223003070301d07400301c8200c1c0240d841d244c006907081c140322100d200d1645117a00074000d121607d2030550040d40c4180186d07003d4203000c110400222034a44682205e010f1a96900c540360020000001d090002034a03400080640c28002441011102d21807201480c0c044442c0315503409680c5002e906001000000540c007501d4403850144158003c95000100c5141c40420401585c0740180c03012500d00c0306450180c482e8050228a00841c040c01c014070b1030b40380132228640745440c0f10860105541c2960012520f080c1c80e540100110358243c00751940404c00060102c14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 409865980 1250 409864730 409864787
    0x30905430605120c250204140402130c020102070507080706112e200309010e0a0b0708071116092d020d11030f061c050c041d030a02010c 60
    0x2141c0102c3c904404121040390105000084450448004031016002c0302201340030041c910380c1801104105902480c1000c01111100c0c40f1001c449209540c020506028200d13802c64440003020b0351907180003035650801403003021a000f00300010081440c0e9008051032400e00c2401010800345420002e501d900504000f108094504c0015401040d0130031003001d12895945884040c0c01c45c090b02d08241e200a44540e16200c402000031481500c2802c003d02110740000d5110340d4030450700d40d01400070700c894804242594403455813190041c1d0945410390614011048550500026618500191a0740e50703023041a41d44600424030b189964500c03130640700c04483e440301c4810700505150b0301040c1e03000642e40c5044c0d100d6030024040c0404280125103915210507001c40905040d11141d2107084184159041c02070315030103042180d6400409030000c01c01d1141071102608610205100d4120102a004d80d02a0104050040304101d81d0001c40c14001e0400c014240d2102c0c4c0b030700100c248818404144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 409867230 1250 409865980 409865987
    0x9080301090b030303040f030e0406031a01061b0512090d0510020304120e09190f0e030702030613150504020670081b0d0c020f010309054306 62
    0x2600032381500305140792040c0000090000e0085030401014500003014000024580500c540c2c10380302251101c103107040803011149840d2008403030081c1a80d00040440c0000f410a001034035103c20084c10040140c82a984d81c4e030b081c0f58a41ca00c01c283c81e98040104004e024520310342440300c040600340b8440241c2e04c0c401150178008010308104031140d80783d819208070301d4164000200d038030120208000f04586d90a840b0788036805030006a1003407003100081210020803594800d25545d00c0115499002083c00f558409460014003d07a4082814003984840c445c0f8500803208008010042c00401d04000301c1c00c0b0100c202c42c1c044695506005011034081c0f2022040c0140035000c402c00301d07440c40081c3d80c00416010000d50340207000b180b0205000400300e282d10801104c100560301070340c001e4211000101e8031002d0580004c0c2d4022140b03040c2a403154043c1e4400030640c1d0040040e2402d0b02e20700075808c6885400201030480e001d40b5a103103004600c0450a2161000d2030703140d07030180f540d85060701c0213 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 409868480 1250 409867230 409867253
    0x216150905040203070207090c0207061701050f1c0f080d150602060c070203070803070b10080303040f0201080402131103431101060e1b0a0f050a050d09080301090b03030304 76
    0x750003075034004007240c0c000303000704240b80013061038a400b07101903c040400207444608034402c10000c100c2c050201007d052012070100c0c10380350701801c130821024004003044601d0015502c40103005113450180070110301c0c2ca4001080c11030007000525550381c9864004011210152880d00007400203070700c188240ca42c017040d526003010101d290141c031240c65000090800089600143d030350720000400108005a070085103102d5528070030302240c03403581c03200c0480d01e03884100d80003000e1321520f03c24800150f004418451300140040e00c80d42000c0d0070300d00f1600444580c102c61a02d19200402004030b48204000b110405082021000e643c41c0500307460f0180024110903441c000d2040407103100140341c030a130096030b030059202c0c0007409021b607580e0141d003040d1380c2030b0383d00d0a114142c0e6010010000c0000100d40140215a03a2506a07641d54002254a80c00031080300b402c01404001050440a5078000c1092290007002c11036502d501d024111710840700840021402900140104000300d2280c40c00d0303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 409869730 1250 409868480 409868489
    0xc030c0503040e010311041a060903010609020d0912140a05070602040e0403020f06011d0606070201141804060f05062a010218090a090c2102041811061827010602161509 74
    0x1903852b403050301f00090141c41c65400c441005840850340b016107086035007203440c0c2580035201d01c6504020a41003181c130a54003020402c2544001c10441680a2040d40203107070b410300811006040542700c401140710607405441c10b50045c0c1c4048540103100c641440940c0c010081c003038059460803810341510034940c000a000c0e504c80e01000c5445d00542e4054030b0f81d0003070b0441d00c1050542d00c1640d02d00403046070404c181c921b8011440d00342d02240c00d00300c5601c1c10f030030fa45001303006034208007021000c9451581000300340106084c1d1441e5200102e9024005000f9203403000704000d00d04081601449900c0400030003d0120604055440010400c4002354000340c0d459131214000020380343d0004c04080e0340b0310308002d40061030000032000c0084010b000712140f03403140e150800c2030f030469002c10440303000f150726481101031901490f4805142151010009035504044094188201c0c0c020a00c40c003426405900075800911805419409040130340010701002801203800c010014070091211640d400f6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 409870980 1250 409869730 409869739
    0x50417160b0309121c1d060915060402070201020a02120a0303110304030f05160812220c090b0f0d1b080102130509040f05100b0114190c030c0503040e010311041a 71
    0x28505d40c102000d181d484010201e0140a00c9100e0042e22000c1695090300c1c088155801a10041182d07036502081d144020719840d5000c10180e114802084000c1d48010700403819071045c558080011786550401c611351034820303005440c0038440742c1030103400c0e50407803580c688040ca401c104000002c0c0d048001e03515444403030700d4550b44034001c0390380925810181810142c428440441c0324600080e080c070000303100d10000028aa15401c20034410b2403001051a001003115070102d5085c4003a803026806175150070f100800c03440310301070320070045500f4010002040e00d400010088903407075000c4c550a000c00401c10800214640038100c040810340c01400c1c00703400c1c0325002c9840460140403200c0704100c0a550404241c650403604192500c0081020f491502e002c030b000c55450005140d80902034031611203030311005401c451000c0340221800381049a0890900490080384d0000c201c0410240001c0c1c01c1c1035040361001d504600701298207040b0440161b2295043c04810340178400320748401c2a49071030569 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 409872230 1250 409870980 409870987
    0x5151503010b0f040e010f15050a080a02091309080901091509090203190c080f0601090509041101020a0503070b0702070b030c16020406080d03091406091903050417160b030912 77
    0x9443c1001413003a07034800142c510394900040f1f50030840e20154412602c51540341c1c60403224104090b9154060b601100b008210081e00082c41c0380340b00e80007800c50b23a80c010454a202c0c0000070140e8101c1e0503202e0140d130991404179000030b40d560800015006005a40c001107881040340740700030104d0510380071340c3d0781154021010441c0b0902086c444045407499010a2010021031000103007040b00840311040d0a8448902007103641d40164003100982e00090038a401e03d940300d4403600308040d41032000e181103100311010600400c0342480030340300707a40c8503543c198400d04003080000d00d0f060917a0401310181004100707001e03441d0424005c82303090814011242d01540420b00010f4001c15013603000400c103008841c036841c2440c3c2d0540c40340c40f44c5840b9603080d40c0d0340c0843e05007860386e41d0070442d071fa24141d0340003560000d40b031055100320301300e51880f034540140782680358a25010380c400002d000c03180640c000c9010151049400300d15101828400750018103501d030084140f5580d00380c0c078052070401807001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 409873480 1250 409872230 409872247
    0xe010e190f06060e0106020d0e01030e0a1e0209180105010b0306010e220e010c021e0a080d0902060708030109140412050901030609110a1106130b130501050a05151503010b 75
    0x40d00510004c00e003900d1001e00c1580d50b064080d40750000352410800080c0c6a10030b40c441c960203441a800105503007030062200200d0707613940301d006148004030080011907040420300166114401988241420907002008c40b00c80c0007410309492040c0c100c07104104040c420405940da001d840500c1901c070484411245210411460b612031900c1113544030800d041012003c0030f000150400d0401240355821610441000900c0d504a081252004e0440c2e030440d420500c0030405000160407540c00884002a5608051740000c1d1183e02c03008003190300590110042024050f18414000c88a4442c4600c2e44249469961601d2042c02c44000600340000410300800f0340e4441c1d800200a448180300810003080c5420f80c03025142c0111840c940043e4211061a0240c4008100e80d402031424960303040b040c2102c1d07a28001d0b00540104201e8141c0c00e10800300300484d20900905014083d40d450000d101d0402c10a1011030301c038100740780d0307008000358440c551007030250200700d90454441050a0f0740b100041e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 409874730 1250 409873480 409873493
    0x105030c2109060711060c040b0a0203040b040305060402090a090f020418020d23120306040f1b0306061b0209011a2b05011d0711030f0a030e010e190f 66
    0x14002140d01021121040110701c0d080050000d0044019417504140e169402e640241d50b01811a0b030014108001d1100f0040c18000c0c00140c4007020103801581d090507103a060092064106074030903691580300f50f0900040d07061440a1a4205070032035002d2203200d0300c82c0ca50001c80cd07c1130300003c1c0219558144004110b200c032501510352036000345508400811428500c1002942c2d40761a489011806180e440c004000104d403a1540001c4c1c41c075604507582c01c41007000070085100c0b440c40c0c513a1250055001c01c039440719400022051030b00d00064040c10550010301e0750300c41c182040480010150340d103001da5100641c940c1141c84070040700c86400010100141c4c14003418811002c030f203030311500348620652a86030309011040d40800400c020f81c1d035070040c00304510101460402d16200000402c1420340300c1c440c06440203041c01c0440e0310703045c021696020181d000c482101d001036502c565504803c00d0038064511380e24505001004610081c0d00d040c103c03008011030040a490305140f500307003040030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 409875980 1250 409874730 409874767
    0x90c0d0813030606090c030b010207120203030d020406050c010f020f043008030411040b10230417100c020c011b0503210703060806180f0a061b0c020105030c 69
    0x1c403024030940d4a6600e25192001d09440d00810708a43d0a080580600b18480d01c2200690b40f0140d005004031480d0122a0944082d0018160b0b00341c0001c10030364501800900051005004541d41e1603500c944040e00c66017110840d0928071403041c01040498490700b46141aa016550001c4050b01e100b60102a400690307404075001c440c942d04400e005070203001a01019500c1240a00c855100c1965042d00300011140303210340b0560301c030201081403480d6500c106101e04c0507100c8242004001410041d901d4640d80007540b08000061001110740b04981c400e00907410030a641e100c013400f076601e500343c0103501c9240070383c0460304120780c00f01002c0380419800c440c03080c40f42e007100c2601d994000c01813410403e08010151450009034210109120901c00d01c1003804540c1c41c000601a1074450348402c04400000c500e01c48964413381005070788800c824014156401e2184100240d60411400c0d0040d034144e01d200c042c001d0104414040c13000d80d8000c400c590f07121500c20300c80c0d5507426140040040084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 409877230 1250 409875980 409875997
    0x12060c0a0f20030c12090a06050c03160c1a030c030109020901020304180504113709060b0307090f0e01060c02120105070305090c0f0609040c030e0a050a11010503090c0d08 75
    0x104001030300c1d00030b18400310003803804a401d035080e65164441c812162000c2d124003546141c00031802038040201380e04c1440030780807108070401aa07291028090f60fa10840600800985140c102040100801c0700407182d04011030418001003415464410310307084850005108041c140740d000200400c07207a100b88210303030207000c03110071610b1070000c02c08110004010881301140d030324030b48440c80c0f51a45001e950000c01a82920360802035062aa60038619000d50748100203400b50380305a0124081c400e501851002e41b660300c060030380701e14164a00901143d0141c1c007009a00440c52801d1044041d8022542e0544e5242c2c00c190f01010510f10210b074100110614822040d4600b034180144ad42d856000709004e0828038003100d42602c0000e08100f80c414007003503450390050040190107890701701a08000c80000301400c4c0000d10ba1281441c250502c0c582ca0412540c3c1d070046201f00e020000008122071502a080c605181103142c881c100e0f9944111450b4030911500050f01c5800800c056841100c0c03012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 409878480 1250 409877230 409877267
    0x12020f0a0303031a0406050603060d150207111327150219030609021c0e0c06070f03030c08010b07031107080f0a030206010e0601171b12040212060c0a0f 67
    0x20359a0307080040c001c0c659003100b0b4000d8000352140c1c041a02c0d15000700700a40d400100018516110303241000300d80d0803011b00443e401c00707070000c19551071350051028181d039034081c0000008141038031042040c1ba8180d403400c82101860a00740004d1a0744080e046032484041800c100d29008080c01c1c1681c0a182c0c01c0c41c14640e0600000c0c9200c61620592260807020707120f80c9051209580303480b41441a405040304500c10b05140c0024040c4c0f07608141c001e08261200403084d65085010080413074065030041c0020350709051518548004c140d418400c00710b04038150724244289504104003000d41b441007440203020028100c07512141803005001c204003c11203041150707951012034400c2902d501c01e260303095000d80508000020110214003050b8807404c0160740b40d0001071a0705000d0615070501400d6a0100303290454003010034a05040100855540e68504280510b400d00c1004050050b8144074445030b000780c4140070002044100b0340d0450100d508044421520b5000200c0310070700901503280b0390 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 409879730 1250 409878480 409878499
    0x1401140705070603060819150c0c06060603020703080f010e04020d060f060e060301060611070306020f0c1912170a0e0a0209040b09010c0903080a050702130e0d020d0309080412020f 79
    0x5213900359000c0310440d44c0d10b1040c0d85001c0da90690320104624000c401078040c81000c0320202150016601411040c03c86041200c501c01c9079856400440308640c2004000c00c1d03000413042c041c175400194190307200054250789401f0398100f48500c03600031400340c0024020b18001802a080012a4008040400703040d042040074640e01c441c04140054180d0340a8041e500c0c140010820a00c215100c8010b940311400400002b4a550740e804000c2d8881100c0e44494003041c00b4050442c10700b40200081c00045050b10721a120240c104034400c002201c40b224140943c0c5110401040e00c440c48456100d6001140050440c16103050681080c040940080d4040440400c1004000081d904a4095882c0f6802000305403040380040d00c1140c2d044c00041d005240501003000214820002800300c94405040004202007802030401034801c90114001160001003010f17040c0c42c2c2c1004040c030842d000d4a002c0c03144440da501c0300d2010f44994000c04c05154180412007041d501c6010711003115080207005a000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 409880980 1250 409879730 409879739
    0x90319060b04060f03020f030f03040b07050d05120a0e03040b12370203150618100e0a0b07020406080609030324150327070905060604140114070507 65
    0x42849504694080c5032004014181c10648120820340f03e4041c20b49040c03500719002c01002418480c04941e03d4442c08000501c000000c0c4003a0004002c0441400d4607586d05140c098180300e98440a18100300f028821502092040040e02e41c00c55601c400c0001c02205034280750341540316035040b5008042d800506030380040d500701c000c81c0c40f038170a503014241e107061690900c852041459014030385080e241003100c1c43c070210302c0c0d0046400c0036082110b00c500038014008910b8a4202e1803215021041003d422122410075506c01001443e440c0b402515040311000000e852101798021200910790100f1100c046440f0b0740d1040b400303400300c1011104c80785025041c5aa496008031103682500b0310821f10000790622462060075407010041008400010300d11401d03401d600020009030900c6540c500702e40d201e020780e0301540c001845c07a8010f801528107042c081e800b41d541c081c01c800e01075a410032040100009403052010184003d1810701c50111954100e0400f900507181c010f029405a80070005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 409882230 1250 409880980 409881013
    0x30309030d060b0301060e010f0c02040c08181519091502070c090506030c0d0f02120618190b0c12010e0601030c0531090203091e030c03120c0903 64
    0x2041c0c038120700c041c08a80d468891415140c08203114078400301304800c0d841c04441d07008440d0602810107030704d030100d039903000c80d0002000c1c0e0b22400700311001f00d1441030501c8488007040c40d0100d124103440000744088811240710315013015004158500c81e20203000ca9424500440c0c00c64010141c000b1404d030954508502c1c900e00950100900320341401454900140441d0b040c0185841040b00501902e4030743d800b0340c10301000348119030041383d1303110422142c10016591078401340c8406143c0700051100345000a05a5503248851888510740d070700403451052000c215070108004a80d1100902801e0703140c091010100d400389011141141003000000309004c540380c52580e2103440260390503c070b8040003510aa6043c402e0b010481850400c600c0380c240e440c0301c0d40800a00b411210b524411156607030390380d0b100032600151691801d42c0c019820490700c0c41c04100400b20501d1403036011f1460b01002c15036482e641d1040810080340344200400103050311460340203580c000303d03020b1b0580d82507014051142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 409883480 1250 409882230 409882237
    0xa0501021b010612171b030c060603070618031716050c03010f0b0105090d23010501090b03030405090708070903060c030b090f0c0703030509010216031e14161403030903 74
    0x20207158a030400c0000d203c90b504c2e941240554201c10240c422800c2e944100500e64808035903202110b101d48050f5400c540d007007004103250780d02200a00703c0c600380350b800c02d801c09040fa800b2404011074011800da0410300020b9410840e41c0c840d07581002014494041c2105004440c40c50f010003000448400070b100b00031a0340b188080c800c82c020801107112282c00070440f103404000ca40003800c00e22030584142414464085a24003c9407000752940f0340310440c8020343c00d0100591080c2c0d4480004000503581d60242a01c4520210091400c0c1400c1902140030301800604210030041140081642603002c5c0c0c080b18081d5030800d0003031162101ca650b01501505642103a640507030b0f04140010714100000c0306560040c0045910b60303160844a4031f00724060f12000d8806566554208003e04003000d5013184041e0051003900e40010b500b5143c50078840e82c0020789040010301c4150b171241202d6891044c02c64982c030201004298207126941440f901010f51002d01035850b11001003805072052000029 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 409884730 1250 409883480 409883527
    0x170604030201060e1003030e030f03031005033d06080a061b0e0303040b0d2301060215060307121e0804150216050906012303010e0f0402031c020a050102 67
    0xf0300503280c0c0c9000e11a441c071000c0b9401c0c00385540c082c000b400001c0c0b24101c4000d8405000381250004401040700c03d086900544540b800031070008020402c509050003031014007a17617408803074900d9200300c181803101c400280110300903a002c1100f03002458180c1e0702620113483d1920445511404914080009000b4515500500180d05031400c8020f407240c12200441035000e0081c1d81000d00d455142c070300720b07040060010110307070715a031104102c55003040e01114446849078100c60103500d4003034068200300c10752110325981d0204100300a005e481c0055a0360443d01400c50500f4805403900307246004550462224000c551083e03d140d050080398030150060b1480e01d02e02400000048205903a2012032b40300b4034001c804004400c000740e01d00fa1655681c000d0b01810306021459841c41440c41420348142d15100c810000305c0144451070688140560100304000f48403a80d044c00d800095460440b22981e9000c0d901050301c01e0102d52090000003451a4043d000795154034510b81079000c4c0340340c000213 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 409885980 1250 409884730 409884733
    0xf060801150c021c080d0524010f050408030f0a030507051215040b04050708070305060a03150522050d0e01081510140a0815010801061418060309010f0b0609100e0a1706040302 77
    0xc61002180107203603c0b91401d8034058042c404014800645180c0410ac03a54020301106100004000c00c0500c0284a2035444440f89680d4500001020301240c0e0064101d1042200074454060320302c00300d07649145c0201d0144105001850490002000761104490070740d0454240001c0c002c0c507907089083c9502452303042c1c0b0240003a5442100340325615815210190a9411908a1101ca01c00c0c50f4030803900101e00c800e1503504044000c1031841010803012089403154040139114101da82d2244448400c2982407074680d1040c2008840382c842c08900001592140c480001a03400d054002e40300c002110307a00d01800f0b03444818400c0c000c2d00c2d00400316601c920003d42e200020310a58425802181a5411038842c032004002c401c0c05200a600016004580120382401a1865944000180d80b282400d500085859036a5481100c1500c0e107030b14103a80a91424441e2220555034000c825124180c0b516151034095000c100180081001c0d0f4066243c040c505410f442c41745e0360100345548100c0c000d80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 409887230 1250 409885980 409885991
    0x60603050a050c0c0d0c1110050d1107080f16060f0e070812040e040f0c030818030106050a14060f030a0203070f0f02070b03060d0c080102040f060801150c021c080d 72
    0x94003075030a00c144da12820150700181820780546001d60504883d850040e020380d03840c00380c2d41d8042244003da0202c0507021841c0400c00300b21f40c16040c090002d01d0082d02000d079081c800305607213610082c0500c241d00d03400707020041202132580350300451a44d88a0703009001401281241c40d541c0c4018082c0f00c0e00010305004044001c1814240062030030045080502268035003407601113900070504015004031030141180000001142d000030038100070f98003904480c1e030fa464420004079040c2c0c414201d4a40240d05024041001d940c90004035012210800744055280b08401c00207201c600c11903920302c00ca610040180f0001d00611f0303000d90700c6202c05480e0035603040c4141e041a9603002205400343d006070b1003024180000c020050180d031b037000000d00788a00c03105495403142c5142031036402c000e626a50101e03003000143cad81032150324014a801e0501c0303900e07541031040c030418248201c05202c003030011000300314046469201e61030540803114070703d800300380b40c003850300346010751040040c0a0a01d040c40d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 409888480 1250 409887230 409887241
    0x10b0d0606050f03061c060507120c0c0203070e072c03070611060424021803060117100c020f0303070c020103050a110d050601111b03100c051615060603050a05 70
    0x21421510f14501ca800058159a140810003120300c40c0116030640e42c515031250100085c4490142a000300801d4803100d0304a55101d0071034003144d070380c3e11031041040482d03403806000d40c50126221040c1c80700410300c644680d0740e0300015200101d4a8003040c0485038001c1c01e12000e9203605402e0b604042e012030a0700c103010799400040b03465180a2202c4405904060b0225001500c2d001954104604890000e60a0450050f859007242c10114042130301c002a800b1810a0341307010b20134207014020541c40700000c5000601c406039200030a16083c05e03950340d80d036640e6411034000c1010301644c1d10108116962450005002410f0702c240341e2040303021a04010204010201a000e0079060f60768100c191814005020340200c040d040c0907244905020408090385040401032111000400c050b582c02d07003a8840e000e051601d41007000305c2d0344101e00d2410154141043c2e0010844110080214081c281082107050481c0c40d41e041c0450803401c18a030000004034141c1681241c0d04c40d803072020381000305589a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 409889730 1250 409888480 409888487
    0x406090e0f0103120e190806040210111b032b0908190201050703030905030d0902090603060402030715090f140111070803030a2708030f1501020319030212010b0d0606 73
    0x280801040c401e8008981c084c0d4912400b002031507034000903c0050030121201c02405a1020360300322480c2908541c0c00c000c01d6007010541d5418600c540d25017412108810f106181d11542c10354828040110007040c1e030152584d00300500781881d116901131181c1030a9000d550003802c05841810720110303509440028481e000401c81045060f925556504c600c002c40d401194154805401102410342c0c402c1080c004c40c0d070410181c10412822280007a40d00810b004205600a0060031144a03a000104000050710086594000c41e400c1440140c80300200000c2a200c0351307015000200300d07691b42c440000b0b10440000c42e00c102803d0a03241c00200611801c445070700c2c1d941e1800350032019070040003c0b03a001983e40e4001d0390320201245452401e11041c103074011041e829005d05071030740741e808001c0c010365040d52113a8940001104900b01d8090404400117034807130043e885964007070702030310b40c018148500a404079098981601c040c6401d40da11028400600e401503034400c17032110726000e00411240e01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 409890980 1250 409889730 409889761
    0x1005031204030f060203060103020c15060406050a15030b0111011b080105030a0b06010503090316080909090604050a0318150c03030c0f0c062711040c140702040f060b0406090e 77
    0x20802100c2d050f8810307545480000e540040c0145040503420062080251001d01104031400300c10400d52005041045c204402d8500e180c00ca144206400381d13041000102070408584010b445050100d000c0460500503034138440c2c1001054529420700800000503010b032081c40304604015281d07403445903203c1060555401c40c9040013441110002c0100d0265030044000c0c562054036401184e141c00038424140244850100040b00c5012011031900e00d6883c0c00e50f64103921142410040206240130340300c1329544d10301c03010043d090044460340342200307124500c429406841a0322007400041841500105100c00000f010360009107011041c2d51100e22804408075101d8041d40d460407003070425250340c00109039000000c0c2d5054180c420b107104146900209103059030040210490500307a000622041d1407421050a040043c84559085100f0002058912040c1c05403030004402d13020101d40e00c0100101c0c0c0220f01c0791040894001b44107036200704041e055615401402ca40c9455400b6803841e00c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 409892086 1106 409890980 409890983
    0x190804050c0d05030c0f072c0c13030c060809010c020303060f01120608010516090b03011206050910050c2101060519090b041203021506010504090b01050d0203100503120403 76
    0x150082407291007202c05d11107002302c06090440700307802c61008010070b920140100303824048090201000000c2c6501070750080c0a03d49440010b00031003c00c540b00811582084200030f0590305c0031060300d02418010349408040c40302c42005660b0b8601c5000440320f01980d034007000030307100030074015a030041e0590b07140d90740443e440041c01020b114480c1c00240310820f04200401000b18542d2441d0b55064201d0303000903aa4441c0076015050048030fa1480b2900d5041c2002c1c00040e600c240010600001c41282246807642040d83c4c404d54440c09110310000702e10240580d105a1440e20b80d00c0c04d2120b280d141040845031a01c600201c981c026410080c0a0040071400070205030701003140c0b003150103560101e0fa070b172880c00304002030080c8200e025130324440e0f444806903001a4040e000361400311214100335074403454084910804603d2611801e8828800c0341c07441c181001d070640c02c54064a = true := by decide +kernel

theorem cover : BRFrame.Cov 409712230 409892086 := by
  have h0 := BRFrame.cov_init 409712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 409712230 ≤ n) (h2 : n < 409892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
