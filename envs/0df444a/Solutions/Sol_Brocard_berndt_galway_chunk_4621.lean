-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4621
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:12:27.476156+00:00
-- url     : https://prove2.me/submissions/55a3877e-a46f-44c5-b386-c0f6be52115e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 830935251 ≤ n < 831115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 830936501 1250 830935251 830935267
    0xf090a05091204093321120801050f06070302060c0919030b0103120e090703050604020f0a02060108061003260d0204320a0b0c031204050a06060e0615 66
    0x1240200500d0b918420703020220b000708030403109421078000e24000401c001140d9180c41d80300040d150422410b0090709040036410846540c11103c0030801205480040b14010815114040c0c65106a0b00d900002030303412006104928003d030300c1a03010308003540c00d541450741350f603400f0f951035070b011b044e241c00c0400124240ca030607540da1a050503540f40950b160801c4580d24509815107810a020489200c030700c0c5500000940c0c0300e54890041510000c00c20022601c401c902580142000387c00e654001d41c007009803400c01e9285000901c1c02c003999900818a940c9004040ea0070450050103080000106520410205a024510001c0407204003902ca40d040350038880a43d80340703c1c224102603180d001090005200d40c52442c060640d800e03508101e441d250b4441e03581138075101c0035145240d105030032401c24171240000034007610355030070b901c8202d038a0661050001f03160742004070340899259004804400c01c00650b40078810040002c030420300c106080134800100c00d402140c0076203014078000b00b0418 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 830937751 1250 830936501 830936503
    0x306090a0c0c200616030806040506060a2316051506061e0d05040c1401020705100f030b120a02011205100e04020d120f020d090f0506031015030f06050f090a0509 71
    0x4000ca03800101810740d11805c01c040410b41c052600f100f5030100301141c00080060800c0e019a0380304010003044c3c94038001d4280002c0d500c0742003000f4600d0380d98400c0c400c2e9144080c4143d0042550340c152604011030940f4500d441440c0035518044002918150018852a900ea550641d04071100000700054490035110003048107002b852502c006103810001804280710608207032109540d000d20b03108441c040840d0041e40e80d19614031829800462a14105006900c1002c085450240d140340c040798241141c0001070101c502c60410300070b1034001c14000c02c21503800020300f000030281c14a042c4524504541d5071089032149100301c1d0010b60319500041c0855841d0610030b07101a5115107032000104526038010203120354007c0400140c801ca26140c1c54881c010004001110026030030640d182d414082407092036007001d030140e006446a080b010130b2410101024400000547d43c0014031700550350054400e480b0f0950103070340200c0e085480f144241e2150282e0319440080c2450100b4241c59940840d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 830939001 1250 830937751 830937803
    0xa030609140624010f0c031d060c0c1008010f0506071a07020c0109170c0d0804030b1303030f06050f0114160b060307061e0e0303040902030c0306090a0c0c 68
    0x1405030007150b042108015003004a01e0303900d1452031440d00b428070660010f42e556104c020380100800c40342d01458002901c50040303100e004031035440001c402c02c0c405000ca00c01d42c0041c0c440d61100d400c8402c0541440c1002280c0300038806942c580f08840c0c2d40350460703404c00307010300780507040c0107120000380c4005000c42c0c5a0082a000d000c546107212a1405910094a070a0207030320140c0010b10b6910009020b81300d0540e401e1020380302c40302508424401d0b1041059851400c071003140d258109000000114086420843c8141303d03886d11411036022501d80101100c40d0f00b14030031a840e1410006001d5502c1d400301d002d510703460130308100d128624080228070b00f078011030741c5c509e0b0b1101c001e003a1780d003c000c0e08241c0daa0080030140d007201d041c583ca40c01d05440714041190301600c81100c40074408100361060300100900000902540e10b4152201c607980180d90040b00c844141020000c240842418019030260b4407100d4150100000114100024640001014051300c5000030389085006294000c00c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 830940251 1250 830939001 830939033
    0x150a1d09210703080105060a020d0e03150c0301080606031b0108130203070b0d180f080f0c34030c05060903031c0516020706120c1205041b0f03020a030609 68
    0xa00ca2503401c1c014000a03568462a402c50004181d10300009650400c5015a5001d0099402400e00c0e0342d40518202e800745019015103a161040200440381c000314020018080c8a00d1160f240d43c960610040900d81807015103994041d50041011b64040a0403100c800040b000918040e402901d52064803986404c00002c0658180504600010071f00c4070480100020403948006114003c4900703994070b072082c1804405020520460003090000300c5a078001c00d09105804109070410342041d411600e00244044003020524400f05101c80c05112845805601c001c5825180324441c11035489003500c2c0f1541c42218000d400200d4064a20755041c4140c03040c1d0000e414000d90300c02e80110284c805844192008503503403c56030b807040c01c000d10100d8500b0a40342203860320b592085903c042d10004100403c010001c21032003080c10b6000e0f48044c05098046c40c01400c1030407603158005620484c1c900580e0189007243c01c080270810058441119081c200e07030300410300040d0801c00c0d0414151000078400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 830941501 1250 830940251 830940283
    0x20904060801020a170108060a11071218091b110703080c030a08060612010302010509061b070501080901020408341806140d0204050a11070308150a1d09 67
    0x8804150a0030540c013800c55100690b9840303030703030301d4a0340d5600000c0c841c04c0c003c20441340c0000000800c1509150007062112015071100c0d868540c9517110001506141d41d5001d00080c0781034001e40c0c00c400d142c21583e000e00f408603010807003036501581c845a0b0004800111003480035042c40758465030130a1048074000c5400140b032542d900c1c43c5c800c40d543c03a41e0105298a010800c94404a09641850410760318000c40450340240b140c2d00750340040d201c81d006110f00039031104040005908181b0084850140d9141000040c0700040c10040050240d4000400d04003c5a00c1400108046000069254000711050b08050340b19085821060f01905030a10b40c603a01c842c2240d000a58400c0084030300b4665a4500c0c4104040c82e110030050014103d100340f81c541c002020a68400507242039407095400200400340000c1103a81c08031f405085411540f030a6000c81c4400d0100f24030808064402612104120380300303450035090850300021405080810301304107181000080308070300200030380c40b201c4071644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 830942751 1250 830941501 830941511
    0x1314330c01021309060305030f130308070b0a0b060c1209041b0503071209030518030a02040501080c01030b0d0302151f030f11041515050d14160203120c0904020904 72
    0x40503000c0d60008006440f03c0c020003400003072502042c4140c506036940240030f103240148441303035511a9080600101200000c070f140000006512000404039107105542180c2c45142400708181162107054026000b41800c003c118030215001c2400c1c45c09454078a071a68a420243c400f2a00400800000d002d41504442c4d1600500e41c1100c003852003015640d84500c11040c001114409652a9060040118405006480404034100800c145a50307002d01151500c00d11500041c0c01e0ba942139100c08600d42048030321040b01c1d603041c0502c0c0c0c50280c042d42d03010700544156038003d540b00c031410030201c40140e403c00410559080214680c00a069070380b20f14503010b440b401c04000d0304264403c105c2d02d8020145140e50141030a0207080b0176840c01d0a441c6011078903101ea03030240303007600304003810401ca000c1028074800450341c400c41c004c5008507000160b0030306d00071100c2e40e10708450500345010740d481840121000c0000001b00c50b070040b051000d150302d0381d500300c001c200139005500c40654814204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 830944001 1250 830942751 830942767
    0x60e06010e1801090c120201050d0507180b03040f08030603031e040528180f0603140106051807050702210109150204080a02041a0a080102131433 64
    0x40740024001c8035440a814200c07181c0e00941400c86401410040007101203440c1044102501c0358644111401810034519042403011040304540c1c08942800200e51420901617941c4814a82003025140c03a8001c0380c614107098503100610070501070010b144660000c00114a600d00b4025156a0101c01c8080318201c06600140d162540240c003806010304146101040300e03810031030004080c4421413900a0386030b030500c855100d1801e8214480000a44c40c2ca8100c3c07140303885841410001e60291212083c001840b200b031304d003594002c1c0d2003144185081442c403000e40b441d241c80550003214505200b40e88502901c0445c1c9019a000303c0a8101c1c002071407143d402d940190031002c030840c4255400b2480f0025070110104034000c0f8054080290f000c1c10307030440107060036070003603500c1c41100c2980328541200200107058458240c010504994000c00e441984000506480c8080e00203c3c82040d01c42d6180c03400f2810b003d2840c4124400541001c104401c00c20741025040d6007610903081c3e4541d14151 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 830945251 1250 830944001 830944019
    0xf0f050c040b0f0d0b06220213050f0310230702030a030e0714040e01020409020c0f0c01020303060904080a030609020d14180d1103091e1e1c060e0601 66
    0x1840d440c0550304000d40140c407450700907120000301c43c0041c00f82002600c19101e62041d0240140020f4110f1002d07050303060000110321080f10105004c1c0400f40c0d440d8401c224208902c070040e40050b000340c44002550300183d130003044201c911000f40400040b26400c052400f6192840c0c904d600025226040078810383d184c1c04001807130f6401040e10144045406840000d5540610f40b00d07090a51240c00c03010842c5180c990070108100389488009810240c82d03081c21412030780f020b1034030b60455101c145031848029062000a5180c40240051400d602e00400421114540248000c080840016080601d6800f80c1d00400140800308411503c1c1e46c0002190b1009140012000202e46030000004071722808042c0e01d081c20851700300280c060300e04003500540c0c40843e50035600107140802e102d83c00e5903807a80e041d0601c0d12001c2c1072010703c0c25100c2c0024821000200c481441542e2004940c403000798854059018840b8002e20f07aa80d000c5400c0e0400000074001d9602c3c4c019180a4030000145040c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 830946501 1250 830945251 830945263
    0x80a0c1e030e0f15180109090c02030a0f0908060c070201021504150b150f03060109080d080a05010806040c030809180117150403080a0903050702030609061807050a090203040f0f05 79
    0xc2c0e5020b003228100904121391300c400300b401141104401c0082c42170214048603515084001810441c030380944480500c8262a142a40040144e1010036103007241c541c071080d20790404000d404d1000c01641040585519071600503c07a40009200040f1282164801c100e90041c10300034800005c0d45040c140b500501e058409100382c81d68506081c00281903280c25010f00300003810114086250141c004002c04a981000f08014140f203a4a20001490001071010412800c4c0740c1da1116001d250080501081742c81c182c0100045a100b075042000060b0030f28006000d4a4000145e20740784c40340a000a80d8081c1c0d660b441368003074981180006400214804248a0002050169a10721b11000550b8400f1002214040c00103070b50080811380701e514940c4030300f080b14020b107041c519120a82c2c010074a000d1701654038400d140d00600401c040790a5a00d107100201100d40042c02e206807070f200004100000c103014183e039003070740040810104151a08070516a503170090781c240c5440305030f0074202c2d2610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 830947751 1250 830946501 830946527
    0x40b0a0c050f01021812030c1203060102061803120903161b1d0109050705090d0b061e060a03020d06030215040303090f0e010303080402120609010b1309080a0c1e03 72
    0x407149900c59582040180240d40c50180d421002c2030038040d01d101000542c07086c51240342d2090008000e080c1c031400c020b010301032140381c4070b60348182d407400c004000a2511000500803601150510003296013200003008641c28118401c48002072a128034480b1800c0d4801d8003c0108905252007038031081000c2c0483c0d048144801c00c030780d00c05203503031401719861116000c890441e88210841c01400420507951000350031421920386241001159804143c0c9004410403e4404a000000300720395881c044103030130b405410120300b240443c9081e4000c03c103e80140e4101c0400c0c150082107040b24814164099001142c008181139480c40c15002c03024180d60041c001640080c10f000d00200315400710b081800116a0350000c90b08042c0c0c40c51b141100e9900018000b00d9200c00c4000381e40b90420810407486000d45000400001d5040c909020814010003200b919400c06050054030804540c000040d60a0910903090020110403a072402c001c00e003520510901c41e409061010005040e031200c010344c444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 830949001 1250 830947751 830947753
    0x1051905180d090810050919030311070c0509060f0924151b031e0c01021e04060906110a1b09020711011d030c21011107020127140105040b0a0c05 64
    0x4a00100708400556904130b1f45070752298040c42242901e8409144194072041c002d180c00a09040031707600004081d0b21013007043c0d9824201704030031301c52460200160b68000c0b00455002c0c0d00d0a1602c408111000303030044c021a96072145c010b801c1c01d048841000c409800f000203080c60b03403500800ea841c0c200c40d005403211154214024554101007440041218602e482da100d0100d2a041000c0144000d9807040320780c000c0a54091040c1000c001c01088865510607000c6403450301d45003030410017819000c2c981d000f80700304038020107000040d03400416101005508900b802c262105035542402d01f00e421584107800031071002070780a0904c82c1034014030f200c4803004d1703840c8540002c01c0017261060040c41c103c51a4503812840d5240032500e00040820300c1c0c800d074103c816142000d4000410700312607030718440c18403507440090244115a402a0103880d11103c0c3c201000707051400d50038500301040c890086a0191901c0110340ca102d030300902c1038400524403c210550b90301200c46000b404180000403c03641 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 830950251 1250 830949001 830949013
    0x1605130305100218090103050a150609020d0c030f06060e1512180d0c050d08061f03060816031527260a021902041805061801051905180d0908 62
    0x40b074500b8805c1c0030b04a0340c00400030302070304206440700140c000007e00e1801d215661680c00040b0075005002420901404660001e810080c8603005000d940c0c030500d504c030206140038814000c07507801851000c04014152610b503031008035024440040e2148104410b409000581040301011000782c2c8020341c50038180070b41e07a2a0f04401c01c240c4100a1207038005065402c02c10024904034032800c0101c0e40818002c00013601075800c0407840c016500102c100c4400030342c4946090210400411184a17000f02c520307440d8520a186440e0960021048c00030501082d803541c0701d4040c012545c000c0701140f07043c103814082e00600d1501e008081c608003112200c400c560039401250503803002000f0b495141a841c0c02400350000c0c002c03c400b0600010b01e000300d074003984c0e800c042c022015990f40b07045483d038854802002141400b01780e2505403e41c00010204582c10300007044010078144805024190b94202e010034992204404088c00c00240c0403000c406104500d0040649507101000e2402c40e100b1406980c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 830951501 1250 830950251 830950297
    0xc0706021c0804032d0e03030304080712050708040e01082109010e060d0e2a0d0f02011b0303051504090f03081b0406050a090e16051303051002 63
    0xa11814030410356180011034004008510780280202503200e4400d10704801d0711500c5d0018001c00a010084c50050303000c10056041440e50400380100d4100802c81c011410b51505607508940c1e0710078007000030054042041d138808581e01801c291088140e02c111050740300d40c1c480342800700034142480f03401103034032850f00b22610104080754140d42e2940600c0209140c01c1c02400151003010140c1d41c0703a60816010041d2010b070340c8249c071801c4004d001d40c1001d40480404030f014100010058862031004034004110361040ba0340d005030300c100301079120541c480041030600043c0c982050410000d4a00b07000003e0400c109989580000d110303a802c5404c0f01d083d161450305000c221241500000d101c20040f202450100740a08100c82e441000b04210040c0c080030400c52501d00d030019488400420408a0240103141d040362420000c2d000000e803010192403c03420318200881388031031007400d1000004100842c01d90701010400910382200482da609110010448001d45c4000d8504030155292032190b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 830952751 1250 830951501 830951503
    0x23a03050421050715060f06082806050d140d09030b04061a030307051f020705030a03110903030a09090e010c0f0806180c091302162003120c070602 65
    0x24016038001441c20644401c0b800030900e0851040072110501100340207180c00190301c2c3c500c1c1c00c114158040c0c04130301c3c80e142c4020034601300c034250010424010390604115420312400e0403c001e000054003008801c1030210a488001c0c074880d08020b03040458903016406001c41446030744ca04035010011640c1034160b0702421520b400c181d0100511004401000c0340114140e50081c290b50001101c1c001e401140100c000303403460784449422141354000c0d2402c0c01d0b410ba191040c1d116240c00942d415484d08000360390703a07030f2030344034070b14100042c15960581d021a03c4120340642c0c11150740038084176a80c00c411000900b03034481c03621078805218204408545164010701404d0100c016030b031103220400d042c24405480c480c00003000f603604090381903042d5100e2115004030301e01454242d2542c43d40c1314880b0051191401c0c01080c4884210b0041061407a01d25200b050062003540046850b04200c0c10301e8480c00d11052080780c0140d140c480c0000c2247c08042c540300520b4a804010100d515059480c1010303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 830954001 1250 830952751 830952761
    0x1d06040b070f051605030d050906010e1302010c02190e10050f0303040302010c02101403010b121f1401030906020309010506240405010309050a061a0418050706050a023a03 75
    0x62000280c0500101d13041036036440f030180d8014840c41c182c900300480c1c481900300703c80040b00c40c014550b005800400030f00e81a0300b9042d40040ac2c40d0302c1481c10300c6c06900040d1214182c01c50003400381202c0c2185400d01192076a441c1c014180b4080d506803a82070816841c1202500b90007214031a0313480c0d881403041480c001003107504aa034180c4810502d480d19400b0030050800e0742ca40341c41803040041c4042e5a041902c4001c502030004003501584a0411031300102c2084401040d440b150030059420302810ba960391880e1013182c1204107000c246000b00c00048024001645000301018004800d0140840040d00300c03910491094840c0f0404440000e001d040403040b8a810789407103013007004280401e5200740c218040003400f0704e0458840c000145c1d03402c3c08a503e84442441c016084401c00d03511840c01d0700507250401e03403c0004400d940607580700e0781c3e1100700500c60101071040c00903095913194000c2c003004100300c2c0f6284d0038500345600c0480d84408500501d08080840a000c55001c0d2024003d11034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 830955251 1250 830954001 830954027
    0x40e030901171e0702031b03130519031103011401080109022d090606070515012d2607060e0a0608090d0c030509040623032b031d06040b07 61
    0x600f071400207904a12090284003601c1e030030840c0003c01c645d00b10360405814414107195040c1c004c41c1c3c0c52103200d400c1c01c00e5241e145c0041e4403403003658603015801490301340382d44103881c0c101c0130900340f008101c40000d00600c5c04500052010000c02c000050643c010b511200e5598001d8070285d60a40d10988800b00940809003002042c3d1300c0314068000608140081e02d41c004406040c4514001e0f07507440e072524100d141c0b5428156505150700500c0194007106202c440042501078040114498116160f502803040c001c40071744040120880003000d8241d07101c0443e0040c4101900c07001c0361954402032140d070300074019a00400881c24000f8403a07100f4500c0504c102c10423005004018000b00c3c04444200c02004282c1c100001482000701946e40c620800006005501000d455854a180115a1140000071442c42078000e00c2220108400052405004408a42c0a1141a0800c0009400800003400c00748080303e0013200b650181c10001508038041d5000f60740801882c1d40d4100b00f01c514542c4003407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 830956501 1250 830955251 830955271
    0x801050c160f0507030b19060b04120b0c04050909101107110111010e01050c0405030c030f030306010c15050f0609090109020f240d02070b16230702040e03090117 71
    0x84000040b5004600c0004402d109105880d1031369540d8456042030348007039940281d1486900d4050701c0b600c0761803040c0c400500e004c0e01d0a074185441c2ca192544070340c0300e101d070203404e402c6214005054540308c8401c4401a1600070100003840c1084451969100050b041d4101424a80240d08600c2a00c1009880800703a10180d00410181d080d001198119564140c28040751748aa1030510b29800a0013158800c0302c0083c1c4081d122403030f00e01010b02d840c0403690154080e81280354034404503c0d010007181e034440000c3c00c0000300d038551480c003030708031011800000d10001d01d0300040c00b5082104000041c0200c1c1d048980224075200d40400601701e40344400f0096002030300c50342502d114205040808810500d00500100b000713080c11040c0d01d6980456040b411241d40002c00c40e0421034032440158000145107440e122030000a8005446100d041a0b262170300c01c80230101000305a00001180e0324140c0c06442030051006811078a6038076000100d030725010a4000f402c041540d8490b107020f5101301c1c4040e07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 830957751 1250 830956501 830956537
    0x30d021324030b030f0a030815011d04021b07080d0e062706041e080d02030a0903030e040f0c03060807050409050606040b0a0e18060a0902010e0f041d0102040801050c 73
    0x2101030b401040450300e40da40601404d0507402d00c8400601c0b649078142d010792103541041c40c20079104411041103490f401c0c184612490f100190480c00c0c1d450120040c419940107a4400080c0040e10410b00300d0706a03800c0d280301e5108041200000440d403005101d0294440f031125005480810640e405100440e20000f8154a502c42d00f0f42800e8524840b101c00c0544a070345020f032100448004450019400e000341140f1700d104101d420700801140e03034000038a101460030014213407001089184030348000750030010b010000e68200e80d266800102144108601045076581000002d0041d04003440b0309880d900640600103128206030003420b4519500c40e0203081c407642c0301c00801c00202548140b96402c82c2c00200c1c013080b40500412103c0c01080d114403195440b41d0385510b0a4906a0002c00030452039003444048070060341c20502da40c1e41608112400b003608501000420000e201ca4110705941206160b100000300006500601c147c0340d801c0024041070352560740c1c0c4089445001d8001c00000610 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 830959001 1250 830957751 830957819
    0x81207020603070311041a0c0c182e06030f06050102060c070609050a0503040e041e0803010b031f14090603060421020c1801050108093c030d0213 64
    0x96014401707401e19058401c0c205a25007503c0ba9040303152a01d45440c80344d0015080b4400141003082124201d01241c504046050b912600d081c9954083c1c80c21010410041c10f03d120228000340d007038015208800c502c007034581d9505004024060701c5121a101510301000812a948003180d814440c8888032a0a442d10400350b482c800101034205003911203004203c0200002a0f09000030001000440d552003c90304203410828040003072140048014803c1181c2200050300d040e050700d04403407034030b042c140c1ca0f503803140e91a503116071142070b003894030341c00f0394038041565200c196015625030310560301040030795104401d05580d1002543c018100c3c2208440d05040300110405407440c040441c419100c520903640c0205500203280c0c940300c85c0716000ca400502a40d40d21510b600d0b4011030003401044491074400c1c039114102041c7c1c0300d14440d0313158044420078030f882c03075944058800c6000b0120b942e61402c80001a0080d004094010400f2422020010781c2d01400320411648604800e20720b0442446 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 830960251 1250 830959001 830959007
    0x1009080706051606050405030a140306100c061d030c070e0609160903061107170703080f1003050a0803040309050a03030215040c0e1303080105030102071e02030703050709020408120702060307 84
    0x1015142c3d4025082c0c10001002411a001e1075014521030001541c1303030614070401a1100d025024181c440e2001402008166a1034241580120b0668204a42021054103284026000b01c903441e00b04002c031140001d4906c0c4000000f80000540001943d00641c3c50309202d080015080d104198005031a0000c201395240341d40b021240e0441d1401c01d401d20f179a036035450405684003242ca80141d208086044014013055400100c81c01a0f210889450001540d070080c10003000034000301000000a0001201c1000b107a8616000d5600321040314900704103071401c1c201540c0115421000107503c0d4000240d2400c1500c0080f003542d901d0b03000b030302c500c5104000c14501c1800c01002074910741c0d002840026500b2446803072601070811226200700100150501a1041006034011800b0340e204102c040041812258020f00031044a10040c03548416800064a44242504050310901902000080c07038201c83d40104125042d013016184030141c0d5504184a501483c00003940140c1c00300002403581e44 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 830961501 1250 830960251 830960257
    0xe060306040e161d06011706061606020d06060206070c060c1b031e0e1806060d020a020d020606010c03050f13150201020406080f15011101230105100908070605 70
    0x1101400005400360080030181c604003c5420110401810071428002c0d04072007182000218000c0401c0802d82c10194002132401810314110381d01c564110001c5100741c1e485030f0480b0304805075042d03000e01000203400d190009502c110b00c54480340f450014005500b80c004a2001d11403415920b4642030030480e601c4420241c0100303a400c10402400c0900c107a11441c05130348980000d4041d40e521000c11503143c2d14201600e40e107000c3c01c001e0003106121071182da0f84c0d00a0500403466240c0404103d5100c42d00401d249009001c81020520300104446045560000d01d0140915240e800c45015444200042d52884580c100150010700100068036890f6443d0000b4088000c5240c23150781003d030b1302c4c0d1031203c82004200742e003c0140d40000d02001405d600010790303a00400d1503c0b626086040294130b00c1c40e03030358507141050f0500400c220750030003010081d407007159025504a14103034221803200d140c603085002409110710600c00840943c0103940700784035250a48a520000700340729800d0600640b40390f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 830962751 1250 830961501 830961511
    0x4030f03030f06180c090807120c051e1809060703090516060f0f09050d0f0c170c040621023705090106140403110111060f0a05160e0603 60
    0x5030700d80b07180d030300c9816440c030079200240515107080c1c0704440d07800510015528945030107810000250b40500c2905804600c20044440c001105910f00000c7d280051880232280c0c085a0f000e40300690000b04035021000b0765180c904d04440c6010b06a0140c10140003042058942c40e105902610000e82024065480245680e000c2c404840c0c80329030502015854211a802210001d0100340306940343c15008070314059600d0003800c0210b007480c207080c00300b8110304443e000504054403420740001440089540c090203440c2c4038004020004640804941d02c203180c2c101c1a0081d4500540021422441c034144484850032099404400003250200a41c00034210810304981e220709103100c0c2441042e81134122080303608403c01c403040345840200b0044050581c800b00034007203211440d00e8000c21000446069039403000c403000a00c1c01020040361a03140b244102000780c4644002c0c0420740951000c01441420070701c5083c0b1165842c1e1041c0d16562240c176605001040c0b941d480040c1d00d140a50143d503100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 830964001 1250 830962751 830962757
    0x15010320090405010b0a1a12041a01030302210301051f1b06092006191b1401150b090d050111070b0414011b081801020301090b04050a0903020304030f03 67
    0xe40c0c40000003840040041da01122144e542d0b0030401701a003001046003000b044d2400d40c41015480b010201461840360f0509a002d0108000001c1c0c204010344c1c03600082c0c0ca48401d010700003036840303240181d920b088440b64100c9000b003400d4918245070704541180d040e50405040c141006403402c4800400490320300c0e01005210006902c5403c05c0c0310008800110f0340504400b2586040354140600100c4a1a00403240c280310268450a540c54990407609039030f0301540a850f81801400048500f921000c05000c3c8207002082d800c8203020040c01da2610b0103603228000c00c403480840c456035803454414403c001849a05200403011441c0c107007580010180120000709003203d01d2024402c03da40072040c2156100150401d0200380152016601c2d4040c1104000b044044450a000712001c1803e454450170042180001620704405c81414461100407400940d101e5071030f0080007018001303490516020394030304400981010203078000e00005a405402540c0b429055888000305502004415414 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 830965251 1250 830964001 830964053
    0x501030f0b13091a0720010e0d032306150901030204120f0b07030504030504050f01020a120207080c01020a0b0105010e240d1b0f0e0d1401050702070503150103 70
    0x1a152001c40b59a5680d52100009007208a031502805501262250003010b042c41802c001d40c85410411104040d41459405060180348140d10f602514074100c01c1d400300d0048404039120700750143c004409080044203007007114102e4041054021800302d40c0d55500c003404c036001c3c102d00c8560318010110100b047c0b40252900352105c4002d01e0b03240a041c0119460107800102e0010b1040c0380c9919500108030f494240802c1c10203481c000c1142c041c80c01610f1007040506242c450a03030081140480d603a0380160300c441c0000c071680001e500d84803280b00d41003107401080300c8000a588040781446095600030000700351a42000c00444042c1901ca0fa40c0390050b44080041000c00340d020032951040c00703091949a035803017a451040041c1c901072600308184078607a40900d140150890030510304c0d1130300d61030301c0f41c1c1da08804000907208454020303000e0450b01004001007600c00c811340110740b180e4015000c84490300d1b518400c2c190b071507a10121003a01502250010300c0080c0c4c00c1e0910b50804002002c0d2105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 830966501 1250 830965251 830965271
    0x120306011e0c02130e0f030a0e0303120411060c06070c062d050c0f1b010f02030f0f06010e06130806010e3d06170f07020c01030e4801090501030f 64
    0x3c030b010002088001c51fa44080f441700c00c441c1d40920b01c00e01d40c002c1500994104824056002412200078200030098402c800c8100001d03181d0070292440318110900301c50741c0d1700f440000a00300104240c4142c580a0800000441e0300c10b00302d0125508044181c0540311040c40e4085039001441e015200310244a410014240030302c10280203041c0381085070307032401d06411410040900b10341c649040d5112550060080002c55500030f0201303680b080f40201d9a1030380342c0c2c502004a402850441610703502902c0484d99003140e541100c400020394820404803141c0b80d80310f2004506203102160b050201c02100082800003c500b0054103002503601c045418030500646100d240d01c1005420038400180d070303600290140305003c2c0303496401038504200c070041428541d2000b5111b5403a1100141813589503991042048401c01c03c43c600200c001100341c01d11001941555440b4140c1d50500d00424801d41c2d85014540625082c0c0e441c1c000145c4620f45c6c010701c4c1030019006408296001c554056031a01e400e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 830967751 1250 830966501 830966503
    0x20c240708032a040504050402040906060902120a110405120330070314010b18101e0314040b0c2b14150405040f05120306011e0c02130e 60
    0x80601445001020b880c1e00e4481c07103415003044902e41d890a144482c0072500000d080d000101c038151103040d03c010540d81d4403400070501a02e01c1c8074008007000d02d801c4001905c181d040d4094000031340e4562100c4001c0d22074020800c00e032540d440750b0811000c8104403c2100e440d001003034030042000701e02900d060076500c1607000003c81581300c015108106806140b130010940c009915400605030804003c1d03199940c5202c80d10100500034242034070000110703600c040c070031225011103001d03004014000c071f0603900a00130300f40002d098941c0c0d40c0c01c1c02408140328840c002e0060007031400c1540f164549036680d40e2544020000040c02c01c000c4030500304000ba804c420140307202ea030070340040240c0042108500060b142280d13404052003c50180c10343c2440920344004641d40c82079513048038007081649550900300c40c4120303402002805485200c540c0c0300f803011580c1c00b0354403811098032112000011945400c110040b000341200015000344c60300c80c01403a103031016244d280c2500d100019098804400c107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 830969001 1250 830967751 830967757
    0x121b04020a1704060902040501120c0e09010f060b04060207050603190914100608070503070608010b030709050303040e0402010810030327080f0703060e030a0207090902060d0507050d050a020a020c24 87
    0x4e480d02625801c26030b0650070117004c2c1e1030060040340280071481035240c403948682015809000c002810f954081241c6100035005003510031050030013000308941d105a2201258410b10600c2d0150084030b0001a29140003000e0740d01c01c0080c0020300c0c600e80403102c1d00390000c01945908030b5449d0b00d444000c02d100c0c003040040c03100c0d443c40301c0700029070175052040051a003181c5078042c0b8429408542d051120640c01030286045640b00b04500c1e031039890300001074452180d41e8100036010312000c00e00090045400d0756a81c080c5000f1388804200c0d4031030801c200c2210016001c003401181c4403a12080c244040300d545c408034102080c1080444513102d80f00b090428268100c034000c15807103040284203000d074a00c180407030010040c009503d4081c0109010791540070901c6030b019030596404004065490300c03000c41d500a03110301420800c0749403a81d400790294010004500816203031800080f00e03031100b0302c00c5802901041c2c00815003e01008100b090010b00c2541040b000c1084100300d2a00c4551000a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 830970251 1250 830969001 830969003
    0x50a060b161406070507140c0d081c02070803060f0109080609071a09030c13020f0a0c1a041707080f0307030227010503190e0d02010605121b04020a1704 67
    0xa20203003000142002c0d0100c40b0744988076201074001e0300920003041d802074103e450203680b1039044220074182d02800d90070007d5400d0b8207a000026100014200000003004080a110700507038018800780400c03030f41c0101e0080031002030000404002013001407500070005421010145010410b40d070b12021510b00f040303c2a204000701da444028280040d02c0024840000c440365141d05034200441c00c40000d0369003109403a00790141035a030060507100c120316011101503101c1040082d907603851214000b01041c18620f015070b40789980d0400d41d0120801c0081a0380120341112101d9040c80501b21040b0342680b040740216003009040042e4280400b1200c041c0d4400c1100303840c0144c940c0b2103c0720011180c1e2005c21240d52045000c04c030550541e07000300589401103003c000381200c03070070070368500801001e4500b0110154441d44840b001113a80c1500700780c1c00c0c3c440039100d0410051a0307041650b5111061462000e522401959600306030030035601600ca242c80620f042d200014042828001035803003558 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 830971501 1250 830970251 830970277
    0xc09020405011409060f0f0c01180201081f050f010e0909060105180903160c0305010e2b020c100c020a031b050901080a120e12070311150d050a060b 65
    0x40800503580c01142c44469028050f881c0d0f8034100354000040c210780700e2548801c4c6202800b0416001142d180c2e010b480c10990094000c10408404085912901456140c100d001510101c0041c0c1802c6100080d030320381299042902040c0d03800c1804110034000030449080c1040100c4d00500c401d5650009214000c2c807001000e000d903941010f041c80b00500803e01e00d152140c070301c0000d2181c0c00b20700004940407081041c00d1211459090300d00690015110b50001e4025802c2c4400d1142c440004660044403049141203403209181c090100c0031422a000810f1015810500000b0541d041c90068509401d043e450109004074031540050702c0c501e00c981007504d02c0384942d1070f510514018002400040d00048504e2500fa40c9000c40c0c50741d03207208414004000e1882e007007c0c111100c3c022803a1071440301c40142003160441d080c0200542c3c5024078802035841d1242640c01a4071410034950182d1908801c0f400307103282240050000020b020041c007034a00940d0b407001d00180301150301c0c01616004c94405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 830972751 1250 830971501 830971507
    0x321010f06171f0b07030f3b03010e06010e04030306050604030f060b030a06050c121303090510050408070b07060c1d040c05090405150120060109180c0902 68
    0xd4854101190070703041402480454201210b014181541041c0d101c0d00c0905000100881801c2c180414a01a800300e9031000c008580c020805810104c80c0e240b40c12555501c00320110403640c412140ba1100491260301d01030001840b0101d0301d172100c0c0b6005d0310005000810f80c0218592520700d0104268001501000c00e01c080c04100b41e0701d0b010b284010002181c8150606045841c1d00c0c500114055006110903a07a54180b00640c500b80400043c003074110400700011f00c0c00034528a420342c0700c42951440d0440c40e000280e004000764030422a06609603842070441c5007010f041c4092140003a80d82c400340b02c414040003614041c200034402c0900070005545844840391701e014415280e6040780c0f00709101500784174000c01d074004040e202a00c0021034000c640188040b405444a00c5285113407900182000101302da43c01205100040e00b490030313610303815039482071140802015840d1f803020b00349401100c0100040040c6401c000a0041030034046d042d0a005c0d6510501c00402680c00320413040e0f008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 830974001 1250 830972751 830972759
    0x50f06090d080a03050415090c05060a11010911040f020c0c01200703051f05150f01030905030f03090607110c1e300c03030f0c01140405030403110402120a0e032101 72
    0x110b07c904560703600c28090200340216902c0e100c01d5910740c09171a0003614007095a54400e40314a0500c0715119995000304480c1c00c0b14103060703604e06402c4510074025400c201082140200303910032614202d02c0c600144c0300340011440110340d038040001003140200303190070a140305000c003404102c004520400040a0424062480d540403101d40ba1142400d45d1610040240c03008242c009001e64881c1140c20f10b40e404540c10040c4c2c0208090300c0050300302d11001c5009030b80007070004000c43c00f900760a412103003580c3c1c400380100c9a0011360700303950b54580c005110a01150a00802401701d84c4a000312401307164046402051600b07000100720388a00e90806500c004c08a081c060143c400b0340d10350301501d176011580011a50721310501d03a01060003c00081d060301d11f5002948560001d10540b0701ca0310b02030030541842c0b035403500703c1d0000707549022889602020386e103440d1003242d1000d008a5600b01e0603607a0b01030080020004c0c0340802c20540001c03c0341c0b030303080642e0700040303080101c80c090640f000d5410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 830975251 1250 830974001 830974013
    0x1206190b01050a0813080f040807080705030c0d0b0a09060903020a2d15023001051c12140a050c010513050619060504060b0a02010f06050f06090d080a030504 69
    0x300000c09030501000708800c0d651541e004002c1070340401302c4155040f00c80f001389040b51a0388110644540454008100811601c502141f44070468000500311124241c55504240e1a20100c40350b030781d4000701c0b01e8028000200c0a800e85d41c0d010850b09400151004e40d501c40d20140c620717540d0201c0041e0070032000e400c200720301503044a4001c08466903104540001918000d80c0e8412201c014040350148400180d0a075210f80440d07506a996a90490107060301c08125220b14612400d00d940e00c03169000003054030304100c0420078091405580e0721260701007a40350220020411004d1008000341851442d010703400c1c078401000c2c60401c03680c6007540c0c0e100441c01a42120b101400c601000961119400081100020140c0d00000580c112290202d07002140f81c00606a41c0c0c0700c990440e08180000900c00801d03006071071044c82c03a40017400380001800015041b12868001c1540c0701c2401138800115051040c0505003400018185409009090701d598946800044480c0e00180d1100200020001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 830976501 1250 830975251 830975261
    0x60204091b0207060e12150612010e2a0a061805030703050a0212070e07030609060608040c0b161704050325140a03060f14061005030c09120619 63
    0x60040701c40d04040c000c41c04002e450301c80b00d1241310100040b20502d07011590b04d810780c0c0800311403410f084902408020546020080003196018070811107010b00610f410018004c42010101040241040e0440c03996083d003da01228a4664048038001e0316034015281c54414101030196034890f11527070400c00300301039102c0f141c54002c1402900192010000500001510801160304461288416006024440c41d003d04e40c1d003d4140c1c81034010074080c00b0350705580a901074442009082c0322141d2211810b588142040d030700100403e51411003081086005409004074504405080340c1004158640c040c0300320314409038500d042d100050030032807403804101e9031442904c003821504098585000303040d000d11441c42900d0311808001580a181d658003002d14010795440039082002002007181a0000c00c46409030381a80e22000c1c1c08581070345030114001002c20240da842529550341c00b0780c0101107821140310070741c00c160090710f940380c02e072400c0c400c3ca4441d41c0070000500c6194502104182510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 830977751 1250 830976501 830976521
    0x20a050d030c021c1a0403020d030c050306150d09080d0c020a03051b030409050f420d0515090c0901030f0b04301112090909120706020409 61
    0x21400191000000b034001e4990365445404907080e94148481c0c100280c1403490340107000b8040f02907031400c0510729102c0324a96000f1030003542207620102c007030801074045a051504103c0401c07800c2c03001803200d01d00509400d1078018240c070340c20700b04841c2c0010001a030309003c0046529420104404081256610a51010407100d02c010040310708a40c0300901300d4071a54030381d90325000e07003240703446040881003003120014143c1c00410050b40c5040e1701c0b5403103000420385114102680500e40e951444241d044401410b10140c0d0402c1c0362001e010501444100303844a803660030130003504290380803c00c148020800110001d1484009181c1401d80608005900494601c201c20042c0180080340161190280b1503520266070710442d20b4030b0030301e01a103003046100032005040d88060305104c0042c1641d0401d1013441600d8030355080305c6501c0c506898904050b000c07440380748244aa003030030780340030f0b4455070b0000f000c9010b070344200800210881c5503074044c140998005400281c208a00e0b40288588a961 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 830979001 1250 830977751 830977759
    0x507171f02030c040b25031d030c03060727030303021e04151412042418021c05030309150a0e15070302040e01080c01030e210a090801021204020a05 65
    0x514003c02103480c0c50149008011070907802007020703642a40307a04008940140360102500d4100ca440c03070000c2980d05000710003071440c14005204102c6050001e001051440000c020f0b210715554264102d8072200002e691403189420007402a0000d043c040c080c601441c002c0d0f50260b0380e01c420003640034401c1034848030712592407401c0004010702d40c60001b00e0480c071200740c82c00d6400d141d803480041085014800c0c800014185940a010800c810802c8106240080e4000000c01000c101d0026003110460104000031100c40c1c0e54600c0145040c0081801220140c404048140c142d0307242c5074595041110704030043c1d070021900c80b002c00105007055038002900d42d01030040400010707440b52036041c070201901c80c070000080410442030094064074040d200300c1c0d00e020403660351407141c1960b42035490000f902191a00005203071154000c280351800c00c002c02100e903110540c0c02040708140d40100f606604000200401048060080c001051106006030b410b00c13603420a8010800040c2081c0d01407449 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 830980251 1250 830979001 830979007
    0x90d08040c0e151c060e07051c02060c061602120901121e09060f1a03030f0a020102131211012604060902281202010804020d0507171f02 60
    0x552190700841076500c505112100394841180a9403032900902480b58441041003480c00060340c80c2100070300380d40c003070303c17060050185541e00161180c10300d015681e0050703c01c41182910440000b6081c801c10700c050302d400c0c940210282000c2c2412010740c0c59191840590621041465041000114042c1c4000e278883c9131200e0304001078058040042c01c00215520f4040e95040d00071100f11100e4030f0507455600380800c4001d0f142500041c40d90913404102c69203080c08001d500160810811412800940154540b021350810107940350060443c2c0411990200800c0303070141502c0c100790000b086540000b80c060b070240e24101c0b04c0c80c0800d0500604100060164294840b119080d0f81d41e0000101c0c80010103441e00e041c0381e00540000b440294120394403401b035a480e088005d00b141d842c40b00c0070114441003a1542d40c01c1d5454100910041d001401c0540400c000d460902c0041c40c1040c401c000325040c2c02e550704841c000340d10b4040641c00b05504100400701a070081c05c1c110405d500c80e032840441c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 830981501 1250 830980251 830980253
    0x140109140a09020307120c05030c0a08130b070c200303041a070c270e0706110c180f1815220b19090c140a030512280801090b0301020d090b090d0804 65
    0x16014585540b010080b81101192140e00304837402290507800c030000703c40b41d1900e040098040800d050081380c41078009030110300a01d01a042641040b10000d010b03502e0940780240c0c2081414402080d840025000c000c7d003000201078100d9280100014018580f16040b0000f0103c2c280090703900c4503420500348600042d031090049003400c1a140c5d82d05104c1044041605c8103850801c08100c510307084050070541c03c4101000c1e00020344200c009900740740312a030302c80462102c070b102c401101040652000d8400c0b141d0400300d126060380320500031040c116508240002000d0310b00e0800080c1c1e603070001003082c00341280b00b8040c02c0c01900c0d90803130b05001c03c5039544c0d100002c030090340c4103c581c800c00001481c0c003150340e00e0904000558004088601030390b400c5055080540c45003070400b09901600c01010019404040820241c1d003140d120715000b82e10b400c040c200a001082c54442d40b65500708400922505a481041c0c0303102e006100074000f0b40303044e0107a0b9150400302e0445030248428030b030803c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 830982751 1250 830981501 830981521
    0x6030403090306270609140a0302060403031a131406010e0319020d1211210a08060a1208070209010503120a050a03140c13140109140a09020307120c0503 67
    0x204480c0e2011001900d40301c030790035428040c4410505440c0c060400d2511900740146904500545401107c0350040704083c100380d5684d842c00a100100560071400015011902a62000c800384c0b08030441031a681045000080800f06000e148405003581c0700a401d40e035558466000794024020300b440101c4031032450010b60355002400000d007441d8441301c03030801152669404240141e500500e101c0000382c0441c4080c00070303a05100c2a00c590301c10041e180b60300004041c2d21041000650390042d2401036900022592000001d10650700f003940c40c400020070108964810034002c0c010321046858134101e104004160406030300040c800c2d4442802c504110f100f14040710416451b50a00640d141c44042d000d4000c0c112100103080e81c00f40e910200300c40440c102c80240b170203250200d80a80d000b0380b5a000f40c44651100e010403030005901c41010302202c1a03a419000444400500742d560306907580300b064050f40d004564400c000348101030040b0340703010b96000e038412141043c2009400c503d4003103284 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 830984001 1250 830982751 830982767
    0x8030714060712090204020d0203090703060b010e09040f03170a0204050a09060e010b16021906031b08060f0103062402100c0509040504140a0b1806010e0105060c0f1b04050606030403 80
    0x203540c45907a40d401440440d5211f0341241c410000c407100c1551246032440d02d068907440c05100035107a2905090b10f820f0799610a412100a140e0004c0104019481e0303900da82e140036440070004c07820700002d011b45444800c100303046144140300400025960324104010701100011952101500c0c90400320f007803001c440104019815607000b0306409813503501d02c41d2054100120290084d41001c0c4012400503080915440d1a0540301c0c19107040c0f00210440148599800c00407000500041290000c101c1c18600b4104020340c0c081c05240202d601912242d142e601d81c0400c040c1d0715900702803400c15071951901801144040000d1010030860041586009850b83c403400c1e60040c451591480010100800b03545030b04205103107074084980e00c00c02071400c001d5043c420394105941c80103003448179100c8080055401d040e42c414003d00c1440d81d280005111040e0080c040c3c00320b19000e41514405c50010402035400c104011441c485441603034501408100e80015182070301450040003000046034001c458 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 830985251 1250 830984001 830984027
    0x140405071a312301030c05130e07020c030f1b090c0409182f0604180203090309190612050105011d010201021312061503030f05090118080307140607 65
    0x250702c0016041d07003210031861107801c00c01e01c90200d289048248104141c0201c461542a2020005140e0300b1005441d60300442e18550090369801406000751540d280e440c5401510741e00440d40100300f0080042c1c18a000e80394110b4003548090000c3d4482d140a5030122010081903442440b40c2c01d0205501d5258403403030061240c1d03540c4400d0840c421440c08200c80b2459a0004132031110080100d81242101c550b12103250041c0316442e802407440e02c0c15004032011182c4a0490819044204407150040d4000419458950005000b40c034502d072109050560522a098a105001418040040d00b4a540d412201040920b40300040c0560798000c40e001210130807118140c1d031003814510040380640701c1c44007040301500d03c11100103100350041e400704100d584102030600c80c00f00315083d0f690342c040007880090005a1031000383e4440c0e5024030700805600c10185088075501c1c40b100c00c8020000c031550300640b242c0d8800035502d01800720310744812108601e800050680b0b400c025000038045081508 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 830986501 1250 830985251 830985307
    0xc0c040c0c021c0807020604030605090f0106050d1b2412062d03140a03020f011404080706060302060f1206030703080418141e07090303120f140405071a 67
    0x3d03050003440142c005460b4044d5004181a80c0d9913202d10300b41c0c000c2d010a44000d803581c0314500b4044880c3c1c6040c040c0303005480028120174144005900c550188600829180c11403001c0f840c0701140c0f030b0741c0c211046003480f5200d5002c1078680214102c02400076010426400d407003460301c1c40c01c0c002c000e81016080801050301910091170003440c0200da0b4196200d910080481c010040d28003003080f0045a50310800c2c2c0640c09a41805c0020020706090b0340404d01c1d0084007186a00005002501d42c0018000c150302450000500d0741d1290301040b180d51040b98550380c1c1e000d010800c81c025603170181e005640401c0540c00f40546034a199103401d070900990145021007400000c0c44c5d5000c0d600342e4400303651880d600c3d02c07102c2d903030824000501c0381440b80104000e020308014002407a4038040e6442c00d040340e505a80d0f600c040c1d00200d00c0c81c4010030f60081d5091465468440b22010954030141c59802103004001134800d2500c2c10601159004440c031031b0f11450300003444103000d00d183c00c11f0726011910541d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 830987751 1250 830986501 830986549
    0x80c03060a182307021905030904110c0a05071701020910051c0513030201060e071b03090e1e130f0803090c030307030906080c09030a060b010210020c0c040c0c02 71
    0x4048050104031003240d50b507003016100e2034052032420f203025001d01150b400781d03030300200083c54110354a00101400b4150764420421b034440c1d81803c0d0b2009100c52040d040182c14403280841c0c26090110300042034810380c0c4040707001e00284490407507202006c018100218944a03200011981c3d84120301d90542c14400041101401c45001340501528248680c40402c9180f90860381d600c1d441e1445031041c0d00540c6001008181d030546680818000c0011340c68070007c402241031113000c00003d0304411010800e000e00005410418000c0560058502d14502254500311a09008480a00030015031442d01c1ea554800003080c04441150005a00030104d0ba99962b901600135240c054a040695014440001e401c002d140d4055010410750308166920089900c98103440207050060a00e4180d2641107807240302c00003403580d80500b40c1c5e982d060059401e00d004407440001241c001c01c0825a503a008521207144501c0c291007081e8450705d0509017080c100099130041000030000c6144501400e03868 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 830989001 1250 830987751 830987789
    0x207211b0503100501030b0f09061801090b09100c05040605040509091c02031305220207060b0a1215201b010c0c0203061303140d02040b041203080c03060a 68
    0x2405400c0c0a0000502241c002c0042c080344000141070910040d160058a200810225882c0e850640e020342c842c60000c180503150383c0c900712034412a01194030010b66803051044001a580781c1312030320401c802009040d01d5241e00030184283d0304090811010090704100a00c03800b40c11005503003c0d40e1040d654440ca81d6524500b00d483c003070703041c4100021031200da104619074075030000c007c08610340c001c0c910046095440b4148440e110030000340350703002c07868024100c900708155409401c41720300a10000c16244100004a04012801e412081c0e03c0540c0c01840700601a00c4160b560101000c0d40c81000703100302c5c16115144a12140086291025000422451030a0030300c21402090700540700801c40c44a80c40c1c0080c0a000881400700d0090184100103000c01d501035000a08050301516510640c42c0200e0311400b0a91155480b00c51307256090001203940011403000e00068085c41051540b03210003401c01400301c00c401050140243c6040040040d00d2302c9540150007201e45001c0240916009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 830990251 1250 830989001 830989043
    0x80f1f0e0c040609090c080d080604050601020309090c0c012711011e03020405090105061602090702190c06140307023313030e0102030c06060f031c0906020721 70
    0x407103000da8807500b49034010030082e0719540510329980c03140150703c1600380d540000948032801d14803804080b94010000510b241819000700364070040500c1980d02d070010a0002030000801904d031407202d4170000c01c0e0000c1001003445440c2600058810305845000205c4500c0c03079041540c40700920002d80c0d8240034446900403074680900d80d1000c20f170800c560914110043c029003140c450244a01051400050310381040011140e2030546181160b031074000640034090760f500041c0c5058214030480c501e4990a1004403400481b0512501c1003070241d510703000004014208641e04054030040800c01c1c051440c1d00003440b6a03c1e00385c030000403c81c8103001d42050340b4609481d001003000507104c208102d1041d60550030441039911a4403010b59100101004a81d030b070040c2c16050704941c0c880404940755150141d54107012400c01400c40d0951842404041f94051404a0f020701266252100f03120880d0180088005010000c65040410051444030034080412180c06080c50341035101003444060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 830991501 1250 830990251 830990263
    0x60f010207030507080309040f060503030a0c022413050109060f08070e13021201090b130e120a02030c0c010816030513050706181205062716080f1f0e 66
    0xf4215082e64285a901c042041e01c0ba4849410a44680e162540f40003280240d80708010650b0f802500841c20300d01e071100242c81080c903c900c01d980c4091042150114043c0c20340e5500c4a41c0300a00d40182c980003054038203a6000c180381c21060600c060f001c4207100c41c50b030061a103035060120345041d413002d444d590380c20b480c1c400c1c4405102c1d07044420282c1001428000b07800920524507019494401d42c1c4e0f03902c580d1000c0b500181c8806030300c1401e15a0104c00c2441c40d07080440756150f00001c5c0d41891203403482c0703002c240c0c0c45282c140340540c0010440c502c1201c4107011f0010180420308110450346803054002c480342c400b0035654028541e0ba2004100d000800e610140443c80c0d010040302d10140d00c801e0068040e0580412283c9090031064010600310308001c96541c0055108004145584540b42012580c0462401e100702403819103801d2055900200705404041c0300741c0c2400080681061076040c1001302c80541060710368054500828a00c3c4600c01d841c645a082c0000012149401d1503030a0910b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 830992751 1250 830991501 830991503
    0x21060f07090e0c0901020f0111091014070606050913020f0d03020c0d06050a0f0209061615020304061a03010e0c2b0b0a180c270c0807020d020c09060f01020703 70
    0x8642c810800405814038402040002c130240c0880d0074400b050a041420b80703c0c04013008400135030601c50b162450074001c0c1c840e0803030700c07042c20010412040c9101400843d0002542540e09076142d0504104504200340b10340d4010301e40130740303510f8000143d80103d50440c0c1c0060f0014010032000f007610090500c00d0180214a0f18020000c401040c201c0c242400038010942e00744000070b142001c00c1b41a081c4600c212500c00360040c2009007409558001514054000d07030060740c00d2014095108404244e9100540c4170710310501c4d000811400c001c545040d4406204c3e078031806070389482c0a8182141c00020844400031080341d44000407440101b84500c6180c2a6a4440c0d18091040c141c0d0100400e200b402c0b885001902d40030010360825225560388204000c00c054001d09000e40140401e0b550034022200d9003080200b0440da0b0001c04241901319011141c4910020f420318060003007450b810312400c1070a0a841c0300600c45000b407a40090340385400940349502c5010b6051401039a43d000380f151100071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 830994001 1250 830992751 830992769
    0x6030b0306130201083301020705030d090e091c0320090d020915040c0305060414010b0301140402090d0f0615230319050d02120f09091509100521060f0709 68
    0x1841072094400f00c04400d683e20315015009d81d040202c0d25050020707200c404000d0030b40d10840b0440c0760207403200c0308a8002e8804001402811007806d48508640000744010499a030002146403a0a80c00700480540742e0892200150400800003a51344040810040580403107000ba01ca8407010b41e441c003541d641c09250782c0c009051402c0c405443d5010313400980304000a0303a06000140151011070004c400034026516041800d00041c003800b100036030201c2d003155010700010300c0d0583c0b4800080000c410307408101c0f4103d41d80d030400701c1004842d01803c0040c119030702c101d151032410070204802a00400944480004640401c295140e60420440400c21005050048154a02d00b89151200842030b899405880381038030002c2d0354022001250621311055a005040c040020100300c42c9850180ca081150800301c2ca00380120b5580920300780c041d00c071031201a0586850b04092281c00012740301e40441d6184900f12040e03101001087e015800860080c00c0e10303940da0746803c191107040c1203403c07031000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 830995251 1250 830994001 830994061
    0x51911011a0f0616030807031104090603110108060303090409050c09100806130f120203070b0a0219090803030109050c1303030f030f0506030703031101061e06030b030613020108 78
    0x404203031006024041801e80c1e00e0500d58542c0c005020036031140044010f52402c00e504c1143c042441501d0003504a4907914000c100001c5021481c0c0081e0803c0d04007011440ea5410204100850f4095885079000d003801d140c600c510702600069140d000e42d507000c41c0070704d840c0c11a81c420040d0030b20462200c200d004001891505100203560150030160007026114484e03c004900075251060f0141c0704103611140300c40c0b4100e429034070038403102824150507040d44401c0c410707840082d0029444520582e008079005031205c1c000b1000c1400b4910b41d4001405000e22a04144030961000c000c80c0d0544120070000700f45074403012142ea80511038100c0c03d136400703c00b60b507000c010590b201d9003d20464400d0f03602417000740400300c0c00750115201600d200758160721030101000001e00a030440c03512801984000640c0c103903140c000f01604114411207696581185100348003054040c070480302051000c1c1c0c000c1c40e2a00d0507074464003141010b40c00180c14041140005080e440d20710031301c1d4094556048000c11f0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 830996501 1250 830995251 830995271
    0x204110405040f1d15150d08031608060a081002180d030e04061d0402010e04022a0f01020a050a120605060c06040b0a110f072d05070b090105191101 65
    0x10040c0200106280025280c000000100c1c1380002c591050041803035140307440b6125802d081c131669491440c090340110705a000a0045501d5601540c45034000041107042d02e040c07081e00400190f00180450300c0382d22071280c28042480002600714040c0c658134001aa600c00f130701c48980000482540c0b09034032440702e060b120b0405503c0a0100d440c000305071401d200307140c2c90310a012060705556585401500303502d80040c4c0990310450400a000d200074000502c1c110080101030080d0072016507040803030b040c00000a030303440d00c1000203100504901000f18105888a9002061880340422410802070808203851140380e00354030440c000c00b8010101c959400c001c080d25900c440d4105c4c2e09441c80442c5000158900761140644840c50f40e887e0300301d5280440e418041641e603003041d80181d592121283c2d0400489020349811904020f41009070300d02100d051910074900106608292080d213401d02949482d40d03040310a54a091b444840d8200c914041c10b07100300c802c0b02400300d5441c0e0a60030180018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 830997751 1250 830996501 830996531
    0x170a0e030403031706010804020f0402180a090c120207020303070f21120b030a02012309030601060203041701140610030f1104140a0e060d050304120b0a230103020411040504 76
    0x40300c80c2031802441030740366585c0401035950040c1200c0103904042060804a8989071644c02400c00100b0000c50710419201c48004c65004007c43d086134a400e96602948042c1e9a0014414245132403407060540c81e2100c035501203502c90152020003041250b5402a041c10800300c0d01d800301d6000c90410605120110444006221180103010804028540242009242008600e03c8080b035010303110340180c54826016483c880003442100c04030f10406000c44540369074280a954000c0c200d43d40150b0311241003203a1400941761160131454640c1c54442e22100041070a0b545541c084411101c05090106e40d0f881540034185180011541d00c1c03908004402a000c0003018209071aa10108200c16280304814040806060b0040404d11070703007000054103515189840b1003800b880ba00030b4a0074280c1c0e03909101c2d00306000c2c01007162000140f00800481107400d00c540c0c51074190302411240c1c03000501503da455a801070001a0013035445004050407031040c2c2c0211001060064801c014070740d02000c01c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 830999001 1250 830997751 830997767
    0x806040302031e070506010b03130501020403081321120309080c07030b0105030706050f0714030406091a0403020f0906010207080d0c0203011a0319051005010314010c080106170a0e03040303 83
    0x24200c0c43d00d04002100711140164180d4008580c044002d00c6140d00704030805c030842d04010a5004034001549004001407000c0c005800114420b00546864451000038200580003a400210300a0f1008040c0e100703d1b82e40d84030340900d440d00124041c00500702c500c81240503004c8884060700c214000100350040d90070000345041264090806d501843e40c8810030192103d00d40c0c441d2100103101448810011242c1c0e070001c1090fa441100710401a21180600a080d40c0203a0b1004010621284040003251000e50412503180540643c1c0d0b854242954001001031a0080300140540d00d002d00181345e40e4001c10100000e04118021144c941100c2e00c4000c02c4c500b641e203c120300a500309141019148090441d110008400034007802d1262a148400031490060030b000340c50742d100381620b850b400581c46c0302d958041e5026490b40050b0701c050100190a684c0c00b0600c800c10086030100400c50181e01015100900c141d5011908442c1c0f252180f00c005010920340928042c0030005000040640041d80c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 831000251 1250 830999001 830999017
    0x7030c15020d050310030b0c070204060f060e0a0303080a0b0112020c0c1c0f03140409020d0203040218071b020406050405180f0c06091002100609150506031b0310080604030203 77
    0x2110311062140b8011280c070b00041e0751501410013254400e0000030000680203900000700341c40607081c80c9880d00014140c4116900c0b00d4003242c1002c00034800144d02000041440340305550b0108100d103140d070f004043e10380003000e01c42115035508201038982e200d00510340009912001c01d41d00ca2848480c0796441e04190780d000e610640101502104940d50010720303401c0c454119142000c0306400c2e0b141607c2803a1089040d800e4107600f008082005200762010303140101c40d2510050310f0745040e205102e030000700210403500d070a103080c0070401c141e43e0141b03000a00c100f041420701e9881d02c0900c04500a06440e801c86a40182014100306803175091018401c01c01803400200c42c0c0070110090259200c080d4507501c9034001d60100040c07606401c0448441c0c0140d0103510441c6c030540c4011150004641039170300071035559503e42503001010440b001c44000a0882114000c0c51070502e400c00e0075005076510302610b0310000100005010000180e40d48000304261800d9416500e81440c00071740320f80c03002e59 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 831001501 1250 831000251 831000253
    0xa1202060a0e121615030e0303010905060102031603020114010e1605090d0c0b0d141501030506180910061d01141f17010b18090402031f140601020f070e06010207030c1502 75
    0x440340480178840c7c02508030614454002e146140d0820603d413001c0c1c01c0041105040d480304220350a000c0300f4441c0091841c90080d400003542c8a40c40080081c1942d0690102c1c418000d0328003402030140185100741c0300c090a40c20b0540e03541050300007041c0700b0540150050070031303204042c0010743d80c12020700510444000326010407188404103145401448261780251410240203110071080d4000d40c4516081400201900a401240900300c02001801c031002025500065421914040f180c01031a02420826a510880700c40b2a544c4c0520804144200000d02d04982500c3e00981c481010560700c0140c8a44000400301081c04050864590100c1c0d05400708074040002900c03e0f4840155001440395402d420000007031101040110040a4000e981c1405000000700b12a400c14001c5000d40e801542d01103002241c100b200503800700000e0001e419900300170203220f0740c0400402d4140680d80300140c0801181c65041c0102e24069083c0c00c02009803070480303000728189030001201305034800558 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 831002751 1250 831001501 831001529
    0x20a051306050c0a0f150207062a0e060f191e03110a0509040b1309020f0904080a14040915030b1e060d08070b0f060a1202060a0e1216 59
    0x41022a040c3c403d1100c03a250b55005003000c14001000c1003100f506013401049014503c0001890100c101d138040310045808960700d0000c01c071440c0b00160310740ca0b000100040342041900d1060040c14103500380c81d40078441c0900260701403810507024280c0d06102501041c440c41d4040d81c027000b500e200c820081281501c1c0c0020580180d242c42405641082c0072040c800a091008a42066859400600c4040e50054480c0800901078450b0498451b0020000380b021a0661071401480f4034285100011b0b40148d004108000c003041c0d8200071900c0d56141c601d03084084144c004c610a20702d01035030300510006810310503c0c04011108180900990b80038140c1411151510001200e0101100f00466418560000010400d10344100342e4454a406015140d00d00700b6580c0d5030b140b04a03c00c69407106144504001d008890400d0300c002805440b000601c4441c03030070141c0000c3c105008100703503502003005100191189881d4051758020401c500002c070740e8803260176840d00c4c100c00100c3c002d02d0b005d20448 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 831004001 1250 831002751 831002759
    0x50f010606140c0f0a0b07030f1a0d02240306120d0c080c0a0b0f090705180c09040912120b040216082b020309061501020c011d04020a0513 61
    0x18490901140c0258070341850b01400100400600d40010303400c00c200380200c00c1c00040d00042800035150305071260f0914420361030000c1000d011201925480c001142c5000c0c040700703031100b900200c8000014129041d14030440c280c80020700038060844610a01c1c201c5610340b02e03141c47e40300040c1d0301460044a4000320400260200c503a111001340d12030300010521003001002c40c0c00718004052000c140416101c07641d8030f07070711a0320b0f40b406c0a4034403034088800c40040104508090003a14060042101c526070b030805a13109480c20f14901900b05a9009000600c0b0311050351681d004d601869800020380f10141110b440151406501d040640d00160518040c042c0529103031080340c840503034001a4004081580c0c49114a0303402c074500c01e181e01c18a00070718400d900e860b00e0081d40c1c448451030300983c3c0d9103010680e843c107048000d02a46001c0300014910411071384c000c251000044020300c0c00c901640c03d0500364144c0030440880d00c5070890304c001041c201d002c0e40000113100006643c08101801c47d66 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 831005251 1250 831004001 831004003
    0x915040e1305191506060c11031203010b250f112b0c0b070c170c010519120c050405040b0a050306010e190f0207060b04110d24090603050f 61
    0x6040e0004103a50030480240d0260716500b403060f80024020041c0c009076035098258401152803130303007020b07000c01c05403180d00d420441c1141c50101d0580c810390142c0710303052503070102110b00d02042c003502654020204d000308140b01255181d905031030440c80013642544150400340c20f00741d001d68065901006924042d811400c0402c01178041b4010f0140492905042c06212040713507a0b211011258410081000038040491202a00c809805821700b80340c00c0385800c010004c103202900608506811501048050740e805c8000c0e03900340005014201c803071aa01c0c0904440e981c1c10000030f0500c451600d007002c45544c0e44000580f0507940244d40410003000100c0401108805500c62150b142e44100014030601c0d0704aa91030707400c68141c0b243d04045103610400d1106442c80b00c000601d48139070101d9590180000307400340c55000201640c1c00c000b10846d020141ca4a44141c0d96164042621605115258400f118104d641181c40503c110b00640d04c0b4038010010700244d20080e2954030a041c941210100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 831006501 1250 831005251 831005281
    0x30e0d030f1407080c0d092a06021204051c050706030605040e014d0a08131a130204020c1c0f091505041d010e0915130204020915040e 59
    0x583c1d4548080983d01c04036100102d5015907080300120341c0f03130308160700080c0240b03102c494000c010605100c000e42d10000301c0c2d41341680707681c0a202103505c080300c0407400403000002c4600307403403061b0307005100009103001d02d44500070549002005842076000014201d80c2c1075025000780c6104a80502480c0c0c04462200d0a9641013000c14074681c3c1d000449034400c1401006881261030000400a00c0405905403420500c0d01400d407008010000100d0424180d44050500e40c010450099820b005080f5103840c900c02840396040a241a045404503403415110b00030a400194000c20a65a9a85d00001d8a880e941000010300c1c8200b00e04421b100480e0241600241c45c44a540da00c04116191591078254070804401100500030104000b181c1d100841c07041d02d01010b480c00c00e00109502d004035090741071400400307040711a004000301109048015170602c2d04014080c0410700ca10003d400060000e210b9000340300d13485044034a02d07000c06a090806001250720380840c840f0183d65503914444400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 831007751 1250 831006501 831006511
    0x507140a171f090e0d0306080a02101b08180103060b12060f130e0c1504090506040e01020c160609031a09011b0207030b100305031603030e0d030f14 65
    0x10001001420340381800000c00c0d60004891115071102c103a841140d40102145402c400b05441e21a8084d102c100ba040080f000038040a00c3d0810510340b500202c90740b21100702800034070a0207c4001e00740079510400d1100192003604d00301c092060b00c03030702c0c1030940c940c46540103c8114252105140880d8028856007045500c00785400785000e01921140c000c2d048000d0400d58003958411284e140c548451340b400814441010780008c0c00c0d165030401d40e24040c0501962441101360402c0e00c008a052481070300e0440f02d007140301141d00c2c0c48290005000d4509549003000d07540c03022607900410140055910001c2000c40d20b50503009803108401c0b100e041a902002e03040032403000f00d400b00d8805040c1c00c03c0c1e0294a280c0001a0b140102100540c22060303036580e4030041e80302c00c6041c01401030b15a03055030402110f019420070740d86180d403900d0301c038041c6288050310554a241c4403c24940660003200c2c552725884151405120b100030007900034600d091145031580d182040d852100c0d42c0703030b0920501030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 831009001 1250 831007751 831007757
    0x207140a0618030f151802030d030b150c0d0f030204060c080d02090a09050702120306030d08060102071a04060f0e01121109091503061f060e21010507140a 68
    0x15605200041d1001114030309994200000b10000002103280c4c3c1c2e0701074030a41c1c81540300c09055101401c42205454a150980140b60000d51a100c0144d43c0043c0100e411540c608020072000c5030701000400c070351414480d81808000c00100c2c0412542c010501c0d0505001946400d009401c2c21b203021401c900540c010403020907408000342010864030005041141020304000d490543c241c40415582d00700740e0320450010f602c6d802840a000e806000c5440c40100c94000a41107181100010356520300810b4000c0c00d12400101103152a4420b01a03680903180d009003014034081d520000150712344c00b070b100f1400020541c20254500318410304200b50a80816074840544041d0005940d00401061600301e00c6464104043c200310f423500506103202d0030074000031b4408104020245402c2071001822501c480b8805403226020741c016002d020244c07407091074044907075121600454507040507071985a1080340c3d4030707505007049401500318500c1000156a801400444c66a81554501035941c100001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 831010251 1250 831009001 831009019
    0xf070806091513061a030d020106170a031707020109020d03050901020c010f1d041d011e0203010b1209010f02031315020307020309091003020414010f140619020705150406020714 78
    0x4903031281c1240019140170030603465185070843c0000d142c04a4480c4060141c3d4660340100200250f850020020008850140240d0f00341c6072f6000340070315600300e184187c6040100c08107c0d928401d40c820740c4404d50242c20380a00b0829414040c040d500000015401031040811001c01035100d10150f200700701c501c0c1c58503402c21740900078490300c10442c041441c1c0c0080d60741c950004003600f41e6144625400101c2c00014181c0c1d160303600d80038a80480e600c20400c081c01007004000c4901060b084541444000d5500d40143c0c544040346c50248c06901d4000800900200a00c04000024000c0050240c401d11100c0308607000180500f0070390004841c104050f80007840100701c00d080202c000f5608c81e010240101c4400d861b030b80040c0413290f042c1e00d00462446201c006100c601400d25101d00603001c0051034811801e60900000c3c141d02c10a403907121000007134502280362500800000c800760200410301000501c807610503c00a40240c400c420040c81440c00000303110000810f0200200c20242000344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 831011501 1250 831010251 831010253
    0x20405102a1a1e010f0303030b030102040f0608070203130b0c010e280201020717030a11120702280305010b03010f06030c2601020d02070c090507200f070806091513 72
    0x142c0c14100a00450482600105103200380c0300e0141e096010703041045070002c1c01411820020112801101e401e13000fa07104010500151070404121003c45003d890034140c00d40d45c2d00002c9085000d0081c1c0741c80c00550302c01010030041400030160803a0200e2800070403510003203038441039a0300492200070a2354110501a00062a95202c41504031030041c0111645240e0b00d650031300118200008250707858001095002a290307005410345903800c1c1d05001014040c07903016000c072091240742802032081c2c010804004c404425000d0f80031000002a1645000c039a6905207540600564040c55209501c2c01c50401c09002c0d140c451719094a4004421041c00f40c20300005607110000c2459041140c681c000e07415490720024001403003030001244000d43c80d40c541e1b203071048515140790003551750705040000708807000380e0240912910b9500d0303160314805229948a01814402c281200004900940344041480e03440002d070b1900031401c0300300300d6801100d440310b042e20340c04056075000200b612070003c2030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 831012751 1250 831011501 831011543
    0x50a0c0e2e031d030403050c1206011401032306030105130b01051c08070c050f04060b0d05150a0305060f060616110402042303070915050112020405102a 67
    0x7080680c06030a0001d0400003079010a0011201034a00b66025400001c0510400400740030980d5030300d40940d0a40914200340a01c00c2d201e4005001360088004603242e41019684a5000071502440d10301c841c031840e840c82c920f40790100504440280c000c0d030800c004034400701e00d5582c0c90150103400403d10005c036400e16003082101806854040e0418070489460f00104940f400140403440c030507601300b0581c0c0d01e400140105180c0f10f20701c251040b49807083c1007008003410300c1203c0d4079200f03001b8005000d6a6074400040c80c0b40307016901d10780000202c1004130402900040340740c0908480d0300e03030121030344d240e108000700ca01c1002e0354040c1d2101000d2903180010000b0416400d520001880036050a866850b031281e10742d100c003250007910b007617000c89c00c2c00743c10203020020251522403c240311580d10311b40c01001c43c0e00c161007494100460301c4001184001654140c40c080c04004098100040c089900102000708006540784511840940f02d20300000c1e03160841703100c542c000301c3c4402d111b054440715 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 831014001 1250 831012751 831012829
    0x615010f05090a0314030304060615080f18060702070810060602070b03071b030f1b0201022503050304240804020901181503150c021f020715050a0c0e 66
    0x503d8000c0840701000c00011090002c000549000380015a100e245c542410b506440c034542c81070f1512803070b01100b003040940c0302c41040e6100c103561601d52101d440c2ca0442d40840e020003042200240116024401c0035640030603c0c6044a10101c1260004c1207125407210841e065441100023503413080a08018a41e507134400b03154029464108000e1030a002142c4481180c842d2000b100015980f035050106c0c80d400101d441c2e00c6e0705001d030714142942030702e500113580c0c3c0d19401c80041a41401480744000c40b41440c1502c030156500c10292620741d40e40700401c011100b10341d0b803510703d12010400719410070307271003902c03514840c6030002c14007503403640f810000303545060228140c603440a495030504000c0c5149a0782c1100214442e00d888145503007880083c000701c4545030a00811508403400325041032501e04540114006d00140c01030b41d601c00d5207002940341d88003541d41d071500c900301001c2004040032544600c482c0d030351030384542e00000c00020401035186c3c24503440107030505001c4ca1a0080c408100aa = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 831015251 1250 831014001 831014017
    0x501090e120d0b190803030f0f040b04030e03160f06020c06190c0606030203030a0f081308070b090c03070315050c0316180b040b031501020f030703030e01110c030c0615010f05 77
    0xf981c68140601c91850700004d458105140c2c0764000030a1089400d034281d440c40d4072111076460350703049040c6680e81074468140508090100324904420304000d9806000034018800c4203001c3c44051941d403e8400819600340c4541c402602400d4111511400d0107003c50b04281046c140c0499500c0301508152000030b0841026240c0c260350f14000310068078200020301841c06251958203a9890000340206007d800814400c0c46074820580030000502010507030f524598003c2d844055076031050521840c6c00c1403120940d9042c400c2200010900265001d003001c80e201c5d0b0b00c820301042e500c140c42d000301c500c001e03914400390200580319000654401ca030021450300d414244014042d640e200c503004113030010303048200b001030004280103240f0300ca00d0300c060f40f40e1420700142c4140c202d040381690722800f5049003d8149505d034800050844c100303510800651814822440c1c880f40c0b1030b04199034a4200e44150b2105100b6180460382c00f500b0f07203c09001c4440305a50310715003c8a121401c503050380003001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 831016501 1250 831015251 831015259
    0x50d090c0f3503070c24020102040524090913120810030b04050708030c010c1205040203030a051e16030e0906060409021e040617070c02010e0d03210501090e120d0b 72
    0xc6480090b02d10304441c001806004400b541c40108005606c512a0b000c0d02d03142c086d0ba10401c010030481c0c8605480b10389000c103001003581e41c8040450401e1030761003010040b5500c041c00a04110710a000080f85c20f03070450040001104414010409440c2404180d42903020368103203040400001e40550340c6203501900c80d8040d5051a80d950010ba413540e04003451944459444944248000303910107004004090440410f12980c1801d4022030788a11038500ca00c003c02000198680c290341d56541a0020040040c142e17981d102d80070040000070101c3e03080b0440004281041c0300401c0d28001e00402e0182600904c0d00385800c0c40d00c1c021000075444040d402d0381548000c02540c07400003611010b400104007588880f40e8003283c1c00b444204924000b868007040c081120b80d040c0250740e1001c000d40e0003660030344541d403940c403240c203080d620800c40341e141031144481c1c03030482c0318184220f0708010704980546401340311564603641025102e210301142d20100311014403020741d517050316401404208030068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 831017751 1250 831016501 831016507
    0x20c1e070e0703090c03110f0a0b040b220807140d1106030703060e010312080c04060509060706060305030a0c050708030c0a060c0903021c110405070e10050d090c0f3503 74
    0x7940d50402581703154410345405007409407544070360411244075003118008a880c44903c82c10000800018016401402440301001c994903030b5149040e10081c2c900851400c001c500280e0b02c254032561100c041c02a0901401441030022483c2484a010565203502500c01c032168040d030000d202064200030f0a2800300750302c030f1900069a580d40c0d00d0543c003031030003880501074824120101074900314024081201c0b88000304020849070f5406000d03102140405c0780d429542d50147d00300140600031940000d800c60100040d0003182a4121860304042441413050704c111690300c20b00c0549170300a84040d11190303041111628000746140d80440c40b514100e0800700d1001f51650041095004424400da080401c014001070501030103107195907052600b110180214a03180380014002000081c5d443e01072151140555101c40c06001034410241201008100d544c1c02400d0060a210039441030100c29820f003280411100d1745407500310b000000c244079824040b00a1002c01c010318103541c0050545000074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 831019001 1250 831017751 831017753
    0xf060a0c0b250305060906030f070e1e160f0504210212060f0a05150a091d031824040e1015080702010c09150302090f060d020c1e070e070309 62
    0x80d88400c5060b0750340c1d0380018180740140511032044e5001d00228413039030000b113020900b0a030001c0c000c010b654080044207a40d403101d007014004c1c81d0300c14204c807403032500c10410003480c07028440711318000001c10303039480c05814500341060f035140c0b241d4050b490000c024142b280e0074a85104454005440c405082c00360510403540d5840d0a100003580d101000d42245401d1100c101c0840c019036400a020311108a800000700c0c0c00210100030f01d2140301886070319108800c1214031007a101da03902c00b00c10f00a45e60781d04a66441000401c030100480341c80348080b42c4e9900a81e0301e1030001e4050500004070f07540d24060410322a041802401000302d4006090fa600104d114894402d400346640426240c041d510300b0b1100d401307820340e80c8440c1d481c820400d4490007001903000314000c509000489050040e600c00d0384101040c0d0444070191600e420840c001101321200505500514813444140c0c00d60b9401185220960000400043d9078201548801024810701d02000b00c41a003140403800c0004814041e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 831020251 1250 831019001 831019051
    0x31c0e10020628181b0b160203030c060c030a11040803030612030d0204180501090b1305100803070f3807170a09050601141c080912010b0f060a0c0b 65
    0x20300c4542440d095400e03103c0d034080102c01c5011540390b11036010040e07202ea003080d1b0f0b610340314059081c040700c01c030b8a04500e41d011364806008449950304280160355052918000c0048035034815940b842d41f940c640f00000f01000100c405503419038282c1c0c1e02440c61600c941d000c1201014604d40e9035a0203000800a000c02d9180b00d10007400245501d40d0b0075070300803410541220441c0c805900c009411410120680c0d09903561483c80c406081442000003015242ca6100d2003409016400c000174501c80000d20f8000e00c4030171070244400920654000c140039058200920b809628034008882d111000c0d0810740d038000504038516844981840d055041c0c0311001c8400c1c81112080d61502c420319a94027181b01442401e002300c40c0035120604180002a6034180895454800708181c08054010003015404024023a01240c000200081030084802c001200080c02090500038851080c25240c1303403240c8505090003680c60008160315000c07441e10003a21089600c0c0c1000300810880900c0c040582c0c1e4110f9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 831021501 1250 831020251 831020261
    0x30f0703172a071430030f040605071202070302030604060504110d08090301060b090a12020406170d02060106080c070b0901090606060210050c091518031c0e10020628 73
    0x455100603d07401d032401c83e013400d074401c40c80c035101d000b1484c0900c69100c5043c4540100c3c0340034100421240b00320303a8000341074114001c01c2012502c80d28001000542154000041c1c00003e005444008000f0400c0c04280d0b45ca00003407100940580200c1e00080114120f5841560302501500c03020155404490005103010802d45048602c00380200c0d4100356824240f1902e070203020949a0340d8a080520350020741480b20521076002c404a20f9802d040454955421840041425522520113a0100f25510b511074040c0200480144117640001420600c2400c22382c3c041d43c1640301492902c1d1050b1550050081c1c01004800350303640340d01048002455600c84c500041440d54003030058074080c079540e00306803540904404000e600a0007006099905e09901a04504c2c1803045540d4400060702100c2070281c90b800d80c04e505000384410300c401000300d40e030221014003042c1d44502110390700c101081a900b200b41700c680e0040c7d10403800200c405044144400c0c070b903e03100031804c5c0c07410001408541079038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 831022751 1250 831021501 831021577
    0x40b100e01030f05100e100e1f020301030b09120d020d1d0f0c03070311010c020d081801080109091115040308070614010b0c030906070212060f010302030f070317 71
    0x3001c0030f810018401c1c284030a0b036a058090320309008032001018810385d1584040c001d03404456032201e0b6011340c40c1d02000715140c1000c5c502070110b20545a084544001d400074402030364040c00000000c1e03d03004021a40c4403003c480010118240f004403a142d030000c1d00042120030100b0780c1d0311074030040d520a0184003580198490b00034a024965051110700300002c406500d8069803007800c05100251585010403c01d50b001e190070001c0c0300c42d07800018540c09003018054040701000801036680400d04000c5e2403070803420b881e4000a80d070b8400c80c02048511640c0c1c0580040f1a02440050614090308410b2900d40302050141c10540c894032500810347c4141c0342200c020340c0d10030488c404c0510041490f8010914610745a0510905a403507517160311841942c0c0d88500000604c00c0115038540740e10f8101c46000d1000c40d0280e01c3d0111007418503110a000a0b031192046140340b0000080c00a200c005032503000000000e216040e515080a42e0404003141035000703400320701240c8031002959610300b00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 831024001 1250 831022751 831022763
    0xd09080909090d0207090908030610140304030f0305060d030819020d110702040c0e03060103060c091a030a05060402090604050904081605061008120a050c0705130603021504050306040b100e0103 85
    0x1070400d142c0281c07802c617982c0c3c40b0240007030404e0300280c045080003050720760064041c0c400409000026034201e80346044000401d041d410084140300078154171010016071519140c60402c05519240f0402c41c480c0c40f8500001c00180803080080c40d81803007400550940340c42d00a0140c10140c101411506881903145070070f2110f1804121101989020300810703541e0612410055016000200481d0301c1d8601404048c022030780340d081e4405018412900c0310000c26074a1111114481c0c21041d121450744240c071851002030500c00400c00900d03080c4201c6455807002031089290520701014003046002c001c000f60358004040c88103d02d0000c5400e6500b0000b845031000e4441850000c034014010340140e00a0340c016400151726052003050b180c212044160941000d82c0c40381401d11100e454404140c208540081d9020050300085030184c20032410790f40b08540310034001c6496144084c682c0100d20406030305134480c1e0085008142c4184825401c0f1060020610409440d0541c406000000f0b0f8404c60341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 831025251 1250 831024001 831024013
    0x30c050106181d0607081e0c0304030f021b10020a0b0a14070e030d030b120d02060105100309080904091712013023060f07030e060c0d0908090909 64
    0x3091803181c44402c0038100c0f200514030084400076580c4040c0181081c00f07008644000c5050481602d550416101401c1030b103c2c02c5150040c10748103250020798080780031030001031410041600101e15900210824011004c030f8103c0181080706002c1c5c9030890320154041c400c174040100380201c4015216079100f500c0454103600c50603011050100c010f200740100280f001d00b0510fa99008034111655100625010911848850002d06101140ca0f2540618031446410200054020800f181212000c440c0990480d113a65010340940708240b42c018486030007000f00c1c1d201c9107440d500c000382250160000b0340460042e114034205a43c00a2100b6096000c424010000a0030404102d40600100c00b520700e40c10010b2401c882c480511000020001e200301420f40e9428288180c0c48000908020100e80540c100138603402031b601c4c03040c1c403104000707400d104018100440004405e400354691955032440c0c1034080f9680b50042400840490b4440010040c00a041d40c40841c0c0300c5c010146d41025180d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 831026501 1250 831025251 831025289
    0x19290405011b0f050726070b07080912031602070302181603060506090f011b1a0f010e07081b0f030609090d120f09020a032a0e01050d030c050106 64
    0x4110411040500100418101d0800400d0b50103400d82c0c841960040e10603444102e960a2046c0140301d111078030328090070100b06e400c103108603018034038060210754a848610b6120700f20981d4652000100c07201c01c81b0707020004104054601300c96001c68014a105580c159501d0740d000404000900442c0c40091003007a0a1102d6810384480240500c034217030808100b00351802010a400d4002c40078490b11940484045000316400750040c0302e540300c0b081006d02840c0040303285c5440610b02c070f401c5c1000080000b07000111651506c01d01103043e03610a11542480ba03490603011640c41000a01c1040d031513000120140340d050300c0c0340c0a05080d51032042110b487e0b2900d90300b4000c0128004200d4041c0740c0c020080c01d503055030800c5e0103140c0201141c5002c00d4000d05032015001420020500030741145107880c001081c0070000e0b07003091207015002d080082d840700d03101c251100000c0701d00501c00c0344620b40004100d030340380441c100b80c111482400c1040d80000142c458608440240e803013284807800e8040202 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 831027751 1250 831026501 831026531
    0x41b0c03090e060114030a060902030c04081b0102070515040509010f082a130e060f1603060608062707050315010908070905451929040501 61
    0x1c00600100c400e41c0070140343c0640000d0000174a00741580d4203140010100742101d4003600220050040200700759683c1c241210488483d0780070b4800e40782c00d401141511064080c410003183c5651905a008090003420320341000320000d80c00d400f5800c609000c00c800101270321400c0e50940201044803070300c908a4a828881414070300d92240444480403006200841038603c4402254208025240030f10448401c00c0c00b240100003d000b0741c3c1840c070800040100550340c03480220f1045001415100f0b484035940001c2c1c050314458054000401c0450002038041d013402e403100140940446107070001c4169004642d4002541078400000184000081203c040e55081c441c5040840a28003040d905103001c074000c2c0ca80c030282c001c4200154440d03021030b0002070381190354864070118148101d050307d910310144118002132070500c000602c95480c15145c10346c0215462045c584a007401040124031030303403504805289401415401104074039009921801040f07035070f100d039108030700001c0d0000c0522007007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 831029001 1250 831027751 831027767
    0xc0a0309140303031b0309071d010515070f060b15190e0613050f04061a0a080a0504020d0303090510061d18120705070b03040b0a0f020c1b041b0c03 65
    0x306001e94030400a000303d2520307140f24060344100441c0d03646c1d00c039150000145c0c1840107580c0310010703207100303030f4907001448a240c3c03a00d0341227171011036000700788000340c1d1b035204094000e114018124801d0078440401007207854000b211070f4034008140710480c03014006440d48540054529204604c0c0c90b61a81003c285c100740d8101805c0c00c12500c41703040510100c0c1d030b03480c0c0100c603010355400f03100080c514020940f15900300c41c0c0075200710070403608610030012105c11903402c101041800100d11501042100d1100d22505000b2038001d4801119903115846c150043d000d008005c95a91141030503c01280e0918030808000e4456941a0001d5260984c0c0d011885440501400c00d050500e41e08404929000901c085036a140010101d4680c0c41505085040c550f00350700940480318008104410402c055960500c55404200100402c0d0340012408040340110303084969540d110040342c51603400d0f460a10404040010f0001c10b00ca5102c49035520710122084c921004900c00011500400d9088011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 831030251 1250 831029001 831029039
    0x303021c1509110403060911030f1b010e012a02060d0903020606030102031608040c0f0e01031a0606091513033c03030c0516120e330c0a0309 62
    0x28480d203a060007040e00e151290b40701c01080e45560328003807800c10001c03009100503020020280c2b940043c51071030968460300300340b0b1115140d40b01150903503200c3d800b0b050038501c03194069568140c03201190550100c20f80440592444881000d00c0d0480180da036107008202c0c1841c1d104022130070000c107140103841c1501c0030340f215100e85d00520410511084037000c07000268202e240c40074413070f2541d003064001c46445410401c07416030780440c049002c000e8400d42038105e9114040081d16104540c00d90304e0700ba41d094a0b4594000e00810200c90f191805071070500340492403140091402c10ba010480354814421f80c0100c40f0040700c640c1c2c1d102e800348801c4419001c850b0144240460a80d45103a144500300880c00050a0641d0b03418424002c03440344050328901c18234024040c0800059091080c212600076141c1d000281c00510040b502e4200031360b40b01124610a1420f05443c10400c400440c60a480301803443c04207010700c031070035184104000f01070211b4002d45072480c072141050014249081c6c0c140e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 831031501 1250 831030251 831030269
    0x181209030d110a081608220803070b0a0b0a0e010e040215040b04050402030a09052509060506070807020f09041a0f010e2e0603060f0923040303021c15 66
    0x1000030740e0580490180040ca600481c4c090b81c03407a80800c0c5030820400002d01505084001c107072920021188038800954a01101c070405c0070310b94508145549104000c0c0007441c601d107080c08200d201c00560403c0001900c010460300b810303900c456944c0c00c404001d901181031400c80300c042c442942482c101000d0510307180c420003480c15040c025003da0310320407440b03054000c0f9400400074140c05816440341a8007035004007070fa100d840706050034100344041350040300561001920001110640d13841003208841e0302a10070741c141035107612440132941002c00103982241800f251100123545000d00288501e01c1410f03020b001210748400c1c6071050742c2c024807000d0300780400c50051090005c11100294401c4440c5094180610001503240d0790710000136900301c0328501c802000c1031468140c0c012000759a24001c1d404045aa509106001c1e074500d08800c1e030f030b45040320f400e81c00480c0806811544c003034082d0402504e00343c02c101c41c1580310444007030101c3d0341d01da0b200c0c140d910a018031000c1000910840f5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 831032751 1250 831031501 831031517
    0x12010f060f300201140414010e03010c02071a0c0f1c0f080109050901270219030f03180f2705270f0a1110080915181209030d 55
    0x1c0082e454810018054030481c00d442c00d0104580c411101c050380c10b501d03440d0f000e0b10346a031540c60b000282101409030780803e41404d44042141014030451b1043c1f000383c1c2c000d1440c00c0ca00350350043c4c89400c1140b2098161810041189030010030404020850001c4005001c8c50300005603080c109481e0024402c1000100050594042d0b07001c900300f8195080b14800050a880c0e071300343c481c010480001c0842140149800e91000d4450107100182440d000f652100d608518481140c0c940103098000100000444102c1001091041c40324102410310703d00d09400d60f68545138420b80c142019480b250000d040301c8150900c0343c7c80c0701e030402c01c001400c000034081030600c40a1400d80c003100c22207003040003a0074010920102800c004201e039180c903440980d1002c0340c06060194071000c04c040450b000d006034409130210346104a1415100f21401e030060000c20600040c001304a607800340071001c0309a200d60305030302070720000d221038101600500301180d074808928050501380b090705c0b0884003e100d40f003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 831034001 1250 831032751 831032789
    0x3110a080a14070f06061415041e030605010b1b1908090a032907020a03020d031503120c0b060d03120209150c010204030c0e15090612010f060f 63
    0x80415036451901da81002101c0d806425820500da0142c40005031000d0050414030301404015440002941ca214148045032018201030040400124040940c4240200030030061401e41140d03640c0603000d0900e50448481d03403600e0f0082500c0302a082503020b0b10001400c0c610420000c2c03007225412130003034061b041c03403100c10f1041a06501c0d0140c02410510f000658050300d99100160307240a0755201c00340181c0412058113844489245810701c2151078031240200d03030100d000140b5007002d01e44c9075000b86407901d100002100905000e2801440c0440c28120110000300c07030321084028001d1a99500c0c103000d110b070400c900500d00140c134a40c0500800005100400c0d48040d9001e0407a2007035801582e18000103011a0008281d0031220182c0180030641c41d041000640051044138003445180740ca081e01c480490070855030039103840581c01c194201180c03242c00e083c00081d82c0190020704815480d0078124000d07094403140910b845a895035820b081c444244c00100910160148069004540c014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 831035251 1250 831034001 831034013
    0x1b030e150a0608100203160c0818150a0309020a051212031009020c160501021204050d140d020c090c16150612060903031406090105041a0306100303110a 67
    0x1809040d1503240914000154400c0d0280c000d01e00034410300c0c00310389040260100700350003074205690f40b900d41824030b03c842d000c85118804094101c2e4000c2901440c001c0340c20549482a0300e00d404c45074100c0030000d4240950041c000141a240820b51800706035480540304001d0b1403806030704001c0c40347c091080084200c0c2c50015184d00e48200c0e8444842c0e03aa1241500981000d002d0b511038407115000141c144509000410300507070b02c488840c50141216150801607031528003006001c10300380740c10700040009283c4001005605d0740035484600403850845031300c608184c10012241c01680c000005484c40d41062043e03030b81c4c00060318440c103041c0b040012001904045a0070050124605082100304202051344444000c4c03281c1110340e801c034015490400050400c074441580401c2c5450000002d080361049521300c10b00b8024050700b850f80c00c00007000f000f406402c68000c820604d840c01002c16403001c02090740191084010551258950b00d4000e08803d80340b8120180ca4200c030100070000b500d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 831036501 1250 831035251 831035263
    0x1e06030f060a020c1006060f141e0f09100908071d04060504021c0501090611030405120c070b041d061903030f260f100303050d0c05040b0408011b030e 66
    0x42e245070250b9284403003d03d49182001040d480395140303203000b40005160740c10a0540005004030303258120520381ca800302403002d020302440c1418082c20b2641c42c0308220900390081810b084649009407c10b100c01022a018480c05c61181011070b45480d0240321100041042100070000200f8904d84404071400d070079245000a4402401c3e1620359000c1800c556800c0c00c060108200d440252909200c00d06046010305030700101075940500c2c01401e403480342846002c4a200d250400c0040c0807200500000c0c007000c1e400204c10f41c1c25400380c01c0b0042003101360000200001d150001c26018071b446142c82203030300c00001400c86481078a221800c2180100105280c10450343c142c18008a0501c0c00c18058500d01015406242c0c02c074410701d054070422201d030b04054000c11401d242250340c1e56600540040340940c6000203008540144800c0c03441c03611170b80210440c0c40c401c1c0f03061820b265462601d9042070b00136801c0484165101c80d01039405003405030b1a802d0581c118035061041c412002d681c1500c0700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 831037751 1250 831036501 831036511
    0x50402070309290a0201091211030a121b02010608160e0a090c03230706080108120f160c0305100b130c0e100c0201080c071101051b03031e06030f06 65
    0x300c415101d0254640c103c103911980c8159820515610000800028000c241c43c1104036030f90700b0921404c1d08154843c0c18840b515003800300085280c15108481903480c40e101c18254126903490300740c00d0304c0001002c103058084052640021450b14204002e450900400c00e114150040100700100920748003080c0342604a52589400503480100382001481d00c4202d400140c80da01e1020240f000c01525000e0003000001e0501c10f543c0401c0d04d4000481d490003080c4a012040e90141000d502503081c41030050041d910328010451900411440005111150810689042030b80050410520030305000c256860500c0e4401004544045800140c1c02c100d2440301f41e00d074550b1035901c1c2491038040e142245000b8402003c000d02182c1d070100c0207209080d41102240001d86001c0070903080c02c00d500980702241da110103180c400740301c0080111070071341164042c80c1158900030348101c0c02100c184002c2d03004604015031050305c260f15006c00d614a440c05820203009a001481c0c0c441e4548010884a8200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 831039001 1250 831037751 831037769
    0xd1e08010501140408032b090b0a0b03010b030a0c0608090c0d12030f06151403060603010e040812010b040504230a0f02091f0206060a080607050708250309050402070309 74
    0x420301e4140d982e04140142d803c0340706071b440001000c2c1c03001c2d10003040010b01241030564004d940e4620890308015038444290041c400c004503c0850740e000c1d82074003c829114400b0f000000d00c9061040002c3c034002c0365040641d900714682c40c00b40300f8950b10046040d405489032005080c3d12643c180480e94600c1024005401c100141c58589010b80c03298004812049030780e8002c0c8049a20390005401031006406c1280108003400040b008424412081c1ea20505004240609503813820101004041004104485503001004040e044065200f44a80030f01050b40c0155280c50800003030100301c5a440003d24140c02580034068083c942070f15440380d0102c28a0000301d0251000c0d00404068000c032030840e584042d40400807201315001403003c3c459074140c0c0e030032a0340c40d8940c6030511544440c20700440c1d05c1c40c5c22805c009601ca82c0140020841c1c2403080000034a00044140f0304c40b01d21980d49034a1600940c21703112401811746c0b0800361405820100ca00310710b80300c51a50301901d607560510801c856 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 831040251 1250 831039001 831039017
    0x604140112020112022b0501050f0a30110f2e02010b0409051c050f160809100201090b0702030408150a0b0d0503030708010f030804350d1e08010501 65
    0x842c504c03d0f0151019050540e00b04c011886140c0b01407060400c07a0401c6000e4036251000005081c6040d0400214084010b0468884203050504545141080d501084103d00b1002420200c0086500c86018200d0240c08400d0005005608102c480e1041c255024860f4089080c20140c0301001d189640b014040c413900e2025030100c11405170b000d0300e504040c056001d85032100c903e05000d0049414202500b9602107100e5004440105440e24010040b0012000c5818442ca03625001070100030031070036025115139820a604a0002503800a0310305000c0c0c0181d441c2c1020004104200c1011500a00980003943c2001d04000075107640304405000c1c40c039202c20391404204900002e600c80c989104025214800c110040e06010340d40b540281c03030340d40003e0580c500004000004000d5034042e0390340000018034217458000d030711003d02403036201c4030360000442d2401401d40042151110404d80480064022030301c4c4044050842402403465400a500050a000510f503009110a0540d202420705841d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 831041501 1250 831040251 831040277
    0x50f040b010207181d01020705250b040b21040b070e0f15041505090609102c040f06080703030c170a09140f0a14040207150506041401120201 62
    0x11510107581c0c024108928994035500c689041908610a5030201818034440c0c5d0340700c0d48401e4201d10074003402500035005400b0071541040b05c118210707002c2801c0a180c820300c40e142c41843d201c503401503004560400e00010040568440e04008003840c168800303000760b6514245d15a24680c9400409400070811282808034055071808401e0004036000f4041c0320290340081c440a140394011300540e44c101180302c074401c410074820400c40380280800380c0414101680307501840840e626044152041c40320704c0c0e8011002100d0fa00200c0c0f140c800740d044070074203900d014051100311490a034001d130a003400d010062016450000d40e030300c202d0342e042c03521061300030246c00d00d041800c4401031080c6440d01c0c002f80c40340c3d1450340140000169540f0356529a9a040003070208506425209140e540261007100200288950311510300100740000c1d00140c40c1840e00e0342c0d1070500700b000d119443d401d60707510400c0c401d540c14a4440e68550040c0c0800b403552650500d55001c1e6511000b0302c0007410005900301c00e030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 831042751 1250 831041501 831041503
    0x1e1302010822080f070b040c050f030d0c030f03020c0109050709060603020c0a0b0403020c030303070f02070603050f0720030a0210060f03020321040306090b0615040b0a05340605070207050f040b0102 87
    0x611741c0f90f00400d0705a2070b4142441c14050740a4944913203480b64520032901c080d20b01d40400c1c04d951507520b03078444510b038a82c03079502641c2c219010100e4006142c0d091013407070385510080c00b80d440380c1c1d845000502600c034103254180c0704480054000c1010548180218101440009480d44000c0e4101182c80c25039074503071404a21703014014000c00d40500010041c401643d802c405000e416444503002d07541c480352505821411a103013110300c1090400c0c0d00001c902c2c01400307044c450b24511510301408441d40c00300c8588030720f55407003141c0e20001030340b10142c0110070120b2072013502c02510311034003003210719032070364000968408030191123032f01812403401410390f001c0f0f501e011200219400f0105012003200d50411005500080329128054100c140750645002c0d004d40440703041d102ea000380942000314804045546800003080b0640c0001c00341040c08404440b0703001241c01d14203441e0203000300ca809260000170385201402079025544440c81c284507907562035409801c03400c0c6c01e44000403420f802400403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 831044001 1250 831042751 831042757
    0xc060d0e07030812010e0a0b0604060f090506041401030e1b091504050406020408251202120106151e0801120827010f0c080703081e1302010822080f 65
    0x404207480040c100310300c1340340c140845040710003103e00c5003001ea803006e2810003500d450024882d848481008140001c0e4010403201580082034900300101d15154004078481e5440b07604900f9441590052880307036582c0c140143c140b02d44032800a860400f0720003407401200c00d41940c9040c8640501e5002441000d204100030902c1040284140071030304017424250000e5110f805043d02500991070482c4d00100c0d0003110120f20710390619528100e52a02c1e58800c5203072242d140032a0b0003140401580361150f0b0900501d4003428940180210928a1702c001810303000b440d080c0880b0b50311038440c110900070341005100c0c1c11903280c610707a84000c01c020b01d4088a18413420311440903541291403040b103004070303084955016107030a89501301480d5a5000039520001e002c9070041c01c602080018a0000e440750221903041401d0484270b42e1284541e64a52440070000c5403a264011f90304103c3c44199030780103a41c540c009c03120321039401d19845507001c10303640c071003010034060a0490000f41310320802c006a002c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 831045251 1250 831044001 831044003
    0xf0a11100623010519030f0e151015050a0c1103060f0f010b1305040b0307080f06060907171303050c160f1d070815060409090302010507020c060d0e0703 67
    0x410003000e82c503010b461882c00d0100070400c0e15807509518128a55020f242282c140c0c0b948251076501e90482d058040b0b02a041c88a030304084507880d00e400c00ca40d0740c801c200d00c00d4106481c60581c000352402da12520052030081e072200d03c80400442c81c0120154201d0201e56420055241c4244c8031107103420031400d5114440d610725058070500b0f081000d18001449064024a403c80501c1200c1e6600d0420950701e00810110051189040508210a1800e44c0c8905152140901902c1e00c1c107503560110303400c1c181001c14800840d000602001070502d070000d031690780a000c5080000c0324504da503000e1001d0107001070018104196400034002418095000d540c1ca400c0c4103030444004440c5c0041c1c1410000c00c03482a055507041c581e5003c201c1100b0b4440c10020304d400001a41e450340d584010413128048003402c01c4206150355103400b000c980300d40c0020800740507201000b042e88540d40c0740003421500c00a0250b401c64021251400303050b03a4280480325a88501c44010451078503440146080c4003080d40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 831046501 1250 831045251 831045283
    0x31216020d24050601140405090a0908030103030c0b0603160308030a09080a020a0515070807081005090c121602071205010b0303040305150901051e07030b09090c150f0a11 75
    0x10705054941021500102d08907045809000740e840304001540c3d4a4010400c03402a40401d02060216003050092140c0c8006182408545071405856041113a4800e80040e000601800790140c140441242d4031078005005030001d0040301c410324045211080c0b40e0000812060001010502c40010364100110040d0021036031603a032040124045c1d505c02e1620001ca441e401041342d050030048010207540d100c0d003020389a0740c1460303903044011140c00030000c204040e035150492011910f600c0742d0322003d1040c00c00f40340c1c50360b80c2d0b26400c01c4042d8405005101c4050340c1c00425000081c250b0109000045800c5580c83e0001d00f01e0a18026000d821402000740c0c00d44800320b00001030000c001154001569400751400d850703250001c50609940048072a1042c20f1124001c3c202c400c18407032201984040301c0d180c002040d078081c800146c1900c0c815942803542c1e83c407100c6002c2680c038144000b80b2302402c1d500780192520321001c81c541501c0c0908580041484100d00c0d1181e00303050241700c0714400e503070220 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831047751 1250 831046501 831046523
    0xf0522080610050907111608061e04081818160909090507030209070e090408040512071514090301090f05060a09030c0602090406080d032a0c11060d1e0506031216020d 73
    0x50462750b2588121514403980c0030803507044000400e4012042e0007190060b03410381c82d000e4844001d0001356800005d26401c1a03400700c49412100600d880d2500a49090580c3c410402c01084010a801800d82020440900d00f564040c0001c00014070001205e5061b908071140360b490300300580312501203040450300710209104010411a0100080080c1d8000300c58503c8980c0c001e102455031101c490007000a03100a0007101001c480c024807520300c3e0000a241c0c0c046c035280202c0c001c2402d44c0e0031084110359000084280c1d0003001000c0c480d0035886155000200a14042d641707006140c5400460040d1003168001180d02040d140d42d00088050440301e021240080e01500000b4000e0403a070036001c200701e0780c886080c901c000d10145a1035843c0707140c1d525854071610300d0300c0c0c05019491104c803a5178010010002d04101103803d014500c040900c0345002d4442c400071003403840581d0170040140344260000c011100c91509c110003641c441540074404110020090301c0403400c9400042405041c43c1c03030b65 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 831049001 1250 831047751 831047759
    0x513090605150306101b1406070e0f01050703050705070902071a060a060806131b050c1b09130f06091101030c1701060f05220806100509071116 63
    0x1a400000c119003069940445400c104000d81c01c16000070354500341c1c0000781040f0090103511560661100d50080c5412800003130040c2e0300c07200408409140e0101c20f4114400f040760941c1c11000710300c000d0030142c40d005c80b070002402c0000c210344070b4418001c0612401046440500004000c5000505407200f411582c2d81c0c41c0d82441010200c9200c1806c8034650a2000590340382401034840088400544882807207407a940100060360843c1030140044030396a83c1e160b8410f0f0f03007852140e0600801900e54913555030038040000c0c20031070002c4c80380b54503840901b40c045a580303404040d168000b40000c92202c0084407440c2c4111b6888948501a191f0790902c403043d001e004000303141d81d8107030209032400c0004625206003541d0f1031401d48500e03520105070400410044d805001701d0341c410501031914078505007002c0c2400251032048c40b8140480740a070300040c8140041045013030303008139005481240e5646490001465060700900c400c0802440081102e9040003c10114050f0030f0648120b110150300e07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 831050251 1250 831049001 831049019
    0x41509110d0c05120a0812090309100905030706021209060c0712320d1b050709050405010501050105040f0303122306031212060d0311030d0f0c110c0409030513 70
    0x781c001c0c3ca10909461228626a202c00114482803591000ca581d040c1010040003820440d00200449400c0c0020031010b08141c0d10041440c0e80008585c0300d40308030f50301304018503181041c2c40d00502c007903520009040881101e0b440070747d0784141003100c4499a9511145c4400d0a0455030761000030400380c1e408480c0200007241c0d41c2d0191034207611030074615407085008080008241c645d180600c1d41c000c0c040c103140d4513200c3d01c0d4860800340281c0480d40040c3e09a03554610304002c0358020a00691303a501030008002c8207000709030041101b40b8211f8105070904062007680100307440000c00344100500c61031841c000036081901104a01540140c00c0200c1c03050081d0100c03021115248a0300420b0ba081d240142c24030f09480d60045055042c0916641d170b201030204003030908005030b0038046400c0b02c00c075862604200401d80003919800128000c01014140415184004c7d80c1030148096508400d070305500025264494050031a004a61062103003016580b912a084020010148000000c240000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 831051501 1250 831050251 831050273
    0x140a080304141e010f120605060d0f0b01020a05030406050d0b090705090307060327080c06090d1115042301020408030a120501150c150f1407020105041509110d 70
    0x101030700d0f54602c0302d82940001508120321000c40d40030076260044284694031980c000a0000c00101d40095003548031030000d115908030003401602c068641004085002c81801903440c914401c0c0001e1010789140c0c0c1c1c0b030980302c1c001d1740207403c00c019021034a80c0803402c0342c0c0c00804940078054a289500d041c4030310020219840102c05500a1080032030000d407a40c0300307202d8504c0b03801075600d00d00c0b25400f510300280c2cac090720b0000c4141e41002c81440200c802c83e80034031580340524074020050002000d00781020308807035201d4134203062940101d00d20712240c0c00c041d420f2070352240c1e0148030209481c905601e0010000c90001d60080d5640c4080340100d00218000020003586d4100c0c0c44405d04000007502c05415150240034868101e0305040b040103182e4050111040000d00c43c00d907050800d4052145041207403000721410707440d6034907480031f0070301e2440500085811130540e1000340034519064952900c18406040121101a81c507004401480350010403643c3c3d10000402c120715a02c218103080c252070b0307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 831052751 1250 831051501 831051539
    0xb04061415040507080108101122031a01060210420e060f0402130905131502032403030f0408010c030b191a1c0f0b010c0c140a080304 59
    0xb914100121300c20754004c1002d18102c400382c20040c0109140040440c1c09021a909082203007102480f0503052440c041740c0b0001c4207111b000d01c0d560780c3c6286040c01d000f030400c2c03070181d20b00e082071040051006c80e41c08264594421001e4a0116403508051214613401c0070558110481070310405141ca07001075a540d401c000e095590107406142501d85002506080c8261550313a8007a1115500c0005c5041c140c01802e801d03040d400c40300965564502c540020340301e04540f01111082078000c1082013080242c0e40852040c0364100441c1189800c44900340c20300b00440001d495840300968000d5290340410481c2c40700044403102d03030307121542d8207501800381c50740c007820802003400c002c00c06500e81002500d4104854200c2c0b03017011044d10f00756659100b607050051400310074000b002460038450440303400c1c013031300c003103240c000070304008482000012106940f0302c0e10304014000c1c1c2e0707da0120345c03071f600d2039400c2d650440103030340300c44c5044000550102c01c3c070341c0316440d98040810f0001b144000016140700d02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 831054001 1250 831052751 831052759
    0x40b160506060103140f0403091211040f0504080909090c100e100509010f05090301091a04051509030a05091206041b15090e100b03100504110909040b04061415 70
    0xc0d455100c015000c2d2546903481d03601102d1900d000034521b0f5042c41c1c3d21b5400034001d0900301e400e10f03120808624901800c85054410054001d901401c0742818415810580b492030401c2042c0c1c2029035650700e50348906003140f0311801c0b1100210319140c00600039140c07403200051031818984104d0001402845402e02c46d1071041c0c5c4204440c0a14901600480301604130581d150640603141c800241c03a5600f100441a41566a90384940c0000c4e401e00340502000b0441c000110a52800d458503074600100304124150f4161242c0c180601c4070b80020542c1c40300001800d280782c5620180300824403042071002406031920900c0144402c1c801100103500d1203001d03001c0b441c02c4541d100e09607490048820042e40c40000e01c401c200300303d0318002c0310711540c10204442084200c1a91034001100780c1d0400c1d03813200d01450102c2000c1016107058850031070b62860680007242800d00000c000342c0598801000505000710401c001401c02407079034003002c000314005c40700700d85600f0150020361000340351107243d03406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 831055251 1250 831054001 831054013
    0x3030d09020a1a19090509040311101b1b021e011205090a11030a02090a0605010906021b27040f0210081b0a02030f0309060703060b0f0a0e06040b1605 66
    0xf140c441008504401c4101c01d072107450090400305001c50203030074406100070810981008121030f1f882c42c401d05d02450180c0c0d0755812100d03560b141c1d00d0a00e143c0c5a555001c00c1e292580129400c030100508000e50b1196007454070710400100308403449800280b02c004e521140403071800c00e060082c8600c00800c03140c2a40c52014507803400c54040d08032042981c0c238600503406030240b24002061501c0c0310b080000c028042e02c00c4800641d000c01e44101d419034407aaa02034072000140905e5034090804002000c07503100030100d284080c812100c0b40ca0030682d80d140124085044911141b000311140d0038074841e032580c0070f031141c5400e0800080151010208030311070f06e6041c0b0540401c0e4410083c140c040c04401e449184680b004071005280c41d03108251103815400280082600c00c210f00015502c81c440f4900034282900d8410303c010708446e002d411083c00f0400c14001214280400c0c0280c0d000b0840504110607000405800500940280e42c42100c4480c00040c182034600e800d0303915402141c0c4070b6021240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 831056501 1250 831055251 831055259
    0x20d020d2c070e0609070e10030e01050606070c1a0f04060504080d05030f07200a0c05030c06032a0d0f02070c170a031209050d0203030717010506070f020f03030d09020a 74
    0xb840341c0707041c4a106514649140480e50034508050990340008003814020140300361000400c24080843daa0b170780120f96590480c0420031828003c480d44404111012072905010ba5a0303010440040d00030700c0403103905024003107044441d100485d254100b404101c5034440750f803510700409a0b40f00f4002c0c40703410f024a0550070042e034000c20580b40110f425010741c800e07941d50058101d8440c03440d00c4078020154043d0060401160b402e00061034800d000e180408181805c003014180781c8180c5980b500d0042c1010020061001203602d440c0b0800260b07001c000c1c64072010310100240c107020f0801100c202528121340c0380304070002d660050458a1042c2808e42425689200402e6007814207211442ca9400c200500c50000381f04a48a0f44103252010000a09842c03540b11949403080b18801400503905c00001c0c03080403600710030204090b1201c0924501c656041501080850250344001000d8020600d410030840d9180400c0b0f6030500e502400300e98450108440c0d94024180c901c0c01a4014480768078042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 831057751 1250 831056501 831056503
    0x8071703040c06050c011d03040806010b07050c19050307170105060a030302060a020f040f0303080121230120032e030b041703070315050f0108010306020d020d2c 71
    0x900c00c030b4104a00d0403809241c140300b500d0b01e51000624050719503885c070a841e809044405019100350180d0021611241484051441c102040c0c02c101240b003800e200190004800003000c4502c69020784108034600724030b07042100843c10307a800c580e03894040d40f000071580980ea500b81e41c41c87d0810100910080d12504107205c40d122403400060b0058000d80700155006078140c0043c20784e03021411101c1d01d802ea03200e0140c0101010b54008030b00195440004019107030b19080c010402c054002c0c0d0780c2081d03090b5640c4055462517051265040b0030b420f410342100ba40000e6000520984150440d141c0040300b01c050b03000c1907801140c40c141002c1146800510320707000d015010043c500c003245070043ca54110303103d00000e07081c000c0c01101c1d401d010b0301940d42d079000c0c1c0002960181015440100c0d01041018025444111a802650146030f40c05811002c981e400100941100d801840050b03464044004074000f034499075541592103400c21101401003045281400d54243c141003203140f40401c110545 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 831059001 1250 831057751 831057757
    0x1f030903172e0909080406170c041a0702090a0b1009080316020409020604060201051512060a050a0b18040203011109030d0f1707030203090706020c030d05180607080717 74
    0x280340b44034030810a00c03100c0e950380e0341d0084462208000d0025035990a00d209462010004a03018400464200b0045400c1043c541c0fa055a00300c48c03406074904030940d071016001da442200a8074908101d4a02e01100040460b007803c0c0c0c0141004c0060b01d400d6444202514403102100e00400c8103052202c812440303040400e083c0c81c4014059482e00303011b0b40c01d880f40c0c5040c00c030090780c0c450750751015400143d036150010701c01450341da00082210718181d441c00c010891074051076030141c0c510206002c400c1401155075940700b444000e0008154a031a40c41d01c2c000c284030500d40350844100d543d201c1104041e404070b00e100300d200310024850194800c6101e8100c0c003450030704035050350180704c0c0f0440c1070b4001c49030780d10301e040380345800812880007032031204070f43c64213039800e0b400320364000107100802c1401c0c410280036020724001402d100d940400469500c03101413040b03404100c004106101d4041d1010ba0700101a88002c0c0100e45824a504050078158405141111144048429008002e04900603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 831060251 1250 831059001 831059011
    0x6060306150109120c1512050702152206050a09060b06070519080d060b0903010b030f07050120070305150a0902010203070b0405030d1104050411040317091f03090317 73
    0x103c12429251040700d4074101041e0f44100c0f1040c49940000c22010000b401c02d819000c5a82d403503d04517034144641c3c03401c4600c05031906085410400902c00380b05221010103810020440c01c1c140c449254442100141c034003444000c080070300700414400700f80036a170090703840c09004403000c110768a1083d041210390701c01d13203000a1203a044041c12140410704441811075440c020005145000c01402c44c941c1124642d1f000781d408800b0124501885003024410013140c0c4da0305030010081004010038495440480d44516810030110001d1a030311540f486002601c005003c0e4121280240c030391521316219402450b5148210b070f48400007441900d01400742803100343c0c060b0069440c00b185074840329842c28009209484611041204004c1d5840034441c509107500102002521b603410002007009403651415088100c00c5c0a010500c08140c00618241c6d07200352480a1a03500e80101e00400c40001c1403402620b08e1045007210142d90541580255401601c80da446a074100e6004d080c8004541c01650 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 831061501 1250 831060251 831060257
    0x40503161224020301080a0b09011505090703090204151d010b0306040b0f101116060219062c0705011409210d1d01090317070c050d05060603061501 65
    0x703600001c100d9404a040710751050b140341801015606642400b640d000780e214070b8499011222503070500c070625503090380001414000740000c268a016403040c81044e40280e910405e004000310700b08a010782c0c41040c003180c1c0a0802d000c41840142d80c022600780900c145030580b402c104400100c2d240c01c100340e40c10f1310b9240f200e141c08c546807102031100421000300c01581141c070165a421440d80c03500d103640004042541c1d860304012642c030309a410001f10162541c04001c0d4404140001600800c15529012101c2e01c4a642170005082c010050103940001c0e9501c1c074032844c0d0881e107024103401400200d950b4201190280d660b54001103a8601c0e00c900c42082201062010540c9841d046044c1d40c1001e9400c600506038245141d841740c200541c5002440c04200110204100d1270900701210f20403075000d082c80c022052454441310307440080c3c03d1007840307010f00c0011030a08004d14000f403c0050035020f08065180c01c00d502c0d0141e80c4580075207400703110307100da0f2000a0013039280380100340d43d491040e5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 831062751 1250 831061501 831061529
    0x5010516030b0a03030c0f021203071406061011101404060612020a0501030e070b041d01050a0b0a11011104090e0f0c060d020c031c020301031b06050730030204050316 73
    0x18900725240c040140d000c071042e00c429090240540e0b20400c5c020f640c03107007a8012b16598501807401000e0400c5450641c44160416800c004071a40c419100f9103560800341400004036088500310360800c072082250a054900d4407020301541c400905903d84118880d11041140c10b440c0c400780c00d10800030810080d80210301c00703401c0c01154030030380010071801344500444442075120340b81005150460b0b00194044022a103000c203104070403692241c0100401d8030a942070303d0810b1002102d0f44980c02640c002e1141822892109000941c0596030341d4007900315007034a80c0c0e115015000509010844c5000b80d208215081d11568004904440801c50040030076150003d003041201c080d42084e2a1091540802e010f86508c1807196817400400b80024040103aaa40c15803800d100400089811410039406512091200d180c000c2c040380d040d0b6412440d007003444161948022030380c4691148501c0c03149400386419005580613006401076820031816100230420000d842c0c16400355070710603003143c08524 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 831064001 1250 831062751 831062753
    0x905031e072105010908091c110d0c0e07180e06030c010e0d06090f1b0b030a050604090f0b01060e030309150a03091e0606060302070b24030a05010516030b0a03 70
    0x2001102c0703000e4007050b0102e4004085034880608480b031241d4141e0765842d0001d0001e82d0752074451120388400c3c1070a01000c003488001d880d0020110300301d403c0203001e001c000406005000112030074500030040340c40d000461b4030701840014014035621240400d0852912800701e1a0f480c20300030700b8407076403010b00102100c50909004496440200502e0342e041102d4801e0301c004a05140a1403071010301520204803200d0051500d1000701440c100e01c0380700c64003039000511410503018200e0350400c550700d10100f00c90319074070009002485032220061040441030b90b43c0023000300e16074025040f51903a840d1900b0409504041c1502c078421171002d10b9004030b0800d002140c1010b4040540040055480d00180b5940d56950360000e542010f50362811450300c1c1200c80e1f00300880707405040080c005a107800d50400300303a507880d100058005000382c40341d078100c8290740601e100a01b46203211004005d045030141d082e80d080450082c8001e50340c2c4070001c00594641072259001c0e02039556514400f6250b15082859 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 831065251 1250 831064001 831064019
    0x6050d0f0201090b0c0618030306030604080c01020d021603030e070605040303030213320a030b041211160501140a020303010b03100f0f080613021005090616030905031e07 75
    0x480608a0502c00c043ea030100718034020700701604100c41c0d200c00620b054200391490440311207080b139107481c00351302c00c008124103901e001c54250740055001e1910345c3c4408040711300c2030280c00f42205503400148046802c00030010041c0c1d89040541c000d443c200b20703580078403400e40e0304d880c03040c0501d40101c0c1c810003080000038800da004100300302e144840007404d00c3e100c20500c000001d40c1c4407014814107000034510300818840307402c0727281c0e210201c0301000518a1030b50ba451040c8001040070f00341d080c1d8070302d07010b03d2b031400342c0402003401602d041a2190724001002c1400034984a008035800501100e082281548181003110003008050700150701310f80ca440c800e03034050361005000000921055400049481c4d0081441021b0300660407408091810001c80ba860721b48c0c001c00001c00c0944003008040581c1300c040c4080da02d5100c500d40241da418080000c0f501394800c518404500c0082c00c8028014113901094050503606c04406543c840818111000700140201c2e202e02000e4100240c10070400711 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 831066501 1250 831065251 831065273
    0x3050406030b04090b180a0b01320f0105070f0c0b0c0d020106080a0f0c031a011403010b0f130b09011409011e150e03030304030206060a0501020a1703130503030a060305060a06050d 79
    0x1007001b080300c40d492030a5480f8025000c081c0e00290340d81002c03510340303645460451030086164640d038005060703101d01c1c07400040e00103a54000340d5052000000c1c0d0788042c425103000c041c2c606d540116180e0440c65541c1090745695021103818051801052103081642d44180034500880d07a03445c5c0142040c102c503494451000f20400350465440e0500341d00000040c84080c060054010004058002c81d0f00d854116001140741b040130901c039900d0440c64044956660414109600080c0c5d00d500061480032481c2d0000c1c003a02c9042544140b80400001e10720601080354030390f44006980f004410790741c1e01000c54440d00c2a00c014251108840400c3c4024640d492000c003281e0b18030710b02014140203003400309040d68020f83c0d00b500140c01110070800541803c40e1028010715007071004103a11090394880001041c0090429500c81d2000004100913160f18821201c5890700030059950700e00b0801c1c0c0c01d00003080e076440110340c01c0c05950002a1984840e01c6050210744001c0c1072103a43d8202641d50000c0c1c65 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 831067751 1250 831066501 831066541
    0x10305071d0a1508060f040210031e0f0b03010f06050310110409020304081b030a03150f0605220b0a020606271f08010c0207080d0219140a03050406030b04090b 70
    0x400300f0009601002000b1880c05030581880c2130ba020700303180c0140b00d050080c8094440c2414200b2080c03056480070104140292169041c00240b10000307014010302400080050359855800c1210040c42641030740e101c0005c40700d0850446072080d002d024800195580c1910300521303500c0a100800034071038107070021a03000348120b00261034003004102020314035a00c4170301354056600120f010003a1507003510903c6030b070103440d480b43c1d000a840d000e20801c04402c5409294100000800c40101c00310f9100710510030660380540d140f81803500c400228515800100c01500103104180c042545403d004044428049904504c003c801400018590311800003624a840303d81c6080c00f180d40300301407100352402512200380045070b566602500245042102d400180082c2c00007140c11403919000509000d000035000103082141c0101e044c49960034100f020101064005c18068100301540080184195a440c3d201081918802010301c0300301c03554008000c0040b01d100c0701280a400990004070885 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 831069001 1250 831067751 831067781
    0x3030c08040803040b0429090f0a18090507060801050a03032a08031801020f16021504030303020301090e0f0d0e0d06060e0108010b12060408031b030708010305071d0a 73
    0x819070360441146954021792000b000b464020034180880000b20010205100a40c144d5080142c41d01c48101d08070b10075008c405102e0007014421140c1c50300c17101041e07001800d40010401080d0140035004001d01000b40003180c40380030710311000c18014022aa01c5050741c402034199001c1c0d038155a004e80340c0c0000f0240704030a188041c61611800c90209017600a407600c140d600d191203090100d044a0800000310004889c0d07401800382032000e0064805460b80c071603080b001c82455078010700120f8401854040074500203e4001408014550941c0040d4100c48400604002c0110130384401038540c0306988000c1c40b50f41000005540c903e2040035601c4412500800c248003000c13440e501c10003114420b5012000e10207991340100300c540c80070b125441d0703143ca0644540a80241040e401912140c0060004004290200c04125160300812001117080e4600d41340c1680c3c2d00305188050304483c000d200888445c0b00e5140045001440502c601c0e00e62003050003520400c2d103130b98050502030a61410130803c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 831070251 1250 831069001 831069007
    0x303120c0509030607020706090801090b06040209010504030b090a030e010e1e0102100c11010b0a0819030302070b18070b040f180b090103030c03032a0e014a060403030c08 75
    0x2e40d5030103100f01070040100e07030020711440345420805082050310b41d02581080e49803120100202e0140c0800560102040b100141d0f2101c400e40140c0d4540513540002e070442d120207041100ea8180003403608a07143c001c5e2213900c0a0141e010044441d284c90050032030300a0102800c1039048425146442c1c0c43c0c03401401070f04d00050030110030341d0494a02100305000a220002055501e420030310a440024a06540a00604c1d0426259603038030641005004500d400d81001c220a0600ca86c0c15a43d1450707104c1c0765454141004405072000c2c154140d14044513004240000a418544d58116030807142030819902e080d91910717003064035241e440c0c480045096212808162036543d0645081d0203180709403a1840d002c265070400804940f007855101e414480d00c412001d00002c03070554901c0d051800d520303005448000074001242c08a51416100c60f40803d01c2041245803090050040b40e4483c550510005201c19510445100b1012080207a08001c00f00024008039204440c1c10a0003800307940c0c2070b86 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 831071501 1250 831070251 831070267
    0x6090a0b030723040b09090709030819080610020d18051005031f030218040609020406091b03060e0408030612060a021b0f07090f09080408060711070303120c05 70
    0x1915401100d0580028a1075508102e83c90b0015050514900007810480e04243c20080c0030210362040510342881790142c034000a013034508c9640d044000e903602c04a010344a034090508800300e8617140e41d2590100d10300034001101b6017003055598403110003d5004000715051801d06550380d007d5814560382c00307210b1000125050f01c981c80540c402070851381d81d0983d03a05d000c2e01d0b0440e415990707802e110524140d0708004c10250b40ca4151405034120600b07980d481589691500038010412054000d41240c14210300180b0b80f01c1951245000c4800940003180e10204404103d0440b00310703004180c0501c9605c404a8081043c00010316405840508401d1120328200d60340c9103042400c0301c1117094660001002c1c48519206802640b00c000741e40000d20915209050710342e182c11450017000986692103049207011000f0340c002c0c04409030415021942ca0ba203640c0915100c4004443c46400300b0917141c2d441140840006004041701c0e0155180c40701c42d941108414080d00d80341c240201003002c1404500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 831072751 1250 831071501 831071519
    0x270a05061302030d0f050a0509010306030f03080702010c030b0d0b2d100b0414150d020a03021209060606040b031312080406051803040b09240403060b0d1106090a 71
    0xa07000300d5000158045a041c1c0d403040601d030504d074145540410051500b4512010340040c15541c1c5902c850504a48071148440101c000b84a40e6001404000c0804100001d06400803141401104140e000744076580030503c065064071025180c60350410201091000807464040d040c50300f204000402e80007a0400c8040500c0c951142c0702c0c5d41e000380c02c20301d01744100c800c8204480c20003040c03041c0101d41882c0c90700010140504544840e5400361046843c07180030a03452004884085c0103420045440f8000104001c009411021290050507008008039000250010340d1a108400041c01c0720719080c101000709640e90000f801c1100008039028a44001680703003020010502c01907510300d00316140a0400000340c0300d0203440324401030317500001e04150300700210440301951880304010740da640140c4040b4510740f003100c1e01000c4a4640c40741c42c2019437800d01c010001c585c028041480000394400400840143c2080001d1141100c081880300c1424170a0140c400640c00429490100d5a00e001503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 831074001 1250 831072751 831072763
    0x2060708040308031014030a081207020c120d08061e0607060b0306010909060b0a080d050903070f1212050324121e010e0604020604030303151707170105270a05 70
    0x364508403035046017800361b50070007029007020003c100c0c014401101182c0704e0469030b10480d1104d10400a00d40c0004c6d11050081106846072140606200300d1715030351207081c0b51683c117012105400100003e020902a140c0308040f41c07101e05003401c0b4502c0840740c0d034041040691240300211001511801d45c02c2da2a9421f00085000740103460011441d4a810310702107080b40e011440031481841d40700018081214001901041c8401c02e042c8681d490080c900000d103080242e511075200c81c01101c1e804610101c0c007482045d8014030550038405026203c03c01030b5442c1c002100c1904880e48941540e84441c15800400291500c0251650b01c0c00703283e40c5082401e0184598075079211455406880d25040b409100d0029007107241d4024051500300f580c000760052069120103000c060700d888894031000030030103c000042c80210214401150344120517a1a800d8602c5284881c1e80b0200c105004c0b200180242c505c0303803028142c11848404200c000800e1500d25806262644c031901041c0c40001d1020092 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 831075251 1250 831074001 831074011
    0x909060306020901030b0429040f2f07030806061c090501090c14130f06170f01060b0a1b060f02040303051207090303022a090c120105010e06070206070804030803 71
    0x5a07a03a00054005020707940000b03506c2c6d0246280c07143c204a6010700c024594550411842560782814030031000030094541c510250000f246024601128140c40d1000074412051000b8048408804c0c3c070f1074a2201d01941c1006008241408001101460043c00074000001c4400c4504104c4418481400488800c6102111140c0d550900741d01440514040701009200390408000f1031035401c408628913105089045400da6101ca103102c0700040e15801074405002c40d090003402d00c429064015559000c60641d522032546490b00c04150280f540080b04c4c7c010042d505c40b041d1903100300100d007100000c40ea1040c2c85a031395440c00404100703458001000114065a9000d44804103c00303907602c6010083c0c480340c00e00000c4030080000075004200a28860a407090030040030351054181030003c1000e4032031507072100c00b1a041000410b41b040141041440003e00215a6030701d4030019180c811070410708582c071440c203020510041c90088014592148106c0700581000d40e26520034116420a0302d13 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 831076501 1250 831075251 831075263
    0x1a040306050c0c1605180c09031501170a020d030c0201020f01050a060303090e040f031d2224151101050106020a030206090c150f09030d0810080a08030f0709090603 72
    0x6a18142c000d020028614400e81070400444001d02d0b11001906403498042e800308480c0c03401e80002c0c11f00c2d0035017040d110000400f9043e9110070001071940c0c4c0c42a5403d0242c545504c080b40c41d44040742400044551200d9406401a05607000644003a03881c5000d4880132070440c400c982c81103242c0c1d04d0a0249038001c2c03040300804076025003076280c09032207030714150401894441030740200400b0a002031000c19039144c150a00c14911050000303d650340a80c1c0010071608011300c00400300c03104c0b40504c650000d144258008000c00a031505543d00c4100c05e880c684425205000018001d07140c1e5001ca26042103000d08142c000381c0559003c441c20740310264805009a04003007505002e050b01031001691100000001d0015845008005201000c61900740d580803500402c070803c680401404888002000508540010030803000041200c2800c0f5000c1c00d4016018000162070900010261011a0300035003d60855580d40c00f6140510343c01803404080010340c5000050b214002e214550145000315 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 831077751 1250 831076501 831076507
    0x70f1509031d04110405060915040b040f0902030712021c0608060a0e0d02120a090e0a0f0c020a051f06031406072a260c070302100e09011a040306050c 66
    0x2d030300304a41141d01504030301035428075480c1c06070b01c14000d04490540d00220303030154541d0301607004100c0e02c512a01250700c041d107002501040c101000710141c0100d030400b95071484819200c5074814180c0c0000e0314100040742c6101c880d10320f882141d401034404900c240100314103125000e43c00d01c0a8800640c00b13042580c00c42c00900150b040369029010409001d83c005001100309040700954a50000403400006003011420700c1040b440b0700c01000082071a0302d00760300181440492440123041c29041c01d520985860f100303e0300580041000108150850050800400c1254004103014201d8411002d203d0741e940c40400080e26903408104440202c000030115481c0255000e404440c408181e1142032161600591049141d9004c880c10a540300b441040c00300c904506042d40d03041050a00f512030000442c42d5106524000760f000c049038002c5400381203001c450001925050109180380342c125a0500040c0b1940b410030b40340c49a6500031014103883c1a54a459460450b4425103000d00c03184c40c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 831079001 1250 831077751 831077777
    0x406120b012f060f071e051e03063a06021224010311192d170f0402101b0b1e06030304180f021801081308070f150903 52
    0x40020031361160302d0a6158100c0d06020201170011004048080c1260909096008626210710150760141880300050f02080383c0b041d8268650785c0044401c180204040a01c06410340d80c0d601c3c001106407101001e0a140b040c54481080d24014000002c4d90400c0e02005082c4ad40307940c00010510030300040035220222084035180010001040c090a0304042c00c01000131040d4880308121030440d64101c4181140301084c5c13100380d9020310703400c02060321002c075441d0084801400e840c000184c220280c0e40e1011000500e81c9014020350150780c0341380b48200c00000500142040400c4004013000c600344404201e502942c1200aa40307100000c0314030075860024409850110804601a0090070320030500e9450324001207540ca00541c03040b03049420b1021840101904c440d4480c811500e44010150b54950307103030fa8004000403510355400d002440200008024444100c04000b050390b10018041c40e10ba0552a80140a4688501500c0c03c0240c0300010070007001521440c0300c135621986406612400b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 831080251 1250 831079001 831079003
    0xb060901080a050d08060409060603030e15161118130b15030606040c03180c0311030f03040b030705090409061b0f08010e040f0c0f0e0c0406120b012f 66
    0x40c1d2004009510180510000a50129141c8603210052401040690700c034000103020b010300e410042c18091820501000f8194400301034034014000b520403403180c440d582c50f1f0031f07030a1081514404900182419000000720303a4012520743c107000404000840f04c010402c0301e4104425111002d030880400203940030411301e460120741c050720340091404503000e03140210703481d160020126880349a5600404031858000e40c0905c2103a528510b80c0d1720200e48a1404541e105802c2c0429101c1d600520011035051600080030b031081d0340d0010186041902e01000a4020b400141080c024820306006080da1515548034801095000d60400f041d5161000c281c0a1806403e800ca80104021600940c281300e0704407070320702e0441d00011500314250b50f45003024810104410b2005200d014445000a45000900c03202d0701900c1000d41d04071b6a58440c2421040c0a211b04e00c00c400c04a0f0110b000c44a00c80d190383d00115038044181880311380310b49001c8005040317249241c1c06002501180b207a482c65188 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 831081501 1250 831080251 831080269
    0x408030408011e020301121b090606200105251b03021b060328020904090503131d041b091506080105060301050d0f0311031b0d020111090d02010306120b06 68
    0xc44030300c210301d11b505150120b40711607501c0201078400c0420703014003409000065a280011300e40002d04001c070070b80303441d402032400843d52680c00b94202213401c2a403803070750184a2203004030032420542c5101911803039070f4188508002c2400d810700c0020801c81c5c0142c1d10f03000820b82d5192103540542031840885220080052000d0b500e60302464040c000c200406490b8941604005c21800f001c03240c01840d910088041d1241c031400e56001414002c0ca90708101000010f000d000d0032841240a545440301804028021018a030b038011030b400d800403802069203102d050300c2ca041c1840c0d801c20001d41700c910a9043d542d4a4002c04011104507804001c0749034070420860140400700c9110386194903180000318400c42c06d410160150441c60a200101401041d903c0b20100c2c1c024296501d5840e104002c00390322208118a16080c000d031346811141c244188104203031300341d5000700c02d4104038000040c8070f41c5a01d041c600300e05040c1d941201107002c00d108080c441c0b910707100b0910085186040d10910003024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 831082751 1250 831081501 831081551
    0x10030b09014115130204030f06020c0607050304080d0b0f121b01080402030c120a1401050601120b0306070e03160b030105030706090312030b0a0b030925060e060f040803040801 77
    0x2d4070200380507041c2000301030000050002c5590400403513030343c41040020b214590005120b0043c12000b0020840e803a00641800f135090340c19600b01c0c3da154401a2030a1104940007400041d0800c200e034241d1145500c091a10b41020b802c110010ae120404212030054604240758282d101e443c007001d007041d501c498100d01030710a1900012504003540405d0752014500681ca105840411415a030034508220b022041a040807112841e001e90000745402450141c40003400a0b0f69141040c2c02d6070813501650b0914a406001000301c5d42d200101200c181d01a403690507814094140d901d451b4044180c40d04014010f60f0782031603569490b01042605e0600d06a00000030f10400400810104040300504c1d6480c112600740407030b032002035000240301ea001e07680102c0725408000c402e0140304000041c80600c0180710044103140d000440003599007140803032103208001000c1564800715400e050015003000808034483c603041903240c500003421034100e03801028841e0343d100400c0d55401f03994001c0c09102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 831084001 1250 831082751 831082871
    0xc062b0f0b0a0f03062f04030312050105060702040903230903010c0e130203070c080c010c030c14070f1104050f0f06060f04060809070e09101410030b0901 68
    0x91464a41e1241c0c1c400b00c0c520020b4515a40e030b00030b180c1075a210711b5600101b0464001110070505440c01d01910f160424007090300064010416000f80b0007061082d86d043e40c000a040e00d0a0a90310b5081001410b50a842201001030003070400301c0c2c40c985598004103005541307203d6034a8035000014103085501d002c001c20100080b9400407a07046d1154083c880c1d075641040005662940d8000b010340d121400800020021000020700301540807065000300e0601a45076000c3c442201e04640c00c907580032183c1010504441c0800640340001d40e0801d00541542c8240003110b4040100e1000038100c89007111b0400c6000c41d00010410100c04d825a8503501c00c0c4210345007030800100c0500c03800f260013a80146003d01442d0300100d01408c204005540c0104454851500c151505c55075444d01c0d080d003105030788039003818126043d0085c00c400c54850b01c64683d04002c00c04e42c40c030310303124541440310151103807105550300c001074842c1e030440d96020502800184094105648002161a894890880c1035040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 831085251 1250 831084001 831084019
    0x90f01110423060a030f150b0f030403030e030307081e012d0302040e010b01090602010203190b0d060507020124050f06072108060906010201020711150d1406040e030301080c062b0f0b 80
    0x840f80704050b502c9e202c010303c04194403503440380f4082d070080009440c002c42602c00030003001445688184001e100d2440c0b40203000d0b510342a600c0200501000303004210368540360701c40c40b000900c4408001700c02c0301c4e0080c0c850a41203a40303802140803030b400a882030702c8913511400244c4180d40c211150350000d1200c4c2c8021071031860f003414400c0000c00a41a981e1095445010b1401c0301d5070384d0264400030a40040c401c02040c100410083d0080100303004041038207040342c0e20305187c1c0328030724146022144017030121600408020100103180d4450442240d003034012446c054404210610300c0c0810441c00d032505c150500340b9104010b001c1800400072411a0300410108000400e00ea42c000c45080c0305659000e00c4101c841d8011000c1c1c00340340c3c9000001481c0020300e56824954003055801218269001c0008410320729400d0f03240c8c0300901416a80d07a008843c100401e051070301c000c14500c1040c011550001c0407241d900c0544412070902d03a52119150b601c4507604c910544160b845410b02100c00d061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 831086501 1250 831085251 831085259
    0x306050c070b04120c08130303090803070b010312090f06020114010918020906060c0d020c0f09040b0c21010303050d0b030d0c031809060608090f01110423060a030f15 73
    0x7412030040c40180302800000c9206012030007040544401640f08108a03150914111f1882089040c0d21041c4d000940160700041c8501010045446041d00141803079403076070841c0c945103a000da540c1140020844010381c001126240b0b44045d0303001d40007aa00224403803040f5140320f0603401041c1c01c2100342c285001c42460001c0c000e610104141541540d256129a58600004d600c13806030300c840222078000e20141314000740d40480c00e401071020880700b80240030b91034014440c051104a0780201010401004500c10040900107000700000b0b007408044214008042009669001c0e0700c2100070444c0851a00c1180b4203e00a140304480309400401d5034101d1000c2c005c00c0038112040150a02010003c0c00c40704414810201014251076042444100c1c0e079010014542001152040001e014900418a81c8041801052104101074441604090404010040c0c4500380079003c01c50b00d51501c00c5480d41e4407860050101c4c10610b8400140c902c441c0302c400b00c1a6080c680f502c070100510550188 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 831087751 1250 831086501 831086513
    0xc0304060e060310061211030c12090a02100c0c03021003020301171506010c0c0803130302010f030c0f0e010c14100f050f010303051309060909021c23070504150306050c07 75
    0x80200c170803501d401e8500d070810b00344180042c83e1030f01340c00326000310020400400115a1000740802412001a419169140850b031170700c8001d601c00081d2b11081f038a0020303007014803c02c1d240d030f03480e4010700c102d032140d43d85c030380c00142458240c42e0039001094021004200310685041351041003aa950060303d80c240482c04101d80300c00c80103000b1414000d01c080d081042c0000c10074200007400c40441120f0790b8040d40b030ba00c500168010310049000072403000f5040e144c04c3c4a8010041a000c4c1c0f80c80720202190201c80542d040b940b0003c41d54100040083d40e0008580502000600e0090407005443c1801b400f40e080003e03600200b105080d424103207005e0007004c04201c5030190450741c243c80c18a440740a00380e00707182e50029652011800c00e0520740049006a01a4840d0b06454400c699002903950000e030950800c1107d044094810080050720907c1d0700e0b8104624040c0e00e9404064800032030329500043c007164060f451507a49441c3c944c7d802c0c0700b0014513205440d000f080c3c49202c6800c114035030b540c0c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 831089001 1250 831087751 831087781
    0x60906040308070537090f030b0a2a020607050a14090307030b1501090905150d11031519060e18070306090803190c0507030e03120c0304060e0603 64
    0x38108900380d00000d411510078010740352186414142800c0e20754208084440c0ca98480265141c0b0600f0b81c505d4024860051041508940d0203c402d50042d502d143c80b010002030700146a40d0145407500750700009952010307003034103002c0407004c3c249580c00741c0320ba002803030a8402802c8800b4403800f0490400d4454000c0440c03686c4207103455007140d0781c0000c0310209040072074603032000307290003802d100780100c80345c6440c2528690031003a42d50041a550300d00e10340d0b0a48a094964034484034186000109906200c0315a4210034010802c125074a100350010910b031118108164040ca841da100b8021a403c3c414140c2d4005038550038184201c508016880580141c043d10000c205600021003911507601808150000c1d600725004004808550a185075180d10841c1d101e405012542c00c0c40c0d40184282c0306083c201c111542c1c80c6030a002480d5000d4500f540300d240640d51503c910413030720b2517010444d0010041352003004090b43c0c5480c070f81280905000c00c0190329610078201407040001204001440d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 831090251 1250 831089001 831089003
    0x31c0512130c14132408030a08100e010308071a01090207050624011b0c06030207120f05090d08070c0602010212090f0c04020f130906172109270103030f0206090604 72
    0x70015017180c80d0795034408004c05800d0101550441a100010a581e010001c3c1900c190b80c0c3c1c640107015502c41001494038402d500950740d0000b1140018000315010304058450640714070702c2d51010146520802c4e5100c40241d21000d003060700003488008112003400202c0e0488184808420030910701304411010300030b008038040c100003001c4100642e03240500b03507a800b417a0f00054401c942e0342c0c0700c1030001c010317500c1a4030683c4e195001108001c00d03240b0515080199550310f940300e500308031a10081000d080f075203a40c1030740c0703921051054002240100300000001e0806800041c0d40703402c00d20003e460307c0c10090020016401444801c20000b4010581501043c003c84005982d00b0820101030710078007a150802c0c00d80700c40c0301404601440c950f030021058941d4100e07080300070341f10041074556840038603201003010f0703001e00804480d20907123101500c003000c401404040c024611000c000510144054403e00d0703502c1e020f00400c10305400080c401c48038035992002c7c04441c0342607070041c1e03a52034000d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 831091501 1250 831090251 831090289
    0xb040b030c06220906031a072007030516090b10020d030b0109030b040b07020f01110403060c14071a070504050d03080402031204090608010608010b031c0512130c14 72
    0x1489a03820710003064640d410f00307045000345800700d4440b02e0210050080d40411100c42103c0440001000005940984034010350b948000c802c80401c140d1010150440d50150480d00c5800030220010304103204003000c00300c0c421010b2610310700d4400c100064401207405c06016201854220484a074041789035072415081c0c1c01c02190b00541c2c200100e0300d040c170641c00034081c0c00945084c082002611004603000d040160301712a106c000035a0303d1070881e5540c1604410078a002c00c03003040060001d80210103e00c1709810450485448050032445690019104445c2017000d00581c801008814281a07081001450100c2c141824400401c1201c05104009410700541800040466404101c1580c0c00490200d256403560355842610018041500400c042542801004210b1400501c68020b1030b43c0014028001c6018800707405408402011003803003003010411062041480d6090600d0041d10407a8000d041100b175400c2c0100fa001c1c0380e800401c02c5226801c00c14501e035032071444280417500f00403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 831092751 1250 831091501 831091507
    0x80103060b150f0a02060a05101205150f09011b090504050603100c0e1318080715020f0904150506030a0c12051302030f0a080f2203080408010b040b030c06 68
    0x1c0c0000340048200000c104141000045000c408a864009021451603a40894002c0d464005900c0c003650700450f118010000a0007041041c102940f81c0803800720f01507416141c081381c0040ca428200a4111460001d900c4890144000d8900920800e40a01ca49006040b683c0c0302102c0010074a0740c99200300c03441161500046030f510364060101150041903401c0400484400b50350141c8512005036030726214030b056041c00d81d03070940c03140100c6001012000501c0d2078140d00d40d5503425241c014100c1624103021241c100c0b88200300300d100811054100034020354a90f08103070104415568061610b002c82072501c81c0c208142d403606400d4941281d65488089001c1301e9100c1c04036176210042c140f29000908010a100c15009901c4101d03071407038002d50035190001c004d030311071715501d009409005001d90010800408400172a50180003804856003540540d010221010303102c0302004d0300152074000c0f000408110150092017880d024050695040c0320703021140e030002e529400741c10b83e03d0740691800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 831094001 1250 831092751 831092771
    0x31223030f0402220c1b0206070308101d010510230901051608030a1506120c140705010606110a030507020f06090a0e0a0c0806030c011d0a08010510090c08010306 71
    0x2054100c8001e8116521540032004c1c000754200261100e502440003080340003203581114694042050303101600500b02e80c2ca4504c659400302e0305104001c054035410b1030540740108881d0b4103d0395001203440c441d030703c030a002c1d41094200020160100760b88010303c018940c03500b074411108008001c8140080902d0341e210700070007005035000c0c800d0740b01c401c80900c0c1001100341041003100c040d5006e180500010007881480c43c0c2c2c1701c85050510301621010502c2c0340035640207861103030058480e445031890040445081d10758001c01035004408100e07650b07510b404c01030107080d51000c081e64580ca0302100414600c065030314003400e00e21a4400282c06500ea0145180ca151900030072207480d0031010304019002c0c5d54502c02c40004c100155a1020301d14101404025098401d1080c42e01850004020380900c48a4500558200c22064070070075000000041c07140850b030720039a1000c0142110740010078140342c1090307444440071950308044001e911b000174000030302d680039141c1d9064035408100080d1100c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 831095251 1250 831094001 831094009
    0x2d04051e0f01020c031c0e03250c0b0a170709060315050306011502100c1d04060302030316053a03020f040f14040e1c1107031223030f0402 61
    0x41c100307403191507000041031407051070004020705510b0001c2c514442d0b804103800b179080a40780003280400c0e1320703030084c02000e0000011b2069240d6001d42140b100c0d04d203801e5941e80484450a6a0041029907000704200c2d241e0358005048400c0240f981b405441645071030340c1c0140c80401603000701d501b0140d541c0b4003101d4580482480300c0141100030115601903035540b80072003900020f0b544a80050050013215000b1084502503039001c0c111340e440c0d50802c01055030a40803010004146603500a846080000160310140001d11010360000d40d900030080071410684c2c9000e100b02c28002c1f0b0055925850710300d41c3c080311110f02c80300041c030315080c05075148a03604801034000c20084100d40e12001400044089020503200c04440d800b14042c1c240044903020401210b800182800040d00010364032080c00d0031007083c000d54030b485800d0030a14081c10450030b0303140801a41003250643c0503945d8000e11142c0080380780c00f4a500d810401c41c0d1010116001e0305040c0030140c41d00064040c0200803c046540f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 831096501 1250 831095251 831095263
    0x6150819080d050f061e0f15070f0b06100207080c100215010f0f060c12030b03100906020a23090d15050a050f1506040302060d0902092d04051e 63
    0x3182d020103200e9810942a01030522806481d0f00d80706062100080803c1002c00707080d50715072200284844940382c0810140001d46140c00060100c134101006080009800780f2080e840481c0200810805c5240c5001400300d0189400c0c40c14080d07500680e010000c1060000e103103d11890161035015181c0c80c010b41c00d030300d0100050826004e00313030000000b003984a80ca10135601150501c40c5007c0c035103a81d41105803001c000484c8050070a0941c20b1075103208501a03003005c030344004098115001207444521280c203c1d010604210381d09034000a03944000c1d40d01c0100c500b00c500d011242c0ba06540b44071083c400151089400c02401005a09425010f00c40b003681d00701c5000403040d07c24089442c010800030020802144e03400c40d01e1414902140c514140003184000c00c0c0c07030180c0f0440c5014115000c01003141c014a50141c0c503a61030710200c80041e00d40109480c01403481c103c200e4203001c0e150f40004036a0b05024240503115055404004c04920f000860401ca04000ca82d4601c0f50740b142c2290b6403c080d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 831097751 1250 831096501 831096517
    0x10b060f07020a0e0114040b040e0a02010c030e030a1a0109290616050607020f030301061d03031905040f0b03040c050409060b03031801090e070915091a070615081908 73
    0x604160002030020a8500c841c06c1481d4221010001000c2c0407040104450901441e540035502580ca82d000550090a00040040c0030703080080200d000c213400a4134184070300d202123030700d070300031a00780b800c6440d50545603405440650014440c01182c450343c100144001d1101900c00116002140300a480c0d950888400d8254403c1100440040e0f0030030300d680b282c06a4840c0f00510907042d042c01654004001c1d2416500c0564444100c420414203041c50002010782403a03040c00104281c007020401c034000042604c0407610380704e40b030764580784c240114440d481d03000320440c1504104000014003907900c0761040d1641118000f600020301d040c500000c0241c0c051282d00341c80001010f10511062f403040310b981d514261384155155454201e11264424203071620408034000710011311101e100c0c2044201d62072000e2070501c0750310b0b90721107940307007108100001c101031050001b80d90020700c8400c0c00b8800c0345005080040111514126000395920300541048840c2d40c0305a002a0070030542303a044031264 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 831099001 1250 831097751 831097769
    0x1e04050d060b0f0a05010e122410060e1819060f090612050309010e0d08031e0601020f1c030b1509030606092404020c01181202010b060f07020a 63
    0x11400390301d0000010065114002e11848401115003c9460440c1c904029518180e46690030406400280718004425104c1e601440c09886981081c440320311882c0e60184845907950003041c10410702d031110800d050b0700288204805d54002d445130352a100d105140c5020054906422550b91261040080c0f6018580341c1c81c6600f0024002607030b0030101d03003003801d80e415030030b041112075039406005000b41c100940084c1107030814001480e42d176004110010a0381d002400e00b49001c00b00b980c90b4030f480e600454200d101e030341000c202401c4100e8020031980d4801400e000406070381902e406010341d9004250100c840f41401210146000342c130a8008802c0a04050700910124005007181d0905410114480d400382c4100c10000c0d0861814903042e901a090700d0514402c001c2e4bd1340d410b258202c10319401290056003c1101101148092080302c2070310034440340070700303640f0302514010402c401e8190000381168140508a55240d480c42c0c1207802120100f905155100200d1000c00c60a0140d40d01001e01c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 831100251 1250 831099001 831099019
    0x80f07031209091a03010c030902090408070c0302060f0a02061302240d0204170c090c0d0207020f0d050105040c0e070207052101140106080109050f070804110301110705010e01020a051e0405 83
    0x701040002a0500c130032048000b031011500e0007004404450b10302e54065405042c040105000c1810a0000c00516001b64245540c45440b40c011400607030200401c008852800a60b05000350b1381404015080001c000e1038580c002002c2d00000c0c04035002c0c4689024048400c2c0e2a03500210301c2c60112064000c2024095403101d44d111035403941d8481c20b8002801c6406290801e0101d071405480c220301c203650b40000c030750900c140030005800030f42200c14102d03006041b5004040d0680e0310784541400d5203100e1800420240303030500d4000540c0310356a10141c0181108018000000d401061000c2038071010f440d44080b100282003034640c580c1000021072115480c1c42803400d16840060101d5040e14000d031240d03001640d80d42042800c803030040341c4800c0c21080d07141c0802c11003442080020f40060003000c03030030308624840b000242103848500104282a00000300e607405c2180a010f60215030303035548000c50401c45c6003240070301584141c1c008040705148811a0304500c3c1188015640604400381150b11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 831101501 1250 831100251 831100271
    0x140c0901060908010b0a0f1502071d0603010c030902030d2d051e0f0d0506060d050a0209030c060316050c0a0b070c020411070f080903031e090109080f0703120909 71
    0x3100d00618050a00294208042032003d8240ba8503c4c0c1b0486400c000c13450741062071b2a56600e085070f5000e0120046000351080040c1d50801021600040c00892401c2003250800d2000c16084404206164051605100040001d0384e404180c2c03e441c2c200c0d5041c070b070b540d50020702e030380d560403e020351300054040015a900f0f10103982d01401a100305000110b1200803240365410117280360041801c4d520040c501003204568040300b680040c0d81201000e001c00e802c001690041c2c44c00d40f8400c4403900000c582c003003081845840e04005ca0311400006440d40303440c45c100a000e00506109400010080c00710004054080440400615403030755000b41c04034078035003408080200030304900b007000e0303105500b0111260305d4145068100c80b07120398003519076460b6104603550706029410007680c46515000078448001600440050342d507895401d0b128803075807200a000007504e88081c1c2e42122410340c0c00141c4051811100103640005c0d241c110b49160071088801c8800c5801214641050340c119040c004680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 831102751 1250 831101501 831101507
    0x1020712020313180b0d030c0302070f05090610050f03010303080609071e080c0c070b0909100e0403110a021c060615120f02070602030709090c020118140c090106 71
    0x805480e22801180c0c8656001050803a902d005911030800008030704042044498034100f2810342c0c107a040c103070128214440c90001501880300311016800b0031401d2600c05c04040d41404140007500c00d85d40e184502d03d0a0001007015008020b01040c0105039140c0b103144102d014a0030f43d0304101360007807507568940e16460024555030060b5000c41c06041d4660110b0802c5014400060f0708050080320002c00d44243c01007150129005095002c0c03220007080380c1039541c001405a80702038003c0080c0c075651140c4000520050040052010f1103020040c0e5080c072844400c0c0b03201e1a0402d400d460f0040f1160314010b4002d04000c501d040007580a0140c0210042419204402c0c2c01240d00420040004a0340c440b0030604c1c440e4419150000151090748407208070016510207009002c61040c0141416200c0e5604001ca074001c0ea521404151484000c0201020502600c210301d0800e100900c44602c00c8a03000f11403d2400b18024520084207100d403001c103200308050980345400500c002c00b40e5a4943c005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 831104001 1250 831102751 831102757
    0x40207020f1903050d140d1d100e060a060302010c031d210c0301140c0d0e03030901052a04030201050c19060209040b0103060f090c02100e1005011d0114010e09090102 73
    0x884241c001c03c4265038005000d200c150303811801c4180400d10b1f01d0881c4100200808140c121030094a0080007210444030003000044151240c111001643c986044c452501d00715004001c400d515081840900040c0da001391403048803581820071000000300075601c4905959032400650300403407039540c5600020581030423100c950504c08240d5101c0c1030510149800d84415550240b15000014042107c0704031607401081000040900004d000e100380344040d007164400c0d1100e0010340e445030244098480091440e885090105190004418202c1c0c00040240210720020b4107002c3e0225400d082058207001e00c622078403541c0c4500c03d1002403450714000a401c070703242045c000d62070300c0702d41005540648550b0341907070036840a51003041c0c0b5090020007e0101c070b00c0844110700a161076035010b034038030340505001801c02c613019203540d007100066941140d038140e0280f00041e1548985844c400c000c03920b03c40c192101d085081442001c52801620014072802000e50094103602c1000015541075002d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 831105251 1250 831104001 831104003
    0xc010902040f0b0a030b06060c01092307060909092d14010209030a080706140708011a031311150a0509031207051506010309080c0102130b041202040207020f1903 71
    0x3040040c40400c1c142d5508441c036024035950484d00110f4240049558000350607840b000040c140c5281806040303003a800c0d5130103030030204c444e00b001e54216114a00300c00c00c56155420701c6001825205d1414070001d1001025101c0c444904d0741d5407a20f1001c0c0001c44402d4000103116100001102c0c43e8100d4483c02e244644505941810041c071030b43c00000c070306000b140c10940e4014020031108559840c0c8c680b0991022000700d030915551220100a81d4040071f0881c03044915031140103166140c1a807030a150f81c40c100000c03821040070020018146550110055400e40041541c012000006c011443c900c0e16011a2203030500c002c5042054185c0c031400074100c144064064641020a500881180d0b0045100043c07a50b0040441e019145014002556211405260120b215803868642240e00c0e80524403604131a50001192440d28420100000083c01e01020340d0345018034001034a43d00c14ce0301e05009108a0300020024155921840c0309045800d000b04004000e1402c00b0388100b0358800703884 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 831106501 1250 831105251 831105259
    0x140303040312200118022824030203010e012105030f25080406050f070812070e03070803031b090411090a060f08040f050a060c09290a110a05030c010902 67
    0x1841c1c003d00a418040c08905501861aa100c2e0030129401c100c07080e5080d403640c501d8901d05082502c48200c026103443c000b8145000c191841d401d052102e080c40703460444291081c0760041004008941c1c0e030303010881c11036103402c2c2c03450040b003100050101030036181c2e4405020b510010800c151501180401030007010380781541c40483c40c00b002a8140e1403481c00b1b00240940c2c500303010420990b80110010a002d450b10408a8944000399490881903040b20307004079456040c00d070812150b0794104161010805c0308030024481035181080150340e92000420082e4400c0a000072060562105800e0382c2402800410038850743c0740c2004601404e0b003025180900c1280d6901000500c00d01401280c008103440f0b6650829903138544c2c80d0112610340da244120303a0752281d2140c2c500824410f10800080c00c00c185d4407080d08514120300000007005c41c041c8001c8079030485a4040c01d03100341400701d80c1806ca40f420b02c0c401c4000c0c010f110f54100040300c00068a240800100d05400c00030643c040c24200b44211 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 831107751 1250 831106501 831106547
    0x510050103050607320f0d0e010207031b051b0d0c030809091b0409152304050a020f0322142406210106050d0b1509070504140303040312 60
    0x10448205541a001c41207465100014417071a0444018000d208a440c085601490324403030840800031034034110f540c210030341d60100740102010b6000e118a041207200120000c40007000d920f400da1145025111101441d40d41c030b0382009113407505200255036942102901d0009613890600310519480421064411a072000000300f12980301500c1c408007441c034030ba0701802c25041a00c188000c2c105070200d07980c204c0c80c7c50f00008402c07407610f03001d4040060301c40c80c200350303d4507640134007054038005012071034014014070000b0921940319042ea43e22481c1c140a00850014840050027003000041020300401e000382255070340f40c0f0000442c0d910000301e401d04c0d501c07d80d0030040400ea6021040d1115603104641d0007009000449090550703040445040c00004c40c15640c400268000c2d10203001107980010600c1044503c0000700101500700109544410140c82c00c201e00a101d4803c44c003980602a02584000320992010001e44028592080701c3d05c01c00d85844402400c202c2405180f045000c40d11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 831109001 1250 831107751 831107777
    0xf0f1018212907080c040e13020312090d1e020d0f03090e010b04062712031209020612040302010902060f04050f0121111c050603190209040f0510050103050607 70
    0xc800b00711000445100d183e20303070b0791007280d0012024041c0100c008092101248904070545214010040d00506016801183c810b00d8203020316291041d0717141005116100140d121490803800060340501c00038000e50314541c8400c40c4c2840f21501940200d0300c0d21411040010030840c0e07195240c000c4d29401d000710b60319403c01900762001d014860403441d00f4041041400c0c0030300010360348118020501c1c0600146114803680f644039a601c40d00c14140345440382024581c1040c520f030a8071070901c60038010300d5059004200d81d845402403050803c50010300040a06101703522121690f0750041c2440d549641241c2225810b8206004081c410700c24086403044c0c1c1e40c081e4040105902110114058040221038190000d228004500380000030070404141c200c103078088080040c016003d400101410b10030281464000302e4880d001c8403046200c2e40c000946d480010b41984260f020b000d00c09409001d190480c2843d000000e030300b08860a000020003042300100d61980300310607550b01c0180d08119 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 831110251 1250 831109001 831109043
    0x1506021515030c01050c0a0b190e06010b0304020d030c171201060320090d1403031f082e230903070807060c02120304050601050f0f101821 61
    0x1c10803003542c5680f10003801000c95004034040c10400c840c04080d18100b0015071100d82c42c2c80c4044a40300c011100250320200c0700701c0036106e03210868000100400156041c04c60916441c80301a002034410800503014208040c42680d00350007565110080b0708022540720002c01564008a29600c0c81740522400403904501c64820b00341c0c1b0a0300610340c0f410950052030340205540c802c0c40c0c05a00002c181c0141000b08040c0c0f00040c0040075903030015030742d91a00e005e0540203040c80c115a46955003a091080200c0d8030300051620700090b0f1a084014400450541c2450301c007005042d8060b20303400c02600800011952130055030242006030100a541d4542160544910800c44000c0480001b0700c05140032420562117001c0c1c1042e1401120700c04100c104100348283c01c200d60841d096403000f00180480d00305075545841d004019a050402c500b0120002001031041e5400c003410092883e010003015200300180000034560782c0c0c4e4200e0190000140324081c0d400c240420760717841e050180c0094058070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 831111501 1250 831110251 831110281
    0xc0b13051815010c060f0608030c010f0501050a03080a050d090f030e04061a0f0405041b0f020c0108150415090c08010b0408060402130f020a0309021201050108190615060215 76
    0x1e502c05008207504110340c01035404504a074019101255280c1303142590902038414507010b040d500c001591030b01c0c0001c034030b2400c1d074030b4001c9491400342c10000108460b888428000c4162a0300640054a03299540c1045507940505608826914101011001400000010150320900130b64402150304041c5043c0b000ba140103120b441e00b4a040400f5035000383c0e82d6400505403c000301c8001902c5c01e0b07030303440c0003406661008440c1042a84006c40000078a41c00091022003414180090f040010070000081c0804000a1012042510301011001c1c250780d10b510003018100c1c81d09a074842980c03034082c0c0b50000e001840700c4a0100f0000000418154074907001c0c0d60840740d0242c0109855075440d82842800b407a215048003032107407568800185100c4030300140151410325640040d54083c240104481c40c5180c00c42010303c0c2e40f41c000140800d00c8042080071403540c00b2049010a058035243c428001c00c5409901e00510460300ac0210782d056021404031105e030315881198580e600e90700c162117211a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 831112751 1250 831111501 831111511
    0xa031b050c15191e050903010603080a180f061704031e080a06050909070510021f0c030605060c0703030315081b0102010c210b0a0b070b0402130903020a0f0c0b130518 73
    0x408811311440c00074810402422500005400407600750368a0351090071036084241500041405404a50f0700401170a84081c02000700840040032903240c150003519161100e11403080486446000805040c0105104921030500c0324040503c1c6e841c0e140014110942130790720454442c280940002c1d00d00c2d205030050b0240c0000c5c0c0162034802d1401c002c01059020540300c00080d4003078075013464a40f5810401049261464900101e090b04810400404603259030300928401c040502c91103880c40c2c0d0010f4008141d0350315003400101ea1000041c441400035066002c00710503c2509c0d6044641c64130310781e00b08040c070000e800a02c0080c09490050f17680780c442c98010341180c01003210f000d122800b0313600081216840a130840004c0f0382c40b0714142074240e10080040c2e0328400c10344180001c5003803003004550500002c060400c00181d04d40d40094840181c0c180180494003d2000e100c140290305410703400929260780280d68a00c2c1030309079025140464071985200c5e007501c080c541510b000c0301100611130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 831114001 1250 831112751 831112787
    0x16230309060c0f030c030c01050609010608040f1e0507051c08271002060930030618090616090608071b050f0307060e0a031b050c1519 59
    0x45030503003400800d4100c40c2d50700c1d030702d4400d0390807902481030300380b0061854202400240d6a41d074014251582560400b40030540101044001000055484444141c020344e02c0380c0d018480143c1420103258021500180c2010b14001d14030358010840c00103845d0048440a80743e00d00300303804022091402d00c120a41c0589a20f0040203c0480c0d0300020405044440c1400c00340707100340030b072400494000c44141707040d00c015034000418009015010000094074800100c4622558001c145881000c01c2c003859034030101c1c8002002243c039540e501500d044000300d1952138031031a480c0920503250f030ba0740103884500c860000031012000aa00c43e80c6001709403801911459610b8907840801c584801d90314102c4442003408450200001d80240800c0480e9041d030b200560f00c0e1112030904004940016803035a0103a13011800200010b60402e0241c007100c2c0c402e1000080c0340381c581c04c06038201480014150381c440e810112807201c41e200c00c0e0141403104e6100d0580d0350011215642691104480201e813201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 831115107 1106 831114001 831114007
    0x30e0601091a030a0302070b07050a1e0b0906061c21021b0301090c0e0402060d050109091734061806180b0f1b162303 52
    0x2c01c4a00f00d0151030404001d60340031b9030f146100d204034414424003060312010f0200a01140110503004150a00d007400e0030b0701c010610442014044070f20311000c0e40032968005000542c14070402e0090700c00c8450840074041c0d03105840391300750100c0b0003080c0300c421300c2c031100c41c215100d25071110340341c0040c03c0c080700c00340425084c1010b0542c04c82c0240e00d07000c010400310740d03080d00410441d1030200b440f80c861340325800852010312401a9840c0c5485c201400025903220715404040000e004040000304000c0708000703482c0da84a80d084100440d0010f05542d14509a008450155105801e43c3c040810447daa91001501d61542c51600386c09400800101440301c00d005150003284440800c0c60039504030350340c00e0300c2044042c004031654601b00d0001951401c0d0017038a6030b40e0040c04036031b01752600ba0a98000c881045500d90440d004054150f907601c0e100340d546640c8034440010300103182 = true := by decide +kernel

theorem cover : BRFrame.Cov 830935251 831115107 := by
  have h0 := BRFrame.cov_init 830935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 830935251 ≤ n) (h2 : n < 831115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
