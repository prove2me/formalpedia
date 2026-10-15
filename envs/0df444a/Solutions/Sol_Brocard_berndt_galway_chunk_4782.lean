-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4782
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:56.217469+00:00
-- url     : https://prove2.me/submissions/f5a55021-92b5-4dfd-a518-e92c64c0a4e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 859892086 ≤ n < 860071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 859893336 1250 859892086 859892107
    0x1e1803030310081b10050309010609140403030506011404060309080d02070f0309080a0c0b1606321b0306131a09013201050c120c0c120a0b040c0b 64
    0x220043e20910b0314511503008100000303c2030702c80508606401605810101401c900b00359202e0304010021111990f88120000b07004c120383c05641109030042e12418014101401c0090a60b0300040205041c0309114905000005802007100c0c221452850000350140e45407900110500c2003220310359186001203828018804110b482a110078820b03140d20303070155038480400d901c0e0341c90010050031780f641c421820001445c008004129034100103501c2440000b4581e10a42207410b42420800f081c40d00d05000d40185032541201110005034260b0300c92a0b00d07042402c01801c1145081c02002907001001190f050384424200c4904240001814060142c00a004031800c5200c0b907916440b802d400400060794141c4c09100d440c0d55002c40c16a5406072042c0d14144007102035450900f0b04212081200305460f40e4184041e5511107690818150f03501800200e40d4649002202c10a11840c0e501060403100302001461404041e4004001e03d0a5500e03810b0240002d20b13540e220780b80c047c20005140000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 859894586 1250 859893336 859893361
    0x60608281d060106170907050405040f0203010203072102090303031914011409060105090906190f090204090606170103030e06040b030705070302010507080c091203091908121e18030303 81
    0x1600c0c082d513104a592404203c5c804070805003518408540e0b0816107050259040580103203078401d006620410441c461a804071782242e1044802d41e0000c2c00c80a201a02c0e11442d65000c40414241a8103501b48000c8000203601e0344805041940035003000da00658030003001e50080a80c44040490007465584d403060400440505128041d00c80c540e10000608190b01503001e0711101d00000d400010582c4d90030041c00f0340c40c42821240303d0700303805a0340001002c040541c810b030003a056012000d41c0300d0b89425944001c0d10300617001802442180c00e039581d5414051850107044a826240c01c04903503200002103404c602c03c030341010000e800e00008000d0700c2900400182101e41c800ea00802150b074401208a5440e5000d640b1030441010030014041c0c10b1902012817146024070340166031404035441c00103201c18010307080a282c13803030212034100724010042c001da041500a0702c982610701544103e030710101294584c01603507001804100d8248a4040180c42d41c20312401404803a84c03410010702c0540d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 859895836 1250 859894586 859894589
    0x3040605070315030f150501080d09080a0302030f0a09080712030809060403080c0706060909030c2001050a051606050f1602011a0603040f0c1206060608281d0601 71
    0x505a09000100d040180329100d004203c01084403921030650550b59041d414100780310054442c00e0480c08642e4980080d449460700800c044c40c001c00f08034209040141819499902929940d0407040903240400d0b0007108481070001060040b981d00c101090b01a11850b02507040701c0401d11480c1008901d11840c10040c0f804580642c407041e0b075903030720f10f0721403641c507641168020001090600416510803443c8c01074403e440c403032040803410f070741c4501e8000c04542e081304013603002480d21550031092001c8041c12003000c00082c0d03046502c10000c0d50010f0400d11038801c50908002001512805800da81c580000007503501050a01c464207041d2400f100160068403141541c84982c4624a08140144100c000c018242ca0710340c80304800d0f0f00100038640d04010410f03904440010382000004240c0030806020300314003452441100c81500307005049940c0da401c2101808005000d001d20004010744007140065218a40300d07a04407401c03058006800b00d5105408142055240040d4200000c2013290 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 859897086 1250 859895836 859895843
    0x9190b0415110c010210050604060305030d06141e060a140d0b01090803040f0509180d0201050403080f061f030f0213031109010f1205120711040e0313061805150304 72
    0x20310a04202e0415521079000c070080030f0140c0d100000d58042d00c141c40c0c100d10751104005000044a60752500e48d54110ba001031156121241d80c1d4409100486428900b4000d44c5030a88030080c09001d18090480030019400445106200100328482d140384200b00100e0300741060407031a5140c0a017240c040000d0504400c5050100d4400000420060000000c1d201101c60036070f034600082c0d20b001c3c01e07c0544500640012402d602c040e02032603200c3c000b0040d456000320564000919454203040040050f0b03805449030a6007140c9034180a019980d0210000303003c1e040c2e00d9007001c1d0803000d920640042c00e000000360682400854514a49244014120110390041000314031500d5010204540c0d842d09004e9050103044c039080610000c0d640720002d1108034802c2c1c00f12155844662660101504038080440e0003004460304141c09040c64000e030f501440720100114180880c00d6028052100700313000d48130400c200448480101d1000902c004000c1201502c40003a0f02c134620f800c2183c5038000c64094 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 859898336 1250 859897086 859897097
    0x6030b01020c090c0d050a09050106151d1318050d02030702150c030f0a0504030b01141305040b060618100c2a032012010b03100e0309190b0415 63
    0x102c22800c001101c01c1c400c418419410f4900b400d00c2d2407290062401402d100742d101c0d9641407610000d8003d03c100b0b0040c12900d041ca540343c54412000501020103404602440c0c0801070f0001c4680e00c8580722604401e20803e030214410f401d0004d10341701c1f0309000c000a0440d20640d018603080070740200c003c25000340260317010b0042c1c2e48905003020780c900c2a10540b050b5a80b0401a10b1046000c8002921120400b07140507031030141c0c0d0b6158001150740a81081d0201070300c03204210704500c0d0503001e942080e000076805000c1442c02d03860320360259500900d914000c0600082403200005007440c00f00d40c88138005c0003d004400c1d41b080c001e01e00c61013890225400070b040b0fa031000c4401840d00d03001c90010456000741c01e4090869072144071b8510780c0d451070411902002c0946582d5038a204404410f040c1050000803010a030341c0030035140c8150262800031407072501030351100f40d000104c200d810f00030040c0c0707124000848911543c120018254404451315201007400300b840007185802403030103810340d680d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 859899586 1250 859898336 859898353
    0x3120509150a260615130801020a170906060f041805060718120303111c240b03010e060105071a1b0a05120910090501150e1308090409080406030b0102 66
    0x31010700d803a001c0100b040c41c01002000407003030300d000d060030321201d00310325182411b282c4121b0300b00481100c00d800814a17a5000b02e90f0036200b50380004000507204101c4a20666810701014140c1c407003c01406260003001a50180306080e181c6070000441000442c2d4140200758603424696200ca20540d10400001d9515848421101c03c603c4bc2c60f0580b8a04a03d01c85620f205940c02e80003005040c0800c04072880034030449001540710750f081c200800c60509c003c50001e100511202c0c0e01c0302e040c031102200c081c0030002404807000352810b50b030642e8002c0b0010f403030316120000141c1c0c541c00f0b8240002d0604032404141d981e0100c2610340700e4018490b210107100030184070700d010310b070343c1c054030016500150080c0180c540049107201c1064015503403e040c0d841d0342001520f5181a1241078100b074500b60b442e080407818819034000000000c0c0a6000c50145c03900b4012200c81003030074034510141c180c40022850325020b95480e441221080d50180303034203030340307507502c0740050040c1480380405c0340540a644070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 859900836 1250 859899586 859899617
    0x30a05270310150f03050321010602100b0d050d0c110612070c030306080d180503030702010e1002010213090e0d0f020d031109060307090e0a060b0403120509150a 71
    0xd0a564212008024201e180d08401800000304070342c05551884428000002913008121504140030b14010006165103020b118402480c2e10607652020612100c0c071030041040c0b6502051454140c0900c6602050b00300e03080000424480d03050f10050700e54029000411303002034105514080451082138055003000d0407008205030b40c011a00d4208400e086e03e00080d070524410060010510301c641000221103443d462a107290030401511403001c26080c9000666126242510400924040740258603108050b4002861101e40001d80780c0142140c01d01142e07150f00039016680300081003003003800802d5880e022030015000380d1444089a01900070444900381c89460320703111611640c8c0050440c140704040840040100800c921100003041c010702e922980c0b41c000441c016402666100711481c240008406606809016254114903181c4100080540d8009440840e6084800901d040703441040c1900d2a00c6a00800b030f600510259241c035050640a010f09007090b801c1d6244000d040303ea00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 859902086 1250 859900836 859900897
    0x909020901021207050f100b030f0703082209050709150201051510050d05040f0507050102150c090d1509120e030c280e09060a0c0f0c02040b03030a05 66
    0x303010034016000900001030344841c0c00c00818000d4481e00407100b41210768034103070b41041040d640f5403407040d0300c03000b03070800624003009209414101d00d800303064040d00d149e8034604107111f440506003442d0342c4c9581d104200c4048400740340061072403010500441c98050001400360543e80552513000d202800082d421030303c1442814460300040340d440442502010401c0502040801d0300740c2005420044501104000d0041c1400b03244221020011444c240c84c10030700b09107168002038110f5002481c2040103070006e561454208002c0103c00741d40c1c00c0c0c0704000c6071a4084891003c0c0800580d05e5007491103010540c052440e040c040c510030440f803440100105c4610034124040760b40f660000c40319102070710b804041200c00a40c505041158140c2031458030940b0411640f00b403400030360340c0d003c0020807042441982ea01c8070707901c40c080007590001d660140c414021190303641c0401183c1000c1d1b4085451341c0d40060102d001c0101169120812820000d2007540042d2040703159110341070b810291102c180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 859903336 1250 859902086 859902097
    0x20c0d080409230a0b0402090301021804060909150209031509030d2009220504140d03090c03030305103c03020603040b040c0302090c04030605070c0c060f020a0b0f0601090902 77
    0xb040d0042c1a1101c6a04c980a020042d900300e9009600b00301041266909100a002000d0312800e04405848503004200843c7e1007a4450308000d400c00c03181d1700019014001241040c0070b401130060311584d910000c02d141c64035880b40c04001819860500425140001c05001490700e005014081c0c00c040c14011000184030059030078072003c1c10f00000c4036900c1c10031900d00301d6100944030200314080c2444c1003407da8109070303000c0d07403140c00c11002108180300510070a120380b46107040c141710303139401c0d60389107002c15520703200c090708150361580419241e0071000030f0400100070881110400800100b40e555003465800300d803031884505a01c601005115a1f203004003101c0e0011301d202d0456459842d402c3e00120f000b0412034160171080c80c04001607450280c850b004d02d14035900561110b0851814a0031034101400742d4003842402642d6400190301001107400342d803442d1409804040803110164945240300c10010020400802002000c42c443c02d125031240200766078040f8505d0340c1d600301c8400c078441d0f03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 859904586 1250 859903336 859903391
    0x60507050d020f07300305040608010605030c03013c08010c14040b0f0c030408060a0c1715030c030106150f260c0f03090d08010f05010801090c020c0d080409 69
    0x8444104501c0c00d08100c0f8000c200036101702c290315a00b28002001407031011400071004100081818840c0984c00282c00d4090301890030200e20f10708004080d100c15010500c650480a41e44420b80c58690850110150f0001030300354040c0c0340d1035100300307580302c2c2c484450042c015103600e04070421401611a81c008000c004880c00018a05030509400d0348065104940088421104000400810303008000400c0101204c1d0007800c0d681c00c00b03601601c140c800d0802a10b00b04000f04c0c0c407030b045600d40c0c940700075000489502c1c9444260903140c0801d0511000107002945546000c0d00050f1180020b03042c00c00c5442c0c10341d15064050f807940390030b4400640409450301100016450011148018100c0c03a40020100d500e0b03d003055041708416907554400c50300442aa0007a41c42001c0c400d40080307030b06000d0202d03101190710309803d1030b0008260120510641d200a038840d40c0c3d850100e8024030074100240c0e0080c00d402140017150034a605103502c64441e602e030442c5040021090418507800852a0045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 859905836 1250 859904586 859904593
    0xe070c050d030b210a0218010e070c02030c091f030506061201020f071101170106120c050408210f0a020a03110d0c0209040302150a1d060c03270106060507050d020f 72
    0xc08281c030003004604590f444c4c5a901ca55148200503139110354200070f020620382c1206205604000910300c5000340503110340305100d20654040c0041e540401c004510000039900c800043e6500a0030115000318980000c50542c041400032003030040c0403420302d1191005650480b007210100c2c0300f043c201e1003a46c40c02440c1000170b2182130002010f042c6002000c4205246c07040c0400b080b50041c405440382a4001c02c04900ca50420080502a500450246031520b082c4942003a02d020b12103a1201c2c4041d072907010980301d01c1686480d40e1402e000340d0b4161b12080c4002c50300d81034442000b82d0b46050700142640410500060391202a000088002251919640d440c28106951b403d021b075546024001320154020b911200702c140502542e49842419085000714031100b0046404844081180240140380c1241c030400c00c801d0080c00071207030480301107141e10105000c40b64a04c2e14410040c441c0c036009500300003000604c1a0301c00080c040c0540240f0940e903403d01005000e0380d60b20700c031000c903080e140c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 859907086 1250 859905836 859905859
    0x17070c0b1b13080105060d02011d04180609021503013b04051c03020c06070e03031e070605060409030207032a0b03040b07170c0706060e070c050d030b 66
    0x80008111941044214440030061244030005031065001070501c400401c0c00302d00c081102d007109001e62038101d03905843c0000140c1c401c3d00001d00802030903005c010501c00e110401e404945450740030400c0c0242030407050260400914002003c3d2488000c1640f04112900c01658052224030403a170480f940d40e00140300034071964070004038a000c24081c842c0c0380c090b4070b600c4401c0700a01422052095102d034010b0a44040c0c0104161018040400008109072042c415800840b03000118913400c185035041040005c060000024a18419081400e141d003140103400c00d52006002c0141441d42c1c4215410f00c074135030b40d01003408122440c1180140050340040e400700045a08000000c5540302e500f610301a00700a022101c0e51060301036403000c1110b9500100b0401802401300c600c1303070828005d00d00210751032101d942e0700792008400741102c001000000380d0041084042e5000c0c00041003082f0f4880954a000304002d0250a03600703405640c1070150410018552740701c1e20901456050040c11140b80c1c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 859908336 1250 859907086 859907093
    0x15110d0309031710080d1704060e03041d06010801091b0c06020c030403140d091a0306011e0f0311090a1406130b0c1b010c02101808010c17070c 63
    0x105110402034060010b60358401560300e5030041e0a80c85403240130074520615181c01001490001030a00c040100281e02c804e921080407003031009504540c011001081030942c1140e80c40c10b61090f40e002068080400d02e004402c5580c460416203d00000d807140350b040d80e60350301c842065503c20a1800c0c031b542ca03040c504040707140c0900c2d07100040c0350088800508080c4512284d9143d0b40c42500152031461015000c0d502c0120704001ea48015841840d040e60340c645016011074001072810001c9450f00404070006500d40d00c51540c20b01c580810503403c0e207105030b03012000b0300018104500400080d0400c104001003aa4031001c81d01030300800390442e489146007200d0300c4401d02c00d0114165014100700714060420b4018034190002c0c0c4412034a4640d18455509400e01d0048802002d503002220110005401da03048100c2d49000c07501610f900700d82000550048440e2900e030100480b0305480030f03102255055055100c20100c06047c2c03205140700c004400e00086902c0120382802c0003e03555000310740003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 859909586 1250 859908336 859908341
    0x1806020a120809281e0c0605030a0b040204060305090f0109080f0901090803041401110a1e0f1a1006090f05120a0606060c020423040305130302090f0115110d03 70
    0x3105211003500c0d030762030b50a00c00d081e003000c2120816261030706030040442404500d0803000c4004203000c0c1038031030505d12980e501c1c01c1d18100e0b10840342804000710010b0308130701d2a0f40159a2010300141308640d140c0d100c8001a0040c40309488445807842a10008601100144180042d01d90046c0c05941000e000201d580e00d941d02c048030301410000060000606103008102800161041d009400c0041203444001407070090800b2103803c0b036912030022039010807000d0900c003102c444181c1c80501855403600701198074030050b520040078243d6502d68901403210011a00d406050505200c0c0380c92580d54004446124407405924010810013408100600c4d002a10300d00c40380b1008142e9040504070740702c90f01119600e910120110f141d82c10510304602c0c2900c00e00d165002c400c10720640b40c0d09071491901c030320b5800400007000d0001c0016108144450205250001c590040a11500745041c4444013114003081c8101c840700502038400c0b00301107019231124100075012000803e4520842c4a04802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 859910836 1250 859909586 859909591
    0x1c0606181716032604030c050d060219080105011d011407020a0f060e040c0507030e012712060b03060412030504080906040b070302070605090f12030d020a1806020a1208 74
    0x16116459108881c000e1003200c8078000d41c0905520712a03940013030008644041c121a0240510f681000240002004091294251041030310b13120902102840c00c1da00911403214290810840701c01d01d00f10090b070142095060395000c0c3d940b0b0b0703490480041e0303070500e11943c0c0719030301e01203400000d500b1a0540300b00050a60345000820303881e100355441c036004034580b28981100c00000c1001030400041d0400b8001c2d036504d0780c906d1038100c0c505002c40e00c00401103407074800e846040141400c448620100300411502000c02c2c0300f40c41000c2141e44d462155601c000c11081218101e04210702c0510524001c100944202c0e01300301c070010107098000b0100c0007810000c0003220103402c1840014170f0340d12100058400b8005d1810005d0f0f48081500300039181c81c8595000004001d0308004004081c0c441c0c645c04258100c05075086000c02e500101e1030741c150b01854034140000380c8081980c0c81c2c0c15130302c5110801f901480101245000340c0310502242c0f00c68446102800180819a81340a494400d9040f9607 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 859912086 1250 859910836 859910879
    0x206030c161a0c04151206030803100e060303090d031103040305191a0633161208091c0315081e1615050403081c060618 53
    0x2454484425003581441d400010141c40329000110101600001050442d800100500a40d810245000400a00344001003400810040c5145240f8500d220a41044e00a15401312565031681303403541c010313444041346120f4045036203100790202d42307141000f0045402d2060b0103000b0220562440d103060315903294010640d4003a210401c000400300c1c005110300201c002c517106040504c440d417810201001b0341d40d010b0b000c000d580c1c5182400328560b111141c9081c10b09000101789160a4000501c0c24205025070180321400800242924010755040500021502c0781d01c809450b00c038402012507005104880721120741d8808624030720381c40c0844003225040a45803030f0214843c020769591410085207607202d03150a602a0a662881500351004907840701d03101001081c0920203045626444c40c1a407284402000c200710104521b180700c0c41c100e402031a000300a89a80d03500000d02209104160410b03189414507280010524500c07501c0c1c5240701d0b90f8558201402a403c0040c1454050f9009220742c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 859913336 1250 859912086 859912111
    0x1406092104060e06042114011a12100e060919050a1b1d0a05310515160e01030507080a1505030109031d09070906031e090b040302010b1c020603 63
    0x10040d49080d555102e0701030a1407809441d8189103003a45100c00d880e1151f0300740381d0405000302050340a02c50104103c9204940d00c000140380c0380d480e40e003001c446040110940d0306155021540180018500f40501000001c85d2141c4841c1c0c040c2c1f40303400840d503000034080d03045140c80b5008511a209880903603c000744221003450351740e10070000740806419000c08200d0404040003413031000c0b4411a07503c014210b00f040c808075184126908940d0310341f4414205100c0030114075041c030108124030038407216000f40810890600601841010300c09001c1d000c000750401e03a55a6a5500c603019840c05000e180c0c071401400c0d26085d41c2d820192141c9031116261030350400000907566000d00a081c14140070742c540c400802ca41001c1e504a1650f0309402034003d0603c9001d2111031075100a441c0100c4a0910b00010180408042c16004041d480c0b4989006801c1c010844140f041c082026030040344290000c02940b5101010700c4107200c1c540c0e0326a42800180013094001d030420702c0c019540041c521075603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 859914586 1250 859913336 859913339
    0xc02010905060d09031d0604090504050c0a33200c03071e14060a0c03091206020c060a0515010507020a0f12021201050606090d020d1406092104060e0604 67
    0x811115000403851580c0c441d04c81c22400140758004400c03880720002101c071400c041b192400454194031444c0314000800b685c1d84002806d10009000e202058040140901e030041c3e9510000045443c187d03c914120340100340c7d87c10703800080c4400e010030304003031034444070105030355400380c8440030000c84501e02481c000d950340c0130115502404040c001e003a81c008040c512820b9a2401440c02c0c1c59904035145a200844036480140d8400007605c84516092400c404c2182d450324040700d000609500c1a10b9902c8246001d50420201c0c3d00034042461002d0100c031010781d50728034040103544050768100c0925102101c020b1240d44901c0045c0142030003c2d10746491656030b5151152000310580c030540758520606000350441c50424034210030560100020720107402c0000006060b48507044a1900c01c001b40041c1c0d504645650780b840d0300060b00000d002d024040c04940d1139454403012500310206003d0081031603d14400320041c107624602c40c1c0d100a05140c00d001042d01c2d100134481c2808d5004405000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 859915836 1250 859914586 859914589
    0x17070c0302010e1e010b0405010302031b030307150b09060907090501052a0a05060c0a0503360d020607020a08030412020a140a02010306050f031921180503010207080a0c02010905 78
    0xa589206600131411800715024986a9084a039030900040c03166040200400150303400180c0d040804e05032046119040f11040002440c40c881c4d044020040480300c50401070509907a80041a010b10656900315641d5400003080038107201180c0c490017092041c1030600c4103503c1813010700720190800713401c0300d00705c011025108490740c10a0742c0095940e028100107010080203008240e003050b060160345040a0000c540906280402400000110020f15582d0071307000d404004c0200c907003c0400000912019001d001c0d48030130300300428101500c2000007180c211440001d45528480c1c00c00c0303e240c10741d1a1581c8094155030140c00071401c522910b643d00700800c1034080d10780040701052004200b102c15502c00075040d60390135070080b80300d806800c0040060307031800b0490300c48080139140122048000e600d01300200c0340346030b03555003802e001c2a400740300344a40191038400e04110034201c281c1010750360002c00d4286e100d101d40060000300184905d0700801d000350012a4841c0c414184103400c1a243e40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 859917086 1250 859915836 859915843
    0x21050c071b0f080c1302090a06051e040608090705091302242b1a061303150b090c0903151801110d050a0c022d030408031917070c0302010e 61
    0x10402482d54005018000e018174207040710000b40340000c54203604207403021000405410041c42500b0600200150710440701c4003086214500164149090740c4031501e800d001010001c045480d600c3e148a51000400e0a1824050382407040303082d0060f10600c120b5960031b02040c91181041c2c200d80008480400c0807032566000900115007041e00c00c814a43e140c3c400c0804c1c400642218102954030f024501182c030441c50340700811130202921a50f645007000b03002c8502c0c6070000c1c2e00103810a901d400342c03400e12110641040607152001c81d1a8213650f280c08610f921a4807581c1013690345a03101d185075440741c080701410180e11100c82040009007458020546094032200308600ca40500c00003280000d039140c034030038140c000c2d01c1c0c036804002406a00c01d000c3c0d139444241d00f080d24100820210360386584a44c08500c4945000700040c4c0b61030f40e6075000b02640ea44c2000c4007030460104904182d2030068420b800075400c202ca90401d45415880d078103030a6546141c0f000c0305408654132402e10224660040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 859918336 1250 859917086 859917089
    0x110a4707140c061303170402010207030609081909180b0d0f0302030c0d0504030b0c0309100e0111040b0408061e0a092a051003140f0606130621050c071b0f 68
    0x4891000440e4200e28001b89811041502141d40310050001d11001d40da00050780c0b01030340d81c00500050042c1a5041000c528000c0ba14081e424603004000c0450359a03005000008940c9800103540c0700b071008500500907180111030075a08402c40c0b840c614042881e1980c0700540134040d0058a20b000f40b0580aa0b0030051088244004514006020001c001c040b10803154400c49203072010741181801c181040d10341c040f407124155400e40ba4140d007218502d007903120303102e0801a0501c00f80c1c1c440c0d90382a440e80e503801900c07440d070550051038002500c01100d000348003e841d50610681031244d941c2803102d0000c0c08c40f5401510a01c60300e842c8a41c8107142d0480d413505030170851030914041850304003001880c6210355000c801301801c0c14212181a4455803820340c004980d8445088295101800705546000c1c03030031820034076004c0d1140000c80300e400500c4100255900b1201d0066141070340003d40a03030300141c64440c05d2000030071581c4041060501000200014810718081c0d80b80d03190160301d080341d031310b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 859919586 1250 859918336 859918351
    0x304081b1522090606050d0f1803120f0506060a12060504020d0b0a090e070626190501140f01030906090b09010c0e04051501110a4707140c06 62
    0x1980d641044002c0c0d5102510080401407414030506003403080040c0180960151703985800d0302c805040301d1030880f54001c400366480046002880c0c48160500902d00d4111100d0010100e213003482128480d03c842c00340070312815010b0030301440d10b001424102d46030240d8140003000c1d01d941c1c0380003043c45e036a91700080c03504004020000c03490080308010403c96805540c4000d00302440c008011031144030100d540c0303044942600b009440e110010040d5010400e034020080c00c8082d4400401c550241c05c0003150100b21600e03c0100700036030b01c1e00070161030b018800c0800e6131300600340c80301180158400d230007284c100f40c410741021509681aa6406106850030b5845810503516171448220b03050b80821441c8c1800c030300312014005401e0840307007004203d01c014030042c100103485e8400b0702030348420000d00440d19401400d1020004080e10110564810703119100601ca40e60f84580303101c3d040302a81c14100c441c240245c0042c2d5201c000d8192900004011181e0350404103000402d040300060041790302c100c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 859920836 1250 859919586 859919617
    0x30910030f0e0705150705010f020a11120c100c03090501090501022110090b2106040209070f09150e030f06010603050c030103030903030516060504030f0305090304081b15 75
    0x4201c0000e015a02c20b16058a101d6200c00c408001c940c2d83e0240d0900c1c40340391405503039034840c0c035400d0a82c01750542d815000c9090f03000003646014150b00c4086142c200204c00d040d15140309181d54820210b12038128001402d030b0142c15050000c1c046a44621007843c110300b40094003a40c03d681c0d003420b60720fa02c03200392a980d5010441d0590306144401c41d8000340f00c42c041c2c11469181c820301486c14580702c0e02854041c2c40d034176840700700300d5100d2101e83e5004040c1c00101c0070081c90040d254640d14041110100c5c06600f401010422440c0070300d50400d0015041c0c0c464007500c07410218220000d80603900351408002441d1050101506d0a0100025031341e0114064520303036060820203026039002500c0c035040450f08100400110340e10002100a40340d240c03404540e106901c00b14298007500b9810050440c6117010140302c00c240d00303c0d00e4050702c070419880911442e5500441552240694800d821590b00803d44520305400104000460003e00609103003029210f0850f174007594000108515517800d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 859922086 1250 859920836 859920851
    0x20a0b191b0306060e0102030a0219060914011e1103060f01050409060e0f060a03150519020a030b0103140123060705030a081b07030e01030b0a05120a060f090b040b070203091003 78
    0x5d6110080c201150300030f0008600d0001e20b110000d59842d031907a0b140502c00b4000454404005407900b0450a81d50072103c000c8400010001240c0203054041c0c80301c969071148000d020044205009807800c0100c41c000c2035085a807000d090128102c1c404400394100041000040b0382c0480c0c5205080c060700048101440624080078222142040035101d2441681c00e0310301080000c54043c600014030480300c80204043e00c0c0c01c80a40018100b00c0040d5a11b14004259a22042c4e072541c0400403000b02680c0a1048010043d4182d120000030300400c02e0313410844500e0246208003c3d1024000031010341101d150400b95201c050454104031144000545030a0a1001c02d00380d102c021a481c803244500c26180c00c070959030140c003160000302101e051640702c60540d009640c1d01000b42000700006407003032402640c0300159644902500c00d088030403c3c60b010070804081d1183c0b01e0440c07441c0c1e211407881819112030300c54901ca0b0000070929800c51208002003070a50300d07170300d21350228050340e52004079412 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 859923336 1250 859922086 859922099
    0x28050415090e241c150b030307080c010f060b090d0302031b0f0d020706020622050703050c1e09010501030b0d0c0608010e0114010807030f020d050c040e010501020a0b191b0306 77
    0x1083e0000b80b24441d00204425404105002c400700d112294000c0d00d1494042001c60020080c05e5a4007840b41d0500002c908a414403035800300910041281200820190745244203803411202d035401101450303681400700707d5050410b503003100702e250701a0044a04000035800c03844082e8480410200392074026015503142e140d41042004042d00550004d000d076142000d000030b540301d6004007090505105090301d011654000a07000c040540c00009859480d43c80e03041003503a800d1200714003400340d80814480c0340c0302419140c010640300401030035885503910b0310700114040d06420b5a403650018001d001440007440c2c10740d0f801d00400027030300d41441c190700d040d841e841c0801c8141d104455204041d000700a490380d100034204e50080050a0020380c02c082144407400901456a0011441e4a0711041c4407da00300d240160003124408201081030b607898a00498950544210003407140c80c1e0300004c80d00764001389140352003d05c00c0d02000920360146043c0104201000414600801c0e039960342800304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 859924586 1250 859923336 859923391
    0x110903011d0309010e0f03060403020f0d05071109061801030c08061501080415110d06170f070e0603120301170601050a1518080a030528050415090e 65
    0x4540c0c01d9590003501d101403481907842e4440e007a0803904000011380001400e40d50142c1c0003058004c007904483c040d26103071401a42c0c400904040e86081c0c440c046d0a0103600d03100d14202c0c1c0f02103511184040400b040705c42131103038400000d401c0030740c048210401c101c4010000001d0074000c50040d105590142d162110060900b00080d2013901800c1940602440990b00000c03115000341d48612a0070300c1064403182500240301000d000b00280000280d10241070086810403001d40e81000c0e68a46400b00f40340102d40d070740e0799010503000f8a420921040000b040c041884560261018095440301d207000401e114042d40301341c010301c80103201c0c005800071241c02080b200e409410f096840b40200750070715015a8503903800700070a20421681d062600c089443c0c100907140140400000c440303007a82103107000307042a0001d40c8414020742d803200358803040154041c2030105220752a02c800b498281803030b10300c55203000589655028080040e00000d00c5560300e105c02d0b8441d800d110701d00802c1c5008050100c10f0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 859925836 1250 859924586 859924601
    0x4050d0803070909022818080106030308010806250207180606032f070602071707020910050d1118101a03040b07030b0d0b07050d0605030307030f031a0411090301 71
    0x1010b10601c252440c206100c4840e00c1c4c0e040101b100c040845100c05000c5903c0701ca03641c0c16103c2070006e070000052920054210800b902d100c0d45583c1c10a81e207a11016640c0e04045484e1049912034074410000101007450303640380d030052441a40c148030b0b00c540301c14012048112810400c01d950702810005aa0701d845482c900705c0c8500720684080c4c9214407480002484c405411540c070307200060150070403940b54103c0c2c03191680010701c0c000740401109004195003101c9820390043d0341c0080002c040d0201104d000040d200014050841007850707032151080c044041d000681c0206018581c2f5015500220a00d40301d03800b103c840180c07083c1040b881c95407101840b25204500c0c0414000e000010303520401455022141c0c0c9800079240c03c502c4d000074122401e00c140500300e5403c1d1002c0c0408254440020540750f000301d40140f00c242d40c1c490074940e0341d20513800043c001072145511028410b200c2d0308101228514250703070519102603400020201c829a40768541240c00014030380180742800c0c004e850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 859927086 1250 859925836 859925849
    0x310081603110f041b030b0a030b010b07020d0605090a110102010209280b1b0c0108060f01030f020f0d0b040b062b110d0f06080304260304050d08030709 67
    0x40300480e16840000c40038410700006001d000407805500458031810400c0242840040041c881c2c90b00e00e240526588111898501c0080d04000482800c0d0a10302d40d03010403254000e54a441e036a103819000340f440c1c2c22041e000c0382d00611a600c203102291050203200d018409480c050802000c0c181752020030101c0c0111901d0559006000306402c41d41c418203802021035410064100c40c081c2c040a8100058060b04800c0007140040303840e040304540c2c581c402c0b407034101500c101c803c2018030700019540038204440090384203000010304402548030360403519191102e44005418107e5030042c04420b90010303819003e0159664101400b10300c6c01e40038815003103500f95411031a00d800c401e1541c482d40c40440703d08c5600c0800301e01c2c20b061171115510034240424142d0741151200c8403d84001c001e04004c00700040301c10b080200224480f01c0101c02c660071140320100751179900c24100c8030a050110000498580382c0014000000c06e610345802d80091035100c0c1e12540c0d80c070300e4404000b401d9038407583c2008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 859928336 1250 859927086 859927093
    0x302010b0d061424060705010f020c060f060306010311120a02030d0f02060c0c120c07030204050c03040219060f031d060901020c16080d030b033a110d0309020d0b0408031008 76
    0x9480c404241000c55080c504c10303690300c3d07a180d140d81000381c0940300d020340003180a48001804070031054013068090040002e2031808415850303400415654103c01e00000d00502e89000880314685000b03412814241420700542c1c0300f01c07900b900040d0600411102c0c3d5400320b0200814040000c1e81801782980c4081e0b9803190134103140d4507815107517440e2803500744060681800240d00f03c001c1800c1248200a6500401c28003a42c98407980c14542d1340c0056400300e02442042c105040d80340c621510b10003e0300c1d03c6694414000c11040c804602404981c0315400c04126080e0040c50111414403002d8441d002d81d6001698a40c1ea5400c1146010240403030078042d03600e103e90500c00c1c1e1802080450115246180101d003080610000a003480c1000440302109990700c0c03200d5013104421a00c2c0650b01c3e900c1c1050310048118802c042d00c2e1405481181d0320642c000700024000140260301481d40c1d0703400a00303607491881855031a07654540040e20280c17030003000801006106003100a05001810454014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 859929586 1250 859928336 859928371
    0xe0307081b0a0e070e0114180a080613081e0c0a02120d02070312050c0d0201061424030403020f03120a05010609080a0b07110a0f1218030f0302010b0d0614 68
    0x100190000d0300750810444c50783e090170000e03813094060101c1e106004070f0055a4211002c05443c014040e411040e0080c00090000504410046003003480340c102c2000c072901e020b02d660340740d26040c3e1100480320403400542c20400350003140311014040240046005004005040c010451882e04030762440c0c406502800c580034991707a000c030312282141d50250840d64001326103901542c2c140108984001c0901c1444480c10a6030390542052048880b0049041428284074040c810071100340c06049001c4480c0d81a10350680e002400156441402441a0394440b02c40304100c6083d940142c0c20440c51502c61420f10a118440d4826039004004600340010340520b800b180c652100c4140e1006040840740b400000d5038280a2084400100c2001d415100d924403585070680c040c4d440f90106540d00c040e408046000d56018100711103814007503038a454080351641e03079501848800800201e08554941405d07208a49902801080c0f4600c1002c004c03466401001a92951104c020301506521042004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 859930836 1250 859929586 859929599
    0x81e0d09060506041802100e03010906050c0a030c023c070605030415020306130f1506020d02070906080712060b040612150b090a0c0203071502120a0912050a0e0307081b0a 75
    0x419801c2e00668240088e055000000081c01070000400c0905154104400c1052040d5240c0092940783c0050b00c042102145040040b83c0d61103400b11510301c003c001c46c0c054290f810b00c0c01e022011900383c000c0114103290a5040f254181080369215002140d40482444108407000e10340400110301804218110300d04080010074485040328182c40c803556031150303080b20000a0b0407429410f40007040380015190744500c002e5451503c808208014015a24081030b1101540075140403210040003c22a190400d40440e110120985045804075664030702e40c100d6032580d0080350000c102540301440c0380802070810258903401000301242d110b02d05019000243d036031244403a00309600b04000a505451101d040c0c0c0b552049210103007140f1140c01c000104542d481d0010a00c0d099031940ca0080c41e211602010144c45151400814081507507500018040c0b15201816030305d01c40d442e02c00301e00f4400c0030101e41080705a030040402600244080b8100c1d909103a08242117840948000140d9450400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 859932086 1250 859930836 859930849
    0x3060a030b040809041b03240b1b0a061d0d1403100305010e0c120304061d130c08040507060e060301050405060111070602010903080a09081e0d09060506041802 70
    0x4010300341c034606804201030094034400d4032100705026004100c418010100383e4214148100c900c0d000904095500003000308080310752000c010286400c1001e91300b48600848960400882c1510740d0004250080400c00c0400c05500c1040c0240000141003880a41c810585800c1c1d0031031507d26403005620001c1940c0c0601201c00f184e4070800c034183c83c1d8582c0072104070940400d60010b0711a42c01c00d0000098a10003250103080a9401c640440000b10f05603240744c0c480c041c510900000c6020905640c440c121900c141c061a0702000380b0b00e5055107014010642141c203c1c1e030300d010000380900d04110400c030040040e00c01400d0103040008042c0c035040d000072200d101c140500c500903030f103840116040ba4020800d1080100000c0c080e20729464903400020f00801c00b1007410780c0012155400b143d030105080c450306d00d20681042205140c03484545900c680c400d803824081070100401c01083c01071240c0703445220f10b0310388a03000214407420b00c8406c00054032440b41103503950003c0740d040705005a5485 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 859933336 1250 859932086 859932089
    0x50904060c0e0d0803011d0f06220c080123010f0305060109180f0e0303010503120c0709050c0a2a03031a030303090c0111030f03010618030605040308061f0207060e0a08011505011403060a 82
    0x44ac0c800034039000d01c030300904160810b918015a03d41c00c0055030819160084401070680784040710301e0708034040300343d2001c05a24442018901062602d002022068466006a41d03c1201814500c411540d20044e001080c501040d50307920503942c03034000c0b81401410f07010b101501e0041c007005600b90750406001a440d410390800c0001d40000010b080a054801400701e00000d00d0450801c101500d0039100c6010103500841060000500042040c07280742004000081d1035942d18400003410740b2980e5043d001005a00b4510a00b0f041c8200c40d030f0f4403540e082004500c10718204010b80550040342001502d07100360381d00e00520941090140924642a440983c0d0442d041442c148086503003241c0d5000390311701142c1018240c50300b064208030034190401c52441c014241551110b81c64520141032401c000e50074001080107030822001001f001c0e214404a21004c40c0c000c219007000b981d901c41c0d030341c219910440e2041143c0c5018808000e55a00541540b40815800b064286145043c10006e00c1c4901c05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 859934586 1250 859933336 859933339
    0x108010f09020a2c0316030f08071109070210060608061e011101290f0a03121b11010207050303031603020f0d181407050904060c0e0d0803011d0f06 65
    0x1c5a2100024032407149000044409240d0468100000b941c4042001c44041114006d00c5428031000d4400081e40081085940180f42d411aa43d887e036074101040d800b00d030080e15480d200a440102c6980c0d07030243c2900070704154004005544091a41109680c0240e21040030b1104420401c622901c81d01a0314998941c4440141025194100182d512005060f5610344030f44c0707042c115248070008054003040300d181549182402500060401011201e5007030181d8014113031500410002c0c90369403503c2508546404c090002020101c0c172520f8259400d0401d071019000740c21a48002d58043c0301090252905401541c91458441400750080c91a040100205030b80003035a0b4080e68800c20688440c6c0d013003103500340709040e482031495900390607001041c0e550305103a400d02c8072140000500c8404990018042c0000c595844d12854010030409104500780f1040c100b80e10303096515542d40c500428842c00803113440c1d5040c01c04007140f08030491005d400b010300240a0001c500908404e0316400f83c0d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 859935836 1250 859934586 859934591
    0xc1a06130626160b0a0306051f0f1202070b010f08010506011d010e060c01020309060121080708130e09010e030301050d1515080102040303020118020604061101090c060507020f0108010f09 82
    0x310080c540c0b0f0000446160008607000201c007244080c80300d0000c22448119507801d01400f81c60703000300201071169003403110380d009242c4d106d07500310b42c0101c5c218420b480e1141090180c0c0041c56407400f0076640702c1303d000c0303614848250060002c408580c2c4600302901664008120301d01d070039030010b0143c00b0308a00031a602007414142001c560300c502d40b804203040e0040e000c40d444640e81d01c12203020350070986003030350540508000403c28098a4298818100400004104e014480d0302c50703001aa020b81e0040e600c051040000c058003070824a028002451900390307018261521210143c00c45009081d10340c071980040004020030303038440419081d01900100038980c600f035002d48010083c241c2d00f00d200b001403400700c000654840306502900450340a034009120200001c070512221150403080294010010b100034440b0034404c0c2010003640002000016900e800e03925243c0d0407155a42c040000104c0c001410011400c154000480c0c0007001c4c01e0050b40e035410003c0040e408810703030140c80d01c1da56 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 859937086 1250 859935836 859935899
    0xb090406080316230a20010f02060a0e010905012a11060114060d0e0601060e01051c02160605160e100c0b07021501030c0303020708190809010c1a061306 67
    0x242d58411391180d211030200c6518290b10301d0403240c044a520350340100c103622503050450a50180d02001d40500255010744015511203103030b000140101914458159614224900000d20922851208903c0c2291101e0040091542042c40c0b40380020600c0401c07400d0300300c10502e0306001400d80d0554404840c08050700e000000410814002c1c845d601ca072140c10b02d051040b400401081c0603040c0d680c0c0360745242c03070341c00c0c51030065509100c0d599258900d00503038540341c0305d808043c0d4098541c004a0140050101009072120700a880066900d0100c82030400c00000680c0d41240290403106019114401c00c02c842c03040240c158625040040d202400c040e000450181c42440001c0410001c0a651b04083d6103a052452110302c071800100c001d48903e62021030044000114651207400c0c3c10b4103d8500c00c0750f03596010f15a00300318222814400101404400a001005404201c00791004604007a02e030250070000c09020b52402800610301d4010148000082180c00f82c0d440008485240f02d1036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 859938336 1250 859937086 859937123
    0x702010836060105040b090f0417070b0a0b040606021c110f03210f070c020103230a0b010e0d0611070206040b03040302010b09010f0501081b040b090406080316 70
    0xa03074400c18600c0d50141901c40c05106100071142001035890310400c4448580c0c841044c00101d988840045910110304000035917407610f40804158002e100d0341110300441a50749821010f50840f00702290310300010380800c110340c98144200c503100b21040f98240941482c01d04040e4490340c40307030780001100003401101e00029000b900000c60030802241102d00c1c05440707100d0380d23449400428004031071040d2011310340da405020000c450300485000a094541c3c0e1a00d1200751416030034140201e050640301d80d51011100400c0000010f44544140d256400d840c1184003030003201e03401134140d410310108503180c0394940c41d2101e560b032207a03502070000503000742540744040300e50041110080d0310040018010880054079000f550043c1d201e50001e100d920213600c10404036203800d0140b61141290150200600d610030144550400068080940c08680b45100d0743c00c10b501503004031681c40c1e40010203c5131420544aa88001c0500002550030f1180ca0001c05c0009520460046d01e1070701c0c0d40d0008000c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 859939586 1250 859938336 859938361
    0x1060813021504051c1101110c06122e120809060406020a0c090204140f0d14160f0b0f07080d0c080402040c080708040327031b060507030507020108 65
    0x10590020810000705441a000c1c0615501c2401014004c1301c0202c5417000a01c012030204076101d0340f05400d0306000004d54011100452400050005403043e400081019107a40780103018241086184150a1500034a81e1080300d10900465441842800c1e00b0021006040c070010140d524200355004507480038181070720140124041035500035000600000d2107a00040c502003814864110003032107a9603004950104e000d24819409c0b18548045050102e20b001440365220040003400300b40200da243d00c54125111030b00182c80341d5507200c0b14071900012082c11a8800500c0d0030100c100c851410f00250054500a16032048541000810750b0310420400c0d40544110401004080000c0010311100400740f103c203071000c0e4007440c58000803410b1144100b0702c145c85030b9000d46540105031100d41c0d0071100102d451681c2d45004644001d00302440742c20320040c07401140140024015228220f01620030a5401d50001040c07140400140002a4100065032a00b50702424400c50340d550b100d2030f00c400b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 859940836 1250 859939586 859939621
    0x2120411010503040c15020a08041502010606021506010804020a03151d1b060903010608030d1a040506030d140c2b1701031410090501140105060301050114090a050910170c0108010608 80
    0xd4120046008a10350380e01c2941103442f4007441c0d009000c0c803a070310303d4243c3e1502c80c00081114900e001c0c80000b0690750146400c1d43d0406e102428074114241c0e80d40f2441b02c035030044044507101d5a128a880350a00869051020242e48040701918044c1115017002c07100180d1490801e000c0c02010400011a41c3d00b0f40c000b1001304140e01c156551124400b10071170040500c54040c0c00c525000c0b0f000c00c2c486003082c2c402c69124400c042c0081c103d441100005071160311942070041c0302d0800c1005141000c3c0002d0010307400100c0351581600364400303000504040312445124920400c81c40c96824481c50600114490449400c0b4104d6901c0d14510b06000d070400d0400791404800c141402062000c0040560040329070140c2221348111590b00d030383c2080003501c42882414001003580b406041c040304000300612603c0c100402c481c04050f6143c010411000084405981c1040618401c0000028007a00d8501c654411000b5000840c61500042c01d2028180100000c10800030006203408010308401075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 859942086 1250 859940836 859940843
    0xc030a23160308090a0b07080a1d1b030c100c03090905010605090306070f050912210c070806040308040f11030f06090d020303040213020f0d02120411010503040c15020a 74
    0x25aa030a10300101c0a102054a030120002a02800000c20003000445c541a05a030b00c030f0092070300c60b1102582101c0401001e040d41c888284d82c0c035000708000300c9403c15441c60102e441c000d440084900403403000700803407072004203009412410307101c1c4569407407490442c0c07400800d0400c90301d01030781e0381021950003500f40c110166441c41c201c00820840e802c5030190040200072011616141e8036044200c0d1400400b800260201e0000d01210b02180703449011000c120795914210740e52030401441c8081d40c02081100040d460740002040038102a00340302540240680100801c40c90502d030b0390040c13012034002c0024005140001c0742c241005100c04222951000040480c4c030080c5c02c0d4021140c82d0302055402c61010712030010f400905a00200a49120b20740041c400c1c1c488009080040000c4d600040401e84034a0040122540e200d001f8405040d410003024031541d0035190625120350030a015500c200d050001c280100000a26041c141505691176101020722044411101f64035194000e072004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 859943336 1250 859942086 859942157
    0x6031d031602120a390b0c0f0a08120c0d0e011512051e01181103240621030c03120105010503070c030503100510050a02060604020c030a 60
    0x440752070581c001110039802116040390342000040784940d1007107800c0f0014400d865900b8800e000c6112103150f4030f0388a80708a005a42266010079855948409400c002d89041b07001ca114014010104551080021404000d003000b005035101c020380d500484031811000040c1800041002416401340c4840301c461400500c006181e07442031300d000c0c000c3c0003520001c207950440c0002d520101040111081a001000f034041e00503640341103c00c041041110740d55664a0f105a80220700e02042e00384c2d0761502440000707080700030f20381c101030800c100c0020100c18406880c00d101c81d50001c040b001504010111015060600d8070201c0e03102d1580755540c6404540030200b0141903258010006210401d83ca6011000a0383c841d0010f641d03e0109650030f00000f80c1003c00500080d014100858106540482e6040c0c507a5681e0009144c810980d0003803000148041050003120b501004100d400001c100c41c25424030100d5181240d036409105030303600402020030201c49083c410064080000f01040c03550 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 859944586 1250 859943336 859943347
    0x20904060e040f060f06060e0d060b1008040317010b090409051002030c04050f06041a1b12120a0608101e05151003091a0601050c0106092f0406031d03 66
    0x180950b0541c12001e46000d0309001016104508502c601b00640e00b01e81c82c0d2000341002380c001d00400c2d4034081e81c04ca80309596000c40ca400d9555000003450250255915503078549003510303004115902d800b2407280701d41e003810018001020901c0030f4440c101001d0360b00180e214518280303070349032040249040440602c000144100102803400030011380301d040d10042483c01c040302c2480058440c40c4900f00d0340c0028000100c40e01030824008140e02000c0c3c0400386401080304120501304407940054080320400001ca0b6007410f401518a507502000220741080384a01d4540b24070f4070380307a14415a8110903501c8242c0940d03e03408141da11000f03401ea61041141c0d140c1510000b4a50310440c0d0494850355a007081c2500c05840380c012008020740c414a101040001039449101440b4003074480381c1480024415100c0701d104c2486000c000f01001c0c080410581040d0760112403400c3c5a5036115040e07032080700d1040c40c01c40308034111011271398107240000d92040c006100c080c040030f004010024070301002030b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 859945836 1250 859944586 859944593
    0x302010f0c0f0816212a06051f080102130501030c020607050f0d0f091b03030c08070213090317100807142d180402030a030f2a0b0601050406080109020904060e04 71
    0x105c030680c0c5045131500781646020702a84003050201c0c01c00d00c240d01c00150103c00008442c0c0d04610742110410240390500103003407040960650b202e4000105076940800d0b0340130001d00c0c03506450300420003070800b0003020034407481c000e417180c0d0700600b03070403d00000059000502144404035900042040fa04014002e82c401c44a030140030030740c2c8227441030014212403420745402a01c042080740d605071202c4103420710346d55855403142c01c115401c0e81d00981510410451861a0142c20501c0e0b12a50b03c00f0508007940d402a020f103080030304141c003900141a414040010b000031450151102000c0c40691b440e000070000710050a14014a0f05003481500305800741800c40040c03401e030003012228000d41502e00c4121b44400901110013a615502500075400424003440c40340c0e90134038492404496000104180300110f280c0801000519002800440d01f444007004000d42c108000340707002c134501440c04100030080340042c0110004a94000342c0898240d07690780c00b1000401c1d2401d2500700d607141608 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 859947086 1250 859945836 859945883
    0x507050c12070b010602010b030d1112030a0b03210f07061b0c0b061903060207030e09090304080609060402030637020a020c0a03080d0c0c0213060302010f0c0f0816 72
    0x30b011039804600b1000441d907540103000baa612076001900400b040003200e002114072962107a004119401890480d80040d099000103501c20704c4c0c400404604140c08000740341ca018002a5520600010802c03801004c43d085821500300041600c0016120f228504002c00185034238440c98520b280802c00c3c00d040d0300e4001700d00d04103042c041c10900f21169115000c1c05019807501d11400c0d401e007042001400060702c290302504149000b440c140245008410100740f06480c01c4d9068802944041420440c2800400640340d108900b800a00000c5c18150f02187d601c4001074400104002100700e01e04079610805000d05c9501090003048074404074455200c0002d40c41240d80c500103001c1c41c0e444000343c0c2047c140c410101c80d886030000b4074041c8403101800007001842014420011414103080c09030351891449045c800c2c6c010f100080051951001620b007020401c000028040c245c94507501007600f44201101c0c803a040700951380d80780b03d000344c050700f4000c07003503001020f00765400c15403a411082103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 859948336 1250 859947086 859947097
    0xa08040302070e1e07050c0a0804050411071104020c0a0512030105090702060405210c1b09072a030c0515180f060a0b0402041d040b06041a01030507050c12 68
    0x940955050a48039040c0c100224070468202d4201d50240d180605404c41c103051581c4e000d1001c4c0780041c1410042510b0394101550707408180c0307a04a0101e0280010b1819208030241e41000c2002540761270003541e501d8100742c100303072281c81c030035540403890b0001c4413018017243c0601940301041d50199003102c201607025030000e00400d4012600c0c080090881d03400003494a00540c3c00400421040c000c980701e030382308402c86d900c202d0268181803010f40d81d01802080040907007002c120914035049060b805000810400500380c0c01040760044046007008030820003441c2040602d00300b0a080c42c83d90806441c0d0101c0181d00501f2480b0710340c0c1403250690704081d400d01860610b40c0030000f03009058120f65a5140041c03040600741c00c1040490140b4036a60f000306d40310305000e40003504169466003030204400d43c808480340507109100c01c200030410034220260340410304a80400442c154858004410620340071050b05055454001c1242c40c2c0c010015219040c00860840b482400c80c18217008098120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 859949586 1250 859948336 859948343
    0x70201020a230c0d0510092604090c0305010b040612021303050307050c03010b010207091d03030f0943080106120519020904030528050418150506130b0a0804 69
    0x7500c240f440390303240003c0c034454043d403c42c0043c10b078600d03240c58407030040c18803175002c80b4100700c24080403401c8801091010000e4026219290720366240000600a81e10110032041c02c0624000050041c800a10290703000e80d10545407400e84640d405120000a00c80d811702e1480c10940748d0b4000080240c000003c044452141045c0c400590100042c1800c1c0c6808054050141c0c10101e41806400200d5020341c81200294120624684400c249541580d00c03c0c1c51040c2154507010030420400c600308862003070b4081240d02e9068148950f229071300301000f1001c4c51035010380d1181e21080480a440030f8413001d044548d0007003002e42e5030b0f48800b082c00e00011030101d605000c0c00030400d00724030b80104940340c015000f0301103210641e1aa50200c80760381c012401c0940140600c0c0d40a00d800701c0d54500d40e50440ca407900c0da250b42d60300304103d035408401450000c0d050f081c20100080141c80c025054217044900a499803529a82d041c5005000408140c0150a151401088004000da44150300d01e004500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 859950836 1250 859949586 859949593
    0x30f17070f0212010603200105090907050c0609030f07060506061b21030402030606042a03150e042105160c0609051915050714060406052802070201020a23 68
    0xc3c00c941c03407401d07100140701c040e040190304002561240b201d80b104000320801498198503158100740003d48920042d074155000403404520201c001c48204000742c6c0005000000b142850b03440351070325483e44503d6000030401ca4550001c01ca0940700c41042d24a8002c42e003500f070003c0815801003503629582c10200c061421060803400700c100e0712410840e0b0042da009400341101765160001d00c0058000c0d81101e1a40c0c41103058078a0020103c5525100b0b4400c4940c2c02040c1c2c06003100140c100b1501a4100792804130b031050078080000c0d10f80780402c8108802c03020a885d003494109058415000d84151403d0300044018040c0030064051ba03007034207a03007554540302c10260321703003061140302100c803400b0703000300b034081e800500c00e1043d10b040f000340a080345e01e000c615069096441101c004d40b254001c01d03071540080180020001c00307004003548038115507004040f101c4061500031481104000003101164002044419a4400d00c401c0050542180403202d455240400800d101c200a0303010400600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 859952086 1250 859950836 859950859
    0xa03080a050112031b1b090203072a0b04020a0504020403110a06140f13050d050c0102010b09150f03121603030f0c08010605090a03140a060e1204030f17070f02 70
    0x18480248400c050390142d45988801c05090005030051101070006e036894000610f028071a0030205d40e0f00701c0035020415002d616410000c2d0003a210384030740904544031b00c3d04259900e01c81c124070000d890101c1c0e00301040100c42e4445002060501005801c030b0350b00980001004418003240340c454048010054880321260769503948111900c081440009000c0c500c04c04c2603811031592240030317001c80504043c1c00604217944d60300142e2904440307201102d00740c00503031442c04190f8081c4210500440c007525190503514040904c80f0500d031030215071a02c03541001c204132620351000c004151110f00001c40d0b150351781d40c0031403041242c0d9010280480020303040071060400d8030a54001c0c0c0d2107407022519034658590804d00309031455045440c540740c211080e50000800f291042c1d410f02d48201900018080c000c015003400002e86101420301101d685c40031000f0345035241503001700c1d402c032500030101c0e041020304c81c50a907105503000341582c0075200000c16401c003070292001c01281010302c200c8080d080803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 859953336 1250 859952086 859952099
    0x41a1b0f040305120a0f080a0f0903090504050703050108070510020a050d030504021504031208090c0409080322080d05090a060615090815190902090a0902090708160f110a03080a0501 80
    0x3031041d008114000340ca41030102c1c01b02ca008442c0d060301b0400051010030b4513803802070800225803a40034203a00048241e9030410003804c2a202d260f8000b00c030791400784910340c1801c41241d80e581c5a0310036140520071402054840d6031003840700d45a10b5a01c8025242c0c0710142000086c090202500c3c10f038441d003034038000001c00b12105400c039800c0782d5020400b010903e070010002d90300400002c184e4241400f400300a00380f41d654604c2801c055510806880340c03030341801e01d20309804444201c003045800c01100300400100b05407c0175910a40240d000c04201641d40c1c41c4440d003080704a003401070046003800c602103000d0000d490408051603e81e518103c0e819581d000c001c1d034030044088010302001020021580380d24003c240c10400000400010840d034001d0b501143c40c44004940030413a17a0b5442c88560118648081c032160000c0091414003003070309250a100c4495001c051242050140042000c80d800f80550704500482d606902a41d0105100e410090040d100445551454503e020000b0400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 859954586 1250 859953336 859953373
    0x5010b0d05010b0a08040b0403092d06030b13020f04150f0e01170411030f1b0a0608101e0308040902030f0a06120201032019080f041a1b0f040305 64
    0x4c20a1940c0340a0a9180c60b1650305480501070416400c210381404080303080031104850403150040419020303100500c98103580d03080305c05030304040d04160074240e41c0741c4035988113034101000c011144001aa203e03000c0d502e044a511640e41301e1040e07904102c0c503d00016400c0104400d02a21a466481541d00070380011580444107444c4130650760b00300008a0049810003c01614060020b01203549141c02d240e505071030800e1141c64020300c00d2505a4851550401d518030030000c195600f000038090038030180349540701c00140505120100354002c5110704240e022000801960440c3e051603407562103000038006540101c444034017000001001c5801d40381244200821a10491b80c0c600500286030b00440290802d07840c0d03100b03019003a41a0180c020075110081c07040c2c50404c009000030341c1c00d21a0152403594018070032218101c100b000c1201007000e900080580840d082410340e4940d5903260803150001c40c18900c2c90310002d01007005074403840b410b4020401d0301d008030211410500b084494402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 859955836 1250 859954586 859954597
    0x7030506010e07182603041e0f06020303070c110d120305060d0302060105060702040209100e120d09062a08090a08010e0309060a020f030c0601030309080a021e0105090405010b0d05010b 81
    0x158598134000c02c000d200c1c1c0034403031070b5160000c2071900302c0c400f00c0782d542051564120740c200c02460100300d00c43c0b05008245a500a00404800e801c1c0c1801624141c406512400018014010f1141913007480307041107582d031401c10111900420b880c5680341e69080500344241c920311380e00003080c50a0007042c80c614161348074a01030b55165000702002d82c01c110030701c9025044200c0032604143c0a014210131030740e450801461401207030395600302000000c0100540001d80b0b02c6400d403590131000e2407d4500d540321040009441990404451102c0070100249416110b600e8041d10062900361440411003520010400d03114100e03100c1640c0c64440304402e08035090310402804541c81080110820b040c900c01070542200f03d40140c030400d01c00880c00382c0c119481040500b080d500144014400c260b00002d45002900031007005148507903455001c100401c061003601c0d03002c0c1011105290080c1e00c96001c54900c8100134100307101c1940d480c1c40b030258507084081808141400c15001103141c516550031790b00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 859957086 1250 859955836 859955867
    0x40509030c0c04020d091505040515071707200d02010e0d09120f0c0b09131407032a1205060114030103060f020d020a05030f0601020f071707030507030506010e07 71
    0x40ba222807801004001d50142d092000f0103a220f9111201290a50201c03042200e40c3c01c101241d5440c0a1900a0a0020304140982e100045405100200d070f40800c10080c406598403c50041c1c3d00e4801c0d09076004513110000301068140ca003003a51302c818001c10161a036030702503002448941500c0c24a03d0b140c1102c40010000600c8404041200480203164800d44600580000d80d500c2481d4aa86540c000030342c1049124410003e031140403401d003a003205003203450142c020400c0040301c14003009041c0d00504104100741c3c5641410800c0d1094001000c02054078690310001000805030282200c2409040305880070724103030004280c2d50140c1034100c07080b86516010b80c41c6070300356039940c002402e0f00502c450f0444d03428049200c2c000c0c258030003002d000301c09446140d164509007001521014004000303d04540090b5084144132000042040c1524202d6880e00c01d190200d00d801c501e05403a5920107000c0d407054240002c00d22001041c8241a81d0b407803003a0007040d941d0742c507040d1080c1520460a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 859958336 1250 859957086 859957093
    0x316091e0c050a0c0807050715110313030f03120c020c0103060b03061c0501020f04230f13090201030e2b031e0c032d0b0103271505070905040509030c 66
    0x11a0940d20408544002910170054142040f1164440b285005529001540d601c0d0062003e00b4000c2d401003003100300c0c0a0420000d6150403580c82e100b2410070900d11000b005030000150301000c05000e40e040b5403404060040801c1102151b6070000c0d910f030442c040007070110b4a0b00c0c802003030001201d0101e81c0310740701c05400200700c0e07800c0c001110034420440000340c2d00f655091104800740381550f0000d000a0460303510b004442c4100000c803581640c3c50440c6c0307520540c10000719000b56200c0304003c40c0308440c0d800c00001c201401c1c2c00160040d182c044084649401352030368600c1000c0004100200b50b000618200705900301c40d0009600b02c0740041c5c6000030404034101c2c89501c0b6055a00600601c56051034082502d02030541803404c00c01c480701c1088aa5011120b104118118900c100203190b0024a000d00903813400c1d00c540c2000c0258840c65410030a0134241c02030a1000c003400c0408408c160540802451415910050035030300e031401400d2250741403801081c00340740300100f0307603c00000b900041d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 859959586 1250 859958336 859958347
    0xc11010b0a0314100510050a0e060a0612110c030c0706080c0304081b01050405210a080a0b061b01020706060b0a1e020115080c030114010b0d0b0316091e0c05 69
    0x2860000383d83c031001d00740f40f40310310074110080c04600e014060040c00340c000340c2405941041d04001c0a9105a001401201d08040401400e9514901e05408442c500d080ca5940c00d02c920034440040c0810501c00c50fa0400f000480c4c0d910f00d20008024610107440506075030815031140002c0710b02d114280c0d21040c0d08001480400c000c40c507400f00a260380d0390f2141c0c544008600003070b5481d0035180126016102a00004d084e09d1240c01c040900001c0600e4940c091460841c034004080c04103038019041d15059640c0d9003070860140c4521b01100c8003907003c07020060b0b4481c0c02032503d6002c1d601c41e0808070f80d04d80c2801c80001daa400100e00f43d50100410341c5415251000d405038031b40701c4041d842c00b602d0840d902d03084070810444081441c5070280403984064070b01040058245070070f480a07020a406030460820041000101e0042622410b02d1080000300e070703000d81d040009280802002021909441350200019840d50300d920403c0c04410054414603100901100c10045845580340c0c05e0110300e04100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 859960836 1250 859959586 859959593
    0x30c1104200a03150602030d05010f0f0611012403060609051e091e0106030c0510200a1e05010b01020109020a1403070b0d05010501110102070f06020306180a0c11010b0a03 75
    0xc1c0810100358500090407510303010321040c4e44140b991160002d03800014580980c0049409054054a12140c0f4420840d00d0604090071400071403017200204020075211001c0d418007904882c001d50103060503083d20358104810381c100340c0c42c1352000304e5020382b0301080012003c000e8042d051044c2c95010200903401d41d010012448024020100d40e0580142c40d0044401550703010b40024a0501000010700b55040d45051840d0303126a412251244040c0700542a015500144001d00006000349144480506510181c500036014500814040e40000e02c20766401c0da0004460815008400a100c408682d4005a0880d42a503802a4114031000d07024800480b881c07a00c2c0c40349000280403980030030b82c0c65625030201c0d041490090340301078660700100542d40c2d021041d40004000800214a0480c49541c0c00c503110b82880001080941c0100004800340d4940180c8560451444214051850701c1d81d602c2c4002c1100c2c941071008a00482c1d00c10340760000501c00d080041c50050700c400070040c1581c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 859962086 1250 859960836 859960901
    0x150f04021c02150306040b190603020c03040806010b0a030b010e09042009150118081b1507030210150f0e06040905070608090c01050f191803030c1104 66
    0xc0c03034501d001000700100041c0c84440f01103030f0000c540c006503030f2207080c05401c0105072182405c020380303d00c4420f00510b81c1100700e00008002c9920705d048c010b83c0d0b5600d46880751700f14090341d032002d4698056a40005a6582c00030024851000e043d902080200c21143c0107491091108101e0364010f04070400060000720f4a43c1e0708000c06040c2030050302000311400025000c1e03401254402000700d58890070908958010f4910f803210076468820360701e02c609152500e9a1041c0c0100d04420704040485501c03401c1d196035500d946081140f0210941d02c5400f420081d60b110107410b80c0418091a182980003004112028103080c0d4441d54030403140185041c10b654021b550180c40c40d47e100303a88400200004c0c2c02000703010b00911050b1a50b807034510301400040d0800c4403074887d690500074100500340780e80310032104236036040b40c052941ca1400750102c001210b400784002d519181c545040f42c0080280344c0c01c9031450b15110f1181e054481400209800d01c000d0ba024015000c40d071a169000c0074040c019200c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 859963336 1250 859962086 859962109
    0x402010e01032403050601060804021c11090c130b091809070905090d2309010f0e13322a0304210201061a0f0403080f040503150f0402 59
    0x525001c5444a06403c005211010581039100c0c0c10502c00410020003400340001c900506490030a0300b0689071540110702000e41c0309840f0600c030203002d10000208a03e81c4458540c003400504282d03000c0c070708001309919644c03000b102d603254891400c0e40055030b481c1c0c0c503080303498080c00030380360841c6001c0d10358200c0100da030081c0404005000b0210046100241c0f4030a80d4403c3c0b4242000700300304000940058681038040001e8900c40c18000c011850f01d006d40e0f022200ca02c00b0a01c2c01c01409803080508079840e4100c20203095106c40b205120079540c0081d6000413451540452902d2103000c4101c078814100b604120344c00d800503900500191b011813035001d10700d8070b00d12017214528510781176240c8070b00ca81d401250100c0d6a18100318a12030301c0246d03050b9000c3d10417160f00081201d1410a86610a54880c101102c000d203c400035410885405c9072007541c009591040d1003030b4680c4030601c001003158201d070081c5800384c407800d40d48070304440060030524041e4030340c10403680640c0ca654091121040c0f40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 859964586 1250 859963336 859963339
    0x30405040908090603040602190219020904020315040311071d011421030418090f06020306010c0804170f0a03090e060d05060708060f04060609121109010f0503061e0402010e 76
    0x144403a146940313441004600c078a21441006039a010072001441c0b0304c4240d06c42850440d070000042002c10400240440c504580403112041c140c0d03564070000c1d02d0880101c01c0c020400c0c03d640240010560440520280c00580c01e00345c91b15141c4803c0344100d07000701e401001c100460a6401040110b402e00340d6001107480181500452981d40b00020030403810700212003d89900c000740400514040561121030395400c0c0e9010700012010383c4580c40e6151035040041c241c82e40c0000822060383c00f80684251403580220100d45542e9280c1c28007a5a000c0000c002040c1e02600d481c203088a10046046e00c4030130780c15144c400d5954149148101485802052550003e024201180202e103003001518400d0007035503965210b918150051007582c28110700c4044c09103043c0001400003030b820001c05001d81741048440303030000351181000440c4401640006420002d60b00001c20682e0004440b035055540640444503140c46a82036462001603148070b03024011990404600150300c03a10482005070300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 859965836 1250 859964586 859964603
    0xb0f220510030803011d0c070f02010807092102120622080f2205011b030c02040f0207051b030303280f020c0c030111210a15090504030815030304050409 67
    0x11290340d824070f181c0c0b007a040110f2001002e94090f40c0c0d440b1403450a41c1c0400c030b98501905255560750785203440607554400070705100c54980042d201512038885c00006014030807aa85503000014200c8110b0f004405003030303008542b07403032204144000024205020354400740541131480c803220184a502114000704486003082080502031410824003d8a0075445444c1c038002c02d071000e2646c0140c80581c5d940041d0500840c080043c02c020040f10200c00b2098140c20100340e1007a0500c00100202032030780c15800341900c0411418240b040003d400031400030160a484400c000a204140e0781e4041220102070140b42e2449004901d41381c0d03900004043d6104030082009909a0036071030698100c3e40c1003035040c0e80b2007101440782e0b103024000c0d00c80488800b00140c2c81c050003006003010503102c800120502903c4000401c0f0056110b038040549428140c8000c0ca00719180c060708005080103940603000201580c011403440554032204100c0460300500451401c0e1810042c0030241003255401d641504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 859967086 1250 859965836 859965839
    0xd020708030a0509010e0706141308010207050705030607140f0f090907270b04060f1103030103121713021c050a050d0f0f0504091109130b0f220510 65
    0x251284090740c010311003144041000e1901d060420b003194841144401d03143d10064040112a4205040c80450341c882003440740d9500000b03407203004411003507102c0d0a2030343c400203000060020115a100c00c1e02d034100e007500d8a0b40c48801d801c6400c5109115100e03d8440f041142d0704040840a0042003d40440016582001c070300c82d0005d850321108aa410380800e25600110f80201042341c031030080b04d85aa041d101807075040c00024646030003140940018020300082440000f4012003101e01d2486030310044079642c7da100e24101c6d204161042089012a0245840340544034a01095030312816584003280c6440010f82c08000f0011301c500c070759401140c2a000641c011031000d100d01d5654901400040c0040340711800c2c0100741d4140240c154040255080b8000005d07540103048804480403100c010403541c0f0301c0b0034009814031031481c0c0303ea48554401030784616100b1a40081078840c008485e950966000c0e0b9080c003512410b4007200c61907000000181c0c40400110f41d0002d41c02480341c002201005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 859968336 1250 859967086 859967093
    0x15030605090717060a240f0f050403020d02030a2102100209032104080109140c1f05030402041b030b15040605120405030c0f030d1b0e121f0c030f090f080d0207 70
    0x6d802c040980440c491010f4240454681050660010108a1030302c2c09402d00b224400800e81d0203a404024071581000541c0c41c150342c2d003004a18107882c1c0016108003d000c0655642c01c5403000442610058020b811082e10307469054401d580100300060054524622020031425910341d02e0900c10400074410b0002045941e800d220b100041072040020076000c800c0e421149207800b0401341040c2c8038852032843d13030344420303592140301c841003034941080b5403691100d1001401410041d103580084000c007501702c202081c1e25400c4007a4402081c2d410003c04106e5070700000140c03189000b4000420002c1000c101e151048500055010f07003d407003941c0c2005204e1100c00d06107210102d0074805070b80081400c0704201510300c1020311244844c1207035040b801401c003000e0149544425540c1c840c012042054015807024400781010107106824100003000c101d11880083c0800c99034080040d00d0842680700c00406489100d16441e0040b03400d9807a060340756104940c50381320902c507803981c0d5001d1011a000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 859969586 1250 859968336 859968359
    0x50909160605270109083306180c12270703080306061b01020c24010609060f120606081602010b09280524090610030e0c03030415030605090717060a 65
    0x101c7c00a0700914492005400301e20b054800407011055550781445c003030150b560b40d1994044040e901e80750814040fa030307410950100900078503081c1ca060b040c110b000c11901c18003100c252400c405001c01c000e802c00c000c0342101582c1c0d5800d400020918001000414003614100e07000e030200811489500c00144440c0360882c9c20b981202ea200003c40e80300a14410201d05600b1000c0d00303416940400c0308032985040c0d401401030700a0710420091291001c500c0010760300c00c000000000103421020f1003915a91031000701110012030301c0d4042204100104c611052040c01041507c040082020405440e141c64100585815100344031001d49041e00c0300c8107640c5a40502e6100d02c4010b0000744044203000d11046141a1200d151480740c0200303030400c036140d078a6110024007411540b40010301407104400f800d1030f10001c80c03c0142e040c40301090000c1c00c0d80041c14000c8001803c2d6034207200150751141444403514058564a010980701c0202035401c0400888036a480701c8020054030f096a40c0340041001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 859970836 1250 859969586 859969603
    0xa060e030406080603030a0206010b031e070c051002070b0f060d0507080601080c041404060b0a05042412030c0b070215091c2303090705090916060527010908 69
    0x60640000c20100481900300740341e19130003401036019601d4800107490003915043d050040800b961404000700d09684c0e150100d01c13520320040007035944513051404020300b400c607280c0412a40c0744160303075032668034490034000d4070000c540c0000802030a4407820b03a8000340348401481c00b9040950303d001280070540c104003500c010300c07150018000950514044a0034441d5490215004506120048070400040c4181c0c544c01500040c0002e8a9000000060b40c02d011503070042e80d00c2803e2103000c10024022210f070f0300c500100e2086017140107030360716900d047c0c00499040290124207203140d03900101d03240c00302c1a80d104066105480aa10030300c44040c499010590740b01c0b0703095000101c3d81141d166030303600000b4003400e64100040718402199482c0d090301c1c0011000080d141000c008182c3d070660410030707030002d008000c01d00c41e4246441d000f5190368041d16501402c8a1201445c00501a4002c008407001c000c0003452445540702e80e494000c42e071604000b00300b0b042111007900060b021809000088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 859972086 1250 859970836 859970861
    0x2e0f0e01090f1101140f09030c060c070504050a05090604020904140601030b0a1d120f0408031206210c0105180909070906050306101a0409090c181b110a06 68
    0x1c0c006505044040f8030310060303244d05000c0e10840c4440000036034406e440c0e001102400d0070740d490300c04001003818400004002c40d000900803903107100311000070803000141c2d1701c00d490400603907450f00c0f801000d03076000380d41008150300102c01080240c24500ca465500c203014010458840303948030681c91514074242c0c0161100c148442c10702800512038082c1204c2c00c0070500303040800c07028145045446510405070119107a00010390401d5200d118000e4a00404003513081d25100c581842e090310140c04102c0d459880f0740e1000c0758800c000201062805a10000b40c0b006050b5910818015142e5130300c011064804031001074044101c581d6054146445418910b02801c4000e282031200b5040d54010380006100390440c07030801802d03d01e84c0ca2110b084883c451000c440c1119120040b045500c00c40d04410401800c150140f801d100dc000000001c036500071a5119840c01a61070711011241e40c118901014944500d501ea6010701c0390020101381c860380f100f07607842c010003070340e6000c00c40d40e0000800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 859973336 1250 859972086 859972103
    0xc1503060a240e030a0b06190306060902090406380702220f180209100b040305030a0e0105040605180111100504303902032e0f0e0109 59
    0x12503102c1e0340320110407000502a07004281c04e904076951405d000000900e0710340514000140d0803282000c8000d540c00031900071404000781902d4610340c001a40c0480305040c0154103100c0000b40c00b50034034069002440f903103002988944010781c40003000340b84201c885a5094401d00040d00565200c10605025081182d01c0e0200654116006030603508000c0138254202c1c030b0301602158030f0700fa500c2c502d00c1c01d507411142525995105a0840e82c890425041280303669808103010080003c000010321003031486807a491100a103c1004403101e1003140204400100188007042d004c4c01d0f013040680c410681414820314410030899060b140c91100c44e01a5056501c5409000500881c41e50800030303080046100c00468051101e00344018514200d04800c00031603490000282c211800941e966071a54440072280c0c2c4040d840741303061b48591540591180c001c40070000200c004c5604003810b100914464000e00303070109000e060040c44810780d00e1001544402d9900440d84007071042a4080340300f107421 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 859974586 1250 859973336 859973399
    0x5040f0605090a0510050d05041406010602060702060f060f011d060d14090a0206070b1e01061d0a2108091816080f040609151407110c1503060a 63
    0x20070000000f56800785001d0404102e8031700400740c0c010202c84511000301000b15594580b80f901c003d203454103107000c0d08a401044008541e03641d002c105c6c1d5000700c0a13542242c500c2d881d000422080007509490f4240d002c46c0004090840754051141d011040c2d141d06400702000c0d0043e0b02181040c1e214070103000a1355a05c9100710151074030b08e82102d40080009004001686455000c51818401c80d4400790075480100300244948a800c0e9906180328454114032019503035458024150101803030b050080c2c800a0902c4011030b003000d0b49500220f80e50510008245010024015100300b209030b0290b0702c9840410100e00951141080a2400400c0c51982282d0f407030b100c5c02151028603000c03245010070130750320288010080089402c540154202c000000d9070180b80c5450380c45c0e0300151000a041b24144007000803140740d103200d110301c910130340e860720790240000740304064869080161442d4020100710700d13960502e142201660303200c01c0180c260244241c03113100c40110030b62400719200300075201c400c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 859975836 1250 859974586 859974589
    0x10121506030c02011803080c19030c030e010c32040810060e040f150612060e12070503040e1803160507120f020103050712150e010f1a03060105040f060509 68
    0x40c840d69200c6407008200c0301c0381d01e500a01c1700300c100c48000380800425001054540060b8001c86020044092000c01c40c2c0d450010003501800c041010b1801003407910468041929040c0114400c40c510360759200365240044880e80303400035840d40440b0f0881403081c8007181ca0b040c8900100094001d5a005160459141c00c464042c0d5110707821149101c1420402c0c400000c181484000e41140c0c4460f00d55106450b200f41e010080c54180d10045008101d01c074400e0500c90946c0c4560703040c2e9907080c10f50301204600b03202d010403842001e8004006600411003005510241c2d04026000441000b00d1840070442c1c401031803568011600640660900301d50140401c04100b00e01c034010090140030100c1e4000c0c6c0e455107030a40900c0300010b41030548a0000401091041c2c240f071505200d1100308018600c1c0490001814003820300030011401103220004c6800b1091180b554200c600d00e0302040390520140c400d100003a000a001c544c18404140400314a010311034280c00003802950f664191611013450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 859977086 1250 859975836 859975841
    0x4390b0408070b040807060e01121a04050709060e0405150a240206010501090e151f1d03030324040f0f1803080a020a0c05010c0206070f0203040e04021012150603 71
    0x1804032000d4002044104040507006c180d5000312002402d10348505510a40160380400021410800c1d2500c1c0254142540303618102004810000751030800c055501c56030243c1f88030480d405500007041c0e010039010032500d01500019842002e54100c1c0300f84620710004100d002d00c65401c0022070b05120b400e115001141281d0b03a000180c0c00303100410095151800191400200740500e005955588000850410380700842c0382241c000500390706002108009103034410081c9041c0750001030141152804000050000c15a002c4070040107940f464940b407114070800350b00c3d0542d0501e040c0d103080802c60180da0364800c0750380c80c12100d00301184140360040c00804440480c590038941c0c954452601021035800f000751580700040020050b529844aa82a07902c1c944000d4000c00d190b08080031189005d6001c6441405003c2e03070b444071012850501800c1c0c0e1280298040c2c0300c0702824482c001809840c08c0b032011041c3e80360724200702c007030740002401800503200d589800c007098401c40306e000c000c07241e03042c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 859978336 1250 859977086 859977089
    0x12030c030d0209190f0905252303042013050a0204030218270718021e0c060a0b0607060c03061401020a080904020a030b0607050a0b060904390b040807 66
    0x30300781c0100c04c600780596024016000d010710b1900d00c0e80e031400980305d101c0c460003660f99043d0000046080b00710040c00100707801041e015001c0395800800c0c44d6827000541c3c5007500c1c01950b004804d0303100c40c040421242500b42c5002e18031076211751149900242c074041442502e029007000b44000da0b40e203007503005200c000340780c043c00c038240158203004004082d000c3c01c000501c00d81480700400311841420b40e4081c0b40c81925001294001d05400e9040850740b140d500a14101ca856081c01491680406060500c0d000346001c0000c5604007900141c0c1d075100d60380c40a2902a07008120314244100f6495510480c0c64010588010036550380c0e003402a08402003005940a600344001c0c011080703250756402c403034041c104805020310780100324011003e009404c9040c100704054442d548507855820543e541e80c40d001700030b6808a6500340402c100307040c001c014500c00c98005050350340d80054100540342d55422140c00405401d0300b120704e140600c2c20401410018200044032a49950a00e0103050402625 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 859979586 1250 859978336 859978369
    0x61115040203031207020c120f0c1c0f061d16092304080c030c10051501080403080a062c0610210e071502010c090302010e12030c030d0209 61
    0x50080100582e40081260130440710850900840e48075850181e142c40042a013540c0d0103041c441826004c0180013800c0200340c04231800311080c1e880200140b1030748114000d02050708840710490721001c038040c0c0d10b40c07644440c0305400029205c281c025418103101c4003108031a50360341003501c0150b07030300000c4094440a080516001c200e6040f0440a8a04103412900000104585113002405110b040004c0d180a078020310103030303a0390307040b0381e203a0507207803500d1401c902095854800800d045841d01c0e203d0301c2c180041038440d4041c90701d0390349081d0380821000b480745041035226240450400102060030070600c440c1080030307503801d10b42c03c2c2c003502d090310040c040c501588082d071300003844c16031003002001d50318104041452658562413545000e01415200f581e001d00c1060340018100c01c1c10441c0407a55034079980200804141c50740d045660810754072019000403007500c4100c10624000c4034a00d910340e000002c5900d030406520603d400d43e082450b0310580f55601046048942c10b0103035480c03052011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 859980836 1250 859979586 859979623
    0x11d01291b0d0c110a0b090d020f03030706050924270708030310050402030609040f151415010c0c06030c0c0618020901050d08030406050c0405300d0c11190611 70
    0x1b071150b00c41185c01016a15849820000b035250150f4841e040e4800d1040b00c06415203907155910308007240034200c1034406140e58854200d241072904a4904240b2a640141c020710b0419200d200306540903e000f001b01440e2950094031524044074200f18800042c1030380d8000e103486c3d01d00350119888243c403551000d4003417401001042095900c01051690095000070f074099101410f040c0152031040c3c0c1c040b402541458140e41009603001042070a10034080e407050110082c0380100112784110707c2000061003458104000d1001600940182e41c0080d81882d06146000150b120f280948461180e41c4800a013015040c0080d07051030b2501c9030161200341c2d50042005015628900c0381c0c0310090025203810781d1200860b2002e02841704482c000c2c0310003410300100c41e070980c00f004c0b06210b0010b448100400951040b85100c1c002048200691000780c56401e0f100070182c4909040d01b020081c001e0348801e005001040400344401c0e11405001c0e07a90f1041d024070030b00c1092a1034070b0301c0c0c1100260300340c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 859982086 1250 859980836 859980839
    0x5041707030906030c052b20030105042702093303070923100509090105070807020f0c0d05070b040e04030906091406160605011d01291b0d0c110a 64
    0x102d0b0402d203420500d0701c94000c02004a03582c65030400503c80c150702c585105c0c011340c842c08c0c140041040a18183c55080360100172016160200243c00d80700091899120000703d4606c20152426920b4181c0c0208140401030520b14108100468180c174208906200340b41a615201d040c14100b006001625442c1c4003044601030b4882486c500c507420402003010215540002182c03880301000728802002c0c0508040c02900b009440c4c2806404204d0740700d800542008000742c0c5540c40005c0d00a01d46403400301816040b0141c0303080c041041415482a1201e1080d00c1e000124000760b50000d0006001e03072420141c140c18240f4000744204240d51146c0c04200006105121000841a50001c40a01221007a0b6500c80044620640034280130b0301500a6103041c00004140034440c50017141e400300c41c4181803003030317803035201c0d40f114040d413854501d407002100290306403000700320002060105460444081c6031681d40007003a2401400325400700c0020b199482c01020802e80c1d000240c00094100c85116003103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 859983336 1250 859982086 859982107
    0xe120301180605030706120f110a0c060212090a151a0609121006050109290705070f060c030f02010507120f02091903050f0a0f0605041707030906030c05 67
    0x180010300480646545100000c08402200c0d84500000d08015042e1803140c3d070f4403d0041c00c2001202901124181421100641c61510b845000c1440e804105a9401d004105004a44c809651002140d11949c01c000c810481c41da80c82c040751150050b24001c0c20070720342902d024095224495030004506060030901c1e4035aa00020390b8405d811001e5454989404288002505854040708184d0442c051128260720034421900320707500f611000c2c0ca82d10034103a5203107111100f07003041d00308050034400c4101e904c003401301c1e0010040c41c9050042d4200d17901740d504c807029400f554003994441000300e915008410300701500026003180400340c50000700700501d001c0401401600d44514184503d81c2e84500c82403c0f515258146d84c03200c4c10181032101480d810860414070360005c3d01041d9078a210303031041a04030703d90004d0100c44559100710200b40f204243d60790074ac003814020304215452040b9054801d43c00766200081d0080078000e5580698043c5861300150031101c1403c2c400041004c10840b44020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 859984586 1250 859983336 859983373
    0xe0304060e1c0b0606070f03180b09030325020603070f08072c040e01020c1e0a2013020f281704080412031106090d1d01230d0e 56
    0x1904079002c0141942c13a00300040f854464142c0017081e00c0d034048440824958807000c2e240880d03d80b0030045c908140c6802c1415441d00581101542c10307842001080d0000502c4200c44041d182c40305104254403150760300041c3c1d40d40003154281c000400500341111010303030040ca4641c002d40d080c20100401d9402c0188000300715050200c044041d240041014035949a961005c0d00b00c0b407102e07000f11f48504640425907201c01e011840c5610200d0200e281c011020004a0071b140312a50101d0840303a07098000e0140f1a2101e0380202c8194000c0c1811103104e00c030342c4171f40020440840d0440720150345045000d044000c3c408420070700f541c0c1c43c0502d134044a81c550810140209031000000c3c05045580b80c1c9004c4502e407041e60440c0c00c0c4401140a280c0c105a0081c01e0042c001d4100310958000e99902822507a40d5080c0d00c524100282c07a000003640d040035240d20035a0b40301410f15001603000a080201c00c0c0741201e000d031441c0d189800082c0b541c0c004105100e4100c02c440b044000c0c240c010007081c4400342 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 859985836 1250 859984586 859984639
    0x90b0711091f090903090503061515130e0a051e07031104031a042306070c14011401090c05090333040b07030e0d0c060b040f0e0304060e 60
    0x2407101e940402c070700b0402d10048042803060001075050050301c1d00c50880c003400030008202c02103480c1d982e0200d000d18010802c0d41c4a1454940b00300034855200d0104442000030704c100140b448130410030880f944166003603282c041d003000c1030000e025050141c0f41c2c2d821244024607c0d0b0000080301440b08410000c844481e800c402c42e0301e00419003481592307542e10705d8850b81d0b000921180004090f500300510602015108034010b0401c8002e099185d011000843d080c6904000c550f0051000161194018059820014020540024500501c084040c2140c0310b48402ca090080468010810b04480b030264000003100c07480e20609201c0d40d4408655502100900700041044080381d010315200c030040100e04080c0f032001b0202c02401e244c200391000c003000f540c0681c0006d051034844608090005804407041c60207540d60740c50620903444010040691140107503000e038a034041c5001c892503901410740e12208450155075200d00c3c03c000900f00490f1100c80074003d41c031924000c640c000d01c0000100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 859987086 1250 859985836 859985839
    0x70c050606040b0406050a0f0e070f090501050a050f120a061403030301050f03031903090c050108010e0a0c031b090e060a21020d0b04030c0b0f090718020c030a0c03090b0711 76
    0x903c0b804810001409060f07260406038004808550000e0701c480b090a1200c111554650080c13026106d001e402c40f0b4049002191401050840341c041100b5403251000306020052441c0c00303402e00790741041c20b44156110040035600e003000344040c001780583c1403280e200103003000032009928000b5107001c6510b0340014800ca40c0304203a00c218a948a85007441201c2500001c01080a11010f44401c0038009000c0321509a800c0180c1190114095004200ba00d0690340d0710040d440c02a030304d441c0708901a05040b02194205516000e203005020801c5916107500d0980d48c8070b8500c90340c10018094034420f001032600e80b10344207610781004480d4041c00342d0442402d9104464111900a0010403130350741040d10b00401c0a603802d8100030134154030602c44281144a0748150095449905580350801e0341602d004182d031b04050820000000c1011183c02c401002150150030401d07140c80d942e0558102903106000310720500fa01008240c0d100c0b5084002c0e11010801e43d0400b815a11a51841c0b03200a5545 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 859988336 1250 859987086 859987091
    0x603010608060d330e101d030705030a090905070504090e071502030c01110406080105100201020f04060905090709060e10031503030c030206010e0417070809040504080a0e0d080306010c2105030708070c05060604 92
    0x48409451f0b8040746191803030060304803503684140c1d16003d603407681301e411010000390328800701281c01c003594060700740200c1d05030303865508150404a022005007010f0300100800c1c030031488002038894040ca84921288580d402468588055850650a680c030901d00c01d00111400c0200f48100350b00200803c0c10340301c0694a000c00b10000410036402403040d109010841c4d400410300041965001250782d00746c8805803400300d0603072a1482e013036800154900859000c40c2d0120710b030030082d0a1400003122959075602d070215030445102400d07040c814040e003064001a020b09100f001745501003080500501d02024038001070720b0725880b2030311081c41d100c951003551840000e00300c091006400a0f1b0700c18040040082080703040c2803a05100c40d602003981240400c142d141541080d242541c4006180764005060514641d609001158400c40b0f1400845084121101002c45041541e00b004c1a0031040d8441e04d5403428503010260904100030100d03000c005d80c0306c602c3d00008102050342c076004007090710003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 859989586 1250 859988336 859988351
    0x303041a07140d0605040b090402030a170d050903120f2a09040c090504060506040f050f121b090c0307022104080d02060406050f0103020603010608060d330e10 70
    0xc440e03003410514030b14001030000c0b914480c0c62900390b02180444d007040320300b0050740d8015000e01c28006c10494002e03505800542c2d141e0f0128441c2d4440c0340b4403190401031035180544e404050b50490f0701c01e81c0e503048954404142c0c0f61082c030b400b1000c5900034100e01c01210462501641e202050f4000c545110750b80640010700092a405c40416107800b08001401403000182e9000002c1c00c1968512441d40300c0d500b00700d00060b10342070034070458086d14030091004841d64200428072041d0304c03000500d81d8020443d5001c5004921060125440c2e92240c8400002405a4442000b651010151038150044420824130024580000c0d0314010f402c1c14403e844800c0e401030311000d00c0740c01103500800d81ca0080c100f1040003e0782c0800c2d46440383c1c0c803810b410070642d10b079444403000500c42404003d402c10310410040c003409001e96422a03010304d00030030340102d8611580e14103488501d00d00e085464403540200016a600e021141c03007804000c110420068a110303041c41c03540d9808964901b80f606581c5000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 859990836 1250 859989586 859989601
    0x6060a11070f080a02190810020c150c130e070503040f0501060f1508010e010609030b1b07150c1812030512040309060f05041805150d0605180303041a 66
    0x201c00018154458441c040c590f45442107900c0350340340d1400303d118200410098540300c0407019868240e8103540010315881030501c01840003507101100031a12417140310344211940005181c0d551086030b04000c41d54403400840e1080723041d210340f500586804003400c0c0400001070b40c8442076990181d080303100803a0610b550f0178018018900d507007210542030810440461541031441102c0e558108541e103c0f41c8617a40e50781440b6803c1000e00404002070804841000401d810701c5007540c02100242e004540e020884513060a6540030000481e080c02601840503107040030381c81074201c41401820012002043c501e0140c01112550240f442020709140c01c020034544031780d042e50340320090074964404508040c107000e80007651511400000841050315100c1d20743c030035000e4504071000140d441040a113120400005448010803000b01049c04441c40381d4984d4610714034182441c011180000d4a003004114a91564140340110f02c540c1d00400920000840c905003098107440c40c03040740e003210b40b00c905 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 859992086 1250 859990836 859990843
    0x815130f1a010806060111150c0f0d09031706220e01200c010507050a0c030530010608010f05030c06090f09010305060601080703110d110c12071a06060a11 68
    0x64222104125141c00401c10340c000240c00c5001d400241c9599003082542c041a0380c0d41c41d5a80d461140001c182004150841042c0004d0081d2010b918415410a040d05820400712000b404c801d42c0058000210411507001c100403880c3c22580540c2c0d4454407018000c41d4031084000c18410400341661640e8501c4480000c0d40410005a6440043e1100045100c40d60341035801202030a141e0303510b01008291110f014104940c08411251900440010aa1000e90b45c5400010300c803100440c0e50b1b01d00060b000726454482d20b5103880d1082c4c20820b9410b140006200c141d0580040307140c40c11803e01406665000103600700c0444048491075665041c1801040581c03001c420100d0b005076a4200200c100f00c0c0100d04170384220000c1e620003582d41e64183c4202c0c19507801003900e190f1402c00b0031252100a505420801d410b9140103076030f61030300801d0103506181c0740c0d07181e030124141d0700003113400805c01c10014803c24005852841181050038590006a403901c24000c600d0300b4040d2442003141e80e00001d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 859993336 1250 859992086 859992113
    0x70c210804030c0615090b03010501080a0f030503070201110a05120709050105041406040e010f030605070c0b060409030c0803010611010e1209010c1b03061a0108091e0f0111040815130f 81
    0x50326175842d50382c1c4800f070f5405440840300e95440b81d400c1c4400440e101d400010040c48658010308000410412920140e901c3c0d84050200b90465494801b107500840c0c03042e0041104483e990350b0503503a01c0014161018091002c3c08220070001d101104105603a4498299410307196501c0401030005400f2000820704d11640d80328141c400c00307140002030184400480c64080b04d0141a0a00869031101030403603000a02d0342c0001c2c148480c00c00402c1941c140340e0300903d042842401c003640300203140d071a0401c0b03d1300241e201c4000100d07124081044844203005d41180c454080c40240810003881c5090032a9000d2194041d04026041d0481403c1c4114400006420f1141c20090301c2c2403512800c103040981190300e001110764030803080c0f10310103520603201c41c0c1c0b24000d0000a0306a003003a0311294103840c00c000152202034400c110380b90b103107298280f04030301ea048d070003c014079915032420304140d091203002d207000c1702c892002004025141c8942c4039500c80080c1d00100101c000245440d100b4040d0310030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 859994586 1250 859993336 859993361
    0x31e1e051b0a030207140108010b03040848100b06040308070c0302150c06070e060c060a060f06090f1e1d0f0903070f0803040804050306070c210804030c06 68
    0x1c00c00441000319000c14542401c40c0654255a001601d03060324100c00040400714900040d442e000410040040b00040e6410074402e900c07540c6071441d00c0080d07210142240380800110b54880500540c126a00314030703c03190010056005000360500c0300d94030b4584100081c0d204810b511480c201d03c0a41d10385080f100034541c00544c007a12000c440c140101560343c40d00040340511300c58600f002140a03210241c40311007a81c04000c00c8159a401011100070907050320b8250091401e00c00d402c030045007070142c640300311a4440d00180980c689a030480c1d010000b9030200040c8041400b050011402058035241a180080d004841c10300346140309001b4030a442d44409010540410800400312030100b001d4080e00d8911145040c070380b101c0310780a0300c0b441054402083e042500000b5030010301d06102459000c1d00170000107042c20390300e0b804a41000821100c0c9400031b082c1910b510104000f050140d000c0c05034460303008840c41c0c41040701511001002c0d0001c0d081c000742c601302108110a54003d842c12605 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 859995836 1250 859994586 859994617
    0xc02030f160f03020609010c050408300d0203040c050d0b010927060b090619141201020c21130302220606020f1002090a06050d180f031e1e05 62
    0x40c0d08001791a9813054440d0f1545500700a0140c141e10312030826102a11441409804030a0ba122254a103507481841c0741d2503214a060400e03541c2d065610080d080c0d0706890400580c2c1c910342032400c241e240700d581c0c00043c410507820502d540407070312901c1d03071606480041000043d8550031b105d042a03074020409210045e07030100c9080c0c0b0b040100c15004401e2802041d550506184c680008100004880040e0740c40144071000c2c0c01c0202e02003111080d0302c03405001c4c00c258600020303079141c1804c0ea4015111050a503000c040050b084945081958280a0780070096500305200240b407002c08940c00c0c440644204228040310318031031507000045040a0820034100116a55040060346a00c0008125007080c0144552100454054001c0300c40e081401001410218203080050b5074682104400ea400103a0352000d02c1b007910fc1d542040c0340414040c0402c81d550311081d1600401010040740009429544113a031403040c150400b000095a202d84c400050404810501c201c48078029182c44d60145803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 859997086 1250 859995836 859995863
    0x408041203030f0203101d07050d0c090305070801140714070201051b0a0c1a040f091113030f2a2c0c123114031218010c02030f16 57
    0x51410359000110f400144103841030360803c0c56100c2c5072407c201c4488010800c100602d100458040d40071011080fa2818110344160312902c47c10301c0c00680303802c1105a82c0d0348003148503c2d09400d144140d442112803900c0045540c0c02d4540070810b0181403c002c0c140304001c598188008111090001400b810310b0840720203100d14200039214003001e1150720480d44c0f016680c0316125195608807001e032030001000700c08041c94030031250b00404010042508001003401103540307003962005000000c40c002d40440c00e000c82c0605041e0b002c800d03445000255560040801c0c070745400740d4514170040302e659141e0580d50b43c1c8007402181c2100720f1011112882ca03406003c10080000445c0076055100e41c9600b10009070f03441c9816105d2682c840d00201004250740301900c01d0411200003008411071151500d1011000c4544007107141d5042462401a00e040045c200309010046202805a80164500078451099000d80207501c03882500c132440050000003400890302e419032812205403660000030f1b1082903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 859998336 1250 859997086 859997101
    0x140709031506030b0f07080702010b010207030b040f020a1e0f030209071409030109050319091a030c250213021303020f0301140c0304110d11090702011b0203070201080f0408041203030f0203 83
    0x31174200c440f0008240c08101203001c0d2881480f5081c5c004006030000c008080c11a01e0309640c01c80028012110304074100025801610385c025245c00030005c50152080078040703010203001044240e04203a0f03c00d07141c02810009a030318182800e402c5103803420b2000e42015208202c0242d446074644007905982005107000402c0000401411855052146081030941e17000c4220360703c0d4120f1065032403041013002c07801a071601c0c45000b9074011480400d20341c45c041c150054480d00b24000300c8080826a0008011825820324017080f0701d20803822001185030003078500d0100300c010190300010b401000c4002e10300480d52025030100f00503030170b40c1038001c00600d40741b103002c0c1240e07104580860300300c664050424614103108541c2c050642d800708000b5044010341c03040c0805c64000600c040110364840c4542640b290b078039460520610002d602550307035250603000250458002030309400048884008000201e03510304207443c1920320004508401c041c0a0900310040e00010302d020701440c1c40042440ba10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 859999586 1250 859998336 859998361
    0x303080723220b0304120203090d03031d070e1f0902030a050601120b130c180e0105010f020c030c040e10020301091a0111100509010905120d140709031506030b 70
    0xc604425104850b401d001d10510109600900c10074884074400c0c4080380024070101c070090501c224601c110fa040900b81000500c1740814100150701103503035001d6094400c2d640070090312158030740030000d118051404c20300545025000b0001005080c021781a01c504000d840e680c0d9009003000c1c40255100e0801400341c800a110541c0e0050203c0c2000d101e0190001060003040291500101100015503800b41da80c00a04030701c4040708100070402074607088050f509000c1c6000341031500810075403581004005000108270701420340541d80000000c060a07540080e60741028001a10081080e8400030303002c074070300303070a10001c0c1005500100020680c41c03082e0380040703480003540754202c00c101c0002d00103640c2540d10f440b4201140e0443c8407603241c298281d0300025040f000045c0001018000c070345920b03041c2049407031030b02500100050f50580d0610180500400708154800d000c04904040c3c80240100d41d180c03100424620110500301d00700072030380d8015001582c10007002c0d003692401d0030203a5003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 860000836 1250 859999586 859999597
    0x201030c1110141e06040906060806090726070b0f040b0c060a0b120a02040510090903030e01062414040f06020d02070609050d0f020d0611120c030f010303080723 71
    0x64014200f0001042d103c0005180000c10045041824150b1602021321014044000b801c0e188103032600310010b0000420010a841404140f001d4a0941e0a001548007482885015180301c031030480480218494042641c5048503241c1c4ca0559858041c02070395191401503501242c0100c9000c909020201004201c1340d00c2488521800c1003d03130415020804c0705091042040e01c181e2044100600604041d44415084100034038030001140c0e0314501c101c10703201c08402c101c0c0040d407690009012903009000b44000380071100b561034100c074000242c54041340407170114401000071201c51410402c607000207d50113082c0b056030303a0084949802d0040d60300d414980210780180300350100020160300c9403201c141545c0000f000c964060446480386041662741100691b800781c03e000000001440d548150703100180d03907900180d141d0780503030300000c0d41010080c506029207c04100b0020408036007030034541560303454245001c040e107802208448401d1894099910406d141c01040b8410f44034130b01074038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 860002086 1250 860000836 860000861
    0x723090612030307230333040c0c03030b03070303020a0b150307060908240109020703020330011d0705031e09070906050303040b04060e01020a0c0b180102010213030201030c1110 78
    0x2c602c4403038407541170640d10040ba009850b00e88084078500d101000305076007410f92065482d5800c0000310400004040780d506124041c003140000d204101010380600502d5826481180503040091840d2006921012500002420607101100040c5c4030348886107022010340d400780880b0003003919802c0c0a040d1121a01800120b0300c1599008450b12180c080c408890744011003000026900e001d17100300c041e410a040460950000b0b0199000040c01151030226004d59038502841109080d40d00040e1102d043c3c000e51000f45c442d4002907220030040c030819403c0a00340c030b0000d49d43e96a440401c4042d05510210080303810500d4240214901c1c005900e41c19641480410803410380c0e507104241e542d02c61441240c800040038082040018090003944c9440c038018016241001115901c1c2090180342e90485002c039400402c0716040c85c101c01c154078400660030b0000714548a40f51800c0c0c00c43c0e100c0c0740300c02030405488050b0711148510803e00c041d01164032000b254807c1482551b203801809041d034122 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 860003336 1250 860002086 860002127
    0x706030b0d0f0807200f130e010f091103030c0312100801090f0302100b0f09040501060b030c07030305150117070210180203060601020c1003050c160b06030723090612030307 76
    0x1900307007001040903403131188001c203000c80f161100d0090082407d40c410b60084616907400900b48415800c4c0541e002620313420b100000c00450514101100c11114241c0034003c1d8414084001c51361000000c0b0303000c446484000d00d0581e51040700d021b02d01c29458004496175401c08100c281040420f42c41007841c94420303003e0b200c0342107058000c4000c4603a43c14465510041507101c410850030480c011030b4102d0b01400001c503a5913110a01c684a550058a0340403e03281c000908906041e4144034007900312080095460306100d401000914001ca9055200210140c000218211078002c105c045a10a48202c2c280009030720070fa1400d0002000e110264028080c85d07001403d10740c80451004d107160b40050078400403c1080d5402c900502008003c1002c0391001c10488003a54803511090420070710903e541c180601d0010203040c00c1c100b0380e91141b0408141452080008401503800c2c1c200d80e94140c400503072079070790003000818901d0a100c00c44002d0000000b441072281d03004556000a40f001ca005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 860004586 1250 860003336 860003363
    0xa060c0323070518060d0509030a030c02060c04090c23070c0b04080a030c0639230c0102040f03080a080906040f031d0301050106090f05120706030b0d0f0807 69
    0x10301c4040c070100ea502000450400102482e14040050340b01d5107400a0700361801c1c0950700c501c08080783d4061301d4024460740013240e0300000a0341400741000d8030345a440035040310f0414184c0c101250143c4c2c06100246915128110a850b1060b44002c4506100310b20145c070500d03d03054064400d610200090310210300402c408241c04412030100c508440c1c00341c0042030918240d480c110703071040e4110421a01c481d1904501006125182010744181c00010301030341440581c2d51140c42d01d800756810b80012300003080e0b01d90b24000006214800e4502d949507043c0c0c0c1d51341203111054020300c140c1e007100600764000c510200a024100e00548550718244d190385150b5110703481807940e0b40c0c0301254003d0103014a0000040007a1040d00d6404400404401080804940070300080c2540d034260010000100300c0c440400034185130202c10001040140d922654131107100084a440c0c0d0818000d0400389601c3d04524801a2180c80c4541d00c0b00e0f4106040b050700030918540b61a4951040c3c009582da41c004034136 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 860005836 1250 860004586 860004641
    0x1b1b300806060306061b030307030219080915181209010207080a080d021c05040f050c060c0304150212040308040f0b0309101e060305010506090702030a020d0c050a060c03 75
    0x2a010750002030149095a60b00820020558030010f8081c003001d0105052081c00750007000a5402140741e5100544c44040d818030300502400000c5000c2d08008518061181802000c00ca184904001d600310f18542d548240c000020b180800d501d800c102e11070030084c507404400c480e025003182942682034440721940c981c4031550f00c10810b07001a06640b410412002807000c56401800783c05014904808104030004802c012030354200e0f4260b6654041030042000c00506000c0e58985401c1251100d00702605150042d07901d010728000c41e061078103040304d0f1014543c000c00841d101165070001096803643c980c40e00e50b21ba078002e1b00c078000c080c40c020640402c0000321a01035a1140c80c0b10402400001e00501d49400585580c0c10703101c4041c00c50b051060b00300e1109000b0a000b841c001e074004102d03804c010060009041000700a1421900f0912120400c0c0381e02080541c031700c6003030b0703c0c2030303680e404860405900b480340ca541c0052040c0c0c1750282c40122190150031052031005e080d055040038407250803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 860007086 1250 860005836 860005847
    0xd110301051f0902090f0913060f02041a0d09080f0406090f03032c09010b090112020712181508091b010203030105151210181b1b30 58
    0x1504001d520340e881c4000c3c0010300b21a4050300303414034000c061002e03150829020601500c0141e581c12044154200d001341030003d03034003402001002921045281905e41020208042803200340c00003422000111b2203000180fa4215604058200703038090354030340b180703070302d641c46a40584251340c0400d91100e00000c01d80249568001202e415403513039880c10451107240f004200428085c84030700d0b003009184103d280c40700c10040780640003401405603980b600100240c01c68058542c4100440e00400c400c20025070751025a4418907143d0410f841140c0425070081c42482407500700301c04aa22889070354054951080400380581e41d00c4050b5003200103c8842c5003011040b07002c64901603413081004010a090001d00062559000001a400c080c4041003440c0740180980c0ca0b40001400100180304508001e00c0420809003d200f04101071034000b11542040810b110744a01030096612103100300c401403492083c000381d844440c16100000c6131801003080c031480ca080b6200340000c203440c03091040c09007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 860008336 1250 860007086 860007121
    0x4020a08010b10030207150c030222030f020907020a08120703051e0f091603050c0114040e011418180d02030a08011e0305100501060806100507021005090d11030105 72
    0x42c100803d440240340041d0040d50207400116081c0c0c8500e81c081200102c0c07403180108011041c0d501690703400000b0b294180d11468040660100b4802c801c0c20000106110120411250f0540c0c0004c1507030384500083c0d003080d0341034078080c28000700010910b02c05c40e54034048038070403030003030301c0401580d01c8220040d4000d000641d0300301c020701d54540c08100b090310060310a6038410500d0b8119591440c440e56030f0480c6031082e51044400c0d50003600404025a084040c0d0b0b8215000284003a080c140b40070492002000c040c030030004516034056503814107450fa800d0381150b4500c0824140164100240b012510031a120b000c42c046005100d40d0280342407000c000c0300c08545040d62500d11a908100008888400c00000000c141c00c00d10400000240140405200300c0b5210308001800c0d0326285026101c5000100011f1080035000380000d021130700102519085074041e91802d07441c01500406461912584010950184c8a610081c0801100904c0314075000d1050700248095120400b480d410903010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 860009586 1250 860008336 860008339
    0x90302030a0b0406060b0f0705010f05090a030f030908070b0f0106050a021e1903020f0f01090317060a03020913060e06060315311b0b0d0b03100509010504020a08010b 73
    0x41101d03076010402e500881d42d04280140000510380e82d80d002c200c0036035480034080c181c1550b8085410350511500384210303000341e458890140b00c540740a202c03441e155110444c00034180106000240c1d10188203a00500f503983d40303c81055910011802d028003006030890b0008032603554070002080e4940f02740140d5140130195001020284240d0010840c1a0b601d4a03124030300d44606c0300d4012940001402c1001c00754000e40181a451001c1800281131a582e21101042607040440500010764481426042180416803482140e111200021030300a020b0313001950003408134050180e11400d4074006000c40340318034820440000e0f481803641d119541220025490780004001c400da80c5803000b00d4590000301e2018190510048400a1400c07000e8501101c5c4200c414540c0e060401003003070040024119032900c19129103190081061880c450a42c03503426254941d0818001034504124403902184c404070f040c805803030104e01803070090200711402d03803240070204800140e0b040c041c070481c1d006070700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 860010836 1250 860009586 860009593
    0xb090a150b07060b0d060605120715080a0207050a030201020c10051b091c0317070c0c14030a0506010305010b01032a35040b0a0e032d04030305041509030203 69
    0x70780041c04160390807500040d20910b0b00d031800d50300c4503554603980050382442030000041032402e150034011b11034218000303011580c0c40b40c0410700030100da04c09200d41921031403515000701c0d55155078250107405500390091052080c4624841019010f4004d482003002a02c1141d11410148803820709581d0142c0e1048202d140304000d020404010500402c81c0c0e1002a02c00562440c081c2e030340c0007290064440640000304007114208601c43ea88a0740c40d0494400c0c9041c0c54400e0482d21580c9201e6041d00c030f8031001c00e000150800c52600c050240c850303419000426034000e580c0d00c2c18058064240494040e001a04e4401c03c940602d90301403190078406140c1300e080c800201544001c0c4c403040580440343e410300b00d034003c80c104040302c402c3d440c40c51002e0b01d119080c001e082ca89000085100003819000c40d031400c064002010000c00819115284078604101c40c20203141080c400b0001900d9103541e8200e200010040300b49030704080100100d500c952144044018940310031221000b01e808029403680 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 860012086 1250 860010836 860010839
    0x1050a0b010e060f070c15090e04050c0432010806060a061d010302040b07060c1101020c190f140a051b0105040902090f09070f110c03210c03030a0b090a15 68
    0x2029009480007020810780c1c2c0e490005c041c2c0712100841035940c00b49006800301d60301c203445035601c4410000104610004c1c01d15605242d92080d403510b24408025001c1d80c2d50301886180034110f08041149410f06042000e002180c8490070700c0c00360402d005882da80e00c200c41c0802e00c107003003441e00401200c210781d80d49030f030750f80494200e4110340b2001c0b00e54038105030b003e01000c00ca0036280b000900c0414401c0c00e001490f4095110042e100340896003013001c041c0d1040c0822211000c0102c4d440141c2440d0070b040311203002c118a000510031080e088060126210500c054001c06400991400c4050007141100c00a42181b1010078400c50b0001d00d076400514180000c00105109401138410032000510f64402e0304c1400d800f041804800302e441c0030024500800d00454260851100e61407800b0358000b40c50180f101c1008607560301070513401003030107003c159603554800c1c1a001c00d0341c4030023080d00142c1e9506d0503c551100050000a103450307100e0480d04002c205c060070107104083d04404501c8079050741c2c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 860013336 1250 860012086 860012089
    0x13080703050c121303030e0a030b0c09010c0f1b0b1e0306010509030f2a03060c03040309090608030d1b0801090b0a1805090c03030f0324030307050703030201050a0b010e 74
    0x60b00101c52600301440f0b1200e1503a810b070360708400f404030741955107400084039185003802050780d90488071707485c0580710380c031802d00c00b160070b42c018551701c0b01c0400455943c07401942c004848402d0b40d130700082d004d07180c080700d403804201515850800d01440761822503135603502c480b140c4541e4415091007030307040401110121000c08001003d10707482401414038a0a101100300403a042200e88941c204107508800c1c1d80c00c0b05071074020340324803200c0b1100000041d880040ca011964400010b04100340407800440014201449810b04001620041e5000d0003204c1d566251160769802698808443c0c074180074200100d481c41c0ca0900c181c20500c2d40d20054142d03e440c5500c2d005203161030785540c01003d901d40200e459506a90320f07540c3c100000c480003a00d450000702850401d035000030250b2190708200a2400d804100809603a0840601030010300700807d10044040580c030700c1d1415640500010801d40c0900c6000b09490007101e000e600240244c0d56044141d6080304e594a15103804502c00c495071029a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 860014586 1250 860013336 860013347
    0x180402090c250206040509151504060e09040809031605010e090702061302030f03041e050d02181306060b03060a2103050f1201030503040314010908220306050a0c030513080703 77
    0x2d0600213894145010345a03808150000030841e440706110f445414030350f005d4100350040c545d031004810a418209414082c000b017070030410300801c903c96143e01001c5024010668200c8140c0d0100404a42c000c50400000c001e00b289148111408a44c20f01031540e450305215040314450407059003c1c03d80d5aa600010100d000c0c80d142090380c161260040348901070104100400c09840480e0784403070107184004d15048444850382017680500c0e00100c0100041c0c44607040022815000502c83c42c6560700d01c800c034040b00550a20103807225081200008040140384011405540b06a03200300ca52501d500d541d03030500c0896043c1d4442060000d0410b004244140054082170004038407940c50a5410745508000c0301d03003a0002e4550342c000040800c2040030021504010103180e074000d001055598880381064040e44181c1110410502c42c1000641103002800028541c044000c200c542030003045a170060800140345400300780f40c1001300344000040b07005419a40e6204143d5494501960703402c5a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 860015836 1250 860014586 860014657
    0x18020a05040e0f030c0f191109070509091e0f060a1703041a04170c0a09110c16180209130902120d020114010902031608070905180402090c 61
    0x10078014072107000c004000510040400280030717001840c1c541c0e002c00700070b0704200d0110002041140c8121074200007902c4015803117040c17a812903500d4480d81d244501518207118661840341c3c41042d4408004460b4514104c0e60055400e400360b0b1543c83c0d0f0381042000d0303000002c0d1364095000450300c008202c80c07140189000410815001502e0800e5551040400100b40071402c0b48403641010409000b000e2640c413030780c2000e004c068000c0c08040c48100c08a03405070101d00070f0080151f01c0728950100f00d0b050100f196001a002812a050110754402c0043c11681c82c0c0521220804050280050307140a4002d0b41d01d64400104084e0340e825250760030800034440c2e0102260008074103d4050903001c0180201e54500b80b041c0c00101e200c0e4840940e9540009050f04150843c520501c2401080d89800c8100e501211a500b8201c440d5200d011041d292080395522007580b1041c2d404400c020310120541c0c0900452003620b00b43d080740c64030803c00143d40203861f07040d03025101c03000360550400c000001c1e541 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 860017086 1250 860015836 860015861
    0x61603030f0507031406091f0e0f071806201501030302100606091202190618051c0f080f0703030b100801381206030d090803040b2809030618020a0504 66
    0x105008401400b5410140c0c48c1e91000d0701c121000001c2080b90364600184075070294007031401d80360182d0310300b844940484941c01251704001054000c80c050213100584541014141002ca03510090801d4030a078403ca400d0104034018010355001a00300080780c0500d105442e1107403594820141802031000400034507980603a0300c1012544001360030300284210001401c0580d0b1050101c092010080944401590046000d91324035501d100a00c0d08600d182c4660311740c011100c135806005802c00182601135501c4e080c0e1494000280b400425030564042015104c090350098501c0014003400c0c1c1d1007500034810501904050100700346051041e91074005a01c102c030f0701610301c143ca0451712a203942c01455842d00d600007043c05219081c41d0401203010002c070540b03003603a260343c20689070944038002c0e44159203448002154450714540340154210201c00300b11840c803510082100010031072840e42c030007554090715081c1158095101c0381c501001c0260090a0111750600d040c090100a00c03d5690300e9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 860018336 1250 860017086 860017111
    0xe0a1508090114090615030607050912070f0f03030201050a0b063a0209191a0705010e2e0b0a0302010c02040f0f02090f010c0b040204050402061603030f050703140609 73
    0x205001c04203440540103031598002051189081461b40c0b8022030041d090610070340c8040c1c108603102d984001100e403c1c040030707601c04d8054100136500529000d625008040f03101907110000c503140c21343e000800112030003a80240126119030404400b1181e46803a02074000f20304221602d0200050a000710311003181c09c040301130b000200415a940041d90b0780d020001541c002401c0e03040c6240c1103541e42441420b044000304040c1c40e20003514401c0703408070071001148502103900c0003808000c0d03001c107200d18102420f50782d400e4480c1c01000702040089800300c01e580000811902e15003c036105414103284041d2a04020301e0a58005440c0e4030b03038119080364016180c52203690144032034022240410030001025880c1c011100420004481d415509810014800060008180300c0030043c9e8019406450004072034840740045032440c0f0840800e415002c1d11400c42e502050361651010ba0740c4211100100f02d00e40340d00404406480c00480d14480b00000c0c180454050701c0d02a02864000c0042c1980c3c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 860019586 1250 860018336 860018351
    0x506011a07150914010506030709051b0304110118080307170c1606080a02131a09090c130f0308030a0b010207050d060605030d0e030d0c0f060513030e0a15080901 71
    0x3440c0300c1d11030700044005115120390f90141001004086940ba02c80d20394004d02140c0b900d03038046030703940380e0503c40c070201a070326940800c0401508040c6120301c20035100360303a40d881c546070520491008940b1010360001e0460380003614002009006041030740e0219019603d03100c850303120000c030304500040f0840e248004100840c20414100803c0121850241c2d290440a18019001e0840f0200800a0b412113004000d0050f54030002c10b200801c0c0d94925620360002000c0c0702c0d25049078099040740da50030042c00d105006400c01084041c00ba11038515038008034081d25194500d82c10f44180c8001040c100c414000b080300443d1940001001e0541031040780d04250f5590005881c05013440300a0712000c1d0b44260600c61428140201100404c00307080000e08150340c080820b56030710034207580304104002c410814040100c02811480d050703822910038442c0e400c1c0080300768203c10720360400710301040750082981564185000502d0403520702d030142c0e4000882401c0e0036102104020501c1c10316541c1c5005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 860020836 1250 860019586 860019593
    0x4090e1005040b0403120c050f0c16030b0103120219290a1e0614010f020c06270f06090d050708151f0f03330e0c0d0506011a07 56
    0x241440b850060800070b03680d00341400c0182c24801c044503010003035405c150311a0801c030303000011074501d414503980c1903a441c40340581c800d0a140c000803030103001d01d00700c0d80000284120380310342d01d050f0303030055260844802c440303c0241d98680c52040c060300d0240400841e10081401c0581c210f014010041c940900c584030407800381500d450403141298102d544044888500e1031950390b801e4003c020300340401c40e55080c86c0f41c11130302500084089040014141c03111003c940b080c044105001302c0902001e40323031041441c1c4c01141c0d82501040031900e0460300030b0f00c00783c0e180400070003600a002400841c6014284401c2c02071800ca6600255510701c100d21000a0b082020010b000741e10341c103140d140459081c00d491080107501e803084034007a8011110011b200c003442105048040743d40c4400501003480400e0103030072284401c01c03420351100f8040d10901c170f001c0300c0c141c001c8003102e1044415030b05280342010802140e64046080a03080f944180c005001d94000c00081403050b4213105c94150030402c0310707074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 860022086 1250 860020836 860020841
    0x602071508040221011e110316051c1b0513030b070201020f0f040e1807180b0613030605071704060b060f0a0e1c081204080f0d1a0306010b04090e10 65
    0x51181c102070703554190720544640781703031506c0c55040d0300100705000380ea5a1400e6400c203070101800c3c4c5000703900700c2648615800d00640841e40da01c0c811040e10102d1115103402e5600802205410380071400c0d800d456402c0321403003201111142562100101035843c01e60729a4000c84c00020422410b541d401c11621403240003d101030301440399801449c61340c45040c410800e000b42c802800007170800401c4540d807020503102107901425a44c8550209102e00900b80350017000d05901444107420040000b01e00d80ca140000f0312840c2640e006000612a07610758641c11100e00a0000b00009148080f501060010780b40b604070344d001080003081c8a09020865031100c1c8154048044000031400d00310a690303032401c0c0040e1002d4404402848a068107185880d818103a00c00c2681c0505819071640c0094100560981a10030380280500040d448186044800c0020f00b410607619015000c1d05080391050b14001481d14140c0b1240d5201905151801102001038014140c5440c80c071f018800d9240c4400b111803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 860023336 1250 860022086 860022139
    0x30c05070810020705071a0708070c0f0602011d030307020304120c0302041805060f0c09010819050a020d0e010e28052a030115060e04090501050a0204060906020715080402 75
    0x3006a07913022500e0080d241c2070866000c05d000500c040041340380c0c100124140c8400c030340c1000b0203680d108040c0c6170650360750300c80e904055407003100c000740403030101e0303056210461513141400404800c0d00c801c148070395680000c44035000181d100b008103203d1604500d082c2045e00d44500c4601c03808603181d030b000600340c8490340b40207507d4216601d80c9409005080017001d0700324100c24004c02e060b05081c002c4a00d02d214a01c10a81400503210205600a000030840300d501244807500300b00c02d0805041c4c0c00e02961015010b260403d08100c425020400188118269640301074001d0200c100e01a0300350180b230002030008051801e18554600c0400d2040c401c035480505400540c5901609120362076620000c4891480d02030383c940035680a01c808908807000a9034000d0a08003564203118001401425840758001c029509040500c07540303042c01e030058000d480f035944544007007984400e02281c1d100c0461040c0200c0002c80f4034000525401903c003a40c0103400a4200516031640440c508100305e500d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 860024586 1250 860023336 860023363
    0xf120912090b03100512030702090708060f09090312060307090207050c1309020a090216080c15010e040b06060a261b120c0904090b011415090d030c050708 68
    0x989445080c840e402030000c009040c0d040c00700c6055040c0344400151543c46406220701074090454004c42c0d003042001922200c0d03600a150228924095000404018080d942580150000d0312500114a05140040d2080c40100019802c00c82020f0540302c0040e009004642c06010782e04021480ca481e50004100701c90146004180454038107062000c44100e00d10700454581c640342c003400040c0d0fa003000301c8080390101d030000b6840b0003412103880c00d0f901e04c0c5c50005218213030000b8200302420700420304480903500c480043d44940c4c0d0f15440d0860f0b0107400c582c020020030b020381c001425031901c0c202604069225291900003910500c0034141140398840c2000740c0e4000d400100400d214852074501c91642003240500e01b0310030a9800070100800141c0369235101354006c503585819449551169160541010021400b0f5130360b54280f0002601b400200f9019141d00501110044210360440d00450400b80c8042c1e68200b042d101224161a5090110344070301030b00c0d9001840b05c40402148412641 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 860025836 1250 860024586 860024603
    0xe0f060d02030604050303041e1101080901060b041202150f0403031d0a180f0c0c020d08071703040516060f080402040e010204060513051c0b090309030307060c02010e1c0f1209 77
    0x8c082c2040303ea1304003550341c906030700002141d2040000d451a0b64070701c4019400e0a0403030141c3c882d4003415001d0500ca400c0382e00400d03c0490001a901104400000c2c0309000342c54580484000c204411030301c1c4624113030380304050020442000017912070001811160342c00600789524002410000d50917121940c82000b00c9810b6039643d0446500c0b40c81032261400201390f0400c80d8545851010300603007030340840039100e40c1120701844217004154088450140c0d000c0d4101101c0e0040004580c01900306560940c0c0d01c1c8a0410058800ca4200fa11a81030b5a41901e80c55229100f1036401c580454005004903040382d101d4203034040068003400504007414154642d0b60322034118908000440107554030143c80341c1c1c04100401c0c00f84140f0b60040c4500c54100d516004955186000d451540c89100c0201c0d825210028000c018807100d580081d00701c030035030750003404030465500d040c03a66150391200c9804080d46c8030307a503590f04a01580020f4a49281401d105070810342d030906850032100700210a507203c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 860027086 1250 860025836 860025841
    0xd14010e0313092a1d0301090305030702120702220209090f16140904020307110a080a0e1e0105090a091104030221060a02070f0204051e010f0e0f060d02030604050303 73
    0x281d484c0294100302c105080701c1d0300c00800c0ca030945079042800c0940d02060003074007114400c585041c0d98000c8000701300178000b4030101001c1d00e0014a03a90088840f00c00500511405128002400084510454004201041343d003144101214282e80d501c4034000c0300c40d402c000c001425255411681e1049001c01d90842e03451500c0d00700d5004e2340140020700d40401c01407140a448100240c820340b148464151030050322a074902400392411384594003100681d1094001d800200703d404001001c88034501c0c0e907080206002c030b509100000c46900f0880322004800180b20f0340d1544240080c1000c08401061840b002c0c0c3c0d45e5840300115040240c0a00203658001f60520650602071148485008444c0380b1040b08807400700703034944036040640a28107090b00054030030140800805c0d000320047e0000c10803c400e050503030103407810407012903041040e0747d6041c0000483c3c0a82e000240104d440f41102c40b41990b80b5000c4e51040e0500003811268000c01c04048000562010030140d03114902c994015603990 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 860028336 1250 860027086 860027099
    0x10302010908010b0604290c0c040c03110a0e01050d0e0c090f061c020d120f02010b0a051e130504300909020a090b0d090b010b0304020d14010e0313 65
    0x300a03410408050b81000500c0b010303911408219401c030b07240120310700c0c60075201c0d00691a0207e0880d10590590201240382544074501150380b10300b4000854081014501d8900c1c1a0107070340c0382d41c13080c020f55181842000c00b60303401032a01c640300040c1490240d1400f000075458400311030710340714011a40d6100203420381382d50070084a0700703030020060180441d4074074098001592160800f460110901000900742c81151a4500c0c10410303a580034100c08141684618002d00300e101ea4208040158201185114a130402e541c0c680300b600d00162021000c440107607005125068a80d03801c50300404140d04a6403811000d01c95036000b82c1c031030300c1c2e4443c0d0304195000d10200030484a5058a8061450b40000380d5142c2040c91001103e00d24a800341c1c507904000310580346c08040d0350141c070500c0000107420302d1a041561001c02c00074841d051056440e42c80e611812110b01080f20300940120405d411440480d1030360050b018200d50140000c11000c0c1540d4165056400152a00955000320f03502440740 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 860029586 1250 860028336 860028347
    0x210030906061706011a1207030504030f030608061803160828050403150e0601030c05040c0203030c181306030309090b01020c010f0302180d050303100b13090513150501030201 77
    0x10212a000340c0c1084096003c019102c400c10301c07030044446140c4d4461341c000c1c8440d0b8182c0c1c0d1811a590306451142c0781095000c2d01a0904440c11000681ca00c0c006201040c024070442060380c110000901080e600c05c0d03030624010b0340c502c0e40c0e07440d90301c41440440804400b4440c1c804506125800c41c40e11a88a091701d42d80d24034450303142c03035000c0c2d090421048159a0040681d0116900081c8074600401c4e061040710080c0101100c4140b10b00682c00040140010010f80e0300494406403030401c441c1500b05130407622400300380c40c40424500200715101c0200344003501b031440e01c0801000e01852500325408142158284e9104a021a0000c90100300d2108140b10b01034001d0003e001034034020810200003440300403400901000d0541c00302e8100c4208540c90440c1c580d162010300759494622043c02c050382c0d02c0d0401c940f80c104030710310f088021600300b08980a40d904020020050b901e9941000201d4000e400020000c110b10b150501484021500d03c0701101d4078542c400c00001103d50450000419 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 860030836 1250 860029586 860029589
    0x90618040605101806240206040213060b0d050711010b1e011e11010614010516080f0c0a0203160812071a010b1804060506070213020904020f030f090d0804060c0c021003090606 77
    0x4011b2141a0420b0803540201c0d0b820303802641101c0c00442d809088065000030269038101241c4003001184008800070305a01140c001d00150300c8445001d4900714140b07081e60f2400d410f86800004100e880410340100c1103040a5082c414109101c80000040305840072042c00c03450240020780c500d40e0600c0c2d07aa020b02c80d0030042c20000d800b10b0410704115002818030b01c680a520303075031441c0c00c04a0005028002c010703100101051090b4a9480e0480c0c0609a6148900e0034144d00c280100f000146e400d00d2034400c414119030741c20014000c42000003080d0145600569001c1c1c40ba484800d03c0741d090b509000340018041c00340c540f041905d604040865044104059407014007861401d00300b44036030340d00c0e03070141e92800e80c0c11a11944000f56440d81d480c060b015124044d90054004070303682c103035a02d40c81c000c1c5100e961a182c0358050b541e5840f4249550f070420010750000708190a001c9404180140c1045041e50710741d0400103171602c4030340c0c081101002c8180f03030b041c0040e41c3c3d42c043e282048828041c520 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 860032086 1250 860030836 860030879
    0x50a23040c05060406090e09010f0c050417073c0e01060f08070212070812040c08190b0403030207020f090109060602101a0402130b0315090618040605101806 69
    0x113042905101740607200d0600360040845110110000400240c02504041641100715105005d01150b43e00e024189070001e0003095401c1306840b11942d6080c400040400031221500e101001d6002030740300c1c00000b1040c0b24841d0105c6c2d540d00b1030701d6100301a80750b400401072030b03607141e0030400390b240500c000d0456403840d0404040203880b00600460a80c00566a8000001d00f1320040e51502280740c075050b68841c0003030300710004400c64100403e100d0a582d2000c00c0380c8100c815264488484949076070003c02160000b451180c0000216004c070b442580a0300c3c1c001c0c40502905c070000500310000b00d80303c5007640801045600c400050141036414094942c100038280c0060100c03d54541c00c00c02d40d03210f0340802c280642d038049514074200e08088480030050280c00c4980d40d80f03040440640c00605600d541c401d0180d511100810600d003850f62031005460400178000c2c20603100c80e921240501000ba04003001c119042501140d41c1941022a0340000c90b4008000b41d01e51901e4160642c1000c8405d401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860033336 1250 860032086 860032099
    0x6030b0102010b0f01050901090f080303010f0e01030b13020a0801020c0a1e0c03020402130e190528110c0d02071401020c0d080a0909090818060405060d050a23040c05 73
    0x216240e84074001c0c0131a0380c507024200b09841780c0c900c1004850509540c0d01404080341011030004803c000440194140d070003d0842d0405240c44282e844040002841f00506159140000410444000c82006041403000304508042e5035501004c80c2a80c00038905e9400b190845986441042a03c50358000a45240744100c0305440c1151588500c000e01488003034000c3ea000503200021840000300040a40801c3c06401e28034103201c03811403070002c6000d4600025070710305030109070528000b12a19894800c951101141c0f1112020141c01070154400311490406e014403070684c0740700050006041c0c04000d50b004014a40ca8a18440f02c00c5207001c0086044d90489001c81c0c01c0c40c2c4812030580d48681d00301071070954501501208a400d180070387c2c04400e03050314080310717082080308500040072000f00c0c0208991300340160360308021541c400c03842202e6204004004014030f000a54104c0c581c84400d03120002003441003440000c0c400c60204807000011043d1100300010000d41c075807110058076094400c2e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 860034586 1250 860033336 860033351
    0x301060503030a0804060207020904032c0922060204090b0310090308071b08030703021902010b0f04090609060905060106120506010206011a1e1806122706010f06030b010201 76
    0xc00c0e00d0b880340200007810404c42c44001814000203404654806901914455803450a8240100712a0120300341c410003801c20580000000904e10f001661560020541c0d0050b460381d81c1040303a1100c0550040d05904c2000b00300c0340101d80c291014000400480348041040c01e031800802d41401c0c007208480b4132030b92a11100c400400d0344002e036640d0001841c00c0503541813a051422000b07900041000400c0214004100302006515402404850385404075440032160460401d074240c660304141207821a24040da0301049140541040b4501401400c0019420440e078031070703800765090120241d6050b840741d00100002ca5000400940c0e1100605c030421450520b50300003520341d1010311440c103861000a00352222028040d04407402d000100c8040024011215181c5000e81c10450148a401510704000582424214125040b45440c0306121590303941707144101c003c20f0215054004810940401d41d11181010480c040c0a048890819110709141050080a1380c040290890469040990 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 860035836 1250 860034586 860034589
    0x3009010b01091805090f0706020c040606020a0b0c030711010203011412060106090e060a080a030f1119230a031706060702061813140f0a060f0b090a1d070e03010605 72
    0x342c421043c0d010510104858440d0f4030010f20b85070351501d4810701c2d0302800e400015203a40009045281b14004d90b410311050750344440503030712464a44005040b2400100006805002180041d6842015824505040461050300908a0308260400303110030300d0315080c00d40c85180600e0040102c00b08640100a158103144c00100400c12030302c292081c482d19000420301a90760145060041c262020464584004608005143c0d07085440b8807070225a4410f1440703415440466141645184004011124240c40d9a014a448080c00d45182e503201003002d22101c0e400244180b40685010f0755410400d2124080090300a600c06020390b80314040400204c401a1038610a5a00098046400d4441000c003070000c149056002480160180e180202486160034101c201e00d006101d00c005144055840c5510441121103c3c00b031b00b521214841c80070403e17800500010084c5400180506a14943c0c2e500115030f4600c02c0c14001070081e914804020710594070040c0380d24040c0c000c41c02030100d01e28080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 860037086 1250 860035836 860035859
    0x3301a12030f0a0c0305041a03150a05031b0301110c071409010f05091003061b0305060f0906100e0a03140c0a0b0d02160f0c05011b020a0b3009010b0109 67
    0x311005100101a42e801454003c0e4140d400800300580c034125043c2c4020110180d60f44125600f00b60ad0800528540003070402d41168801d940c0060010078602c200c08616090036207040f0107003030707040d9251030422a031a4030002c080c00f00d81c0e600400404825081c040f50030030341250013504a00420301c0c0f80040181000c1c16401608445066030100000d8807480c03003c0e4035410403030300007030011800c103002183c0041411342c0f1035840c28501d13901000261205010018007850760f5030400e80c0880c82174041219441c013680c0c403c402c24051f0800ca11044c1401000c98118005035005868030000f01415038041c00c81800b9820303401c442201c0c884d12050500050003480d0003074080440c01c1035404502a90700f9443c2d103118a401c0b50300405901103481d114030700008850214011240012000c81c4000030502d0301c4004000100c1c0d0041c4801d8099040c480008029045a46065070402c1208141d0403a941034000310000c0b0b40319001000384a2030075500d0542501c0c09010310b10b0400190010801c408820074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 860038336 1250 860037086 860037097
    0x3041214060a1103012d03050708070f050d0803090312072d08070807050708120615030c03041509020607050a030908030708030a020a0302090a082803301a12030f 71
    0x800c07214024541c91407540a4162072511b200b03100b07210307601001c0305022000842e201142c00c0901103880d03850f00d034841c2e403100f00c00340d02c6503c1c0c1160030500c8a034001120000030310303803011580c07084070300b0640000c002009550044e6810808108007a08d540380190609003a0b0700d103084141c4080700070640303001d40108030a400520f4a4100a860008151414420b0007140c0003140c01c024800d80b5040c1601e0b01c8400904181c62103445520101461041d000b501000c1c0c9104200c1d0b1081642560389039102d0b440c15a03058004259825640e0006c2d07c010f03078030382c00500300c001e02540092103040e4052502803c01101501b0241855105206003c002802c48003100c3d0b00c80d4040d2400342c4c9400110358150003070b0154400141d40b04400000220700108005803040c2004005803101c0341c11b4104104004e1894107111002c0c000990009101d010740c00c1c6126000b0007207801e514407080340e280043d040b90031625114244414000701c150591024a0112140c81083c0b2501d0051898414035140008561085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 860039586 1250 860038336 860038349
    0x10f0203040b0a0b01211413050a080f1303060509060c030907052107030b1009020f0a03090f02040e0c09250f05120f0702010f0c080a090503041214060a110301 70
    0xa800940010364800c812003407001c1c0488800d248804850341b0b808001d4903a10604070b0018024200050031110103901107100250000d02030090a10309441d06400c07540b0124140c20410b0b4100101c0550501408203e4021070240b0000170f03103414a600e0300350402c84090000c882c91035061040c400d00203004079205003140c0c8216041c0f038012200020114030702d042c2d165032200d6400b482c80000144089518030318400c0a904984541c40c0340c0740d15050b01280107182d90f03016080420310060001038043d6101c010700302d002d501460f01c052140d0b4005810759214200880c0d80b03801c80894800c660810008040d00700b5a41012803081e02c1802d00810000d400b80c0c0c03104400c00c00500110030310345000d5401c940c40840c4e102c0b8100214984140b4090902e01c040d90200019840c11031100881c403003921800c940e91001e5900c0d50074945401c660a03000e00154074082d210b0f03000404c00007403d000000c145100c031920580540d0303650038600c4112401c01300b0041805406500701203031501c0313800016088034156000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 860040836 1250 860039586 860039591
    0xc051501141903050d0801050120060c030c090d120e0109150c0f2a150801090b0a180f0501050901080601030303050c1b0f060106050c1c020a05031209010f0203040b0a 73
    0x40d0002d07245081140c5610240c02c0d401550305100600da07201c0159416107a0a0302c503400890185410145503000020507008643c00103004950040d1100c3d0055400c410f40092080c1044503040001d07046400c09182101c50005005664044503040030690794100004d01b8840c560a181149039031043d00f4204041c020010840842c6007080801c5ca503d42542d504000380044a960900780c440d42da41070004c103480741417460351000440000c0c5000c1c08445010a50305c2001c0c6928081145000e08102001940d10800446003c2041c2d0141d2020b600c40c41c040c020f000c202030030b29840d0501200d2041e00840c0c010a442d4006009454000a0079811a5810b20b0b00043c5a640e0011030001340c0034845107940c0301c0f481005107006c03038880011000052050501079a00590382c5400c00c2da40c500c200a0401c00319000b1759500f06644021007d00566004280141c034119417441e41d0315411580801c117654034200c0b0310010f0118511003403091003a2041c0d9054110f04c0c40c01c0a495415461030020f220b403944070f4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 860042086 1250 860040836 860040859
    0x9030412260301030813090b060901034209090c032a061101050c130b0309070308030c0a0207060905010813020d06060b3c0a030605100c05150114 64
    0xa0740302100000d94040507298407540c5924104078039600c2644100081120700303002003241d04080c450100120002411940b411080c6070054014040c1c0501c1c440c1703003d102c43c4408159841d00e10704607840c00c00504210a208210071403141d511071544e0007101c4074a00d0500c60b90006003900c20b4140580e80c11441442100c46000c0c200e0b04401042020b0206a4010740400141c0720340001010241c010300200a0080d80d542c04030060141c0954240410412001002000600b40b0380c001150041c90b1042901d1501d03840307403100f114a038800d403003260103030314001540640c40340d0503c030303d0020300094900004070071302d050002011008054004158104a90440421582e038590b40c1d41155603c100d0500656a0700d400900301e6800c0f0545441164800b205440c100700048464a02104900c0e1044140b18803030f0782ea501400d070400c544210a25030703500c10105440d0380c3c14200c120461490b81d105c6504c101e440c90f1150902064828800c402012040144603010f00c051803440f241da025039101d411131 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 860043336 1250 860042086 860042123
    0xc03030708031803180405060d1212020c0706210207241409010617070302090c03060d05011503140c100f0203040306060b072609042d1409030412 64
    0x362503070412043c103200000e00074a21601150306080f511404031410811a0f8810080c040f00640080000b02a01130394680d00108038002d400c3d188140c0806880142042031400c040c0340750402d1600b03c103000c540304020300848080c000840c8001418401800d41c1403c00680e030768001e500c46940c03041c2c0c0e4100c40790410020101e20740d000248000d0740440302d12403403c0014105000f82124040c095141094a1a00210201c0040c0c070303004032940500340d021140d582c030aa00007503810142a0700e5000642c000c1d030001003442401032803844180b26103602c0c044c81c81c6150040000c988100c088070f0b6504442000012a43e400c20345c9400b510841c1815200505180403c034190f10490300300a080d5032405d000410a0040e00c000303050300b5446030040705005640020000000c030040034803004104001c018295160500c0d8203c0c90a1691520fc1c04400201e521502082a0340005410345107a03500c00c07039144007401380e54604d50800c2c00071000d10700c1c0500b000018070226451140c050088000c0c0e2a80e888003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 860044586 1250 860043336 860043361
    0x40c020d051e0c01020a0801171f180b07051917060d060e011802130203010f0b0702060f0309060708010611070e2203120e1623031605010801080c0303070803 69
    0x1030f40b01c1000031582c4083c2d202000c1c150541c00e000b0580d61039000c004070302d182c0c480020344100744074072028045003002103050500003900410701020b00c2c444000050786c000030f0100d02d600340900000d45031641c44800d402e041d00100d84980361034404110030b1003081130700c441006003401d030401000d5030503d03070b00e00c100e003004406443c00c1c50101c0713003170343c41c058031404d03845030845040003910700c2200c1404800c030395024100c080c2d01007801000d07a24441d150f0200300380007440c40200241e0703102400136400c1c40085a140c44168008403200e61369504500104001c0070f6000d00c007180503021342d09050b0600111a00b400da624401400780d21011003085001c90319105030081c0301e681c0741030f60f481d0102c0340c0455450b0041500c14000103800075542088850f41e0101c5011600c0784841820084ad114aa842c00d00c101103500030b4a20100881c0b0141d0414140e2500c1c2442001d5004c0184c25160825074030f0140014030a400503030000c030351034122120782c1045079000701c02c6410140c5c2005c40f0541365158178040840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 860045836 1250 860044586 860044597
    0x120c1d0d03020f060109060e10080309060c0a02092e08030d02090102010f0c0f080a0c080411060d050c090a120b040b040203150a06090c020a0201090e270a02040c020d051e 75
    0x7114481c000c000540c1c1c030000c0c7c100b4070903214036401c50112503c4c0e04207419405035560040512542041c0f16a09481c1040e84c060107107291900308a07403240401c1d4000c80d581c3c40d13054501441c101902082c1c4d52000c401c490941241280a03060701c140145015078a070b40320b0140d40200182e050300003600040b40da100b5002140c52400c0c5007001c12a41124000281014818103079400c04120a400050420003041c8078049001496481e19001c03560b595481603d4000c40c040260350000303091240c040184041e208042c841c2201c2c2482175a914568020080d0400d6984d0082042400310700207400041c0034005000e80103603014008017401e441d6480002e0130100c6045a0864124505003088095080c54200d0011108102e00812941c541000201d80340c0110720320107804926910801c01c004040364902903405282428040e12952203d80c1446110031002c5a01003241d00c0283c004013036203010303c0b440105014a000030099540307001006040c5010714402c4103a101802048400954101804c940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 860047086 1250 860045836 860045863
    0x20a050c030c0304080f0d021c17090c2d060309010e060c0a0f0e180c0d0603060b0301050c09090c07020d12020a030207050901260309060a120c1d0d0302 67
    0x944481071040c0043d070300c0d0090300c9aa20544205540361907251008500e14100c2820344d40601400c14001160360851b4403280c14400811101141d82d0a07070b1041e40c2c0510b4080e40304080a88820032102007000340f102c25207100c400e1507410420450581d0b018007090300701c0501040c0c1d072131500ca6a8080c900d40c0101101044164140142c10402580e1070809005103100c11640d15600c6280104882c202ca1210709030910036041041507c9100b0310242000505c0d90122101c2c40c800e103401414600b980076140e285d80212002a10b5120000492400f0b004580d484881c1411150501081c0d00005685020107841409070000c0025200c0554545044d1072050940000e65080d9800814074025920340c01c012041d001400b81150201b01071804410305812140020b200010440c0854000300001090410304902c0d4402001091215200e08014102c0e542e0103031104107074045520100400e403001c80221000b0402401c1030100e034000001010035504100b6174110708400d406240a900e00829080700c030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 860048336 1250 860047086 860047093
    0xd081306050c0d0f020f0708090f460501051b011802040507020c0609041815060e0f090a0639200a110102030f0c0304050108131203020a050c 62
    0x464a842d44400034003202a522004100d004080307115401240904461000440c07801c00240012078201400f4000101c0300920940452030018009000340c2e0601c2200008159060f40c00c6000c4071001400d008503680c01508004040e014030100d4241d910f85c2e00840e4144038010485e10721303058401202d00c0c004840c0a00801035880300707041c501c07000c2404901c1244114200000113091a10120307152100075000340001c0e04010f010070030072003d825200f03500400c2d004240803c0010940d031900f0015880c29010b4005105401c0c05041780c82c03600020862050780401100b80310504000044c1107007840c7d00b107a800150141d28620b1054144d444240840c078885070b5921035103d8214680000c45650705945a075045c01180c00b2203003110514540b40d214503030b000000d212002c0344042c107112804000c144140c9251484020b2841c107960000301a410403540041818000e5582240311281c00c084020003c481c800b580380d440100300311128a00c5020160003081d24108140214180c8110400550030b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 860049586 1250 860048336 860048341
    0x1801141c0209040605041a0105160c090504030216120f0812150102070801091a0604090b04030804110109230103020d090b270607080c0d020c06070216080d08130605 72
    0x31019410881440303208500c0d082c000100c9140911400990145885c2107450540c0598010754094000b45185140b90740041c00c0240061080b081c6a00035200c035030b00018007070410b801c0c02071400340004842c1d00c00b070103030640c00d104042012070103190080e030000c3c054221005a2506160710f004400011031144041c0d814807a048800ca000007900540a070f00706c0b00d00301c6e5207020071801d071050141c01910101c00459450f1504028460b003984c40031000d40042003600e400c6e030307502c1c5091004a0b400e0b07001031743c2d44081c40100404001d21046000003441d200c01b1007420300d00b01304810801100c0803200080014420380c2e00d030340a9010380c4c011181001007000b0292043c01c291180c810102d900b490300448807038001c030071040c02c08404c403c007412220060000d81c0d207034142903403400e8000e0150884004148480500c50302c0c180005c2c245d4010b0702015000904100001030b1a214183d9800c0390749a1179000b060002100020388419500100d1401d01d01c562a1201b041019590811000e003449091004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 860050836 1250 860049586 860049637
    0x4140f04051203060a030807060204052805030d050316021507020d02060c0a09030b04240608060f0c09190911090a0b041508060f0d150b0303180114 65
    0x4100e00c0345029105980450a100303010200c50b220884090340c0c800c07510354040c0003080340b520180ca0500c1c400c42c001403400d42c1702c00001e81c80700b41c1c91400c10480c41668188504821880301312400500c03041c1c00425085903c0c02c4054554040180b40145114640071016061442000015002000d1007029032450800100094440303208007100800361103000007003021602c0030300442d40f10001c0c982c0c602c64007606554404a00030000303403068428150300c5903107480030340d14444030712034a0452060014a0364604401310381002e07401401c19018081034010000b000040008a0340016011100300c540341b100c1c030940300c60310031031600310322021031409008800c505403250091540749001c40d2100b074240c1c1e0390003c0c84800e104501600a000005660719a5424041d902d0785811900c01408000c00d0007000c0045520415904419903c09002100810111046102b150410001030300514505290360724001c013211600d15040d41003003061801007400d032102400380ca0b140001202c0c3d00018194820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 860052086 1250 860050836 860050861
    0x9050303060117010302150717220504051005150f0c0309041404051c030209040216060501050a0b07120203210403080609010303080a090501060f0b0d0e011e0b0414 72
    0x940150225902c1003044000d11110f080c003904880c1e00801903400c2d66006010b04c60140c2181c0021a80384241503030102101c44480c02074603039082d68400074120340b00c2c8040b4034a10301c4420342c400f60040740b0780021302c03540d29211034480d000e60320103a614100f000e80d5180c46442c00e12503590030031080e110100e00c5003201c120210052603488822a030910a508880d1410070358090191401050f546c82090058110007004074a500a038036030381001820504104003007001c0e43d01003401c4055a146040080e07003040f940b031003958050f00054420782401c1d424960110350a1107014000b92505106512410703070641b003041100c00719084040101c9424040880f4020714070002d55088002c600464002403403070410244980c100ca80641e100e418680755641040300400000c8400d0310325548511005c204400700c0e1400304010710f01801000c1e903c50350229074500b100c1210100c0300050341020303078420840340c1700c40d0b404441d50442d100004c0c810300e02c100020002c10020000301e5481200902b042346080c1c004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 860053336 1250 860052086 860052091
    0x105090412111002040e06030601120b060a0b0703020102070c060206070c021504051903120302180f03120a111204050634030518010e220f022808060a12020d0609050303 74
    0x83c0501c1b0702039151074003016120707002405031200d0000011029008900c850102d2904002e01030001100c01da01c8903801490780d403207060180c0160b0740004080c1d04012070040008004c15052004c2c00042c104201c009000c0e000000c00648102555421385040c0c4480004442c02440c00516106000f030303482d1071442c107203180c0d84015507141c000781c00d20034801c1d800b034000c40c1c0313403002e81441814004503013600304000440c005074525014850f400e481e21001100c280104400303201511400000da880c60116450311201c0900306003017880134801044252181c40650381401d500310110020008920010f05005400c80703514482e0720809801101071503005030080210a8150464140480c040401511403400c95120741e82c0290300c0700c2e5811100c0d10300b15800c8a154004d074002003403521140c0744c0101a60400099120920401d00300707000c42c811169a6401c1d145200d0506491a1a03d0700000b81e94024500c41c1102003000d60007007804540e82d440c0c200340c1305640642e00b0002c01040d07081c00c6607603030404c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 860054586 1250 860053336 860053349
    0x6130f08030f0301090f0e01090803060a0b0403080706050c070804030f02130e06040b18160501020c15040e04022b14011109060a020316050c0a0e010509041211100204 73
    0x21010200d841040401100c0303514480015261071640707801050340c01410500c084030325169854100003c1d0aa082c0030710984240100d02c032680301d040001c1048050025039001d0701038410104400c0001418900a0760304860b00108005100ea442e420366651500c01c1c000000d20581c00000c01004001584410100c051700a84021500d003058003001400c541c0d2420b82c207900740e480b01c400900015200d6001e03940c050180e07031902c001010f0102c1e01ea4138000e500107802c0184c40241c1c40c24401942c2c10032000d050b00c40f0856081111882c00200a280e0380314a0040307480c4a11800d002409548600380d4100b0301e282c00d00000c41d111040d40c82c0705014440d003160100d5007240140e075402c0640c4014001c800e10080440380e03442c07400194900308071031a841039100c4c4095010034017580505070b0007014040b440030701520140c02d10039100300402501020350f4002c1c40c4142c80d6280184030703903100e080c03a00398420703070048010900340c030358510a580c0b400c050501c00c800c9201e04083c0f15441c08140e0081d00450300c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 860055836 1250 860054586 860054609
    0x1110171008060105010f02100c02100e0c1203070b0112030c0b0c0306010305010f0b04120f08120118020403031b1a1005040605120604150f0f140a0c0207180b0613 71
    0xb04e45004695190f282d110103001070f07001c541c005400751190741c0a002600c0b0640111030a00d04120003042c2a5000120111442c4e0022030b10b00b4200d0a00018034a40d03028600d002d10701d07004a03a0b444480294041c011006101044051102014002c4010019850b00070701c0d401c0d00c520b005a401c014a41c4226041030029007041c0000a903407070681001c1056840e0035135250f08040c10100c0000c17048160880c140e6001c400240c01c5404150444020304100b402588038071455818407543c1c0415140e40449501d40b01d204000c10008241c0c031003503050079500c0d1900311500001183c28041c2d0305030540c0030f200031284085014450320010405036030088820658042c416180c2d607000300003009014a00081c000c2d0030003400500010b00103031001148200d0b0003000a01518000c108000710355107040100c0381244c0d6002e60032508254160300c40d500405d030074002d2221109000d0000d442d400c0c588583c00c0c1150360142c00090607510313a0001020a000070b0000350b21501d8404400030300040300e2045102180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 860057086 1250 860055836 860055839
    0x605041d0f060403140c01020904090302030304021804080a0f0201151401020f0601030503090105210f01240e0f03013e0408030711040908030711061311101710080601 73
    0x440824540e200704d030951101804040600e0b40358085a02038500c042d40c5550801244900303a503544105008103009a00840d07c2c3d15043c03062000d0310300c043c01c20201000d2043d00f003200240700c500807164100349902e0100769200c82c20b8010380c050110703045911503c400c40c00c004203001c0002e000e0250641c46c243d08403500c503514025542c2d141c0300203000140854204100c55090755019200600003813a0681040d403012a160320050380300881590318256200c03000c0010003842e415a2018045020440c090a0301e805100c000508504d4000c0d407100e0040c41ca10341090500e64003035121a40e540a10b164482d519002d107801c11580a00d66414450009100c5034148210915035041d6415a04603c0056141c800036442d2508106c89901c00c469101307803900680d0b40080d0084001d10302491446d120001554424000306049c01001440880d05540701e4000c800407502c03800f00382502400a603103c00c841410141d08030b402c400650714041404a184092214204c1480361444c1100c1050048c0e1b40682d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 860058336 1250 860057086 860057113
    0x1b0501030c0813020d0c060225051c110d0f061107120e030a12120606020c01020d110715120c0e0f09151509030c0f0d0f03030605041d 59
    0x49400261490000321400005545410b200b444400c407240001c00d0a178680440e507440c0040c048568001900603003210f8150031100c526400b60056403c0c405010070744640c10305011032170101071254040030139071503150741ea010700c03802142d0344c040c10101030b05c04203070541541005080b54200400c112400792410940e0b13011845100252036580b41c4c807907240c0004070300c0034000b11201000e9407001a81400340504590015050582200520100d41c81d8400c1410070581c0003001c90b40b442e4008810754100d1b010703060441ea40441c00c442c0703510741410001c0c0306080c0175080b00c2c90103d8903006901580101c0c00458640e640080da20440b448001406201031039959004840440505803403580114000f5401c1c0154507107400481d03070000041080060200c0c10740000b4030001c80d107a410441d2035800141c1c00ca51800c042c0801442a501903405401303800c2140081000d00c085190040c1000341d0251444013058440d801c13900061100a005014107107201030500090003e074134140b04184120128440c0d0f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 860059586 1250 860058336 860058341
    0x2b050d020f1e0a020d210c0210031e1d01020304110901080a1e031815030f0e03041202120303010b0306100c02091906030209160905011e03020d02040e041b050103 71
    0x490b908400030b040072002e03581c28072036002c2e040681240c0e20903a40512802c809080241c40001210940d81c0003003404040c010320110700c407641240c10405090118005002c075400e506180c0340450f02c50000340724a4591114003040140000000d101d500000600003801040c10070980440001c40d500d2505917030b100607070f41d5181e8417208000c00c054000841e43c102401030780c202e500d1b0107001e03050400c0c13111603c1c28503d2003140550402280441610641035102c2c0c0d140c8907400b01929840c078100031801040111555038012407040c07148d810320340080e200440d224043d003220110a075904403912561a541500300c81c1d002140e54601070030300214040303081e42c82180740800040c0c000d03080d0f1190351200b070741d400400510300c07000d042ca01e9103400b40000140c41e1001e029224000e40803490000c3e2030803207001002040c41d64480c1d410094000c00e08900700740501001c2d0405081d9041c010394030b22680d40c400002c0e005980c0800a4010380c1c400300030a04c0764003001650a8240d500500000b5034440e0b005608 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 860060836 1250 860059586 860059633
    0x60409050124020c13020f0d1a03190f05120a0c0317010b121008031602030115060906032703051c020a050405060f07081908060a052b050d020f 63
    0x592001109242608104d0348014501021501c00361400c00071f80070882003548030100300a040c955030f0901c103000d86c4d900405800644003c4001d4481d00c0c0c503103950b00003080e485d01409040c81c007071854000c081150800c444102100400c080580300c3c003e1040180007550004010b0380401d070344414030700d1130914050b0b14070b050302c2e5824851800c000312008805c00c954001007805002c24400e02d4003040c1c1650400c064003001c83c8927110301a42c2071051051600b9503c441c0703410b05103100501000d10025402903404820360703145290004514858010020f03401003130242092085480c003c141c4145175114000705a600c40324a401c14050041d064040120302c102d0301c2c030000195061005120903e440001400b841d102012070505001c225290001d02e80e0000c6400203403a2034904840c40d00b10b400c030300e40ca54421422a02a40d5003403401e40480d40c2d29140464074210408508039a03c10107020221032131000390030000311496104d01c008065959031550310401510710400a0f07000f002c448090703c506 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 860062086 1250 860060836 860060909
    0x10602030f0a11011d071409060109050d08130f0e15030c1003091a06090901090f030e030a1202010c030e19110d14100b0126070207050604090501 64
    0x20310384040d12400f102d6030761403d070380030700555210100000c0c2c1c41003a1072065038094008002c0d006a03881c1010110020444003081c500030b49a0700200a40c60b030300b00d00d00c1c0003140c0741a501b0041106191400403054401c41c4401c410a00c3e4002010480c1d003070054260041e506041c00d82881901e40102044c0c0d60010800019415884441541180d00b404101031a1000b1a4100072800701180e0742e13583c410a603024a40d81c0003851100402105140c20390500d40c00051002c001c00080074603840f41c190351101000081c05000038043d001146031810408802d440b42c100105281c42101c60380c00a000c0d01405242900283c01d24000c001312b17040100d202e001c005a210180900b80c044c91756107101140c000c0c80b07a0b07a0701c23022050711000850341e031200c180c0c0c142c034043c0003504400138018005011a140701c54114100321109003008004c640c841c001580080c00c14030700626035941d90404070b00c1e24415401568115034041400900710343ca5820950603140120300f0100c0340350112203607200301e005011885 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 860063336 1250 860062086 860062117
    0x3140702090730090c1d0103110a0806040f0501061401020a060f1104141306120b09100207052805060f06010c0c1e0e36070f0e01060203 60
    0x842842c042c1c4030400e09510803e01840000c048950040b58500c80840c0840c082904c034141c140401c074011104034040c2c00b6031540c0c8641d44000d60300c0c0000010301400700405005900c145050603a490300c00e08001805104210388032854145492040102c451300210b07035641c204180440d441d42e4400850b440ca00701070b802000480a113441d00030140400041c07403200a079843c150120180321890007080a03028140303085e5640f003125030a00845071404207030403944030310740b503018070409e4142506070420381c1c0c010080c28000d403070b0782c00d00746c0c1000301801070f4a0071188001000f1080100c0461600d00d0150100c3c0d132050b0240c20b2000384c0c0e00522419100401c150010400925000080b80c0c1c43d41d040a41854410040d0303185036550140030449800c92140c10821018016501100c840580080c10155038100150709190721459003c0c400101c0581c4901d40b10b01644810b00c0e4121291201c4a0b110f20841e03d03d566100c030a2640c21005020b84886140303c140082045070001045440b98002142035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 860064586 1250 860063336 860063341
    0x1050613020706090b07050307021209010c030c02010921020f0a060e090417030c0304050118020f0112090602070b0108070801020f12071b1103011a090f06060d0c0c0314070209 77
    0x40d0002540490000c40349150ba91000a01103110669003a228220545a107592810000000703440c00702d900c001c2d13442e94501041650401d036400342400d0581c5d681070600c01241e00139480182c1349040c00e40c00c046251aa00d40a13030060070100b0034040185c600a80740802c44880b076030184986c9003441d02412000c03983e42e0000310b407141081d00e901c5510600904207c0b40070410201c220405510544404443d80310207c107000c00d00100303101d124001d089140e00b25154001590104440d00544d128090510a401c400c1c211701407840d0b040841c5050340891308542d170b905907241c5890028000c2c090032105101d1a80d010682c80c5d01403007100c00c07000c401c401c810b0508003007620801d40810020008410030890342c4c2620b01c00e0792000707441c4076518032910002c4500c042100505007190400400b00c035072806826402c01c0c41c1c0d01d40070800c2d5001866020686da1659895000c01d019220708011821107038541110600119030095551a80340d20035618010001040182c4078111300550038040e6014881101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 860065836 1250 860064586 860064619
    0x120c0207032d0609050d0305011415030702150c34020613081c02010b030a0f1104021603021513110d060b030d0c054e040620010506 58
    0x981c1861600b820103044242c841a0752480305440d00c0000c116440d5201465895155802d0301500307000d01003901140140609010000d1485292104900342e0880d000011500651003806059505010103079444446d05182004003a154002400210036100220741b0f920420000f0514807840c2c4120540c00303140320080e808021087e8845809180e64803210a800200010305004032043d0402da1a0340175081040040c000e400c0d500c2030310340180b20b50440070383c1c41b0024030b03d500355604284d0010003071007010f100c4101040c002c1c0704140c280e81441d03408401c514201513000030200b150300b01d4107080074202e48880030a455032844052004001c82c0f208003406c0094100000c41c180024040c5401258060301203001c80c3c10030074400c4078000042c400d400143c05100d0104a0b10903500841c04440c107080c00e40d00c2144007401d50104101380c00c00409500e804405041c8048139001003000c65140c0d90356943c8101c0a001c0480402c10011220442d00784850710310010f1080503c60b442c040e1094a61041030342 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 860067086 1250 860065836 860065883
    0x1090303031a040501030b0405010614031b0415080f0f120904051005120312010b07121805090f0609070f05161712040b1501021506060d0507120c020703 67
    0x158055841c050090b480d00707580e5101e0041500842c01500e104141d41014200136003518502c0c1c0211003213130300c035a103011000e80340007403055510800e2508002c480100320001034041e01c40000c0d44045041c00d048007040c8402c01168030940504000122443c265500c0041900c0b6400608400610101800703041c6075070400303400980c4e0040034000d0201c0115211000241c0700054480810441e0b0310114020110501d8400b0550150074801812030800f1040c2e519010881d07901802442081400086020f52000118007040a020024620081454503405030f9a000004460079440780d201140130030b001074003c0c0464042c2c030340c0981e40d0502c0c04600c40c24000c40b0310b41101d41240c400000d4007031200102910805007138003d400303021418a0782428103044d00c1049000e0020342202445e1898158030b6a00000c00c41c95008030304018210550300c06000400900400d41c002660900309410405c07c01d078800c2d4a030020341c22100d4100030201c00c468080341d81e5281c50000074100c80e00c0c45107080350041c0c0407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 860068336 1250 860067086 860067101
    0x1e0f020307060f0e0d02160603020306060301050d1518030815010c0b19141e240d020301090c0e100303090e060f061c1d031b03190818010b0109030303 66
    0x8902060701c01c442c1c44d141c0c1c50020340070400001a0010400c500703042c85c162560034010000c41c82e003541103040c6000003070725a01c010300c02c8a11410f00c0f40c11504c200005007200c4083c00310040f200b0440d881c1c01036418001c11025150450010300b4a60008241d180c408030744801110041c0e403000c04403451559858588100544000320700001d540c0e416003945614056866600c2007a0140e0200e41091100302507d092480051000010381c8070030885000d068031100d022811860f20745203005244034000c00c4401c112110065055401c000c007401c18883ca60007060200c0d00100060b85003a035072441300c8001c50303e403800300a001a41c07002007081780030f03081e40c00750380c00ca40001c0014400f5190400001c030b01e61300c512011020740715a03450714502419103219400c0760500f05040c0142c5400341d11803160b101e00c160320f03e5684100c80c0462203c400030040003a01d40d00a100c660b40d02da5a11501c5028116070b0040f11066695154040c022041403418041d11003089010384403e8402400d41c0d0b020b5001c0c0c032a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 860069586 1250 860068336 860068361
    0x50d1b0c021905060a0207031505010b120a060b04150206010608090309010806061612030501090213030201050a03061a0c0613121b060203070903030f0c170c01060e071e0f02030706 79
    0x60102c0441c0940e0340c5002481a14821780080101901d18907110101007698050446414603150041151040072000c82e00030550780c03004200d8550341c4000210081410381c020b05a10400400c01103280c00448000d07101400c002d40840c2c000e40e9a03003004035280002101c01044541041c484008194011000c190b000702e001826141404141d45c03800e03860890310242503600030782c00102c2c1512190107128550240600c0e220640c0380181c0859a8102c0400721b210080c1084400540404c965210707a008202410710303400c107009503c0015003c01e00035000520180e03054014070020480d40c841354142c048805901402c070300c03c0c00401d0b5009440400d000c684c001540769945103801c0009a040c40154810183d44e1a07020440707045060061500322041700b00b000780100c2285c40004500508498141014680c02c000c3da9001c0034154180904600d502c40102034000400340101660080100c01034200885010640c841c402e13103046407206d24440c800000740e042046945e01091058200b8035408a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 860070836 1250 860069586 860069629
    0x5090d1b0206040305240f100b1606060306020a120e1e030c010c020604151505040f0608030309150c1c0f06031b0509070201290d080a050d1b0c02 64
    0x1138907140e2905000b20b410b9003940801c4460201d011003811840c5258029161929a00c0d240c6840490003801e000d960154140a10b030104000c0c2003040c420031102049540300f141441461341d245800e401039001403000c540070420000249000701143c1c03080300c2c0f107261120700600200307084181c1012280703801080400c1c03d020400184518020901036000c400304143c1c002c018078a09810b00c41c802c4041000c1114165082078202668071000c0302403001aa07204807400110f41c003140001c1d600400d940c0c4c3c4800c016000100030420150b9012030f00c0c14500582e1012107a41e40d84081030340ba214800d0051071081640412507901d24218507620103c5050f4509400040c12a01c940f18070811002900040c00d009109541c01e206074101001d07069000003490000380841c0300c9059500c03414468800980d0340c80508030320f846e02d090307072165003401c1c03034a400018245c3d54149924004080d640104040107615080844a90080fa1500604060f0103429035034212030a07a81d60821107074030811240c5414040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 860071942 1106 860070836 860070839
    0x6010605120414030c1f0b011809020f090a03080a030c0318080f120c03070e22020c0c0a0603020a0806030a02062208120406020105090d1b020604 64
    0x5502c403184440f08010314100b24030f14080c00203500320718898180002c250007440c400060144810030b4007030044840304070055517000421b2000740418001c4040404c01c0c5180d0b54040d0010500010213140b81000b0580003408084080d001941c41400000c0c003040f006405100e10140300c1c881c0d080034841d4404102040c6007180c850840035045001c00a846001c032405070040350300791418892031440b00d007080500900250411200d03280405c00c0581c0b038a10782d14001e05040f4080c40d189040022400382461003402039084124443c03003900c40c01a2403200b47d0b5482e210301d000303098250340058076403c10b03c80c000c1030000040d000714081e8108024403000750300d07a04100c81e40e080c0300c0f07060200c56407001c0781c140390088159407004c007107400b4580e00096520100c40007002120795560080c0115100d000c07107140c8400380d0f00b00c0800800c81c0c6010905e00b00400e0283c1d0168280020103150400d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 859892086 860071942 := by
  have h0 := BRFrame.cov_init 859892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 859892086 ≤ n) (h2 : n < 860071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
