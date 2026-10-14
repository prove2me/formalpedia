-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2473
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:06.760814+00:00
-- url     : https://prove2.me/submissions/c833204a-b60a-4453-a436-fd1854a5b952

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 444604316 ≤ n < 444784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 444605566 1250 444604316 444604331
    0x415020c0a030803241e1f030504021c0c0b03090f0304120204050615120c0c0f0601080f01020a0801030f110604030b04020f0a0e07030b190602150f01030c03060f 71
    0x4903440c003050080c501810f0000e03030b64203044025000035100403181d081100c1c041e424480703140e603645030f00710300d904880380307540c441c800426000070460140d03804003504d04513850300040b40644e016080144594000c444983c807103e0030100c07800e605841404006c10f0301240f104280000b06140015680101259046491000d5014026442c3d98002d40200e1418044c520580e4110300d014058103a1003101610080d5205102000417030312400f030640d410110302c078084000703a0100d900009454444180204881c100c1311110300d0152505030a001e40841d5010741c841d541c1024005000700d4034040a00d40d101d00c45c80c1c1c0f85854030b580c11401264101c50812282440000f10750b80c4902610103035000b40c07c3c651003810184100711035011803d6820303014a81d840410440800b035211007540c06043d0781400315a984007400001c40d841032a2136401d84100c03600c140411050781c0042e105031080540d0300c01581685507050b0400ca440300904c0001c00608210300c007840040c4140c3c00000052461800115008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 444606816 1250 444605566 444605569
    0x405030702040905071806180e0604060b04020706050705030411010905031f091a1603110703180906090207020901080f0a14030c07240e0105040512030c060406050f0702060106050415020c 82
    0x10110203100d1b156a40d1a041d0230300204c412140f100d840d241d440e120402c14100d40320b144503151180144050b140d0b9998184440c01d035115a011100840c3d4491010070007850300e07a0020301036801c140c2d0151844000b00c04003816950080103c24151400180204665060010140d034901c1d940c00442500d582c4801c0e4170300c0000d5000302d0003030010140308215140c2d45805d00740e620480400030202030405060264000d40304141c1422502c0858240c80c00c00011203142a641080380310030361100101a140c02c4002880c940558080c3c81c10b10710807640603019980e5880c04ca6903c1040c4030039200783d50014022800000c41003549240300701c44400c16241085681c40c101420180f480d03100b0002418000c1c2041c20b094440803640c881c803103060801032608900400003c05034040c1c4d005440c010f402c01d595090803000304005131010200540100d60141c074062518101500003030322006440055140448c200c1c2e8000718001e4140c3d1002c3d56800d0826150003444c0c104100c883d100e80d4154003800900722040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 444608066 1250 444606816 444606839
    0x10c0507141804060b010f140d0b010c0f08090f0f030d050703020708010e2410031104090203030f1306080103030c0803060d02120106062309090405120310060807030203040503070204090507 83
    0x60f078002c00d40010341d90440d8001400d00d030b98000c100d004000c02244183c1844070804191070140c0440e42000800b840e035000140d4516442045c06094040a40d4002041100764801040c02030300036036580064681e40002e0000b400311008465a05410014031403507014803078005049054080d1040301c8280ea035400500f42181c28440502009404c803544000007401080139a480700141806010168a844240c416560285000081000e22121b402e10309554658002c50155600101541d68446407200320018961284503810b0200320840c8001030194050565607040303d415844501d40d20300c4680e1440703096131005001c1648641c0b1944401c0140e01c42301048007030030071140d000203041070900130041c1010742950300b8844405100b46010801c04c03c440143c51400c1401e0b2600d194a407503500d003850070801c0005101d030350040b012040186210711b00c030480c000c681075a140c1c1803560300c4245084059100c00c8070301a10341e9008104450040c1015072103200034500400580744220740f07882000c41d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 444609316 1250 444608066 444608071
    0x20a0602180d0804060813110d020105220f060807020604110310020703020c180127110708124002090907030605090f0723100906020606010c05071418 66
    0x40e00f0301d003c40c09200b02a006145980c020102d8400500d004103690b4480742c405007040c0d54103004610042200086901410543c4c3c40c040100320884200c0c4660342e4030200702910751090a5940001c81000200203025407c500e0140d880399010740140d5130b8584070b10840840c080002a0103129402400c150040644050401144207902428020204400304600820744a89a0090910500040002a9000c2d40c49010003d1101090b0f081002c103000f0314000f050214508c4540803000107407031041288440c010301ca41c4429901c200003648510300c4008000002c0140c036051307813070607a600800d51125904640142d41c10486c241a002d001640408c448043c00d480c2401303241d00120301841040a1406510f602002403002803021481c0200507664502e4144a81c0012000860740d00c40290003c400301d050248000d0b000b030521102c211402007009015200b0b020040c000c100101e1015840f030348a030f0702e1058000006003082c90a00442071081132207020619840b002c00e11051807105004c014691 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 444610566 1250 444609316 444609323
    0x90309030304060503010603050a140a0b01050909010b030403080a1a1c121e08090c04050601020a0b070207090c0509031005090a020909010213050316140f030f060115020d020a0602180d 81
    0x40d05c9500d0008080c2c190b41002d480e801c3c0e1142007025505c4800546001e10b5072180d5200d10100e1409100e10041c0d03158452a1641c43e0861410760010401c40700110040d4069886a031b01d031081340d070300c00180d44101c448004403000c0000360210b11881d0303032510580083d2010703040c7c49a000b0b0b036142e42d5100f16031584031001c421b01180745200110401140051031501c401304a0608006030701c2d1400c000c640304c6c005160081d11441d070b5a008103080e648200302c5400d0341548006d144c001c034100480e019640342c000c2d02c90382e1559420500a080402d1054096828045014005000e00380c1808a4640a010010060711041c17082e001100c015a0310782c0b042e940100a20340005036a03103500c40441030000d10310380090f4004d030304c0044000380022940d041c3c2022100842d0000c0c2c001d0200354005080e00b178882c180c1c65814860003084801d4140c0104035603040b2140f450555542403031442059071100344500441d130160704134100b03100209103690010034641e089440140c20180c0c0500010348510361288058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 444611816 1250 444610566 444610577
    0x70e041d100b040c020c062a010b03060703060b030f04050111220b03040b010b16240c1e0e2e0e040b0a053109030e04140f09030903030406 61
    0x1031011001c9481101500d220035a010f21600c034246001a41c5d4455810020b0b002d07403c001505a200c0780da030301e80d031100481044c001c1c41c0100341d44038400c0e01070039032458000e21901400f030111710b9040c0241f00710011513180102684c11a0340342c800c01c05000d00010010394065407205130883c1400d00c6038008202800b047d51003608200408030a220140700b50b03802803242c140041003840f01003202610141e0455442070b900a907107003c6100a108481c90400c3c00070095004014041c4c1404000c1c80542582240a03c0420004024960895460500c22a038400c820307004c420295040e84039002d075410360100a88100c00360b082e00c021142c0d41c0c3c1100154040c00855142c060310000358424410006044215000c5c0800140d04002404e01001c0b84900351292112170b10440700d4000341054500c100761101c0410342d0819100e00c100c0080c1007402802c03400900c46000800c914074283c03050041c81c94000c0f500f8801551400d503d21903403a805007826910340310a00501440d0341c0d0403c0244080c00407035894 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 444613066 1250 444611816 444611833
    0x1e04090c060c14062a04080102070305180d02012f070b030f010f03020114090d0b0103050610050d0b04060c0909060605090a06050c120a09030f05030306091806070e041d 74
    0xd60302c00007408400c070700a81000c2c0038000b1140701c10201c0d103241200464000789045d03036403003050a148601c0d44030b40c030b1a500104902e0107058118015000b901e11200d03100941020303d400b0050300740b0043c5402404260b003910840c003c8910401465003808061001c40031106101a42901e009001d80c00815260342c00410864402d40c0f0000144c010441d051005040a041d07a002a000400382d202c8010b4a0340080342c951f01d640c1d03402a18030b0407680c0000715401e0740d584a0900580701d0320308448070001e0442c0c81d40d00080c1802e101aa020786140c12111040c1c0381d486aa0300c40014103201c5501004210f00950b012070003265501c1110010a51a1507640d6070b4043d10781840304003a0941c0c0081c0911905102c10f070070b8540c01046c08003469022000742540ca14910b001075812881c1030708041c204640c056100410080000b00440c02060100d51901c0a40c0d14803c2414103214141c5c810741c45034100318003050046002c3d03c40c42502600003040490022a242ca800034001030340c94044060741d000580 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 444614316 1250 444613066 444613073
    0xd0f020c0a0501150b030615090d050703020a080d12020d11030f0a05100b071b08010e070806060d0206070f020f10021b0103050c040501050306030c0d120306141e04090c060c 76
    0x10031401e04d0b2640180503502e85402c2d02182d15010042c5640d0040390a1a1500303078101110044501e20b22004210100942c1d40d820303e60307558082400200d02a80603c8404282c090000808288402c07150f5a0740501e001c4280b840c0003c2d42250300000d80040e04c85010740c1350003c00c1005107208220800d80007082e03141150005d8240c80d4040d0100b10302ca8200003051080c10064000c40e001c82e5000035103014203010011001804422603030044c440740d482d00000407203980380802c0c0c0808994804080b1041915400100100c5004a00000703501607020082e040024012080e0075002034001071a1068109104011a01e40000c1481400058011487e04c110855500044c604920300c203283c10456864022641c0c40e951040d8000c0c20b05000011000448036038041000240c17505001d4454401d801c514038000a0729042075204901007810100082094142c2c20351000c0065002000000041c0707160111070440c000c405c02040d0099151840e00c004100001c407a00c000305155a5403d602c000c4908 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 444615566 1250 444614316 444614321
    0x16050c2115040201080f27010c0207080705061233030d030b0102100b030a020a08162103030c030b0a0f080d0c050d0509180c030a0c020607140d0f020c0a0501 69
    0x281c40e555086800740030300c00983d030300150b101d030304c09015002c88485482e00c800404071081a9900750300998219070009103d40d80641241c0e41040c459000c40e0465616003610580700c0e0000c0c021260802c90622801c0c50740c1d100700404a030400000304100c0d030160f60000381400c203050102041c6078001c10b04a0003001718182048100502c031590f2504001c0c25041900007501c1f01102c0302141c14031390b1501d4445c12240d17814090400701c690f0003080c003c189070340c03411217070345800106a00039095400d072040007071681003000d80d01201d80c05501c40f0240b20f1580d42c0d010740c01070403210711380c8080513990003580104d612942d0060015009145140042c03515000b400703441d100e0500d442100300081300050380d0000f071001503660640015410040d0311205101d002c50300d943c1a0010024000c4021000d1202442c20300004500400d0151800c1c0000360550105070380d640016a03034100007411a520150020200b403001d842c0e0713051100d60100d40350204904100c2a6040183c042c1d0080c0c1151800d101044401d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 444616816 1250 444615566 444615583
    0x515070806090103110103020909040b040201090b031b1b010f05040c0906080c040e0321060102060f1905190606020601050a0801050705040e060406050d0f030909060b16050c21 77
    0xa00d8090210700d058008103421000c18440181100a400e2403200a42e0003501a28050100a420b40315546002d04104010410643c0e06074040b8281050100d8104400b0049034401e010044042e580180401c07140e8859500c0a20002c0385202520220110030b142801109a0481c3c01030f13001c14103003010b0601003a015410742c003502806281000400c071202020900f03101d501d6080300d00080811144809605612a5088810007550100c800d5101c8503581130000b8050b040a9088910710703038a000400b40502415110700103d60300ea1401101d1070103454220b240d22161500725a880c4400140e0383c281640c0994010b1700c054bc21440050001e030038100720501c000c0c00d0f002d00a01171170400031000317469889180210202888610006603007502c8a8000000400020385441000da0f2582004940038a800c0030880c002600741c1d00020b0003003814050350003607401c1d41840c1d80c5441030500ca400708a0b00550000c840d5030081c900004282c1c0d4405101c500448a01c3e0380814240500f00c81c103e0130b03c2483c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 444618066 1250 444616816 444616831
    0xa030c080303091e070e061503101404110d090311030c0708010b0d0206030c0f0c0303010308091f020601060c02120d05030103051e07050f040f0c020309040b0d1e080c03070515 77
    0x4450320360b04603442c0003039450116850051b42040c00d07203844010801d8928154403c19240c0000020f0107041103803140500c00300c941500f40034542c400070f90704020541c1d204140301201725405102e0401628070550201d00d81911908060b076030514845441030540d0045902410f40d80c005040400c907911082c0240601c0c03190840d010f8204994950016060b800040c1100c86071540115018103600042000c8400701440e00040301e840c2e6a5030315204006074000c1c8546405a60982c500c40042020f5201c14803039003000d074010b0102d40e800d205040707802d40400041a688603071200100d2180ca00b0030b000707a541100455a41a0352981541803142c40d000700f544009648008091940f00d101601041c140c0c2079900444040782c01c8090080080e01401070b080c1c4240846140029900700540c000000b0f0030400001d03141440140e43e480b0800140c004160300c060002e8080e000e419030001130000801c61150301c2076248504100a118006242d41c214040c1103513030b0f40c84040d44401e9404000d441ca0f40c444030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 444619316 1250 444618066 444618103
    0xa1803081803130608060a030f151a18090309041a0a08030a0e04200c0d0809010e06040f030207030b0c0310231e060a030506040c0206070512060a030c08030309 70
    0x14107014410840c0407482504100700c00178003c02d03815940c1c0a0450001c680000d090141030515080400841e43c803a0000f1503078901d003504411068010510304000f42400604124042d0340c0045040c0038510001c241c5002804100400e0b80c143e9220300c500c5481407004400203207002000014000c0403580c07070300102d19950060012528190744502003204501050380c0105a00e2400c26003006022030188184020321400300f40d0818404000642c3d03c4071100a542c1c070040c0762a129082403c0382c81091400415802420024001c5000201c1004000744240304403000280da81d01d400c40e2002007954a800d5130031001082c010a001c1a08003e800303881500703140d4007400025103444c00440701d00c1c4039803401481000d201c101402001c01a84c40d15503805022559209801900100189030881d609031180d4540414542c64901c005603140c130592040d25074a19025003c41e05442400700180540e03405034580b000400003800d01c80c1040b008140c004002c58a81c01d260f0401c0d4240a22014607a99000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 444620566 1250 444619316 444619327
    0x103050919170a11011508030f210f0f0c12040308070c0b01060c050127030507050f01110c0d0c0c090f0225140706090504050a1803081803 61
    0x6008a1400381c11803640d040d000708020369140011082c40c2c410181110742d500071441000460700018114149914040200710240025148428401060260890316801800030103c1188450001c010a00c0100000841d10103180340b4003140720022501c20204c29540ca05002c49801c44042c1e1a41041e001c030b84180c244030302e44140c403580b03040003440030b0100403400c00440c2d580d500132203500042c190030500000c1550b03141c41018142c0d126032502201d441d80f0f012000c242c2c0d0b5801c80c465105082c1c0781d0782e81360603410641e1000ca505400030001900c0c1c0b80121900703445480d409208800e10a0101c0124507241c0c01444030040c2449200e01082091200440c0d010002841d51407032102640c0c00e0500004d0760003001d0b0b26a90003400f0749441c2589410380d0b0314030482c0c407801c20103402c0641d03445408400c0701405405501915079002c1c3c402d24010885a0006200320b18050708920b0344a01d5003400091106002e00000204031248441a40440c0202e414400c1340750786400c1d4903110503900c0c4021031600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 444621816 1250 444620566 444620581
    0x30911090c0d0b0303221a180f010c050106081e06010b0f030c0f0d0501031403030601021015030611090a0b1806091201090b040c0f030f0204020d1e0f0b0a03120e0103021c0506030c010305 82
    0xc11a541ca034422721100c90041c000307038018465900520f411900070003000f52108131566a0307604105508048801d5512120000280014114180c030b1080e05500e040032003101083d80c030354001a108500b482ea090114011300c1248801a0240420704900440d41d5451410030020704014002c801c3c0c19500201300700100d80e600000d10b40029070303450b40d0010f005801b00d20a50140d0742c90382c00060106003060180841c11800d0030140410840c21034000b10365a50f50441d2005a00c02d81206010100001e043d6031000c2c43c00402402110740e01400343c89214920982c0305003100c908040c129906e520000501060140d65045c1001070580110f10214103030460300c4001006d16035400092145800041000790b03400160400d00c0c1c0304e102d046400d240340140c43c02310400f400e940321201d0b940906e082c0c3c869130540741020001e400c8075000007041460000244080b02c0304070803044402e060603004c102d101154034a5010f10028807198400001e003508140d01014144911146514109410001400030b02d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 444623066 1250 444621816 444621847
    0x40e060d08091011011107021207120b07020715111005060f06070501060504050106020d03050a09030c0303020d110d090b0a050c030c03090715030911090c0d0b0303221a 74
    0xba00e800c5440002c00b9120000440e0038540c000f000c1031340c0c3c0d400c241b103480103006140050110b2a1084a141d00c44061200820b0b54801c1c45100303080c0e040c0c140c0110800401c2e8082d10960f0804020702c143c46400d51110165044010700c8088100055955800d03000d50b1441408540c1003080d1b41003023800b040c1000170001c0c1422803079002d076600c601c0c000911002005003d5200301d0080101810912080d81c0d02d40d40607484514030680c903004282804005202d10b030062050901e07a42d41910b85603d0840a600e048000f500010001c0250503a204001da43c4e02e108600034061400c0c00d90004203030154a440c04044480300500b0742005203041100303000b130b100400800d480d0b02000c10308400e5101d43d00c110016280011700d42c00881d10080b150500d1070640c0c1d060700040140e45c040d4401c503034402107520a01c80403000444014101e0390051100d5a50100c554100c812091402022030f41001880000d21b640341c80032074103902c508494041c2c01c001e01807000c2c820490a0074030302c40943c02e280b107001e201101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 444624316 1250 444623066 444623077
    0x1d04080912010e01050a0204030c080f0a080d181101030e19060b03070e0f160e01080601050a030e1507090605030c04060c08040b030907061b0213180f0305040e060d08 73
    0x301c1c503118203000d180311000350f00c900040083d0400034051410105520b100a41c8140400d4a500d42c00d941c0c04110306070000345116540300d10b50004d1405024980f9200c03d180c00504024488940341d0302a40070070b030b48000e100030049002e1581c65000030628000501100c2d44001d400c80c0c9138006aa0900786030181401010015400003004590081d0040000e030915040c0e0308a0400450403500380050300d20341c031001ca80b06100540007055040700c3e24006a5a00c684500b20324002130300d41000900552240000d080b10308864280400d43c0f21041c10b11a041400c0040c24140c001181070070440710580c0901100000e04003818800e1031400e0040064101d403165014900502000b141c503002004802811540244920600c0580702d0070407050090300c44006210302d00019918200c003081210860000e6043c259000380780a140e20307140118000030304400940c182007003403010401e60104170344040c120b06051103030781c0342503480c4e08002d08508c3c0590301400e09406044080c070000d001503100300c202e41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 444625566 1250 444624316 444624319
    0x916050a03020f2106194508070209011703032e0605090a06030c1b0c15120501080c0d03110703020604230409050a0f03050c030a08011d040809 63
    0x50140c8080032802c02500c01c0c1c0003643c00b200c010148108000d0100703a11b4010440283c2908941d000c0070081026030356801c2000d41002c091745a513420b003805410407a0707080d40200644034824404034524201841181005803081d450018101d0114500550500d0141c8081d089125612103003901d5559240002040812403146605030b84d80401c0346119441d24140d0416460300e90b05440303840051254009032036080c01140580c0b404190745000340a2410280e4160b9510007598004880c000c03445004002e040d1411090741c103020031078600810a40586c200143c032194241d5241005501c101c80d0164440e507125000309005120b82d0740c410120012103074061500780441d64100c500325041012a82c4001c4d400b0100207000135104400c458829140440107000190327030b0700c84070280803e0f540030400081094121400701c400090030000f070f2a105c18000d203801410008070001291841d8020200d40c800701c0c54040042000d086e100c1c81608100c40d80704c00884030703401c096580090301d0060400c0710303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 444626816 1250 444625566 444625579
    0x13020a092d120f0b010b0403030206152d040204090204150201051e04030e0d03230f0405010513030f050a060e0307121b0c150f0f0c020d03030209040903080916050a0302 74
    0x2102031180180c103a01119030440c01e0502c49580d146d410120580c003900c800c80142c0254000038415035200980d038030ba245c4c00503165000e409007542e02e00345a0100b15400b08081e07191003021051a84036440513102400300d500300141ea59080510050300c121384000c04c0d0045a060008001c8045020048030784503080e4010345042c2c0b521103150565004c00810341c807640220902c0b011005150b804004040c0e8129000a03100d4140100d08a69102c3c0c0300f450107805110804100c200000c3d44148010141c0038503002c40c41a016869a8032403851b9020308000741c1d000d40c00b001e44402488220720408142107040801180340c502d1598619010842c0c10081f102071045403c1c0c0d05e01080085003e1110042e4000100340c9856114121101e00109140000c1c001600060060340b0250107803400303c4c0300a46903101c0294420702030f03080110b400100301e411010540c0a00c1014001e45850141003900c034070944a030b40807407410369496454940340520010079000c10786020009078640c0078110080e2501622030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 444628066 1250 444626816 444626849
    0x90c080f030405010c0606080607080f130209012c0c1207031e0b0406120510150b0d0e07120b1603020f0403030309060e0d1107060f0509040b13020a092d 67
    0x146c401408a503000c6a450b0080c1020469815070100c40140b0480b125556141c481d20754094400c541500100300a421042003001480070103000d4444040d0100d0b01c2c07814450100b40303801c031a00200429584402d81080204050700000c1086010f10351042c401c1c50200402078800c00003141d840700129006058a56916448450361581d0700502c000d884000202c03440b4940a14105564903000203c40c4041d0785006080c07101617990048610844082300032150800f90701500d40c4000307007911198401a44651030b000598800d081144440140c024000301600d480d08400100f401800c0e880c00d40308261042020104030180c110030755042d20380510b80040d204011345070070780040005545400c401d00c5001a41041c407680720082c0d85030f111002c42a41c01d00e0f43e964405440034803c204800c40407901c00c0c07000c140f103810b0a505c4140301d0000100450840c1080d40300d00e801b287d0207207402000152070040d082c81081194074602c50fa5160a1180e6103041c1c03035030401c4062402d4180981d019240d1500c0c00e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 444629316 1250 444628066 444628073
    0x60f0f0a03061a0405150108180a0c0b030f0a051b0a1206171c09330302191404210506010b0d0b0906033409090c080f030405010c 57
    0x10350005503a1000c000c100740c8018040b48a4244442405103114604200004810410000b42022400c1040e1200707620780d1500728048051840c6645191020b10501e103903000454400e00c8054020020b04281c99a6814040000c02002c400100710480c03c505200603c03598084014034138400c06c00c02480c080c0c0700c4203280001c98150051050f400072040c203040002c104420f080040843c2ca20340001100e43d140b400c02d41e9184d0421080d910203000c660b0a040c10040c880390b42e03001c0c0d45002282ca065910000a8a10103080d0000e01501c19001135404640301c00b11203103104000c983e904071800c01a413440801000c0403014800e6012f0f40d603e01e10500e6006101d0076441c424411403941c001c00f903403615a110503101c00f00d41c1002010180316030038207802c20b0302410003691031401510050003070716100d029860040241c1c015503215030020200c0d49040d91884648800410141a00c0c840c081503c0c051410102e901e542c0b66040003170b40381c224000d4814144000000c5500b250380a0030300c0c5d07001102608 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 444630566 1250 444629316 444629329
    0xb010201150b0318060a060501020d021906020307050706020304030f0206010b0f04031401110a03020715110901030c0e0307060201091a09100b030c0904060903110c030309120106211505060f0f 84
    0x1080c80301031744114428840e5000b10794020105440007030742101d0001000200072030381c0d103681c800024050040c0c4842000860250f4000b141c0c040d03541d04102e8a85105903039458126801110141d0024065000c50003420b85d05001040c0101039030b542650400c885108161150300c2288030041144211000261090a0030b4203d800d500c003140f00c003280c40b00940c40740580a91320110044036800703c4021060002d0709640b2505144002c1c03490110f080038040e00064000300351004010041c03200340c0b807040006903001c11038403015001c154004500192145000710260241c100c04410401c403120030050345850015052005050703151000c40ca00013171002103420100710017105600b20076a04100010300000c2d8101610b0b85200c3d03913a000783e55164010054031891003050700707a4981c10400000c045c0b4508500301c1107901030300340000110f642d503584d0703280ca4102c4841e031900c016504000e890401c0c400040c00c1041e000311100c401784058640b890000303030b46210403020300703114905000042246403503e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 444631816 1250 444630566 444630601
    0x50c0a0509040f200403060c050a12020a0c0c090c0305061c021903020d030306051201110d11040b0403050a050d0e01020d140705100b0f03030f0405040504080f0d0504060b010201150b03 81
    0xa01c100b84c54909110f844099603000d808242c1d0454203140b190307120340d03104034215044514140e03030b05501450340b21020000303544904004000c2045ca014100c0100e41c14018010041000550000d0256150074000d02501d10092007144108110300d42c52102c22050380802d00e0040c3e040758103190a03030040e180d07c2c03001255600041d4015410403c8001099010783c031000542c7d0003250907451854144448a0980c4d400c44105c0a0b40e90007802021130380c295641000c03c0c6030003082651428903444e42c800d06c0071a046540155401da2290505405110081c001880700300494901000040000c10001c0c0d5a401445500e2081118004583e081c00a00c502500c041c0d940c07100640d80c0d40602c07010020301038006054010310440c0c0350a0555001d2400008032407a4030b00c5002c48508007441c08003004002c000007030081c0e46803c0104584001c012a100040c000c458038a540018641041d0600d842141d00b41a041e17415a0f16013100002c04820905d001c40450700018043d560303030f9031801c00305190fa4411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 444633066 1250 444631816 444631841
    0x1905040b0d05010c05070b06032109010201060512030409060b03040b01030201080c0c0607180b0a2c0307060c0303051003020f042c030702040e010506010f030f0209060418050c0a0509040f 82
    0x24013945506481d801802080c0c150b016051b003034800d40303403032040540756610006c03d0004d841e00040030181da03241d844081c0400f0350301400001001642c034000300740743d198800c100580300d4200280a0000555602c91000034256154a280c00c52030250345581c00f01c201800301074140440e900000d91401d220004648a44c1001d1003a00c00d00d0824800c080c2c0742c84903401d041240406848008240c02110f04140c076401002943c4050280120503064594161303e1451162031070040e180303040d29602c00708140001801c0304d40e80c4007490b80d0307207050050031564058014480808010780420150384c44032241c0f14040021640060000c01c0c15519a0700003442c595245854050710100701a85640400a4440240291800d00c4500700c181042d508941040311024041800c0d1040c84600f14401d03481401040c16441d8014a0b000a00000450b0350700540d2141000c49401c0044029503c0c5c28010603410005400343d140c100031035841c0c094458015a426107000302c4d03561035000c1280985400c95030840e80c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 444634316 1250 444633066 444633071
    0x109021509030601060206160e030f070605030f01140109060e011110090b0c030106090b0708040f09051509010f060e0d060903020307021e060405330d0b1905040b0d0501 74
    0x2580300d100300c1950401d0107298441d0240100001d44039001048451084000b484540c662800d01d41c41542e0030f030040383c10650103115260040035818001c01c0400007900c1d0684446449142c16121650603980c1608480c400500c081c800841d00d076007040c4c20700c05551039410a1882200d1801c0101c80c1441751a0001a04e4898403018191510481d88125070030b41c05241038403659a0740d80000c0344948000e20030000003400e1060200f115541c0000a0600c41e48502d82c1d4900d025a900b01105482240e07401103d00c40e82e0b56014069800005c0c6440c1d4500107065130310742c07025032504190007600c203840e00c07a40b0107002040071110400d660381c1b0a629035155001d80304008034013950500035503d4124242c1203008032502041c101c41d6050b49050b0080c8240018035032490241400280102a900c0e0582e5010700d440314000000c045e041d1900c103600d03c888185000703850300510040b9000340d818510116004080c24102e811110f90364807800b50071341d07030166030102c0c40d4101d15011914899600401410075403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 444635566 1250 444634316 444634339
    0x501090e1906060f0f080103022115040c0f0603090b060103240f03030810031e060e0d020a0c060504080c0d0f1211010b0603060904031107180509010e0d0f11010902 72
    0xa4002c0780c80c0f000744031185d480b9903004a41141c1941c41d00f00a000c0654800b03811580d40c4440e0350342d00d110a004004075010307109a0b82900c04070010f071680030368048400d0038403a47d040c405c1c04952607102005102d40c5c0b40900c030714503042c0c448820b5000701410301c604064660340e078400440128480c181d208280260060710030365803141c1c1030303040300304a02049000405480120744030481d242d05550a40760002c82d0042d2000d2030991003514071045550890324503460f200c00c0414104180070850105003141c01404507540c207403801c1f181c0095640c102030700b408000e02c424050341030700180b2111016400d4030b0450302d00700c25007058108188002801401c6107885000500e04560000200c020307240c41c0002400754100300f0081101c54001202e8054004010f40001000310f40f003040c00e403000c2c054001c1680d15403030310b5a20b0142c85205080c0070049160701c0d8024400d030700809110b440464003600000d800c0000c54040000c1907840c02118000800c141551a8000d000c400e5100c0c001c1942d0090101c00c1d80c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 444636816 1250 444635566 444635579
    0x602060108060702010b1008061801030303020a0806030d02120313051e12122802191b03050a0f030e0118060c080f0a110403020603131202070501090e1906 68
    0x12002401075444500600d404107031090b00500071080c0121000702a0201520100b00440700100300404881c0d1001d40c00c512100800c980e9030280e0301960080e50003585e2000040809005d804014100500942c000310a40104a50115044503c1d0070041c40041e03503a116100440b03540210210058000c2c0245101c50704910340300000804640e44c0141911a012100420045c190203034401c1003990440071800100f00d0300011314011072052006884041405011842c0412a00301c240350a0003030884030304004059401c6140e207000d0308030001130032126241c1aa00103141e80100880e40003804400b085241410b070007500880320701d11542008102403242010001c140944001c03090b01e0b01c40c03038061030b1003c103841016050302c42c0d42a6401c810070740e291408203070001c000b02a01e12451240a01012005a03649001907001e000d030700c0440c1065130154200a000030041c050303a6030540d40403060410069030061014000c07034120f1b007841c1d0380550341c18503805900c5004030703141a01d01e0703d410804142c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 444638066 1250 444636816 444636823
    0x206360c030d030621050312090a0b16140304050316020604170715020303090604110d06021308071d0c03040f081603030b120703060209010c0c0b0a0e010e0f1e06040602 74
    0x3c907804e42c1008003250381c483c5644071345480d001707502400305c0d00100503040c01041c207901001e41001c00300c801c6800d1038006ea1a90b8140c0e0009031108000b804007000c401803400d0340b20a40c01051802c44030340c2c510b5420140d66444c3d90348a400c0340003c10640c1c0203240300130356840205490062001c4000b026840c1d1a44104544441c403d01030500c3e00c20700e0007610f040080c0b00005a81c4551104002083c16441e42d03150a0085448814115070102c2801064400039403140081d10000f10ba601c24105201d0031700d590340e03051a4040d00032901c00304028044540608402e04d003280c0190380100c07030f656203840e0b90078072048030550203602400c10880001e0680d4040002841c0c1e21159000c0d540030402881307503a0800410359070421a1310782c0c40d03000403020700c01704015900030300ca04041414020261850f0faa104803c0c1080c1c0e40c400002040c002c01c5640c00150800c000b00c4442600346000c081c040b0920000442480c41010040c0c060740303410944000c08290304aa4a601c603000620302ca48450751200c000390f4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 444639316 1250 444638066 444638069
    0x20a0c0b180706091d0702060708091002161509080a0c060b04110304030806040e030703110319020d080a02070c03390f08070b1e0d1802010206360c030d0306 69
    0x170425100c0c0c5a0f4400e41d4624280306004041642c06400d450326a00822a0724100141c0516641c3c040c01e25014007900f602c1c030042031502c1c100036982311600564106482c02040320f0360300c00c40e01c40c10100c0f08000614001d0844204107030500b0aa28905071500303000004003a0b90741007d40041ca04050704818400a0000e5446a4440d9035560010f50740c51040c002a40c64100c407000b4658003d0000100007802129015500c26004046900b0180c00e00c0d5440d402030025080718015801c900b10398110158001042640580c06450940c40c00c0da0719038907002031740480d01c0013501252001000940d15a8120a0321040b1340d4950b6208506e400c0351001810f100165103d000701d48210614009600324020509104885031680da03513007021070351410100c1e034075401200f000d4000800c000c101c10300322071031150340a0b080e11110700a442d1070b02c503c006031074280e010f44041640595410a00754081030540481d6841c00b243c4504142c1c0100d41c2e070010f01c2d100c908411180e042c020b100d50700e012154540d001d0380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 444640566 1250 444639316 444639329
    0x515131212051303081b1e0c0708030a050304030e04140a15051f05130305120d0c0e0a0320040501080c040501330e0409030e01080a020a0c0b18070609 66
    0xb440d220040c4030684800d0711040200443e000400103000c0328100c05400c4880040505544d290031501e5403503c10a002002212820f6140440e02070f2503010304210080c040c240b0940198900320400c0c00c003800c0d41c000100009d0411a110f802482c168179103030050b4080c8038441aa090003420700940103c081d00311401c1c1c07000e1200030302c02c0009a07407070030f00110803011130000b84107005004da45404a0f0a0340c00305844c04c0c0742a01a42d0004000b6074100100d8040403402125940c850194a00c0c030401e440038001c400081051600d172121a1381d80351074440c0c3c201d9501280152501c1e0403c154511300c0d81c0c1000b6441d504c54501000000c0001c0081485451418110790800050387ca48242d00381c0d03004d40c10700ba00c5480452100c9964000346000f04a40400d03603500340241803810080018083e44d491460440000350421b002580f00e581001000750401f10600083d800e00004039401032000361003120182c001d060843c08141310740e42c00303040c41104407200c005642000c0c0d103d003400360114109100e0344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 444641816 1250 444640566 444640571
    0x82505041e15020304120f14060702011515020d0c0507080a030c1716080703140705100605010905130f020f04030f0b060604030b04020609040f0c020d1106040515131212 74
    0x41111900c080201c5d010703079280007049441d10f81e046c5c559a2075613009031011142048200070340003c8000c04c01016100b49a913600105080451000340e4100c400b082c0e010010b41c0716188100507485d600414005502040f41c030301354880c10454140185003000b154052002ca018007414403013403561000c00c40c42458010b00c0802050410303c1c484d07000d244188040011310000b031300c09603000580990014904140207203031590301c0e4021000c101075180d120303a00c1101c0b564407a200011a400c200d0080034004c050900b8026511454403003c40d0500c0da810b42501d90a070354600c01500b9004659059541818170100d03982c0e162a1680303021081205107140560f003500c2e080e0005049850000c00301c0c0c040c3c84c3d103c40715005a032126800c0c0056034011641403503221303440b1340d00c5a22140e81c82c41100345503902d0b0f50042254604410000e0200e54121b0442041500304030200400300f800003901d40fa04200455262500e43c4d50391828120b007111100c001004800c4014600006a500c000c0d03030740c40a000113404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 444643066 1250 444641816 444641849
    0x20405011202091006051911070b0d0f0509030906070507380301140607030201140a0b0a050f060328230603010905070509060a050301111801082505041e 67
    0x28103841c61054403440c00003820800107d6088400180034100c00220340c00c0041e61901c200072541e09246203074025401c206004201c45106071000d001d03059004410000030001c5040011019490b4440e0102c143d00680001500408208040001c440109042c440410301d5842c42e8011020b920044500c90725000501f185021400c401e000c2164100e80f8bc416108000030146402d000440c5c001802c268155513031101411800c0f038101e84a1407158070480d10000348003c03840e08101c10040c07190040c074042d03104082c0e07103807070b030f0b207540c03049070b030420300114490726500051100e06002c020882c1e00321000301e04003080300c0c0054003169541031141072414a800015a50321003454200c50503100c01803e01c0c0e005640070411410118125504041e0160581d001107807150b01080c02e40f5081340c5001000040062641c040511195025840503000d19100d0040d02b0a54608603244100c071100c4a01c40614860b1035000c540540f040383c4c0200b00c0340880c0400d518000d1307031440c0a29664451000c850840884 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 444644316 1250 444643066 444643081
    0x9050606300115023c07090516050d020904111b0d0509010503070807050c030417060112020915041d06060f0603012d050931021c05070302040501120209 67
    0x3410003c07050300340d0061500c544822200300c00c240f003c48642c1d21102c440e001c03010030078070031000c40d014594600f002455000c0c0340c15803090441b4801080c0224501d054691701c80d031145c1c0300c0e04a4103080c3c0b0118005d0303115000340001500426440310400c000507000644c014008001030024001d031b64212090311a12080c100c000d540c42d00c50101918005081000045c141c18080c11f00701da04a001490304a082c610340b0070000e441d5900ca90000d54008a903e6003c0030824420040300d4050310a402d02912081003a030b0205404040141401c20f401d20001d01840c12520b8541c00050031140d10001024955515004180c4a845c280ca070503000e82e41c0f2008512860030400212812030305035080c28190601a1081c0b05005002c50650445024040300002000c0d0b540b25140343c0104001d540102c4070113042050440700791164810744001c40d4822030b0400141c0c2e2a6000300c900c660751914186803a50721460407a04001e616080254054506400450815a14503041c41c41500c01e903522001078881c0d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 444645566 1250 444644316 444644339
    0x507020a080910030902031e070b0a020a0b0a11070605041a07020d0c02011e0e01090801061212050903010608250e060f0105070606230409020a090506063001 69
    0x180302511240d42000305081d9401d1200d0309400038286864006622600399000a0038003201a0000d00c0460b4048050001d41809000d158000c00b0200c88086c80c4c5800101c0c042e40712030400c5005440000e40340c00092446185402582c481641605800d96803907d6140c40d10080c04151401d6a40031108003148021180c011100e900881c42d68000f01001440c49808882c2010040e0040b03040100741000c0910891161240c00e240801540b03aa4080c8000180010b012411139446501c05030304040d42000048900a501400250003861400d120114140c00340d42030301c5800718840c0c0540c81d107200001e44550110f204030005090f0040c00080c0e682626842c1c0003000d50340a8000301c0004075001c54640d1801d115105140003060526074202102501c401e02125a00d6001d98810b2245070300c0403c0f001c201e050740b0a240d4800310b0f01085003895607000b1807050342c02401080d1916588802150b0103688801c1038035102c250360160000300b4100c20074007016411601d801c600e0010003400001c40c8002d140d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 444646816 1250 444645566 444645583
    0x92d04060c09140d20090a14092a06090310050103050c0a080303160c08070b150a0e13050309120c040e010e120a120e1e010c0210320a050702 62
    0x24004424042640c44e4506a81624003501e4401003841781100a43c0c0c5440803524440d082d210b04c00124840c0c40000380303032403a030001c1000c58560042c0d01e43e48021070144990280c884d0b51002e0580b004810180807419610805008030750500c50a404030f0101519500028140e0340703d041075603030100e0004140402040f0710b0080c40115001440003501940c003400c0150b0800038036103000350084403a61688062a801103c0644644030400204994143c0400540d0003540003644c0502005180907000d407801c43d030150100380c0744003000c1021018440c0c200196045484002c0204101560701500155122818202280500d080078134402c0b00900601c0780f10008120000505040180c0354160b04055202c016000140a0010a0242095854800c034084080518020428150a00d208501c844080c6443c0c0c4402d0381010304070402c503580401c140d0a4400910740210340489540c141105c1c2c210041c984e40610032040030043e8a81200c40f40380341c0034980c801010419034a13140c80480e12130640 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 444648066 1250 444646816 444646819
    0x4030909051311040605060c03040303030606020d0806040914010e010e0c2b06150b07020934230913050106080705030a1814011505092d04060c0914 65
    0x1008410003ca41d81c0c90b00c8440c0f05030020000a02c290301e0702c3c00200c80f030f0030100b020a46980086010b00030540c0500c01c4001520071800203103500c424020000300743c6840141224080c030303114498101003248075021440c02d4100c000c0203000700f41031010990300a0003030700201940703445000c110315002d08001000040302c450007158481a003040038104802d031090048116602541ca00005824004407000d03080601303a414501540c0742100d00410409010150162111006031070000709a12882d1a000c1c000b0700f401000713441e592004d0300056075014640104036100d01d650002480c0850701c0c41e0001c190340d5104481c0321180005207004002154000d0040300c000c683c0390300200701858082da01540d4400280140030410318481040812001001e600c11101402c000656040901c420b000d58540c1038200340f00c07810a01d10700400200c0060340600404400140d640d44081c04050b145c00301d590210125075202118242864620014003880d03858400082080a010038040c803401d809000c234050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 444649316 1250 444648066 444648091
    0x901060f08100b132405012f030d0509070503061e01090207210810081f0908120f090105070f0203190516030c02030c03030306010c141608060403090905 67
    0x50144002c40181840400c861340304214a4005807090b20718014038a00301d05600022903161070034480503070800c1c002e400c018180181c5071a10703100b24002c407600c14040c02d8108940c072410b07030310443ca690941c4a40d2204408082c1010104015058002501021103500b0b8045510aa4401e8081d011400d42c403000042c040c28030500400101203140c014200c182e0042034203000d0007482c14070301c0c01c1100c0c00c005400045442c2d0020024011540320b000380050260740007510000610b80d00400407120002d80690403580e844140c1001d20582600f62542d503071280326800039508004940a08582003218000b800c0e600304000200d816200302c060b442c2c4180c2d5500154200350f07607502c0c28082240d0580740e980c10443c3c20b00894000c0e503c60268010790038020307108e00e0040780c6a030040c1402d04070841c440a000b544104144191a6408003c010416070007441030700180c61100b552a088c0320b035004042d1000f02070020b010031803070801720780300340294400d0f110112029661620101603581c00c683c102003026 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 444650566 1250 444649316 444649333
    0xc04050c0d110d0c0807090f050d03081306050405061b040e010510030e1609060e270f070312030f06050f060703020309090a1b05040b090618100203030901060f08 71
    0x10032603001404481d07145601c02e410003071030700d400204541d180c0300d03150002448402071198460f009034404000d400d00e4031040a5081c289004110b05411b41c040040c20003004a002504422480901c50111070b8000d000f0300c014181410015039a80341641c008900d80c1c2000e1000d486011420b0131101240c40d04450700c0d07803e038601410091008580d27030414052584903410b1b80c0c20307844144212103030004488000810141072110307240c21a80701da044a0040303160081488001070105c2c1078030645005400500d101cec0904501514100a561054030607140703d20030004c4100507138402001482c0b1580c3e41d08100c130741d041c120043d059032010700c034564021480001c0d251950400500070321030180280102c0c0c0c5002d03206000304503029411501c04c15480d070b031041c03500000c1c000b410a03048280c01c075103801400d060401d41c44140c10701c501040144102c0000070b02c0405103600444080412800030b1a44140710045038000c1d4803940304581c20b071400e500e0a500810782e08032002000c1c069030352480007011280f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 444651816 1250 444650566 444650587
    0x20109061e080402010302130f0f0515160302100c020c0f22050606070f0b0105030f0d0203031f0510031a0102010207030c11040e0f01090b06331b030403050c04050c 72
    0x3640043d00603810160204140c008400300001010700416507598030746007892030881d043c805001d80380c010303500c40c800b50103507908184c541105981c1100c100c603012104024040c40e09074907100d181211803c9003803e0584500c1c8464010550078442034082d5000b0741840f000408003c040c016848500c91180703c0c03004003602001e00303940031a40c0300d1005003003146002191340300c8007111003010b4011200c2c50a98001407005040134403d12946000c08002001d0f00140103a001e500c902005201c0781c0e01d22150441c0081c48000194110001c200c09400c0071100c9108105c0200a41400150610b01e01e1201421b190103510500c2120f1580e50140e4038141000120303581c51101011908a4951081d210184080074000900c15003060840d03031340c00081e1000320f0385040103100320004c040d103104d022010031400d0049412950803017292803034a0215040130860004030b07441e025507410b000e2800b1802042d80440329001008000743c81c0100119003018030340008001c25120101c074040d080c80414045040c84 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 444653066 1250 444651816 444651827
    0x305100f06080102040807181401031104200a090608190510030203030313060b0306060a3c03030905040b0d020d14030711090f06060a051b0307050307020109061e 71
    0x8803001000302080503a60340c140282a80c1194201c0202130b048450704105504255104c0203072039480300828003510000c0c0703611519141051201070104010800c00c0c20450b507a40e4040b140311000e58006a84100300f04501c080181c00680110300414690300e0302240d0300b4010401c0510482110904d10404a4140f1100000c0c007000741c501c83c0e03101e607005404130050313909001441c4110f8500c09030b00380d42c1c01c0600702070040d501c0381100c3e0303030007034015400303010a5450b03410200c025a00c0083c0840d0a148030b100440615010014440503403982c2e9000c41400c5a001450b4881224041e07610fa800c01900d800c01c200460b8801015a41d0100c0794610318401401e040880c08412800b07400a00001c205000c0d1450a6602450080790f40d8013904201200625000c41032680008140c1030324081b40c6842c03008600c0310301c18000528203001d40407c04040900c862a104041152a207054a85508a51421550303a07000310a0490109410b0000800d000e44106140c1004061101c4046110010501e05440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 444654316 1250 444653066 444653081
    0x1d0103020d06051002010207210806010809210d060b0313020f03122b0e120912030d0603120f0504090c03020f1602010f0302180f0a08060c0405011404030510 69
    0x1d441d619080001029607408100c000b01c0100b9400260351400d03249021740ca8a4004000c690501d144510310f004981d52240c1d026600880a080030b6407140c540a032000c0c90110712801385042240300704505441080c080d40a40a4100c6216040c4500c0c0c0c3c450014202c036000880c0c68074680141440c040d0098a046440e8051103400a801d8031400300c010f521224140e44a03585000424482c1188143c0410154115070000c1401e55010020324141e401c6858564105045c40c4030300510100700e8168542d80c07015010b2490090381c0880f95580310802c07141001d803045100545001c0c030710b80d01e01028240900303a40e0012000640d1550301d4641001070907401450040110002c05500f417129081c0b501c82c050080c412400e68801c0511846528400144121003940c51082014010310040f2860207955040c407400c0c07242150052002400d0101048628003694040c0c0e0390351040704180700041c1400300043c8141c0d00300b0303a03a141034100d903078030366082c0345c8100d2200a0540e48150012203420309990720100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 444655566 1250 444654316 444654337
    0x510050f09250507030f08010311150c011d061012060207060209100e0306060301060609030605090a0506040c1406120109020310031202033001061101111305101d010302 74
    0x16012190a400340e008020303007062401c089640000c184c0c05058226056402c0c4210300e00d420740c803546c19662148844420001850700841e80101150840d00c8d0010a85000f981140c000b00000072880e5480c40c51004420b0641c00349002d07180200d104204104c200c0003c0d40c0c4180001d404c6208907075240c1d80290301202c01524050742c00d210003401960f07001d00905138600e05030703140c01074881010101400e113000580340074400da00d07022081201d1a081030340001166000907000840707941d0800b44604002d01c03150b004201e4002c280401040103031004988003a40d1010841000c4024104148207451090700d24400c80042814010005501290001d5030700c08240000d884d5915a242e65026284484c81d11441c056000828540c40502c000c0c0341092000034442c03240d407241004201c482a0011042c01480104058500b040d82000e200350040541e11a000d80807070b0390792100400e51040c04070217002d49031160309403920600b1543e200d011a02140450103003d50f4201d55414015002907100d00c0641 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 444656816 1250 444655566 444655591
    0x4021315030c051306060e150f03010905180a02031005042303030a0b04060b1e1c0204150806010801060305070e030a121b240902090a0606030510050f09 67
    0x21040d980050240348025407180c81000c0806007807804205180c40d4071403120450034544070040080c940d10006040340c20000760740e5025044d00c80b98100e88075104d4944808050741d0b0000c00062007003950f42c09a482062b04103449819004200d41c21515040310340c0b001703949540804519854000d2550040d07030428820381e002c908400302d13007010030407007175852000f01150303000403080000c0b803400d07070160446110b000c0f10204007e5041c022444168010320400c800c502c0144e10310188003040d4034bc100e40c2c803002200d002818142e602480d010203503009004000da80705e4450074a4005ca4000c00456004500584070300c0c0c241c1e030070980100d00400005089034208545168060b4030740d101030003a40d05640c01055098103480020030003070018507c41000c2503040c8000620140482d50362a0742d070722025a01c840300ea5000040f291014003170070005001a500c4840d0500380b1080c40d11030b60103041140c405407810f00c41aa00d01005842e148420b10800350058005400c4030f031030740703400322000e9030000503a03511 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 444658066 1250 444656816 444656831
    0x207031104020c0d0c12110307120329030d0c030519142d030c031909060c0c060c081021050d0206041b0311060a021507200f06040213 59
    0x14507291040c9030890351301145a540405082c011202c07102e07280188142003410004003090a026540d2040c0000506002414214030560500c01d400c0740c1141c1038500355000b03060000c030184000660b003601c0098480d12901d4040c49155000e80314003c0040e4041c0c49090405045a00303034400302081d0f901c07000401125220f83c3c1252542a405802c40d00f071910540c80f213555800e00c0100e00e80c1002a198508a0740034410000445540401c0f60b030b00c00c441407142d00c0c07452440c207603081c042c12880500a00d051b041c0b030254906254024501d9902a019401c1880f1000000d48c040d103240205503003e80844041403418060003040c81c501c40358229501458141300e40c0161149801c00f40e002e5140b0006811a40900c014070018a01007840858039011a070010b41c5542d88000704045010801d502900b00442c1c2028007600a01c100001c030480c200d41080b20f0701d01284028031100c0d400c0039110b0491504c1410000c0003c0019000340070741a200d005100e952030ba6000c2101c402c032003619014400b5160100d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 444659316 1250 444658066 444658087
    0x130311061e010e0606090d0c0807180c0e03070515070c0b0912030306060307080c0c0703030206011701060e0106031d01060e06090f0708040308060a24020d02030a020703110402 77
    0x1425109011079000040030200801e41460340c0301040c3e00a080c40030010003405840c0c0e54810841380360441c11180170101600c1450030341000707641360748446002d01600c500010309181c0c02c4500400200402001c01c80c90303e2200d4107403007507684258410b0f0580c0c00110144080d00344500309800020348450760724240034003690340d0000402e85030460030080b200480c079180f082c140a0588000180e403e00514254680f0101051007400300410301c0c010004280d002c2121080158115902c1d80e807810700380c500b040d4690034065510302c8288500860140000182040c0c60742c1803252a094643c12840c0380c44a9103803020840c094091502d041222421024062007000001d118100c010001c0c0e052541072458920100490201c0c024210b0030440c8800b8104a545a44081d140354403913454100550140c0b206000318041c0312064200030201c00250318007001c110748200c0844480a410740c201d0b002075540400803a100e014859800d00036070300990050002a07131500640b0b0480f0006400141010003489 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 444660566 1250 444659316 444659323
    0xc02211201031109060306040f060b0d08030f01170c090114030705030316060b011706013b0901060c05120f0d050c0a030b1504060507080c0601060f0f0e0108130311 72
    0xb441200e00c030052186000301030070b200200d41d41c403013021400f5003030601d0503840b00203c1020f00900102480d503200018200c81d510006400c1c2c00b103422103071b20f60f1240b410f0301807400c0d01102030150407007010b40c0c5404806503040005200079035040180040d03840764a081252000e03859844e1440c2d40c18085c400703000c0b415440800240c00d000402014051154080e800c04004841c2c0400c02c071410020314040301070f800510b50001a030408402c5c83c0c80d0105000b00100c2e030005070800300300300486500700500d02e0844504030128042140040394100140d0360307100c80079105458598002842c0d500001108565420140050310894201109041c6054940d0050f2011908221248610300c040070400c1c80c6482d505100b01618104181c6030a030644d1001c50504545015610a0408002c0001122410071030020f059447c02106c000c1220000c1d619040302a008a400800c840c0c000342400241d04000b40c0b04500900c40410113841724450740d1140f100134201192019815000d20411100c105801441003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 444661816 1250 444660566 444660569
    0xc150403020619020f0403031101060f080d0e09130308090c03011d0c01090b09060714010905010b0108070903110105032a0307030c02150a02070c0801090605070306090c02211201 78
    0x207901030240c40c0b0f880c80784080c0712074035021406001441804048620020b803000c880641e078040c00c050b46005140c4500070b001d01041e4101882201d101800094142e0002039002c8400c1215103940e0500382d400000d02840781c0d01100c00b00d1000d260080301341d01090082d00324a0300311400000342c0b980e80c589440400d003075501da1440d1051741c0251071200c00c1e41c558240403400390a082440e00108407031030005948594012481428071a150020f9202c0400c44400780c50044c004040c8000d02ca07140c117504100e8000d0285580c003a0104422a0000c0c510521804d1500306603a8421000440e0072180001100c1580000b4528050405021141c11012854041c018140041c0c0c030580d40d81e9292280004058540c0804044c09561004215080c80c915000045902822003c001600c40425081c54104610700742d0142116528058014050080c039402c0f1520502c2d0946003409600d035540004002c40b00904290801600407a241079032064580b6140c41d040c00001d0a5203060440c3c40150741400c132001e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 444663066 1250 444661816 444661823
    0x40f051203100302040c1701180b04060f09061a040608180307060507090b070b0a0b030a0b09030301060e0d02100804021f08040501141b1c061409060306060d02060c1504 74
    0xe001c003c02c00c51516002e041c41c034000700d24001226050070042c03c13156035010701481e009000608180902415960701002104030020024060309681c1c03002510b00034414090100064142800400c4c0151119a0042c4100700280180d107414030340720b0704807015880948546684030755000d650f881410704101410303285015900c00152801e001402078295a11580003020946007801450082104404c110b64024440c03000402c2c100c14450010b418120905070042200d2481c00a202c11104004083c60689806896400c14440a84c4c2041000c04840c0340c025480308a00740030b00b0f8a0b0303110f0307080315402c544080c1c11201707048440681c008010740c4400c0000c0c00901e20504000500c4000d0040d4903074030103285a00c1c4011305008184010a500040c00c44c100381c14001001c0d0444c040f286408001c60000700360130003419807203600c3c1404610441024907c03480c8086d0210b40581b90116907039000d0000140310000d0704145a007440403a4200c4080724140340100341122703d000c1555603009128922 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 444664316 1250 444663066 444663091
    0x513020409110102100b210c09010e0109060803070b0412030605040204120618051903111507110f0304090f020702120309090708011401082802091215040f051203 71
    0x8040b000a10345040c0312080a407042c18440303081015181c908402c6050714103054404000048006401e241000461860f904100d8842c000101c54620000f6581130b00c0c1020410304c103d907a1081016501d00a131307540035118010400100b0700090001054451408490501003521036407140020708a070030a41c0420040701b2848940801c002c00da100d01c181d00310494892241c0c01c0e80903240c06035209150001c0c2170450a240c40048245405003005042c0a00c006c01103038072089400b480074588020135103144011400a61650071011408504448902000002541424509926540506500d00c0c03901c02c401e80c06c0140c000561145055614400300c44802140e8071015038003030117000500104224100b00105006004110810003449000b0b40c0902c2e1165244e1107055070b04008402c0c6950842c60b84c01c21003140420141b40d82c0203804be904080f2417251a44c02d0b5500c1d43e649480d09803141c140c01102160001c0d000071080d00c1c040403200e00603011235070012401450400310b68803c1c0d460b40a61304e07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 444665566 1250 444664316 444664343
    0x20d030f0215090709050919050714040e06060108100b130321020a080901110f0703170901200a051002130b190807030b061209100203040309090513020409 68
    0x15010807240201484407141c1d90070b60301e02110195264807150003481c40b81501c5401290301e01700c0800041680030b10030075540510781e5403071030403598410300c900c142e80c10301c40c000546110a1905200c1c2d80c4041c4640c901a2255581c0c400044800f10001010480701554169011806040c01c0c009014403001d040c019500385802d5050905041881e49451021006191161452907501140243d0350365881541140ca4524841c016645103c0100300e2140398421140c039500384200000305030080380e000e00c0001154030071500d40004203200c0c0c1d0b40f5041c0403515151054003010128546280c1890f0038105a8900c2d5540d0b1340c40e0b48c204000c1c5e6400c40307000d0b0b0b0003081385045c1062800a070001040380809452405c070300025100d900c001e080041c001400446400282200c1c0281c10400940c00d00500a0b40d96201c02e01300e00031003540982c0c0320420b520801c0c04da00c3c5115124801c40e800b654254580c4000d0314641404c08001e400010301d0003100d5400103a01c240140c40d240900448540305502004908 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 444666816 1250 444665566 444665597
    0xc0d0206130609140f0d0609030e06070506060103050a0b0d020f0301060b1c0b030106150804061d1b030d02060f04051f091a060609060a112407051e0c0a020d03 70
    0x7800511315948134a56100c02030b0010390780c01e070900801990149000c910380c000390409841da40f07a10103007107812140008141c400c0200110b40b0038410102600c00700300d02d0300d0707400c0d100701240e031000d154a4009800450301c60242c5400c00e46c0501c0000004c2c004202c0d40e0311003504904c160071181c00c02e03190741303012060a00014194000c103400540180d008105442c5003942148034107140400842c18000c884001c0781c10b000301c5401c0035498907440c440342640004080441c683c4d8207a841d038101203c58500d00300e981e0307d240100c1c51143c0300c80640d00030840ba8131100c0340203022003006001100c01b07120700e0040550f149a0076507901010100c1800000f9052a24100300b206104000c0d407000c902031400082001c1c946d6803030207032002c0c1c0805035000e98072144246400d81c0c0071440500074041910030b6407090303101c20007080038107205880032230f0301d041a5403074604041c0c07110f00400045030315621040d01ca400d1008a0300d000390080013903c1c2c1c121113212a46401080045201030000d8001460322110340420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 444668066 1250 444666816 444666839
    0xf0204080a0b01060c080412020f0d080901170f0a02030702160e0708010602011b18030b0f04020a0b0a081906150206041209050310180b0a060305120304050c0d0206130609 75
    0x1880c407410040b170f00f0b15403036031021814420741c00f0301242000400512030540d200d25400c02c00d0b0041c0504120072410090030a880305400c44001e4500140c05020b081d5000c40c10780d4001030043e10590580781c49501c030050618040cad0001010b00045114040720700c505240c0e199040001030625a81c08211703410101401096400305070050b90a684c10403109001072032910701d02c4205813400303180c100c0803003689800005030750540b6480541151740000c2400075004125803054040c510072a46010003540e10300244405015502a503030100c5e8252000400000340c8580e002c650180303d807400103420b621078040d081c80316594010280168812010401007203004030b101d4500310760b90b0901c43e50301850803000941d62a41d04140e610490384036002143c4114105140070034590780090503821350b02c2c0c9600b81c500205020300c8151400d10030031850b400c0c04055802100c3c011600100a0f140803e4038105000b01010480e000b01d8011504000901c1102a0007443c200a86040d6888484c49454201844071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 444669316 1250 444668066 444668069
    0xa0b03070e33090402011e020c040f0b100809010212130606140607080f04080a0326061305250306050301060f121407090f0e100b10050c010f0204080a0b01 68
    0x512616500102c2c492003445481407000a204035105041c5540c0c070320040b210300c000000314800943c040355126424940210f0100500e4070243e070308200420101240764159004170b28601e8019125255814045205110312a0f00003d040b001501d0f005610000386d110050490314a83c1603404003c12400300086401401c0007000716144d10b00c00444190001340551142800003045240c0000e040a41001800c066030020704200041d0b40d070f4106c05041c043d02a10100220300003603011645031080d68210111242c0c02031a010b45203040808010711454020314001e007a2a541401d40c0784528000c0d02c0341424642041c00c48e5030042045031800c03003072600359040b0f5080310055541c07000c001d00c1003040200035440181d0300824980c402c1e500c0300342c04a09180e15a04000c031840e0502c0c00c0c6800600c0b0580048134940e006100300c40050099040d400101e40d0b5000303400368400c401206241245d0302c81c0b0041c00004c2d00d0080001040c41091510b07000720f0307205030f200c4001a000220880d0910018007091030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 444670566 1250 444669316 444669361
    0x120a0c11160501031802091008100509060a0905010b131b0206090615011b030815040b01020a0b1b12090f03070b0703230a0f05010f06170a0b03070e 65
    0x3200c545602000070254042c002c00381015943c1e24500d00d07a06001d120042d00320303005880d100f190b05010f4007884411005004088a500c203900001d12400d81a100f00392113032140a01038038a80e19211a21720140c8080b4006458a640b90086005181d031000c480055184028000144007044901201c00204034030400304195002403041100080b00458541c0e4481c408108548424000381c0059400b551040c0342541d007000310140407000c042c0c00032036081c0a00c02621161410b4600e9004010a45800102e014010380040c81c0c80000101145441c6800021128001204111310910241c940d0000c840d1000e518508009000301100c042c48403204030038040c0301441c50011207441e049841200500840c0c200b55451110040480060341030004000032105d6281090170600c007404081c005001d00c1084040c50040006047c0b07810341000c008030b80403a250b01d20302098140980841981c003c1c06031112949500240b400c680d000d01404010f030258038201240e5080c25000d40c0c00c010094032010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 444671816 1250 444670566 444670573
    0x30a050a110f040302060d1508010203041e0510050a06080a0302031903090c12060603120c1b050102120f0708160b150f040e12160b0c130e0c120a0c11 66
    0xc1d00c80300407038000c69084c4c07601075502955030440030b01c40500800c3d141c4d0740c2c0c1550704e40c03590000c02e036401f0640046019a01444115144044c555583d5034411b02e24240100f8a0744504452140d964140d08015130061043c00c001410365034503415681010401c0307100324016080000d100c49048007145211000d010207290400c0148425a2a42740e00c41060041c001d00254110b0800100003940e0001c4002e5a407080b4160700d5114100c40103080c012000c1c1e82111400100360341032449510240e2480b04031a03059000300300c01480d10313038a40425400040e102403204010020320001c51060030007031001000551100404480c58102128500d801030901010228150146003659807182c189107640304c41181c3c00146d2507028080c0c64a41110084c0c011291203001c150070744240080e074209500c1c46c3c042d5900010b90358501d10650140e11802001c80241c2c4000301c410b01550101c031608079804185241e41600c2c0c140350b084403440c1d86070202c0d030001006840300d0700280b440313911803000b064088000300107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 444673066 1250 444671816 444671827
    0x115030b100e06150403050109140f0f100213120b01061101090507061413031b0501030908030412091d101401020601060302180405040f0b07050703020705060d06080102030a050a11 79
    0x1202c0c00e100c00901181d1207003440803035051656504004807401950720600810043d192880c0c00a01da0310002c85056190262000101082e81c0104040a0410465001d0524007004161038402034102a0003542e8041c1c1152000c01e8203009220088403103409010708107031641c9030001c01402c104081c4c1e46420582d0420700201c0014000141f0481500c0060070842040c2c00c40d450100c4441c09031300210340c0c1c80940041c0000034068110120070341081c0300a40089003585420064054904050005120316020400580811201c054180c11668286030050000e65260007020211002d00c4801160040174001d00c5040f0705e203038241d02d00510110040c0c501412120b030000c0c3d01c5040500c00c810900d600041c02c20344108041c035040d00c2205001b0020410740c10701c1e080c690205a040513040f52642c02500200c0d907003d0280040e2115194958011f060700b500f000d05010560300a512480d0046441d480c0104040000f0700181d1b1050040c401c001a66140200224058078035a40c514500014100304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 444674316 1250 444673066 444673079
    0xb0309010e190b04030305330f0315010e06060f220f0b19180602060924070c0501090804030b040308011502030f07020f04150f080c0a0e0601110115030b10 68
    0x10f1070380c841d41500380000e1981e5400d00c0010140c01901010324401150102030b01424945407070684140b400b41c50300603d824024080c1551011046d01c10346c6581c05850040142140784514290300c2400601101c2c1807031031000400000b40c020040b07920f08001c98801d01900041140400d90083c160310482000f050f00e40151b03c8214860300400381c0d402d80094541101c800d009a580389581040028000041a56024000d403940c4d001c0e20221140d000f91050004c0001c042540c804140e03103030014514450316844415627805281e62000c44195480c0c111000c0450b2245015100650103074844d0a25450686070082601c01d0581040880c59560b15441d4401d6a002050314400c00c02c8a84031980c41c1c81c03500000303640d42c1e0400e2050342d10908020306c06c2780240b40420900101d80145943c0300ca4152901c03041034880480702c4001e50454102038041080c036103080d461030380007401030501403201c6140e0ba09181c203560507104805400ca15140702042040881e0084592004014480700d403140c0c00c00c41c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 444675566 1250 444674316 444674333
    0x50610082b05030414060703021e130501050304110a120b1819081b010606021002040509070c150e0c1504030203060f070203270117100317040b0309010e19 68
    0x70840800c840840010108600c11038420009400c0d8001c0321100d10b04110010080d40c00300c005e501e080b8501440c0e045c110044034042e200701d00b64820880801c1414000119160b0308010801e0314500d44004865810361520001c03071003d0b096100c58190202c0642c2002442d000b0080c1c05e60100c204108000c0503041808222038501465485002e4240741540c1040c410358001c142c80d031414185400ca400d4800001540b00b042119026002e0f00c4041204084810481c012841f940e5001410700340012800c42c4a072000d10180341c4510010811603041c014000100c030f032031340c9d100e011961000003581745c90300e41031107040c42d03d0300001d00d01c0d4600350456010a0715070001034103c082c40d800c0c8002007370041e40240203071810907207076a01e96101d59900f41c4089201044210701e01c0c3c003240d20340743c2c24481620b80403075040c4240007081c130218044c1d1640c1e50304400e088840c00c080b000c4040910000c200032510030000c500498a800c00803404502c4481c041c4c0c1042901c0c21450008090041080001034050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 444676816 1250 444675566 444675643
    0x3030307080118020f0d4110031a0105041805030d0c020c090405070501080c0705031e0f0403060204140f01021005071b030507050d09080709020c030705061008 70
    0x3c05501c00110700c240c100e480a400f607001e042860403008a0142441701d1541c0c012007140240e414840a16100d80f41c10240c055840c0324050103000e840e00b0700d45650780d003a000e115006101300060045c46641c0792030f056501440b907100451228a40401049070780303028000e041c4180e8000c41070248042c110358401d80d0300d119240302e00380f4040d00c86000f1b0403ca4028400c555403403002810140d114606440c15603100d14050207070038003191038100400c954000039001c1da540300c0d40c0103000394a02841c20300100d400c02c0710451842c540748003c2100300090b1011001810046100381400744c5c40b41e00f804410034125256010642c05800c24200003429688d00003000c58001408000007c4d032522003400480d0092840c0000d121403091100044040603405001004030500420581e41c0c241781c046400c94400f4040e20070721045901a520500403051030f58024041080e0700c0d01101c0c80e281442e0f68580c284002102c2000d0b64140e01034013044119000d02c000325031000d5034515040307601c140c441c0201d62182507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 444678066 1250 444676816 444676829
    0x219050a0e010e0a09060b03010305150c04052e030e1009050d32070506060a2702070b01060201060810020306060f03060d0f0605060112050112020118090204060906030506030303070801 81
    0x505800001503201c904d41070001c4e040000c4103110751900c5101d03100d42d40d13100b0300c421100e903c107640c809915a16807010b01d03800b40402694051408d4949410480e400311030210022881b0b40e0f0036000180a4104c26100c40752580e95100407490380112500141041e00419214540300d09040c48080085c002044140104026041c10400d4032100c40080d84101e130120300107030081d4101010305150400340f401030720071a4490411a00c90796102010b00c80780d00e070148580e03007541d2540740c01d5000341c00410b0b0b0714040003102c1e80390060800000b6102c000d0209420392166000d81d40d50b2100f44104031050180b0807090b560908107602d142480e030003060040c420000310038290f9401001188003960781030074600341c1540002d011017041c0c1080c18102c009000036a00140400d099540000c0d2160850260310704075084050703090034421540d001510ba0300d4403041c0c5040d0108070800d001c03036540d00d80d10140010309641d0f079400c00d449040c04c0d0060111f90012f4002403281d8400c2c0104034480b0f0340f2100c0681500c1d0b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 444679316 1250 444678066 444678077
    0x609160f1e0906060302090f0123030603190c0503121809133e130c050c060103050c010f14222706060801030203030703081e04060219050a0e01 63
    0x5071200c04a003410349a080050000d0401400080d9541e00d40c005e000010400c4641c1e6a2144480300192080b0044c1c00b290001001c1504007185c08210b610082c40e0f02c54800390541d0801400d00c0c200c0fa0395508148021100740055060510540c01c0c10000103184804401c400e82c604961020180c0c11521744103000f51003801200f0005080d110404a03030b050742503000749409110303003c2040501c1c0040fa40d07544203441103c10f0b54501c024850003030742c40c0c5400c20b0140c40301c40c41d920540700f890702030f00c902c05003502806020031007d400041c04201031400be41c014805049400c446400040001000720b80703010070000d0744008041d000c044082201d640d0030140c10825041d030b030789a41e80d06660b04294844112600c2180140102c60040100506914a161020402c40e5110001520310040c2030001940540c010300860000034041c1200640115654050103040e500c407400441c5000c008903022100300d900803c44c43c80502d00da1b020707031442100908084e4148004210014490441a01860304201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 444680566 1250 444679316 444679349
    0x120c02030405090c1b0730050303071d03010b090c0c010f060801062607060503100f1203020d0c020108130c0e010308091306030312020c0f0f0609160f 66
    0x140204201c800401c00500441003d14029416040f29009244603484603909008640450309001c1000011303a002c69007058079903031500780b149504a11070311620102c0c940e11b8032120041402000903605c581782d0f56480c000b0480030040000c00410400d074103075000341c0c1070074110955035a8800180b82e0100300207a0180e111a440d0000c0c4e40544114086520708514042000c11041019088002501c94900d40000c9640c100407080020000c052010380340303500038020900044d0b02c038800031900001d800801c4501c1c1078403507054480001c42a84a50300640080110fa0f0070107030140400014211281030410307d00341d440d0000703030103400300818220140b20445c480f4801c0242d8101e09002902e42005212140c0da100c0c0760180440d440702c112107100b84658896558010b0305400b941060707a0f4580d460a10360241888148040d4005c2200703078556008034646e500392480b00b006038110740c690420003080d250070aa0315460811043c50042505101030240500641d44808141c07011160f02c83d041070801d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 444681816 1250 444680566 444680591
    0x2030d080a02130e01150503041e0f05011b09120b04060b0607050a12090f15050a0e031b0405010b0f030c070f0807031812020d0605072609010c0f12 65
    0x2840f41824030841c92145100106444003c428118181c07000c0860380c40b01034070000350665081c04101c80c02402c1c9114000702110368001c0441120500f8410902562924815504c06003511083c0350400390440a0700c94003a07030540c2c008242801044481600d0030100341540325001c88150040001c0d2015407140c4c0c0d051110380302c5404803a211500300c4103880e010301c06442c1c425640d030007046454000807a1040081151205090300000f15881044400003e4010050903900c0340c01c020b80c110280861110010f0b560746092240d4005a03400c0000086403807075070380801080354010f8020300b60a041c144a00790f40012071004603900049051103690300c4407043d141c400e604010703a00004060039030210fa008200754000b14640300900c0e407a17407030051190f140c0700c0820340301060800195100c540c419601c0d02260f030729030165810110600c0c04001c22202c1d04014803420b0006110310500000364002c11050300300038480d10703c078524140b400c00d5030041d042c1d9000344207040c4a00d156114540d6a00080b505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 444683066 1250 444681816 444681821
    0x1215101809021b0606010305010e0103030c05031309020304151b0809010207051509070914060907030f18030e030a111c0f150b01020703031e090914041a0402030d080a 73
    0xd065000c070a55940801410709240c0d14941d2500043c5442402d0115030258028040d0b24141c4484020804a1ba071031034804031420b842d98642614180410070410301c1200c3c2d00080100a01100c9001590343c0c10603103460f00c02400782d185020142e61030482d81e2100001440d1017414000520300d002c10329030b101c4c541401d00901ca440380003061132090107855541e0303604c0c200c1a580309617911401c2e10f4405945030005810381c1c2410505840c0d038810400002e8840c60094620307600074480341b8000600c1c00c44140c80030101e034100814105c02d0b90014888504265111a240d12041000e802604040140d45e85100824142d0700c0000e10030246d002008801c01c410b07402c206441038001020446054050a011003200e03050f05019201c030341020b04603081540009400003c8030f40c940e4582100c084008210400620122808030420218035400140000c00707006d0f042c9882c50908110911f410a0300d041e002280c031038622140e01c1580c0104020150b50701160108440d82039080000107990b803d18074900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 444684316 1250 444683066 444683069
    0xc0b090a03051614062d01080304090903020c0316170f0607051605030a0801170d0e04050604060b040b03071b05030a050313150504170f09041119020312151018 70
    0x14280300c1d21080101c032180c05031422013212050303000b540783c9031904001b10886a10034011070031603074001c00c810800801c03039902034000a0701034410f582c442803074000001d051148454407400c0c0c0020a040c28428502c440000300048848640200740c0e000b440c0a4203502c132280181a40b060260110355901400d103500c01168aaa9100c020b0365503615480101402c60307078083c080c0080703100004040e8903680d000020017610071040b2352124000c0b810b4404c204400b0b424020503a5070170507220302000a400130203001520161280000c1c0c5d540b685460100100610003d0b400b56003012803a46000c0c0100b600801100c2444c546460031660740d0740c42d414440807a0800d001c004101180c50b040061204e41998000c40c000c621074030f000e1541c0303e00d08099010345d02030307070403003003041102044510450f01c1c20360710482d41c20b4110500c02d82440d406400941941c00210f14500140e0000101c03c0040880492400c0d8481c7c0e80d0003045502048a9000c07a034a08a625040028000b00114008600301821034940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 444685566 1250 444684316 444684353
    0x40c020601121a1602011107050604110a05040212180c06070f170a0c0b06010807090e0a0905010905060a0e031c050711010e100605091b0a05070f030c0b090a030516 72
    0x444a00b058504d41c1501d0050150f6030005500e092640e0080300a51400c841000c0c1d044001015140c851340c584036540c0c1e0440c0b40e1941e00c58004d48000405403524000760002048120b00324099180911061091001400281950b5000009111916910541031f1000c0b150415807501c5c0004c0203261070380303003210503043c100700e0848041060300c41c483c0e0001c807200055224070034030b020540381c5070b00543d800324081d90640041a001b51040c00007085142d070190340400c07485404181d01285855850841d844900d0580706030308281c04004000c88203000e92850380402c01c0c0114901040c40000c0c0440c0c0021045501c01582c0710f00204510f41e01c00c0100340b03450003e480081000710164a4456902c1001060a0340e007141001f10005081c980300c640d60348540340c0c0550594945c0c052a140b907046502210030581440424003082c0041601c0d8070300300104511075111594003c545040c00e00411000900c4603000c1e501110070400020f510005a44840c4c15201008248103a9442e000c40c03115282c4c0b0410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 444686816 1250 444685566 444685613
    0x303071403120c1b0705030c01111203070c02270a0c0323092a061e030108030a030f09050703120c08030a0b0f0303041d061305071d040c02060112 64
    0x410140f0644005100c004510040090244d0306220f20313070b840740e42600c01e155242d0051207050701e031540149000c40d0102c4c007040070f440e6a0764605090f140550001e803444000101200e28010441c180b00c07015a0312440e25a40b00c40115100d0790582d00c0c0880020410b402203500c0755403500c0742900039040b101d218804140e1940382c0b0000030400d44e00301c14003180d140c8081c0c0b14141002039841000b058801140b904108030400c0101d0320001d101807684038214a0b60304081a40142400c042d00e0005140030303221510107190307140030000d0001e0684403400110040f00d0300d41950240020030018000c802c480d4000404012040b0040081e1032004101e4009030032031500204001d1641d4031070f44041c0415904490703072506920300c0c0302071564a010f01e00030440b400345004985008a00d407048065405071004154403100c40480035200c0540b0421340d0300340c02050941c034900225001d2006240e0f100e000c1036404010241c0c18400c02507039124107214030044010415001c805000320706010304d000d00e0340101c18 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 444688066 1250 444686816 444686821
    0xe07050d0b03060f04060c11070302060721030209030d080c09090601020c060f0316020706200a0c03080d06050613050f0f0d03020604050705010f12021b070b04140a0302030307140312 80
    0xc49804d680100c1c1d084401d0740c07030004515921405031003540b0051014900a00d00c4508590074040740e0743c0a10025660340c51a0089000d04403004000714112004a50700541c80d41c0304101818500078894422a0a120b00c00040001d0159411f0a441007698100d4548059885650050382032510001049411003000540d00c0500c080304001140a2a18440d0308075400b61200e004984070482402850001556074440c05038110241092150121034501500d114404681d5000f80c0a0b0b540e42c011603401ca00410031440b0140140301d0103004000640310b1074600407c0e110316048402450103000e2180820100940d459142c074420f04000324805444500000c60504010f03580d45001c407402c81d000c0c80f8050000c10154811410f000050180d610703884000401d09010002079008110056400f0003c0541540480300801c1000d00421540a10b203035124203258480302042c0280b1700d154010b1030700d4401080103072000401c17600180d0b0002440a01031403800344060852281d1040c1620b8030072850706 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 444689316 1250 444688066 444688081
    0x5130807050d06152105120a0503180c091003030810080c010c17070b241c11190f091407030c090909150c0c02090408090a081204050109050603010e07050d0b0306 71
    0x3a050080c040d50403142401204c1c07c11005030711540c5146000134800b400420074155000210348081040c2d2029940a040d52001040401c841110880780c4c03102015820010706411420700d030f411040c01c40c0c5c50040207040503582950342da01c1103211410030003c0400032041c055100d00c405039602200120b2544c502d0749007800b030304d200810740701158280745d03070741c00c5402419441c0307941002c615000d0641d02100340e00c40b04e4541c444803080ca00340c40e403440001104a056071003070084604541c6603001d142c002400c000f101c0080c01e04a4215800d030a207883e121040c4800e08080c1180d02c000f6625020640548030041154000d4140c0e00001210341005d01003010071140d030312040902100e130502040b034501b20703071022134074090202006500080d140c800304001c500b030741c7e004182015010706078404140d03403510901d288c280340340e5003541844000320b8140425a40103881a000380380c00c5a00c1411035040120034810034102820010034440001083c04280034190015916004c0c01000d0394601e1500d0304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 444690566 1250 444689316 444689369
    0x3020a200a1409060105120103150902060d050a0c0f02060c090409080a0203030106080a27020f10030b090601051908090111180411031003030c051c05130807050d0615 73
    0xc41e2622074580f24000420951140b8141c0300044003040c403049441e46503490b5074881108074880041301c5901c441085d4090f07143d14000300440000721600050614001e80500200c8815810070b070100a1400c00d40e4044a500003601a00703c103880d134809a4807000000010b00030300b0940c1c0010410440451802d842e0f03038011004e07604031a101d0300e540800359581c01d042022500910803211403032024a0401c210f02d00e411901601c06440031788034040c42d50162000039114600c803003000e80040c1d107600c640704a505060000f02c5c0c01003020300b001800c0c298024040c180c1c0d0301010440208000c00e6034001a0300034401d401403420003074000846655040a01c940c0d0444600402c001030196007010601000d140c074a804881c0b00d00c0c42041088444d60450b681180e880c80000401d075114031a10715800e140c0900010701d191f0040c15621600e5951a141810401031442e540c010310640e004140200440d84039203d42c10315560b4010340010f0028604251503000c0c2c486a00005810890141c022003070300100c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 444691816 1250 444690566 444690599
    0xa1422150611070b2505120309010902010201062301080c1306051206030703080f07020111062502160302010c021801060203180a1409092a09070c03020a200a 69
    0x5440100d44c0380d04c450786040c070035024101c540c00c00201c20415440c04484141c14945e208000b03403080f01c2d02c01110903160f50403c0d1819180b907590b90012104642e0240b26a50091110b62000312284e1404100800f468001c0e01140303060050394400140354009078011542c62500050750008041d4840200400c9074000703000811180d81e9060200e8590300c1c001a480e400c40e98041c144610301000d54042d41c8003034200010403410b011010088501c915010f00050384034050140f1101c100e8455141d05c0714103240e04282c0082590441501d5544160f124000e5006407502801c183c102a0614070200d1000b40b24151542c04148980001103101d83c2c3c044010f200000c0c1400d90741e500e59140a0070800810090f21903210b940c0c3c000d140940c014240180b50607401205101503441081503204a24100c54050f541c50014001c1e282c40000c0602e0b201c070465401281500c0c0c42a503250f010381c2d0295842d0000303075010300901c01c4484c0c02d01e810b4041100c000d50100c009801e402e98039594640403010440c06 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 444693066 1250 444691816 444691847
    0x5030306090f0415020a0c0c0305030c1207080409020a0c0822090e1009020402160c060306090603020928060608101a0a030e2107020a14221506 63
    0x500d404074680030300d010b034450302840c1c01c030b9064503101402d4000180250302480750b0409106a10100030007041ca01e898503401540130750080c565408003c5d403480e00b00800036803005800c41050040c000031a00719001e56041e2110544016920124a501500c808d008004020102840085d20002c10114051110300c9100154104c045080d00c40a501080e0b070910044502c041e80301921280100342e00e40c0240301400d0000e440145415181e0f075072120940c481c6401900c4010590341c0400c12641c0c9880b0f2036004181c803035010441d0509540c00074004038070292151803203428048404480d500c00d07007000d24501203041c50811001da610707100030700005421260380b12240c0050318006520800b00c4207040130610110303181c52030f1042000c1c1c241c0042140480140345486441c6a2282103210135840380ca45144c0d03801210b45a042c5c40c810040c512016401001c800f00c0c9512260f521910388004414520341525101509a894a12404000c003c5107110b1102c09198510000c1d0b0260403403a83d0705040130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 444694316 1250 444693066 444693079
    0xa2a030209211c020c0d0f140303070206090a0c061d04020301060e040e030a0c031b080a0e031c080604481103090607060b04060602100e0105011a03101205030306 71
    0x443d003441c1001540c0000341c001d60030001c0c2c001110b1800c80c0742240c00d9441031452090049003910313001c116140c6861b0800c80c1d54000000d015410b50100981640031450b00d0080c800e5810701e9850f00b2054030103105640a101d50034250241c0d60214110034481264060320864407980e603110010444035503115840e001c0c1d860a080030380c5803040801254203440711900e41c0c0101c01642d2341c0880d80c104229850303112000308194503000041800e8010140c0d04000c0eaa45c031003000700c1768105070030311804018500340101d4110710031803280d4200103481d40c00030040710002813034590541703080c920307803044d00c10002c40d04051404013012161084001c01843c00b40d81c011030021300d2078102034030316a81c0c8035a40c51076a0f00604c810740945c900b0f84c00400da51441483d010907281c03801d101050a85400b0b401c6407001d80c000c506501c0401c0c06034412203003075020900082c009945051103c07410080302130b030300480c564000800503212103002441c400003031000b0519240600c405007051034807500140c1d0640d11604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 444695566 1250 444694316 444694333
    0x190c1718060705071511010509011a061207030f090506010801060e06091e0c07052d0106050d0f0303020c0601030c0317030105030613030e1005040801050a2a03020921 73
    0x14a2010b40d02c8490b4031030000c0103e039040041c9404080401c1e82817004000600d078483d20004020302429000c0c40e2840c001061852080d0824500e40f100036407a603000d42c00c107020841d21a640540d0464210000b401d0015a1202c01c4010030045e203141c02019200303100d03102c0006422081580200200d0710807a034088070541b01c034010400050410760744280070381204510000700c0080c264881d6004600001114640022992018100309024241c0106030400036150361040c0f1000c1566583c202d4000002c118081c105000100d5409070380328003920404038186070780c00b014000d904075078100307401d0421901107683d2840d000002507004d000440d41c01b0715490034481c64000c49015641620b0b402000b5000961720310f4802400020f080c68294108131002e19035031216100e00265511511141e1341c0c0785d0f81d40b400c048509094842c040c0c400049585411441511040301100f408040101020b800b07030b1100b01288114068020340900e507034804454035030740840300311599016550084420030386d01e43e03a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 444696816 1250 444695566 444695569
    0x9060b04170a0201050414040b0d080d0c02010b011b02130501170106060302030f0c03090705061908090606030604020d05070e0a060608070206070915030608010e030a180605190c1718 80
    0xc000c2c0900c02070100d5001e110138004070030b40c0c0c00c5520510201600024200e0421030001c1c10002c204c0074182e541420003e030802d06d140d110b0180d040018402d000a01003606441c000a00c07540d40301a14803040b00d042d9565004650b6450405043c2680450b4103011a584642400e1300c000c0240c03000100329071900e100003030814028002c2e40d101f54450710805115940c2c02682d0049503200404550060007540d5001c65076507900f801401c0500d13540500026031500e240d0028255890251107200503520090421034982e40000c0c4c005e40c00b03541910060b402c1502450f1030340c03810100d500a0000d05031740c0740402072942001d901c036804039195560f074511552981ca40698441e40150781d05400281c1d840d106022032400d0b80f000d0903152809240000c0d9581c1e40d446000c3c03c5071085101012241c100041240071a6440703144010b00501d503540b4060310a1a00502405520030f8100640800388140b5425034410300405011000d0740e0410064400c400e090700c607009403a401000060341c44450b00d0406d01c221f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 444698066 1250 444696816 444696823
    0xc02060d1409120301050d020118180f0e07092703020a301b020d1a061203030a0b04110a020106061e021203040222060306050703020901020c12030409060b0417 70
    0x7440c80143d1145103909000921981c59003d22042c0e042c4900c80c0c1c0316209061890140800811039030032182c180340000b802e05800e1b240b06220841080d0b080075240100000e010803000219030300311800040441c004504403248107094088000c810105413042c905064020558007285440380c642000d46005c0f62140c00807000c003800044095030140180b100700180110b01c0c2d803c80f00d0844025450b803101550015856894086081b1040280c4001c4100c65070340c46c1031398682250b012165200740540303140d001662030100070207000c10152965035a40320394542c2d5200c80f07100e03026080003507500d034201c11003c2c0c00780025100e0b2400003030b1b25451301044010540010400422164050010344000c450002c0507a040a44142c1e4030035140e00a0245e2020a40e21000c81d030503c80f00042441da1660074000100c0b20014100300c00c0c54010400800e040c2c0e40820307141000380c4221a0b444101c3c5203154464614051a005841040c0c6000c401040d48620306001d03004440d2088102100c0d413000c0b1022548 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 444699316 1250 444698066 444698083
    0x7020109050a0e070833010908010e0a0c05060304050a0602071a0a1b0906050d0515030a1b09020f0d09050a0203061008061f03030f02011118031b0906040c0c02060d1409 74
    0x2880c10003541d00135075141b0b0343c1560210720708140b400101c1c1503241c15a00c1c4c00c4a95040442d0303490361003040e0603000c0007000b010703140061008031051421803030240c841c00e884100446c80108410340c00505002040b000d188071104c3c41c2d44902c2d115003189071141004004010a404841c042107203125500c0c4154030030400e6405490a564071581412075001c5100d028100c09040040101d0701c40b8410001d68604009480841d4000da81d0503000b00030100c181001c0100e03d402c40304099004202d50380900c8210b01c21682c17000000c91000031508002d040003030408040c02d800941c540540414498803004c0000ca000c203407010203081d03440b2600c50803030485589034402d4107010004240704040010a00804a66284040900000c1071820a101002e481380d40500035100b2404000250724025040801c490404017081e0b400c40945009468005a44100014041d920030790b1100c00f4800b00174846c0720425001039024100c113840340080040c02c0d0151100300c05054400103500005405864001901d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 444700566 1250 444699316 444699361
    0xf0f090f09030212090112140106080903030f1819060e011d06131b0803030a0b01050319020d0908031006020f030a0c020d0311030712110307030207050607020109050a0e0708 76
    0x42c940113180c490098a8118841c0e170703414000c4080d00c07650042c0c86401500200000d2615941c0c0a40c108103014254180160640700b55500601c20001c1e01e042010640d074011001c207402c0c1c00480c484060322803a00116088402c000080c0b42c00c0741040041507001800385503d190000d0121712030a0540118003400c0484003800d85d8003140104550b050710442c4040180d000b141076800340c030009118091001199400203e1a920000070410b1503250b61040c1d00c3da402c02480c155195081c0141291041a441100c003c086540026884038051851740600100d070707031003544540c5a1038150001c80020005100320405401507803201001e01c0004802c130344e0340055a45914805a026400703100101b85000c008030213010a012201100501c10405040458450000c105504901d07030b90051200d051243c01403410740c0103000c0c290010781c01203400b205590040c1c4002d501d5840500049a400c1d2240c1d010303540000320014049030000440820900c20b8046854030000c90b20345c1c00104011160209650 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 444701816 1250 444700566 444700573
    0x207030204050a141923060103050a0f09062003040f0b04020319060207111935210f04090209010201090602180909070b040b0a090f0f090f090302 64
    0x14401840c0c00d42c0101c3d0444100000080c0c01d441e80c000c2550044404e43c1d048128841c0d0f105a1101d05049010300594021401e42c940d0040100300500344c40328402400352410f1648030000500d913420203610084292544100c00d004105640c2003540084c180c0000414000d04545152550040200103d82c022603120f2005042c054050300e40048011020300126410301600c40000c0220788003e40709428640039420060380e50003203143c04510030b12142d08c000e01036500000096901050080500d044030740c2c10040c60741e460400c1c41404401219024404580f00d407460f010310131020005000b4001a98500207800c2e05569154591528002d20360809850b0748204001c3c0306855036500907042149041c00003091050560340d40d41c0607a0004a580d82c4000d5040005050754900048020340040f6001c0107007802d941001e0443d0348a1180b030040881b4a136001421201252040041c8001003030302810b40401c16444204504da40d488170311038400e409080c01082c07008001d0600c200c801c1598540c005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 444703066 1250 444701816 444701819
    0x7021905030d050d0209060a12290d0302011d030304120c020a030206071a040501020a0f140a080403020f03220611060a0c0504120c0602010e07060c0f020a0803130311060702010207 79
    0x102c4140d84040e03e04c0c41101d40078006c22400340c403044042c00b034082150b110001001080344800741142c0303100e0203002e0100c1b6540e0504841ba80151000500c5801c00d4880e2640b01e8030600307083e409000c071034014541c0709944c40b40c2c2d03144020001c00994082c62003610806510712000a08942d40418610040c2d880780c0c0484c0200300500e01030004024642c0304000500119401d50803520b840041160252030301d940009141003410b501000c408443c480c43c1c244a48105c11540c030344203441c045d1402801c240300043e00820140b5000300007590f88a83c07071000710b90f5074001c43c010a0503800c6906001c05c00304021a840400c401c5d000348807690044030001c0c01400603a8400040d10040d001c00384160050101c200004a01d0507418502540c0d91303030203074985450b070070b00e40794009003116440c0400d144a41c00582040c40314640c400e9400850310340208800c0c41e410030300e000240d07101c0f1040d40442010b01c00080c3c0c913000e4110700c207100400c89020b284c41500c0c03a800c4506001c80752140110003801038004140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 444704316 1250 444703066 444703093
    0x715021803060c030a0c111b03010b04060311060a051b1c0f171005030703030c05070e0402060d0c0e091f0611070e09010204030c080a06051006050d0b030a0203120702190503 76
    0x40301035011b219282100616240b40c1d480d07800c00c04915404c003401e180b5007019646c141024000c1c0c40c086182500c0c02c00103680740d84c4031459100e07040c5203141c1c4682d00c0050381d01081803042c000e46043c4082c560322400c803a21518000d41d0b0354044444113800d01c601c0c0c0341d8003080c0140600915464401140c4424190045a2401014144d00101001012001204085040c0d2800c110000c0910b00c80d44642d5a81480360a16500e80000355102c00d58143d003e00800c001a15580b041c2c4882c49030007000451050035103507044ea2400000c0046941000031b400400041c2885038075080082100b124008290503180d020466221300c440082d41c003a903200c05810000c40f070341e992802d58030010300c1000608054403580d910740414845c6d400461150b0007080c8003010b008084c400c05801485a2842071030007458844050100c3c050320200c44003041d5207004110b201e403420300c81200c4469000301503921203048400240b1240d0450803041c1c0c054405580140d000d0325061003000d041d14070040c01051309800c00365 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 444705566 1250 444704316 444704321
    0x509010603080708090406080d0c05010605060304020d020d2d02131401061b14010b0316030b0402010c1a07050a1106090c0f030a080406030b010e191a0715021803060c030a 75
    0x170b21540c000f995400b00041c28030302842200074244150360380a80601e003a0406900350382c5c66030401445083c00704188001a038510f003908441c07a1b4180d0b081e45001080f0300788507201c08038540e182031b62248141c038004c00803c4401d12f2454524401c90703046221004c80c41c0f81d4411075031a400c50740840c000325001401010b010340b101070020902d0784060b00d1000079554500043c9a00040ca00310181c4d19682080114603040c01082c00c8846448100842945507407107480e40362034080d10281c140900c40300e1070b40910025880c02e40750b4042d0106c4000007820404c10061031030b0702480a8a0004580082020100340301140144c01000c610000700003120700b040070400100301c1a0030700e55042c80342004100000740c900b0050702c01800e03d5100050001d01c1c003800034000d07144802d03507a403103190f00000c590641d81c0e00c01141c030203482036100c03003240b04501c03284501828401d500000d071511904296145060001da0000c10b03102d003610200510b034010030307002d140e0341c0d10342a95501c1c2c0e100028000180407802a5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 444706816 1250 444705566 444705577
    0x40f30060b03030903010905010207120c080403060c030b1c0606092904090b0709060f141b0304050a0803091201050f010303080402010323061008060604172e0509010603080708 77
    0xb415203107800c0d200d03000a030845d200346000312040d940225001c000d014007400d01d0368807590302e070900111030081c503901c4007110f1050740802003d0594542441d070855110754002041c0171409440200d81003109820000500e840340c108441c618104600401d449100d0700515845208014855810114aa0080031581002d100d42d940081d0744a4041c1d0102d60280c103082c1c080c040310b031984c103006424201e00810002070070f6000b20521648214120305061207608691030b41d105441c40355410325804031003508510940e40841d500c61361003c80800c182001100078814007108030369138900020500c0700c0382c1c282ca10468031003400f2070761000100301203070082448a07030040c4140740010f200a0903603141115201c40503d02c00c0c05c810b51408105e0642030003441003a0358001c40c2840c400d5858583d0015120748210f00400d0741000700342e030b550544030b0020489528806214555555030326480c1400d542121100c514050310a802c08011a003408010f2144c2d40549401025441c9458815220822258001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 444708066 1250 444706816 444706819
    0x6080c0310020c031e070327030b0601361703070b0705040305160519080613020a08120304020a0608010e0406050402120607110c010e13050912040f30060b 68
    0x4121468400079801800c00c2005c00003100c0700c2d1510701038140148040b4140c1c240f52a414180c0020b010600c1c1584d881b6011254400280040380c2e8940f001222a14941d6140d56104050b40c40d01019000d0803100121280304142810500243d0322481040e01d4a104000003049800070804040401c20106065910034103600b00246000d50b69607a00c3e24040b4607141c0000300c2030307901c40c042c40b01d854190b20320342d100424608031840107420704540b00e8454201518451000300765040100c00c644a4919020050400c1030580d60842c00b42e0ba900343c0240e0003140c0880c828504d103000400c0c024052082c0354141c0340183c0d40e60300c140d6a680d403100001d0034064002c2e40d1020003000000140001000314511542d0582d03600700c041900350514902d450204148281403040d2001088210340f220001c0c00c1150700c0350080802e00d03440781d444040c2032084184104808040014011464041c030380340d12402c940988044070000f0f442c4184d03422a010369000015a1580304ac10b4036808103e06802494141d0b80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 444709316 1250 444708066 444708073
    0xd0b0a12030302040914160503150d0b070806010c030819090b1e09030406080a0f02090a030309050316080d0309080c01090b0108010c0e091f0b12040606080c0310020c 73
    0x3150035118440c403603990022000203800203000d1054460700e009070192181c0c10344440302c1e03600701225100711024a0303241460800c2400320000d0140c00540004c210a030340054040a403081250500124480f0212003500c04901c0c510049410f95124004844690b074241e540c0c80f01c3c5032200d01e615941d054564401618617515140200701040203c6403007030041c0680f0341e10700d400020090031a010f02200030824034442c2c0060008200c2541c001c40020b40c014540c001c006004103040c0c0440c002401062031094000140782d00c0442055088990704040d11001c40448140d40680c0c10860180c03103090003640d0f295080010841100e41c02500010121481503064038206009200c4260860f108042c0950308007084e0380040080d10801e00c1441035032912860102618141c1e0408503a00460280080d0020740e10407039000115850482e0003805844c03400c48041e42c881c0c4403012011011001e0b2000d507010351503c2c20000f03660000285545a0a030090060015200300c480d10000a40003400050020702 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 444710566 1250 444709316 444709319
    0xc03041a040f0b1b0309181806010807180b0d0201230307021b040207080322021503090105070201050613110f030112030f0201050c070b0702010912030501081b060d0b0a 74
    0x6420b072101c500a02640c0d00c5442e102c0c0160002c040d5040701d41103050080360820855681180c5842d22444005c6070b184045484903142c521181c0d11032400400101c40a00844c1d00100f1207060224264046410003003e003251400320001e56000c49000401c07081c5c3c051602c03c91132006500660403250101c01c0c2c0d80e0030725525044210b400c403a0358000c4881c1401600701020145000940e00031003071a284c020b441c1141001102d944035941e40c4030113441035540000d000c44280884c1c180101018007075502500b40720720741240700c00c0b003680c030340064944005d00d509207070016020b544142302e00c41c42640700902c01e5900e040c07840380140080c06080030b04000542d00f0800361401c01e546400542c02800d200d0340464882005c3e080c01020701150b981c0e04001c42e410641805003083e807080554250541008040301943c031194020f034010119090000c20032410443c81100c001d4143c0d200c00e04a4000740f00303070703400c0d00c00050450b04408040ca00d0380c0d43c410418407070408032101c80d5000b64030783c06015080ca03022a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 444711816 1250 444710566 444710579
    0x3090206130303020d09121203050c0d060e0105090604150e071713020312030c0a0e0a050301091a130f11121c09050a03020112110f0c060a060b0c03041a04 68
    0xa1500b0980240e4003440d04402803540c018400760041c0860088203558001d80e94803000c2800528124404040e11500810b008591850465004101c820b50802038107a60307084030702c02e56609110302d511440100c4001203590401d0b004145580b402d1040f4102640d040c0244100c0480001d0410b60400038010101d5425460880125010325605400c070310700004030748101854a44850b000480c10710050040c8000100c2c46415a211240c00e400e000045104000124884529943c42203900d0341c02d0000b00410f029401ca15107401002001a000160360303000c4041c0045c07407125400624410312000b20703030003050b4551058025400000e0013501c40031217208501c0e14001402004201000344003800580a0b41c03c5035040f0018502500d18249051458001a100c00d075107101350700380c041d01d440800086081501c1180e10b080740780c442007512a5440452540d0310402168219125880c102c004688581d40e40251540c441c0c0c000011840c09003404200c100080101c4c2c8008900d032030500005c05c0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 444713066 1250 444711816 444711847
    0x90501080a090309170f1c0c0809011206141005040501090b03040804050a170f0a0b04080d0b060406050a140301121b0302061605011407020601151e170a0b030604020103090206 77
    0x9149100317008040e4031202e1040d15040039481c0003c40b4007500c12119890400750001d001403c22500241820b880c1d00f031a10040c0d908440d6540c0c0100b00e145042004601402c103840c5002401101342d4410041244001003500c01c4d1146000d040c0c08200307106030400000c1800b10046521038072907024281003035950004a4500c403e5908540d4000c20031030340091600d803007000701a40074035000000301392450440d10b820400c00c42c0584041c1030030130b00241441030300c101a00300c248184000b810b000d03980c9980d0b2600400542203c0c1d291400159003000c213500c1c1043c0c40090728103980703141041014404050b51003050001d6284484074111131001c50000c0076075109005402c0d600300c1460281c00c00d10013880c290742102d280e0025044000310b42c0c42400203103030b800150346044d0703100820320024030591034000341d4030030a1000e4417005401c82c04000082042d48400802804103002e01041c02d80d0301c4003036940c02542d000c007840c6600359216a000a003d03600c81d4100303440300c60004c1c1800b03262182c0c90344015803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 444714316 1250 444713066 444713099
    0x4090203030a26041101080406090b010305030409060e090303161803080d06060206090c040e0f0613050105090703080a080a060b1b061b04290d1506090501080a090309 73
    0x4600303c80ba0030248000520204140e0708105400403d031440d0503079421941080b41c3c1c2145041014100006040042a43c00380e880c2681000e428046907075a890440d80c0c13503029020b100d41150402600046944c070a10985002d02d50a1020318215a150b80c9010381660503c100507040016106003103140040c4041c50001941c007038000a80d0302c807070100c0e2030010b40705103a2003101190300c1501003000c82c040100e03c0c50718040d0200c40109840f0b17403210540f803074807450700341e10186030203404144210200007031407582146205200038032103a941c10039030750303111002071102030020b541c00c1228a02c0746105803200c0da40000c000342c00140c0c460b2158405075032504000c06105224241c0000405582410001c441d4021103802c03c0180324410801d8000c1c0754021403044000e00f07000e4880c116404009280c0c5444940d0b5422482ca40307a030701108001c0d015180f04070440c900125120700210b01903100d003840905a80303041c2c60b101c0700c68445420f0200107140030740c400d400b00540c8460201e40f100c1d8001c440b44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 444715566 1250 444714316 444714337
    0xf0d09030b0709270c050406050d0515131e11040902030901110307050702011e0903060510030f15060f0501090e1302030706020d08011d0105091503030301031202150c0301050409020409020303 84
    0x800303260400c0301300e0807140007403940c03000c0c80001d01040000ca41d1080460b003051890510208054035407002d0004018170070900f456201c041c80034031607002c20003940b129403a4450b841e48858054081110803040390551000100b0051040100313001743d141a80040da0090a44400010034500032010304001c1d030001c2e01c01e0400a00001075100940d80d11151038542c0000203d2651488039010401508805041c07000401041d240c00c0011b00c1c0035041c48440c0019500701c4081e0720380d200300b454000c103c4480005001001480d003080400c140541d91811801d9441c10384803045541d00300b903650003040350010b1920042c185546002001620144500001000c1c203070000c2c02c20010310503000d0448078058024844003800c6034114030402542521031030441d281922000525120442801e2400080701b03450764040c400003000208011b0803e1241445859543c00c0d919602e4140754140003c03031007501c0c1c020460000b40014003d5150681c40045080e1005200003440c202c0c550200f0f0540d040310f01401c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 444716816 1250 444715566 444715619
    0x315041a012c01050619020102161a090a0f020120070603150e061c03020304170d031107050604033f2304060213051804050f0d09030b0709 61
    0x4031a00c89011201600e52040b0000d41c1155810940443c0e094094411b018200300c0b00250120b00b800e000390b048814110003c2c0d40720b007a40c80182840403600e21440801da0030741015900082d10010f010569040c810b500034510100c3c2c54094004542a2000b1200d852001d03c7d17a4080c3c2c000030804000280061402c0c0e1030200700050055030382244060541c0c8026a240c0035441041000d945481444101402c240845040c1984905049186000700c0d0021030f12092070303024001d00d00d44009051060802550381c18400c3e0b42444c1d03d0350390b050055000003410baa20040c041030019005064003000000c851602180c1041c0c0c480d10303102a0281c0030081031120b14101800d114000d11806400b0700b41c00101c005850503d081401900b9444006001034040e0f035010804c0340030034001c00501001448020301240d5804035041b0410300c1c02c03030305803400c4905100320400480111804503003501c240c0e03078513141e2085052131034071001e144600c010051030801c0400807000c17900d800400f081079030f54101205070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 444718066 1250 444716816 444716849
    0xd080f040b0a2325090302060a0e03071707090b130e0c030123070804020d2604030615141c06090803010f0f0902040b030a0c44060315041a01 62
    0x5021407110a02854204c0364580002011090b4002c1410001c4980c142c0e92195141001d41c42110010101c5928942c0343c00b0301e120000f04110340d0501d190081c1000b00513290b2890f038480d0300c1c0044400002c0c480d600044243d80101c0f0700400b652060101103a18825200601c44420001c3e0844100181ca035100b114414284011211000e00f0075a10101c80d0030b01440600b4650001040340d01d6800c070003894222204014801100400c448072100090b61171850f40350b85e00c2c1e24180700a003000f6141c21592504210002450031181c09400c0300a0402401040540c24110652004c6030321000d401e81d0115240e00a400018001a0046008103004070b20b4002050400c2c1c1c440748940d10b00d81c40343e0328050040c4414054071060004480d08800e42440001d81e10401e20b2094450100740c1c16060394030243e04074940750b65682482040500d410010740c0c1a01d501400d20300e42e050711000d45a040d0154002c0b01c44400150203c20025001801071002c904146520300617502400004d804c004009841840c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 444719316 1250 444718066 444718081
    0x7030b01020c0a06050c100515190f0b2206052706030c090901090e100c020a05070602010b01090609151b1209090c0c0b1611010203010906080d080f040b0a23 69
    0x203800d4000105106000c1401e09a2004004100001d181885400307182004582b00180c85200700042c03000c1030240003071039520640307140c40d0b405c2280e14101e100d40b0140c44079441c2c103103241c505058030510740350b482c10042d848040c0011101d0b034110700b09180d648800155556078070440a0340c414a03000ba8043c0d40c51480509010002c54181d010070007560910403480b4142c4404a00c141c4481640b59001a0350904080102c0c41d106505001a002d8007800c980416016810b4024420003402a01c0d00f21003182d0301c3c802190b001e4190303c01d00000060302c8500c40480e51080b100e4081c404100904945d9a9140780c60b0b00c041c00c0c100c1d2102d100801c03100e078004c00c0714610031301400c4c490090300e0800d2582c10710326840e81a001c000040031309802c07050718030380301c8095402a091240c42c5200303030008549030f40e15800081c00403c02d40c045c03a140e038402e9070a06c2c40c0300d911a4003400c0c883e80d0304001c80343e203039201c40da262080d0080141c149240c842d00d83d6038844200b2245000f500540380ba0300d940c803456040896 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 444720566 1250 444719316 444719323
    0x20010623010e180c0f0d0c030b010206061c060b0105040f0609082811010519170108010908040b03060a050d060c182303100e03030103060e1507030b01020c0a06050c 72
    0x1c80d014060210703400011420f41451450300d5002c419155043e03a0740049003400720661080030b28070b8039010710380900502510b07410383c0040e440b41000c3e0200d4040e62511400c00c084d6102c540c00704019006090500c100240f40c5400c920031555040c1001030804cd1180c0c034441009c100c941010b400100e0211081200140030003644800780c0321580b80100043d070581120740100e881142c003400ea00d031402555140c1e0b9104004841d007800396a196081c0e1044603800003810740702c0c0130000c4c0706501c002900109800406205480d202e6038411a01407519152440c02d2010340c000a1080d035000e46070200c0003500d40c60700e002d150700c1c0a04c210341c00240c1414994000c4c0540452820302c40b0840c060103401d000c200d8030b1111700d041c80d1104032003074000346401c180000e01e4040d890400f401c0960070540d2040388242e000000e50b0607070307200351000d00140da00b5401e950740d6400d80c00c012284000001010175680390023503222524002041c8140c0d04024011404984c01d810160312860029000083c0a40c0e40300051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 444721816 1250 444720566 444720587
    0x1e0603040b1e010f140307030803091011091810050603010608090118050d05160204060602030307120c0806210f160504090b01051c0b0c0d05010e0402012001062301 72
    0x1000b070b5155042403003095010402d8017480940d0040415101d42c140e80800c0340800465001940c10b94a01c0d081c441292a031074030909180d8040d0070326917410a12903a00003907403402c48010300040200007902448044416000d00803940788031201c3d0380400d4903203030580190301821682d00e03040c1103030402d02540c600311030912540d800110505800d541c000b40000c038091106182c545403107500c440400d0505104007003007040080d40031b443d2040c00130350183c010003c0c51240d039054591906000342070310314100780ca000f034241c02c0001f062140000d203d454000c030940c00080c01071000039a094171642403d40751281c0d041e0381440550144420351503030700602c84040007400040d40c05000441640d610042441c0040c080e0a10031114060701c1c99004d08500044a602500100014900c3c00c140d030301c030001984171020007558241814000b06480c41c1405429002c0d0b0b030f06a4644181d41c054400100340043d61172000c220554a071400025400343c10a07a140c8045046d001f100e14100200b0005010140709 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 444723066 1250 444721816 444721861
    0x9180a08090a1d01170f0703150c08010e240409050105060f012f0102071b05150405090a050c0d2325140f030c34021e0603040b 56
    0x220550f110524250003c0340d0440c0c0d4152200303490713420181101d40c10002005008031984c45800800000d10a8103040242c01400c10b4104001c000d40d00542100c90107403d01440c0314440401000c20103c3c15101d00000a0342064035085402900100005090361070199060354a0382d111014804645440801030002d4002401e10500030425501c601126800e2000030415001c003112500d048004290102c0310b443d6880455000e04280b20480318003002518002e03503000b0307604500c80620b01c11030b2404a03025980014403848660340d0b1411190040c3c00000c001148030a402e006044513031000303008103445410700c588507000d00f9421498a0900e500014410001101c2624641c501010150701003e11030070395142c13045d4414032070324001806101e4000c880440d140d00004000c0380400740c102074080d890725180301102040d288003a40b00507050808000c3d45502541402030010b207005040494042420540341c2c2840b0040310010740c4c20341044501307481d81d2a01d802004007080c0d1864403030b160b0880 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 444724316 1250 444723066 444723089
    0xf090607050a0f030509070305010c050406020c2d04110c01060302010e0414041b081504021002010c09050402090d020915120106060504060309030302120108010b0f061809180a08090a 80
    0x42403840140b030704260200400078159102d006ca551107406100840203181c204000b03001325400000002c02c84d900c00d100341c4006004065806091349001d00f81d030307c3c5101100d0083c1c001200440c080700c640000341d811465003c0e0f51801160b91811040d4050406030010ac800001c216180d400003420001240c8500c0784244c0c03800f50110340d101e400c0701e003d50308070b604580c103080e9040c05001d8a00c1c2610103504030303540510584c0440b0070902010403c861042d4800d80e42c100756500d50146c00da0030b130345001441030301240740c4038014807960405902400398114020094822907100d60041044d80200b51850094084100b58014003810424101001c00360480002c11a481c94a24020f080340070303a000e00002c05403201d1516090500c2a0140e90b04a1083d0340c105100356501c401c00c5002b0140704c81e0940c012903d04000c07000d14a05402550a0034003603007034044102111400700401c0c1600241078500c10800c0940001e03003200100314051506100310304059440e00c2481c104003104486a010802040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 444725566 1250 444724316 444724327
    0x10503010f14010e0c0d0e1c0527030109020406090b0a0b0a051603030e0610081c022508030403080d0f0612061d161509060f0c1a0f09060705 62
    0x2d4a04280c1c2d0446501c0d01c06118640ca4a4640320f450713208050040045070308000039281b04a0303002c64150390040c10041802084103c0100656043c014103130711002c0040311041301448084e181c1e00d81d5160020080000a1101d403d5001504899083d00928a41a03480114100b02c0c00c03e802c0d0b2101602186000d9410508081030040003449620240341c0d58110300880481010b000380c12200e0810508020355855140000040103075481d203214036502480342036241c0040040d404590035003021554058940c0902c4190341c204100b84c0b1110705856080c10f9800028a904107001078405544510012580c0760aa80e1011040c0d550540c54004003510b018030070170065040690354101e4540c4644081030340c0c1c5041420b0301c070340510105460310038020f80c04030460b0142c00440002c01e0754041c00d650640200054812a0079910703d0288802082d20048110012030058100c284030701c3c4160303098542301c131032551b00c1e10300c3d1407040d10780442c0c0403108024443c04181c2401069404491860082d0408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 444726816 1250 444725566 444725591
    0x516032a12050c04051c03050f0d1e1b230406050d0e031201140a030605010803250519060b0a0906030302010c0f080c0c1207030203040e010f05100e01020102090a030b010503010f 78
    0x6c6059081c00b000203405c2104041c010170555080d0074a01c142c054980c1140d07040c1c51302506d00b00801010424012001c800131058905c00e8181c202000c05820039096014802900d03003800c6c828400c1250500c4c500c02c0004c0451400060014103802c1e940d00c1c0c0c9070b003501060b0070f060f43d04200c8868003d402c1031021040d01cad0060b84e02641151802410542084103800200d8240c030b6041e000607207018185400490f2584000000f0818001407000034030f4160003001d0386102c2d0103413200c001400c0380c10a1800c0c20800394890342c80e501c1c1c2070040400003004214140060300c0c000042e40039081c4651203000030018140c080c410000c3d5458182807101240b689280300404240004100c2c0060600100e5000e0060300b00708480500d07500948100c42ea1a00350b030402030344d06c2d0054403580d104108994004112106010359a800f02d4034040d000c1070b10600207000c10742c2c0b25918600850704544d42442036400a0f91911802c400031401184680c8165041805050946100c0d12802510301e0420780c032460704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 444728066 1250 444726816 444726829
    0x180b1903141501110a051510061b140709061403030c211611040e010212010b0f0405090c0d05090f030d2304030305040b060d03090302040b0303090d0c060e01030516032a12050c0405 79
    0x34a440cac0c01c40c5c82c0b084483c1e107070624400001e003580606c0791080401c040390b9240c1c143d10020542d420750344850303402125a03042580d00d210700c1e2419078107500004940303e00341031080580c2074494000701d1301c0d90400e18912040300340e100ba209400e6580c0d46441042a48500f0107100b05044a00c03114000d62400c0444002c03258400300600c1402c0f40754200140e080580d042c0c81c000c2da00a01402004821182400c100704a110381141010058030b03442e02001c65071250000410300308140da820084c0d81480c1903080c0d039100521000c50078002c9580c0b14002d0812409145220f03901c11446a01c00003061304043c10184050780000b4041c1d40074040020b508408240c02240900480303a04850108032404060b01007819401a070146541080784d4070740308401c00624000c0d03942664016600d422a40c0468401102503c40a648101560502c3e04144080d01d100f900b242d840d4010811510800d44501c8012000040225075050700081e800350b0100c01034030f400d02409030001c0c00091528107080c10140010328 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 444729316 1250 444728066 444728087
    0x308070831020111010c1806080601020a030c060906050708091005060a1206110406020307060506040614100c051006090b06030702120a180b1903141501110a05151006 73
    0x2940c42841c03014811a071182e0240c40000c080c1c900207100d0071000c2c8002600c6042450040c1d076800c282c0c52008a41180f007051030a00c6400140d008050780c00f45038a007516440d20b03444055425548414001e0702242650003070328010b00a43c2d444290b50301e029100a0304019540344107c80301418a02401050361b944025801030350103c1105284c0080c181c03500d00018034801c0551185140302207000070b8010380101c0503100041c002c0c081400035985010400c000c440b0240180e4000d921140560b920b41c0c00d015030342600303441843c10200300404640c0c68244c0b40c8050525040d4600391291420302c54001c41c1c0c01104c0e445002560200d00314103010001949500900a003a49007040100d90b41c0c5085108074000a007820000419402458840c110100e450f40490101c80340d800050035084c5010b807107441004441002500b85903020384501c0b41e00b1802840d040d64003410412080040303048044180b1900039940d01c688020181c050114041c0a6043c1c00101a08030500d0903c00412280780c029a0000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 444730566 1250 444729316 444729391
    0x20a08031e0f060a1e1203110d11070308090105070501051f0509251e051206030a0c05100203130b1b060403020c0906060d0f0b0301051f0e07050f0703080708 69
    0xa070701c25400345503010185c5580c0100650402044220240768100009040e514008002d42e045c81c1090441650038900108401681b540f103600208041600c54025058821052602524207003a6032982802d403a42074803036080d01d0800711200c4c1500300445007004020001520340e20114905003108240c40000c104451003441480440c49400612400c64041c80140c0c24000c0b0280d9041580024101d13049104100700c0c481f20100851424640000c00f04400ea03409420440c6080c1003406002c40150640c43e040150310007484104000c280444142024104090200703031100741c1c0650040781412100d80002440d0010814403010070f50124080028942c2507488840c00c0c5c58000c00f1805a1013145050341c0518900200e4180c518201e41001044940817002400355454002c441d145480c04807403c0c880380104032404224580450310b80301c1d44078100d41081030420000e4030300180140d20405c070440010301180c0030000350907040301c82d082d04203a1500e25811031442c05081c1080e441c61003401c1c3c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 444731816 1250 444730566 444730589
    0x3010902130f09020a03060203040c0f08030913020c2b03060501090e04020f04090b040506091903080901020f130e0a050f0c031f0f030311030a0e10020a08031e0f060a 73
    0x507403200c141904443d01e041e6024100c014000c0d52800e0030b5009400a0303404607050340e03410500098030000400b0040907250824059850b201e0f101003040080f034900014041d600e5000e01130303c1704110302030244000d00000c800c00ca2011641020f0038945040381c03004c402080c18036002007400070ba41d104131114203584a1078000301c8141c43d01e00000302c070b07410300744025a40701d410101d82c041000050425180114482c40c01c55400303450b903d00440d11400c00c01d8550444016607489035000c00e105280a6411100550005240040c8180c2501069106d0318680c80a1012040e0800010385000480c076844046040c0402250900d00125401004042c042d607101020110125a400c03102c503051440040d000d1140030440c0d50780c2ca2a4201c5d2110910042d004201c001501d00030018012003100c0b1009602e0765000f20291424081003c0f2414000e45003003180300d8512000c0009014000450044d0400240e8005201c488101c00b44011b800030441403c0d0945201440b40c80e48071501000c05803603240c000c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 444733066 1250 444731816 444731831
    0xb1303180b030c0c01180c320120060702070315050709030f02031e0d1b02030d0c0f0515060a051009090203060105120a0606140403030e10121d0c0301090213 69
    0x686024100840c1c80c090826000b140c4001001f8100b0003d008403400c4c0200d231954081001a500ba000d00d40b1280740341102c003004a500104e620441001e950124864410070200e040510a940303800c204950035005a840040c0034018441e8005104038150b9082c0003e1043d880c1611005019810030310000700004a20a18102150307403d201c0c891145143d0301e4100344401d410004180d503020415103807008281d120b1904182214500074092441390003030300a01c0403542e6038004550032040b0040a58201c08224070440001d1018055800440e06540c01039000c1d0401508204895260f60300c0544a18540e40f210101580c00402043c00c48180e1840103803a5940c960041c2d4a9228005080640742e0700d100401000000560060056407401d541d24950a45a46c0c2810102d11441c04050042010206900c40c0362038881001e029501d242d1521030410b41d40710b0f02d0401580e45030b9007100100d9121418581c8512010800000d031050f0440c0244540aa250042400c13841602d04844a05071030f0f841 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 444734316 1250 444733066 444733087
    0x108040602040503030a0c020901090605060f0705031204080a0207050d0f11271e1b0306130c0305061003060f0605090a080a081b15010e040f0b1303180b030c 69
    0x5070b4000380400340660380ea42d0701100c0b00500769140307507a040f4030460800700007080c03009852048030301759803002e01220300d0b090300800d0901c065040f06004880c107120811100c0a070004502209000b20b110341c40b50b81c0ca545002078064207044090b00040c1c0141c50490864003c1000505080d03001768014080710102c400150100d50204c0e178201074001440103e0400710400028030304c0c00e500c5940c400448003100c00110f01c01c40c02e03444050f500860429900e1072000e135203000040003103400c044000e064140354104803100900380c4da91000c1c00d8003c00e550703200300805403d1406c14401a1b55040c40c040001c80d0038202c80c8090f490543c001c0b1020490041040406505c030f40b800c003400b62207090112041c41d141c070f15181c0b200d98001043d044009010307a40c9080c2c0b041c000036440c418803960081c1c3c0c019030b0b030800c040a0307200c410040040da1009081e500c0701010912040005000e0008070800101855040c14060403517080314005095079001c0031001c0020f296014240c903040600c4450b040d64071600050b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 444735566 1250 444734316 444734321
    0xa0207140313080f03070812100317190c1e050703061d070801020403020607200d080c0c060705061b0f03100f0608073509060403030b0d0c030201080406 67
    0xc403008910000960701c0c031441116403001e00b00e03103040c0d040b11201400c11020584034040c000b4020f02c21308007400a80d04400e4164051039010185411003d4041d503a6114084075041a07002e0151354107001420280044000440c00d102c903959003469403609031180e64a03940441040820310940e0085c0c0e0719841007020078080040116000b0710248002c042642030000e608400c0a41c0c0c04091099010001d4000418026907040b640c0040c982410b1140d5900e41c40d0074145101901c10703080700d082c102d03514195114010104040d00074000d1544403201d04074203d01d4020120b020500c6040d0a02c20107001400006900740c0c005007102103040c05800c075241c44107060040180e500211500030040081c80c150031f00302c50b005c0301d2129161641c02980c55800b5180d03014141c4102e000505010241d000a660007003030421000089440815141004c083d02d5241c3c80041c2c7d02c0d400303035070020b0b8140018507515000c0c2e0107810608543c1e00042007001d40d41e074008003901d13100c000d05200b107080010b000e2050302d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 444736816 1250 444735566 444735593
    0x30c0305150f030118230a0b041101050705030a1806031e0b01050c150f0c07051c020f070b040504050c0306010207060f090f03050606010207060302160615120804091802090a0207 78
    0x5c19034903035032070982c40c0200060000104150b58146d0304490180304500005903801419000107040c0e41c0e6445a0710754184031107004c85003d05002d0b00300500c40003c0d00400080440140a50700c5481070101e0400e000418810341c0d100b5030400d800c1003040103030030303513807401501c00c40d101c9030310026442c6001e0f00140d642e03004004079a4014080e10040034500600b460389240f041c0e00f514188070755a5a0840341210310f01600c0c0b80070300154018400c0c1d100c60b03088180103420808642c0116851180c0035498689003684940200100d0351000c5000c1046003031a004068100401c01c05440c20b40c500200001d603181e41500c511010040c000840010044c01030319180e0242c150003001103400341c4c89040c001c2d942d4500b6a14140140b0502100155a0b071080c8241e44100441e0203028031010813548444000c0c040341040c04c04240e81440000804c01c007000d6030003452a01ca040700f19140d45c41d00e403102c41110044104440590412104000160b4581d015180e024a01050042c1c450340d9038202446c100921 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 444738066 1250 444736816 444736841
    0x101b05090a0302270a09030c0308060a050406090b0a0503010c3204030605090d0804110609060c07080d17070504121509050c131503060e0f01180201030c0305150f0301 73
    0x120340d45080c0708401c10301c0d04040c414621042c44c207540c49007943c000031640041009000100240c00000010b4404c442c3c842d00103000610302800300c1d403584002001c60717865501661905599410b24405402c21254031070041c00c00724020056161241c2010700070202c40000030b0b1a100380c10041c1c0f01c81005940c108008003c136966041e80326501c91408600400040ea1814000d00c0340d4882a08010b100d08030707040c0700d03640c8040121000c2c1e10b0403046c4455500704140c1580d01880a0281c2c40c81c91408003d400e00400b0ba0b42d005024850000101812034140300107e00c01081d84d400400c030155410004403800c982c070503101450903a909080c66025040b01081c410394040c1024128007d001001400f4550400d0440f00ca04034180a2180d000880b000f600a0030b004c201200404c2010a070170b03612199040a00200ba644011008101107007182c00c1006612010b83c000e40030001956454403d400d074112041c10100403504000500184038484000c1d8903100704152042d40c002602c0c00e4010700c00d903005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 444739316 1250 444738066 444738079
    0x230d180f0605062805090a1d0705120607050f0310030204022b0c02060a090303091205030a0f0b01020c190510050c0d090308030703090611041502101b05090a0302 71
    0x456280c1407000c0d00050b200c1900c10042000684134401039071003402d03459010400d103514603610f00b009014903503d004140020740b5540312000e0143c40c0c50750701c40c0d0b0111a10140507002003801c040800ca48007442c0c40d0f4a40171540040100801c07203401408641c0115024001180c4a0b5144520b501410003503400007900580007060000980e00110142402c06c0c085d10100000c4032102c01c144811982a07800113001a404080030950040c01903100756403143c024540414001c011381c0341d50b94642a0504039000240e00081000b15007480707449411507020040c901071140a640e080000c3d6241200310582e8414441048bc0718000070540352007030010040646a80d41d0707800040805890750f0009081c902d0039015040080b04c44510a52010003034030b6104c03a01c58215140c3c603038120000c00303e20004407400350b0394600e5038075484402006000103200388480c407040f052280ca4000e060a0308a035404058505140c600304984102d0030b4070300581e002516141da120316004c0c000403402d40d21540041c4d04981e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 444740566 1250 444739316 444739343
    0xd02130e070c031704050a0606090518010b0a050d020a0b0f040602011506090b031f09020c0f0d050328053c1303030b060c01020a021203060604030803090a170a230d18 73
    0x640d03002f0030b10440a0208140305c1c6d420086d1010700303a80d4040c41443d44200040300071320003071402c20170840205002400145410b51546006041d952040c602c2c1c0c5204100481c0c10000035609005039a024410b40228a40701460070764050004d61302d6001d038000814022000a032114210305c11914184004a024802e403560f5140110003580301c44590708030f5008005410401c50000244084044c8190781c0f02c1d4a10b550b048082900782d0268949003400065514040c03099900a020705405884002d500012442c20781001810a10080b940d900100000041c4500c840340c10344886540968900c4600c00c2100c118502240207107050180305511034004508800308020542c00b529003c0341c25022504c1c0104c6072485118540022500550701040422090000411450155422403c0304003100c400481a51f40c20f81c0c0310010740140c0c4481e40000c00c081040b5035000c4444c1c0000c01200d80440c200d4000050010741d00e1041081c0340825980b50074142031280e0120290800c2980c109a804502c074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 444741816 1250 444740566 444740579
    0x7170c01060603061701020f300702060f06030109020a0302040f021204080d0c021603060f021c05060f10021203040218090601030302060606041401140d02130e070c031704050a0606 79
    0x820344c0c2e01a0718141c00c204a0510003010b01442180c4140740000070050170882d0501d46000c0300c104401d8484d200c01c4c3d0481254040c85000e8040d50300501c4142c0107403156140091809455200080540f0301c02da04251100d130158a69040620907640c040d02c011030703922000d403420400b038800c1d42c2204070130440290400042c48841c43c06404ca09400110500030810358544c120303542c04610310441411002440d013040000d4060384010003071000c03140c3c054100b61510000c9030203510607602001c074030b54aa5080000f2480e22250020801d14125084a1440030a8400070b503074030700e0259151003075140000883d06541d80d609045112440d42e092541d000c0c64140380b290384528007072200301d02501c12580814400d2804105680542c1c01d40018650300c1701d024001161140d82042c5c0d0200b40d151b003044280e030000e22900041c0034030105e440c841c1c01744d03503c1c004168694440082800c1e00b00004131146100095100e4024020440246000b964589407820300320308140c0d80601c001d0510b4a400e0000420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 444743066 1250 444741816 444741821
    0x803060d0c0f1d060402033106050115030c0f020c0d1e03050d0b0406060806010f0e1207060908070e0402150913140f07120e01060513050105150403050307170c01060603 74
    0x16529820542e0104d403610814070080c5d0109586040302040c981440400c4416030ba600f801d000f03217082c0c4801113444c0564594004645c800c1c0c03c40380c80b41e503203603075959022605401002c29952051824200c650a8a0310007500d440c0140511446817410f101e03c241400070074500c0d01e032500c0100b801e01c85261268640a00154080100151b0349400c29200c600c07a071a00344a5402101c071151074a81d101d80c0e59000442d0112200c020080a103e42c060014203a9180c8031206a012204034000f4040320341001c002030485000d0340d004140f254801c1d08140326031030b040c0900540260381556030050108415078101190b0203181001c580000a0400c8040d02d250310b40c0044184402c40c0c0d50840312a1640c2641c1c486603681251100080703804400c4e204000000c0341e0000000c42070300c8000140150703c035130026014500e10a10800f0f40d0341c9500062200e450b100d00140c803801c000c003001610b45407459445070744030701406501406072604d50300d9440510310100c080300c4007150460000c0150030744034400a0300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 444744316 1250 444743066 444743099
    0x70e0a0e01050618130c1404030812060303070605010303020f1203090307021512070504030213020a0e011808160819030e0607030302040308070b010e130c0e0907080a060209030111070803060d0c0f 86
    0x3551000303035699191100d500300c0d000e0340d2b00400801d140c980c1819404844880c040c11007500340c8400c01880000c20614803410703020310300c44c0c1c3c050705900f0407409506240c00400c0740351107107912003001403106c4510b00100b100d00d9039130b041d02c1480506942010112590054200428901240700108100d03194810010300589200701c40d81000e1101400080e0200d000e640ad003140071444040b40080380e50b010301507071412a4140c1840488560725002c2071420b0034101504c6900440040301c00740b008000c02d100760001c81c00c0c100401041020907450080000a041c1030040c01810001814814507100750111303005140c018042c1661b50880c2d00e00311480b20000d1042c0301c41d240030700380032440106031a648401c040f500004048040da007821501c03a040280038214441520410000050228041c4503540790139004038801038031150074006043c29a000101c140104000030805040080c0c003080a59801400c10349100101030620715210003003021a810014070303028803880010303451003110400034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 444745566 1250 444744316 444744341
    0x12020c0f0f0109031e120c020f010c050f24061009061206151808010b150310030b1608010b070f03180902040803040f120b1305010f02070308070e0a0e0105061813 71
    0x81d070868019048602c046c40850095002c0450741240785d9030741c0301d000546c20072f80c060800e80e40c000400398229458020780345002e141c0180d4440d1a2030b0407a080c440c03542da1102c4103554101c0108003c49004080714294000d4406024800c030100ca804641c940c09800904a420511500503018003809404c07004500d030724201c0441300c42d10100b0720103818085d002d00104c3c05411052110040c0804110036040108401d04810000b5000000300740c7c000b50940c010407030144510724900c550f0b1001003201405810050300041d0401610b000200300f40401e0815503018a05130101d2404010340000e2090303680d01c042c0c8030b80d0011501140b07440010000b042102d4280000b802281e5a80c441c80c15070031099000034000328040b00000e1962541d030f240094429216100016240e01412041c204036048a07000358005204242003100f0150080003a5242942c1110384143d0180b40050200c0c005005000300f600a000124165002014440c80701007507420003030250300a234010b03950140040c6422044003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 444746816 1250 444745566 444745583
    0x51e09041104201902010902030d05070210030b01020c060304290a0b01080103021302161e140a0f11011403090d080601141e070b0702060412020c0f0f0109031e 70
    0x800c0d000d070503100d040d58100a0f650700a41000c034082c481d0501203c56090802c199521862440010b81e020b2100e1100100d440c0c540a40310b4845006000b64503007a420400705252a0541c010041e0381c00007101108501e040320a41d64940d61450944c2c2102d40710008824440504800030301c04a401e040c11900c510901c030300400001e01d40c2c2004590341d10081c40081d40013650040108081000c64000745420b5202660000101ca8a81c1e1010405000b42c856010603c0111558104020b0110440b1072200101c4005100304181a12520b01040141c100180040c070084c40768507546e405440015030701313280701001980324034020720300b40d482d615009d00140005d1080c000180c0740358001c0a0001e448140040f00ba42003403506407550002200703d0f030214094000600102c80083c000b91445031040840d176024140a04003483c20000c5090301c110618199041101e000d40c2399141c091440d03c04000480c5c046231090800001a107158030a86c00c050849801858081c2e10750849600140501d0300c0342e42c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 444748066 1250 444746816 444746831
    0x2c0918060a0c0816031e0608060a020708031f050d0602090306100608040b1512010b0f04021e0306130606180e01030b1f050402030a150509060a051e09041104 69
    0xc180c00c031a000b03000c00010508500104143e0b076030610741005201d011307040004040c1c01006000c0410240c8040841005031600824440c1441c14071000e9085002c110b41581071918564550119020040403110646105c1010030303601c1c0008518000105000750000c00401e49a00344034000e90b0241ca03c40c0d00a08c5010045054120b4040350241180c0f40340c0c4c0d501c40c140d00c45980e401c070000784c0a451032240c040116005580c56903240d040042c494031140c000907190b4081014405a031542c1030f000c500c00c0c1d106100301c200b030040e0301c11080005020060200c0d41c83c1d44485c0001c2e0100000051413210a00c3c102c3c021802942001203210f00111500c0b6446190f55a05030410b1080004d01000b0325054610022a04105040e000d0980c1c403c12800b4504445442d54045800c9070000c8407080303000c0b9215070320b282c00200c1044408002e440c00341c400081314600703040851010840d500c03d050048040107a1030341c4001c0345010fa03070301512005103451450701703042c01d15010007500f14145a101313038541030a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 444749316 1250 444748066 444748081
    0x703090228030c0f03051e210a030b010305090309040b01090e161709030d0b03190b160201021201030809130218040b0105070203070b0c010e1c1404062c091806 70
    0x1c0035000c403940813004110840102490035003401000e02c0040c60303032040d00015141e80d08c0b120026003d540c100d0300c40e02c0c1c807408101d5000b01551000d142003418103103400d0074448001c001004543e11204161804501c60421000488104425901500c40d94110381c046c448030100014000301021142e5407805014021121094032003c000e0340c2040b01513100b0040c184003101c440e005401914001801c0e200c0e182c110540d0038411889a40c02200c0ba02200d00c00c12929014918082503c60100c0c4001c40c20708c03e2484000321111010700010f02600c1c1d01245081c91580e4a01090014412428044d502d913806207880c9a04a00c1c0740d981c0522650070f00c121250194440d0007615501070300100285441ca00d40211000f00d070340545800f5106548034120040b50700b400b04207030307604519504990110503a1a5800501c008092240040288010482000102e51101003030650803800c00026113201a45459500b0b0100031054090700099520b0400c5268064104090402d100d024182c42041e5600741 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 444750566 1250 444749316 444749339
    0xd0509100b01180e101205060711030403170309070807140103051503061b0d06230d03020303070f05071a1015230d18030f0302120703090228030c 64
    0x3030b504041030b0002c40301001805426905607412004041040c21510b07200c0c1b4180d1803c05090000740c5541d4030040a20141a51201c3e40d280c003503039801c0c00b450806085960752544542000504002100d000c4003003000c1610921229000303140b031b2400c03150718907625140e506a49140a138900e011914200008990b001c0b00f0544000400000b4040e08065a130f000c00c0b030850744110368820b100d100c0c0501002d03101031000e00c10440900410704101c4044018806820304c840b00648106001e000100d204100080e0008240c98108200c0d0402c8007000c446105e04840344e02078010301821413400c60444441044200004034020003140d011b0b1980715031a4100192001c405042d07080000d10100e141c010f8028114010b04044201840003900c3c01c0100c0303260f41c0503104085111454404104480307030402d5084076104613603240904007542401249a4609d1384c00360000d010005140d03c80b002c910071541c076890341054198540312030800b80401021115505003450204072072840a4140125a090310785 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 444751816 1250 444750566 444750587
    0x10e06010806101b080310210b0402011b1a150a06050d1505030114180c2101090b0f010f0501030209030703032703110a06170a0e030d0509100b01 64
    0x40c01d12915801503481c100c4d40d0342141c4207880900c0711041041c1c00000d00400055006000d12506404c05038140b046070080701e03289031841e462214102e582c010025120982050780243c090a062041010030440c2191000d04400c0090074512015840f1348000801300030301d40201246880036020080881c00d001d01c240036405080086842070003451407410300c54100c201784492903000c1140a603500c2003c2070a444002c16a040100d0b21704041080703d80d4141b0300c001c50b20340036400a103584602c00000c0b8800c0d51440030000200582000e087c90b0041c0709402c640710965002c0c1900485103018102e40c541035a0038000c403488044404400241c0e076209000313407045284001c01801c1810700c3c554081d0340c0f00c01c152406420004501415040003031508a001004600414000100d941a02c2c10801032000d160054814002c032003000d50000e070a007454180c0d1203030740325030002000040201d48610790300403c2d061030986420001004004d910104880800050902c0c091048040c0800159809140d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 444753066 1250 444751816 444751819
    0xc030d18121b06180203011e05130b010303030f09120206090c03031314011e1206051f030903050c0712121103030a0b060d0908071a010b07030507060b0d0506010e06010806 75
    0x1081614002c220540d00002c421202c0c84c6045603085030560209080d540807011b600c00c880b80c0d0406040d20b5220034081e0700e030301001119043c003165035540d4800178100030602002c0c0c1010740d03900103448a8070459101150580d00b04008684040004c0c00007561414201c0300304040380034a01201d65141400010740b540b5044425404007444d0406003c070880c001600703085410095409400706424011102c91a0150328075607a845003403078160410000c0d02d0720740c0e01503409a60401006c040716440c000c107048413a90745240108001c500c501741200e0340d0050441c051b4950203400f80010341c0380c070000d440381c02003445401100803540c1400800d940d0480502c3c8054841d8004100103454600d030b0740e0110641d8207000707140310304200600e07441c50308a030b030101f00842c1c0a41d00098440140411b0903808681c0b55617842c917131070140d810915070494500880100805000010940307000308012a00603410100000d400c00c04aa007840c201640d0303d007400c1c49251001c2c0a400080342c8036510460300035209980 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 444754316 1250 444753066 444753107
    0x1103090309011709150903040f0e010f05010e15030a0635070e16030f0f0506040e01060605040504021c0e0a03110a0b0126070303120605030a0b0c0c030d1812 69
    0x88010170741c1402c07402070100345940030411002c03484100030160000a4500d903081140c40c0d40c1030800201d0001075541000f41031007003154001c00740343c2d20301c001e074540e2443d1b8620702e50300da44030801214064896a00303e043c1c1c078150841c0424001cae4070b540182e04190310030380c00051185114401c80380c036100680181010390380483c0000e031000d48512a05608000d0a2600007070822500c12020100c030f0104048560607500c1d20b05001d9540343c07a0048012109104c402040341514160317018220384518400d046c02a500420f000d07590700d15403d020b1b6000c0c00068024000b0907107079142540c590302c121104178007040b2240074050350074100007403a41300e80740e01141e510680d90800060f08003914520f09010031015001440e004003c00c14424100158402d89801c0103124120400c0c03c02d40324035401c203a010360300481d00c15001c140c0790b02702d00d50004510214181c7e141d03241a04c0b0307811881410410701055082001305414000c264840413420b0b8000c040c006101c00c07451004552385004a04800308641 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 444755566 1250 444754316 444754333
    0x3120f050c120a140309072d050906030c04090501090b091f050604060503150402010f020f0a1403090a23011d0108091c0801090608010e1509011103090309011709 71
    0xb0380000140b1044a980c1060000640038000b00e245036402180e5660140c0c005103c1084508203000c1000208128800503001070042c40c4815201801103105107441001d0341d60204010b40c801344022540c1c0711000e40207021655460421a010f891100b07012100d0407007500010b1801400800d08070602d80c85844040c401d142d240d1012406844061b0545902a9440c50000f03244c1c0d4040ac1040e090710390803081c04102e40340600002d452500215881c10a642140003c4042000c0c0451214200d540c060030108040181103400c034914011409045d8125010038000b180301e186030721303004414810002d40340c800c600c0c2500c01140c4241c0c0300018203104885619094030550701400c4d210fa40084000110303020311810050180d4010030550120300410408001032000c44828001c800180074484000d101d0140070148490380c891421000c00003600401d00860b00080d400e4004846801485003000d0b00c074141501401c0c3c80b584092003d90114a007640180d2070340c07540400442c030501080003c0d1040c02c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 444756816 1250 444755566 444755593
    0x30d0e1008040317010321030c1b0606031a01180c09140414130b060a0b07170c0a0804080c0301060e15040617010c080f060a0603111303120f050c 64
    0x15010b40110140140caa541031282c40c503840c130480c001d600550361141180c0340e880c0b0a04d0240700341c1507074804250500c0500c0d000e841c0c0000e00380f410340c91000e400071102040d5040c036200900b0310740c0004100c0c0449007000701c002016500028140c0716002c080c0c1000d0034030308200008641c11040307010302059031481e042142141015044608250107480400c00c03071042d103800040c01208445101300d200d04040b8200c18011a0b56025520034400d81d145503e081c203200c085000c07405410070050103014840010704407010440d0a807085c0840c21002c855020015241c0140300b90003c0c0a108041d10990300303000740c5454140100c5c000c40d032003c0140b0b142070300e4440c1c6002c010882e00e6582d0303401c151100c1000580417080b0100f4021810007400001e94588034020082000b03601030301690f90310314a1000e0000c10f55540003900c0c102d4038a8240007030301c449007901c100481d005440d040c442c1c10b03524074000018451089141443e040e0785a072080d0790000082c209480c03a00a031500c55003668002520b00034007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 444758066 1250 444756816 444756827
    0xf150a0b03030d050406061701060b04050d03170903071a150f032a090c0705033a0e010509240c0f0c010204150305061c170a020705030d0e10 62
    0x2038a0025059a1501503ea0002e0b0140c80090341c0448046540e0802000408051044030101300c0f6400d0091110354075080c60a035050061340200c902c50741550070641c0815005031a4032100e40f401044410191409403607440e101e0b001003600742e03941e0300c02550f2120800d005070100b9210743c1c1c00ca00c05147d41010802484006000d001ca999094403130000807681441c2c1d1405216114141950b00c6007000b440d400a10006c864003400c5094111414001140020008420707500d0000801c07241e100c0e09044110004007c9444402c1d0401c0c0b50030840381060b0501c240d42012000112640080c000c5032200000c80f0b54a0f04042c41d41c2e900c80c6040c808a11485800c4101d1a07080b40001640504040b840f80f80a10301e6480880b0007070035603500003810442540603062a410305c92240c00c04100618100000c42c43c610148244c1d00020b403c845240c204000ba44039107030048040d801b0b2380740e46075410700a0280d80d4603414000c152007441146820010300e0b115164182c07480e10054034074004032000c8031080e1031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 444759316 1250 444758066 444758081
    0xa02010e100f0e03010f0f0e010e03040b1e0d06030f05060114010f030203090313060f030e0a020904060507021c020304060314130311330601170c071a010f080f150a 72
    0x74917549800352410b00d05c500e8065055012810080054948205110b00d42114810f8200b8055a041440b042000e010700006485040c035003401c6182e072040034001201418071450a441c480246421004000d01c0318180030780c1d00480c0f2401c125500750362940944247c00d500d2946841c0007034a0b040090165500c2900651f400003030031000c807411700400510302442c1c0c0145802c500000380400004060040d03150103035120246079000600101c00d2540c000c5641c42c0340080c0301038020350715500490700c031034030800c00500103000f450dd0b00d000d5010301542c001e44991084c812040000e0414044002d01c0e450002101e0050b5440b240f0403074554000c5d40e06031b60419424289040601a038101c200845c910342d2540c040410003401c2d0702e1681c05e402c050b02d002c0104081c100328100a02401051a0800e920500e19000082c1ca810310340c454101f480d01000e0300daa003110345200c0140180c00012104620400c2000352a6076034281da008a14948000d41d0b60060f01d0960003042a0601c081164040d03258403264 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 444760566 1250 444759316 444759319
    0x1503050718090204060305211204060b0f0a0b180102010b06160c081606121503060b0a1221051206040923160605040602061603090b090a02010e100f0e 66
    0x144040b003600050f080381c1c469070041c0c0d0150030030740070400154a0030024401004034091080d06003607540095134048080100300a120340c3d81c800d101113540e641e00d50000e2480c04e004081c50b80703003500c44113001c010b5009280900f4500c08400303083c0b0920341c0180241c090b842005081c40d400c2c44c1c10010707641e006010096058030070302002c007000b050046091100034103505605801001c401d103402c1004040e6056181c0c1a9946032500c00388030044182d24240b03400b01c0ea04200301061890340c840000d4120b002d1750f409080c13242c030305c0d00e44230042142d400c0b042e03a07000c480e04404d036440400441d4151901d1044c9000b510310541c6100003d600c51034070f036006c490520301034501445424000002c0f4401700100c18814001d6500040b208140d40c907050308468050300d09840d116007811319100002c2c2d91403601a0508004442d100109021203201e94810040c060700000310704180e0a0000c041515080c050b6826400a0340c4104240d00d0f50901d05000d0002c2030307050b0747d184981118070344211814142d040180703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 444761816 1250 444760566 444760571
    0xb06060403140a0c06030606020a0212010e0d030b0906010801030f14100c02030c0d05040b0a081305031207091e0303050714010203090c09010905040305042606070801091503050718 79
    0x200102c0c0d41da03941c0020440c0480e004003100b10f468202030b040c4205982c01541018140b8200b4003c0d0b0354080f9118800a6054a1848100b29050f600c64054090080340c03c1d154816941105000350b459080702e6031145054803511070540316400111406803090101030026420a140080040c81901000d0080501302c401d8503071882c0248044030a849065a0f250016132001c24900c07407180e018000c030310000303525080141c506450b00d81d180f885070082c2c3c0d58243c10f001c0400001103140316100e100c21142c61f440025a561400c56200b50076a40748140c95183c0082d020503c040742c3c1d5003494640c00c00c602041c0080c03840461071942e0480309a403113928100c440074400002c50303c00388824000785020740e02c000068a5114401800c0c45100d0b401640184500c60404007071001103604141201c05841f040a8003031007040a8581c041001e441e0200b01581c07900c214810480400d5010600300d050b01e103001d0041c4006400541080d40e82215404050f0458000d10400c01c0480754250340b0040500703011102 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 444763066 1250 444761816 444761819
    0x102070206040603090b09010b090c161b0e0705070302100b010e0d0510140f0a23090303070305010527070c080d02030f16080402010e22060501021006030308040b060604 74
    0x2280442d0070551140010944031050403041010000000c0d9200d14580c000300310081c1d070724001407881140541180903a940000782c48041080001d032440c00c540d04003043c0e40c4070003080100140602820710a01040201d441c0101e070703440e481007089a8005800d0380c010035441a100b6805001004000c28407414043c450500101d81c0c0c4a80c610012040d000d00f029045960b00000c01000317550100c0890b9040910020401000942c80301110350400008440090981d0800c00c89801c1e0740c0c0e509215a043d026004100300850344000b0007184501c08a64040c41030366030342c0c82845840c0890351204403005960311248089813014400c03860b4008a18038005203c0f03d00354950b98119800300420b050700a400000300841098808030454100510356000c240d010b1021000030318a207000b410003810008902000803c5507140030000011810148440048451b00361200004214602c1128054080d018894415080b544640300440c2e4142d2141d404c90f0b52940d80300d1800102c01400240d006009120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 444764316 1250 444763066 444763069
    0xa05060f1e16120209011b0c03050f03040317041511010b061204060501060809070b160236010f0501120e01090b0711070b090603060103090210020307350a0201020702 73
    0x4030035000d01840a0320940c03881844a0003070084040c07500a030b00c0c0d42d00400c17140a01c0c0c2d0b80542003401c05079aa06850030f42a60750724008c0d2458149500150035441820316055507a0804402041140d01c50003c3c1da40500000d0380420060165220340d00080c6d0109803180071150251440841030310003d0000074040760351400080843d0420b0440d48050480b500070001017040a00c6032a000d041c1c80d00b882d081510709620075130383d150000e001e2201c40413000710700d0b808404200408518040c2c2d0040c80c40484c00140c0324420095101c04840c241441c011001044c210f2020020343c5058407050203942d01c42c5820000152800042c0090313080710700342d80310117003500000207220b81d18655100314036204035428062801800c403031103501001415000355104000d46444982260030400c030540345d1075226500d81005070010700c1c6001001e90007410b0316001980059010004002140c81000c00041040611030f00910402c8501d5050014550013411071202020000190203d000d1030300c000740c94601180d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 444765566 1250 444764316 444764371
    0x9030b01080703350f09060d02030406180804170f01050a06181a0d020103140f1b090f060304020a1e050109090903020c120a02060712020c030a05060f 66
    0x7445079545030040c042c00d0080140c61100c0580000304241100000074400f60010195010182c01c42d92121000030000308001c0c090341521070041c1c005040d1512044084a4000a5030007144c084407820700e130582c65481001c0c19a410038665401c9902207080a090002e100742041441484070b80500c42c00d0f980900c421400d01615100340380399540071560919107260038031a02c0b403c20042400a050200a000e242c09a00d419040d084085600b9644101b0a00040c4c006000ca901d1407052142102c0030402031004200c42280501c0f08682e030503104460203000740d0009c1c0515080300e680300324005a4445076140c041c0c040c64200380010154a00d456944621610a01a2002022900403070790307010092503812000700d00042900fa0028806a03109a4000351107003030a0707400270720801d10701905000c00c0a040110019069010f00825a00da00d9400d203403004103005240e40006100f19144440c1e1b504004ca044d0441540c410010025900e40c00548624224000e10100b040b10f51320920f41d003060325a5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 444766816 1250 444765566 444765569
    0x80318011b02070e0115080703021603031e02070f0b0901022a331801330503100209040b0a060f08010915060c0602040302030d05030901060e04030f05090109030b01 72
    0x210070300840c4050110080c2c02d0107400c0e400340410501590040002101010135606450040d19180001d681c0740c0318254028000e40350b49e400030f00d00c0b200c841d404040d055481655003070309401e041124030303031036803060b00aa01c42e00c0002001054152003030720004140021440d005404400054201414000707490301c20306101d034507541003540d004242841c04a06000b44a9465400c401c83c00e909031030300a9400b600250411640c9940c0e415000040c00520301c1200c001000010744001d00045400026514a01240030b10160b4241d203d102c12000e84800005aa4103c1d20003a000d404802c11240204000750004080a43c000c4c2d21201c840c1541e07903506030003901502c0c01da11540014146218002c00841b0160003002c12245007980c1d000401c401520900c00315401c92428503420030291602c0c401074001c0d540020341503c2500003080050f50000059442140c0003002000403960760b8032a20842d40307060710058041555011910887d5100d01c0c02886a1281030408a0700241d89aa503980944003d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 444768066 1250 444766816 444766841
    0xc031110180b0a05040308241905030f030903060105010c080f030721060521030408150610050a0906030e0f0d02030d150e07182c07021908031801 64
    0x300740800e03040222504429400c4101e543c0100000c1c038107a0b602514001c03000d00f11290400340302010030380480444824003034249001d4140d0800d400c656041c141c3c0b0f1000ca0080c140709004800c9465208000042501c00301c0d1001030040400b81d00c0c0000544020844070419922700348104011201450920000c5026200681c2c03100c0700c0c0741c2280b0b940c4c03005014501c00c0a1403c0e0408074100500d17960011840e091a07510310200b50f910018a0400d0303c0c5104c2c0b039105400d01d01134048144446080110760314456242624031072507445080d8407c4075144151003a00006c201c01400900c0402d00c20703440080000d29030801c84402d00011180640760140079084080181d1002405403480342d554001c0910052000030124904d90034100d080381b520800a15070820801caa1840d4032403081031a16800060021000c50b0030302c1001c444222400c4591896409800c01e10000482c03a424800218038001d2650303500c01c05030094403569966a154070140a512204541c200f4092116001b88640780c00841c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 444769316 1250 444768066 444768101
    0x1603050709120312140f16180305060403021509060f04020f06180a150c14031209060403090608060102030702040b06090604060809010c11060f0916031506150c031110 73
    0x8203901d8806407290070b910b551101140205209204150318031984d001282070428211300904a1022160488c402450046640030b004002061102c04a2594000c900941c240c80b09400c0c08950390054007800d983d03010450340003000003001c50704005981c54001c0c5c40182540b19601d403110009640d030704000c0341c0000307401e010f00e01440e207440e0048078032004204c00041124242010302010300380d0b00980c2c1014110402d00314100346101401c0c001c442c01c0141880e203001e400e00780540d201d550b030141114110042440840c0215005010394022803262105074001d5141c42945d5081c0310161007506803241d00000144a111a99903070315003d00050003140e6240c506d45d00d000c50516081d295282c1c40c03a03080c0030000d54408803290002c036003298000d02901307451a0703c0c0c4600910600e00001c01c40c1c402e031104520721020003042402c03841c2000c1c60403805014400d0b1625103034218602864981362102007890480d02c0c1000070300880d00380c11464000c8081d6165045460041c0c0203a4541100a065504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 444770566 1250 444769316 444769337
    0x1d070506090a14181e10050a0e180607091707150513030c121a270c04050103030302070201110d02030a0c03170c07021e0f0f030a060c020c1816030507091203 69
    0x1410010726940046400c01e0381c1c1b0342919240100345240035038000d802c503a0f10040d000030b0b1894000c03002443c40061142c11030310245031014004094942c0d60041c8c0202c2d2800b10800d14001c40d00141001c03d50b180c0980c1004014507101c42a103865004550b061134404100c0000400b14441c0440100107141841e03898a0601452400e40daa1000ca03880d000310300d08a103010312801c41403003040c0c20034003d03008468500000007202000c0c50004040c60460b441801c07c400401010b03455005030036001c2c0b007a2038046c580d1a000c0480e03900e480d1400c20b41c00050344140702e010700c4540700c0c40d8000d28040c0a0b081441d90000c07014a01401c04e03000300c51007400510001005000c41c01d204540d006c0ca9a155058580f008084c0340000e03003000b00e140303201e52140032140e6801035165001d1220100d0070b0350095041112140c0c3e60406074503440c1d11008a841414200b181600516500d0000d030311419942d200038081d046140410707001094090410420040300c2c80002c101801c00c00301c03140416020340c0742d240652 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 444771816 1250 444770566 444770611
    0x106020706021212040f1e030306080a1a07030f05010f17160b1b0a23010603080f21040b1501032c101d070506090a1418 53
    0x103641e44020115071007058404080b10180d010745103d14800150800951201e05005500d1800c2c40400f401c046204100d581d46180035460030000c00c6e2082c0c40510081d543d0f544055102c4c2c0007200040d080c1c808000001d551400d5030044194400114103000a4400e105140c660880b81c00343c1000740810380d091410301c140e24a4505015a040c10f00300105050740e090421108160f5007441000741700f0001140a140001060402c600100c0c8104212503001070700d03080c0011030100819055540e0200c01c03800408500040c054041a80d401001d840d10304845c41c41d100401e50702110154560480500b08c04a450400d0300b9020300885c06001e200410b410078458120703000046903a582e05051800109145081d141d0321038103240035055190300d0410598501e010305000c45095110760701481e1a170218002000141e60b032000c1c402c0c10341100c1c591900d45003841214072030704c844541e01140e909400c000e00e40c4d4545580f40f00e41030103014009103000c46050741e40942d50548031142c080c81089040d4400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 444773066 1250 444771816 444771823
    0x406020717011b0503060d080a0c031e0203042d121203060e191b03021209030403030804231903021603020907030b010212070c0806010b04050603071d03060f010602 72
    0x810020030300030010711403003440c40803c5594841c28031041c80804000070b006580d41404d0120020b400441c060781e1900408401489075056070002c40108001009070070407030326003810541c00c0041c1600103600d8a410232344141d20f140914400343c9a00036000140000f00a441d60910b4007d040c0209050741503030729881c0c1404548070002d02c00c02018030f0305104116450510030f40981046940d00c6800101c1e581091107006001100c074500c0504806086041c107055159000b080d660b800b51407030240f1900c0340d00000703450b4803c500c400380c0005c00c49030108001c00c2c078166035403001d101e64a400180040e0961f0352181041d11855520307100c03004440c16442807503014441300305145000703961200002d05590015281440180200c0c04040d9111500d0140f640200107454001caa50782c60309855100c14900300b180d4100d01d0140c940300707010b8140006040b40c40642501c040c0e41c40203040d1420341e9201501203c0314003d203d0310b1403101c040c41ea400220341c0c0342840034601860031030b0459022507041000c041d00e03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 444774316 1250 444773066 444773099
    0x50106080a02091c03030207170a0210050c091c0f1b080303071e11030456091305270307020d02030c030d090f0f060219080d0204060207 60
    0x1075250040005214643d1008070340c80c18080b12640c41030b030461003070508a0090090442c000d1085081d102d4089030310741030f14041e00e120360266084a084580c1502c01c0419108141d92048081e170050240b011646000f1014070740342d401d800340c605285800b940b5040c01072189c1c140b0648410b643d051a01c000d0703402c44400d8801405c5c1010080d4a1810314500042041140383d401440e007110507107004180c0b500c207040c041c005c1e071169000c80751910b0f151408110180088840075003126243c041124007158903600d070130400600440004410011300d5000301c105200444403802d0540200f10849280d03607800da882d542d40f280c68800103224580203440c940e10400000d58200031103204140d004410000004458003598103030391590301a0b09510101c0d00d4060812038007a41401440001e2402941c448106002c4600c0e111001c00081d079940c80c49408491140200320040c1c01c000964115100b036000b103403003600c0c41244c032a494000d0611101c3d04981081d0400310040c0c0103001f04001aa89125100c407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 444775566 1250 444774316 444774331
    0x11010c090305030a0e1507050f0d1107060507030e0d060207020f1c1b03050111250803180a020a0b0a09090204050f12010905010f0b01170f0601050708040506040905010608 75
    0x1040d81191502c9a4034061182d0368030070400c01d80943c5203a5150060f2011002079034030603c549074499071030302d142c651036250174032007462050342415200588500c3d0742003000c0c0c4c03011016203021402c00c1030485169101840640510420480b00f1310350b81c54a1510500b11402000016101d400910420081c40a0131001c00d104410381c00d800380301000d040316941001c03a4080880341143d01b139018010340c810816403001c0c140d5468032050305090047d01e0000c2c10f66441e01c0c022061221140c903101d0361820544140500021420f0001a0030800b42079800f02146080070b088882d07550703540e80002d0440305990041c52010b13802140194500f9040f15074407000d450306d13280660800341084046259a00003d0b041c51007545680102c115a170400e511051445030400000c0c0b20f580c40d00140c0c100034080c100810750002e0306602d180d01caa2480911802d0041c030007080c0c1d450190300e0300c600450b01c540210300b082c2e81001c0304000005565603a04014001810306800c0401d55600d061409022088024005c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 444776816 1250 444775566 444775577
    0x2b0b0702010c1706010509030f0109030801050306100608150301090f06020d0606110a08030c160f02130b10031e091109010f0e190204080303070c0b090a02030c150f03010611010c 78
    0x3e42424120442d2541c0041c0c20301c0c03ca5280c0c0000710000c3c0c9049244841841154602150101459880f8004506845c0b0540c101c0740c2030b4442c4071003a00800028441e42000444000204e506400c0c1d107e520160048000c001140322480ca40f0791002c3d4589842c0101c40055001a10000f480614011301d0020451410b00340b140c10a14400c0b25150b18110381d0090403400c00000141c000007072001558031100708000e486043d201036103031900a0301240302003070b072140c4d1a41c0303031582d48070b00c03d401400800365014000c8011820800001d0307002c2c010300e6402c1c84041402c10113120b0008201d2045000c1c250190306002d1600c0009828400103c00c1038216078018120315506020324016204400d404c42408030081d410220720744180002405182c101c60386901002090100141e4440080010140206101c4c50b442d203030915400d0f035031052a000203400d0340005141e1038251404070f9400d80041d103800300701407500c515100040d4244d8000d0b00154041030403007000c2103004071b091040e2106080c060815 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 444778066 1250 444776816 444776837
    0x610050406080606040207061e0905011104060c0210140705010603170712050325031b0305010518040f0f0f050706020d1b060e031603031a010e2b0b0702010c 69
    0xc0710740f203200060034203004a400040080810284e5405070389040d07020114244031040d21414003000e40413511040d40c2e551f0a00d0100707500c081304d200c100c40843e4030b2615a180b451000f5802c2c0800404007090070000c1c000240440e07000d5032400d0b0300900403c0e11880001403003d04519100500001518800611901c18801c00c1c0000c0e9929644080d0a0341e5400c08540b00c0e81c0306a4032184020f01c02402200ca0303800345401c0c48825030103401c005103400b1910f54140400880311021401c0303c00901c6503e500584111240548030000c20380103030400e00620500c5085411620b600b041c03c29109022264150ba074000741d01401400c0c0b01c220302921141c805231407124404140249003820715961f00c0b4444809106c0401086420392086100300241d000342d9807110718603007411100e01f56403581038000c80e05018511481d4000c0c003d9a92540905856151030544c00700d007404464600001d00f232030105000304620151982481c011406240310b54a000310610b403804000b4203660620503140140503d5664 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 444779316 1250 444778066 444778079
    0x10f2a0b13121215060512060409030e04020d060f0b0a0215060901051210050a0b030d020309030303010306052a1e09010806010f05040b030c0901110715030b0a0905090610050406 78
    0x400c0e030021528500500d8042c3e031030450304000c08152604510041e0b07803007070000d442600403014024000090b2142847c076681c2e20280404c0e170f05840b0b0b00400162600202d00083d10f02175001c0d001c0e0030404000000d240d515000f148004c20402d400c914154400840c08090456040001c1c0e000e1520445451040d41404408200b02c100c040c002c0e94407980710391030030200c0842c0c10028120b8400000b1001e0005007000c010b05002845554049802070007a80039010641c0d000101329501000003500852850303203540c440100800c400f606842d100c00102000c411100c020a8103071100d00c02d81c0c2c40d0f090307882481c10f0300c40c0b0003101002e00c212000c5205101c40d12460b0307080700800c1d51100082c206a00e1070391070800201c60a04c600d0700402c103028004401d000001070108081c04000400b0b807030f09005100d03851340181e80c556403031080d103034011444840099a40d02c20717009010f01c18030151841c5c22194130b4075410703002d4450885943c1c3c0640c2c070100c2041981030400403008003c180558040210901340030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 444780566 1250 444779316 444779333
    0x20c010f060b1b1207020904060f150906060e030714041509050618130605040201140c06060a0812041517070203030609150312090a1d0f0c041202010f2a0b13 69
    0xb0006e4482c083c0385000a090180c15003000000c0c50f85800c0400800c040c0760f951400250701070103104000c84c50500041005e5005a10a01c0c40e40001030040c1840e52800034040070080c082c00b1019005074a8044003141e4081d5032081c0405000301c203a011896144c44401c1c002d00c4002c3c5210320760403d00322014800301412110000404580107a4081415559800140d60050707940e0038414803201d0025040220100105036036005a9041b15003244142c2d80709206035030741721542084c20b0741000c2000108001d401c04c02050302e00280740c0c10580d928a0396203280d00d1044c40c0841d000b030096000042000042d01c0c005030850341c0b000010b00791185825121000c03c0c0d0310030070f039a52051030042c0095031031245da40700b00e00f0070300a007001080c8844085800100b0889100196812050b0700341c820041012141d412083e1010764412078010783c242c085a4004440b1450300807098400c0c001c032624901510189403611400442d8540521401c3c2245450100700341d050050020f0406506080c443c0001201007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 444781816 1250 444780566 444780577
    0x20307110603090c09010902070b0a020304020a050111120310060f020d080604090204020405030105070f080f01030203060403050306211b0a080a081b1f05070c0213020c010f060b1b12 80
    0x541e1000e03182d940b0700b160701c1d2401d2000d1056507130203e4880c0001481c0000750300241842841030410301800d440d011440400d034001036800a61048a510f02804030394031600c030700c455034080402280c01404888500800d50f905c261002400c00580c400140705140e009a81007548419a100810314206540c4005001d8400070707040c0340c419502d6012440955966805031405810010002c01c02d40c00e0541014100c840e01e92050307804501544d00054203201d08000d554100c13500540940000c0e510780d98100c810780d00040203030b6840700e400482c0303810000a0f101450300032101c40c0001e2014444404007015021905c0030003611860202000740b01d2804085084403d8550042c081d545450b40022031301114a42c25000c1c0c0300510800700c01003201c0f400052a4001d00130300350000c020039110304d20300312010652580065000380303000101c401c02c0505076000302a010010000091620341701c44805080d507190307a000c5540800041801210b415440043c04009c0c107042005010307034101b0f62080111400303070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 444783066 1250 444781816 444781819
    0x2a1205031902040e0915130204050615031003021f02031603050705060702071d010605090d0318080a05060f0118090201170f04110907020309090a380102030711 70
    0x4408245540500081c05a00769000041503440e030303440f00c0c4114840541216070f1101c502c24240140c00c584d0009400c903019103903690007440504566001d21018001c00f408103508a00060001180d0040c0903024501414429642c848038a10b180104240300c6418205074041e50382c0324103125443e94000045035260ba4040071010311540303680c01c007507c40b03025002c0007400c14014801000f007140d90114602080e034205aa51a01090383c55a500301c8400d000d0140102242080100c00c0061030103000141080d0300c245050251840d0035001c40e2150010399000b1200c0350300000f040c6c01002014031a8550180c1e007a445440c0360341c90300855070812441c5108070004e8603601d080305401c2d64810700c0c8001008a0a84c18042c20382040c3c10340340000041101c0540380012a594000000e29000103101d02801540d402142004006400c2029015001d000704400da5030340c00c4800d00c4502e00b00d00002c070283d80f4201c0350001080c0d420307000284a40b002100d03030441d04100722150024000711240c1070315000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 444784172 1106 444783066 444783077
    0x120f02031e1c121505041a15120115031103010609170c0f0f0d1a090d03090503030a020a1704080a02010b010309080301050609060d09032a12 62
    0x40b60001d0030000c0c2d01c1ca05952508541500240004021100b035824800e6840c1d00007002c0303c0c4101c0710954a14540328048059203811341107000c1c01c1c441540742c91b1070b080c071000007500e034132805000344590030200c8000198520710a512a00c006a08103049540e00c2d43c44440c00341c08080d0038466111488101005409803041c08100c0e01180540600031558900000381080100c1440208603608641e07529408408241c0090f0426890f00702510f030090513090400000741402c1d000d009940605041c0211200082e500004984d801440b0a400503241c00701c0e4001290240e00e03144030b00344031811900a010034040440002c1a00c40100e40080052003a69401541034070b05071000030340250001c0c4010451410904014002c0241c010519032500a071103401c6401c4503450b4100741c000884100f10507039402020340301000344800081403002c4404003591002014044000c05d0010840b = true := by decide +kernel

theorem cover : BRFrame.Cov 444604316 444784172 := by
  have h0 := BRFrame.cov_init 444604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 444604316 ≤ n) (h2 : n < 444784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
