-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0921
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:57:37.170362+00:00
-- url     : https://prove2.me/submissions/b594a0e4-0974-4bfe-b7f7-bde22651c855

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 165467625 ≤ n < 165647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 165468875 1250 165467625 165467639
    0x6051021030f0c11090903040b070c0305011407020a1226060a051c11060c03040e0910090c060e130c02010f0e21070c0504060b040501022b0e1810 64
    0x2c1c80c0e508181c203040000c00f181090b25240c200d0462101c425004003400000309a10540401c1168000c2a40c02412600c2d0481c3d031810501e1948648416907071503080408090103401030103182d60040409400512000105940b08140b42c4a508075007014001c210202c144000c070f50003136614155034880080704407407500800304103003400c032a002035002c2c4030301941038201c9141801d26082e904d074005201d408948034400014030540300e0344803c280a40000f09000070000040c0c0015405401e031001640c01a079100403902e001c0751540e0501030220140f2107001c100b214000c1c0ca94890500c3c0144c0300340480002e2001c1071066903180c00c1c6500051f03541d035803100343d02c500c5e91289580c03481d42c4130082e00403041d0700950900c50304d01b80d13403290340c1d4031070009060420054040000300041c10007a005014555680c02d50050315003140c40b4943c00f6005421001d045000b4141c242401c14451800c1210a00d5401c4030032102c3c03c8590340010303084402014880000242c621a1903c541840480840010705101d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 165470125 1250 165468875 165468887
    0x10b0406030507030615030e0705061306200601050f0315090610080109020a03020f0a030f0501050a05060603070c15020c010e031905070302030306090a0b040207230d0c0605102103 79
    0x8072003410907103803100030300c60145512401e600060140c500407a0715123a0350011070412140d0740c0034650216000442034503100c1044141700c125092500e032082400d83c0b4001150100d81200c1c8289859004000140030a20340b5921400c10580c020f4104d540d002d44d0f12207184007650060300c4240107980020100032107500e5060914020300040002845010076a03400f11350550541d01000340324055003c10903005403150143c40000703542007507040044559a0810900800d8140c034959542c608201c00507041c0c0c102101142d00904041e41da4010354440c80d04c684043c8540350145414042e001c0007003180260090040d0f0401c0c82c68100070719941d098240704041070081840001082c4035007031203100c02085d0084181c0780c0c00907007540e0450321a03407621a00d80092000519103a07102c4d101045601c18000b140ea0400d0142800e1502d46c03601804845003259a40881314490b40040c40f0398402a00280503504a1a00007880751a500d1a49480d010101c0f400725400128101140e43c6540c0307003003070580c401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 165471375 1250 165470125 165470131
    0x30105071419020c030d11070b032203111b180118090c0e010602150f01051c0816080703120204050f0d05072607210209090a0506010b04060305 63
    0x4146000020070160450600b4041c07000c16602200d80486400460b5000340000e1503007400080c160b40c001344a070034000c0c2c0600d800c0c0c1101c0200f4858158085005d080b0f0b10100d0340110030100040d68203050800d420800914082401c80411403401515100303d04200040807a1a45410640002001203400c2c09600000c0404a11686010704010022005590840d00c1d040c09940360216284c0b10909200e00003000302c1c0e2040c00d03802111000013500540c042485160005600b0031946a51142c01101e00c0c04c2c80280207099010002080089903a00c4000e0301e40c1031f4a11840c44541010310000144003004007040301681c40300c00001e074010816501040440001062001c11414941001c01044c0001561640d0a015081100030351081c02070400441005110f04002101e42c0c4901100305030b0108100000070032244150701c0040355151220380600108a0002c10f9400303400c00035000c0004018001e01040e001d40030700c4644901186042c0401030191208400e07a0303a0395894080014104e031401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 165472625 1250 165471375 165471377
    0x50d0c03061b120b18132102100608060a1802030a0b071202070b070509031f0f1109063a0203070806041505041a0303030a09020108010e13080a0302040302030f0a0203010507 76
    0x80000d0074005d640f07014a48240343d20a0003081055034074040b52034070f885507960007d00880c004408603a019284072000e035460342d240b58240e40360041d07849e01031015074009001e80310898000d10300185038481300d07505c034400340b1300300e10706000100b489500803a00f00f5a4451041d0341501019042002998100360741d8400f034540d48c04d0851400d070950f161254a40e0000c3e0402040104c0051101281e90b81040988031160805821041e04007281c2c8030303100209081c411041141d81003004800230b0001c003c00352090580042c0065281c5040b845c10030302a04d40c000c598100000800306000d044050100f00c0c0c04214040300300059590410010151801c0c40080100d1f100b03508103180c02d0214019401e001c0b08030f42054601140e080f08800045032010f0410341c401d0740600c000b2080200c822169008944042d000703807520000790740c81d2500003105001c00c40384a40942e107805800c1e800620b60100610801840d441c005061503126400603052841e2000248003650242e02c11500358170742807040d00d03004011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 165473875 1250 165472625 165472631
    0x30b0f061507030e0d050d0306080d051c0b0301090c0807290d1104080115030b180601060e01120507050c07060e010f080a0b030f150a1104050d0c03061b12 68
    0x85411145500c10340d4001020402050726891aa03180e0740403d03400c5c60b9000d0203984000715161001402040c681c402d0341001d10034012084031440c0a2400c5981414820a000c0c3c4c24148144101c4050000700f10300300d0f0159039540c87e010100309544c5220015100d40d00281c15101c1c031b05014a900034006d1070240c9400d42408000000f90326117101211041030700410007150280100710705440d91700840d401990703036509041d61509403410b9103002c41c060f244504d000e0205610b4031884030300748020401242c101980100300501c10f40703016a89144000760305140110380344115140700820754105640c220007094012450010188003404110003134005444c0044408004200083c5005902c041c40420702140c10081a1190b6842d007103003400d10405000c032135001c1c0c01441003036515040f80580d561611400e5001c207040118074003035241c103140c0c280303003c80c00c00e4140006c000c1241040070080302c203041003500010015540f4001c0340750380303140394010704520440913101410843c8100300c03940c10249 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 165475125 1250 165473875 165473899
    0x14060711031204020f04060305030307020307020108100620070305030406211401050d050f0a03180906050a06050c010e0a0804060207080303012411060a02090406121a1003020604030b0f06 82
    0x104100072943d0180d01120344600090001c1c020500a280d00c4d003020300680000010000307810b400100a04501c2c2c401c0c5d841d40c1c900e903203c04603282002498000c20000442905101541407100401da0b00003140b040d0981d1700319584c1e9903c0a185900651241021034480106440155228240d40740b100704004001d220b00d42010004007040701c0c050188500c80c0085200140501c42c007000b480c0c030b0300c94549045955040c51400c015058592000c50008080c06822001c610f040550041808403000906003400050401c5020b0320310340c214003c02483d41d90303a86c0040807400c00c01c10000501e1070151084070340c1c0c1c50402d00000d0415649420020643d4020401085a000d010001c4003404044110205070808234481c103c80c2c60140005202051160005001c00d00b00943d0040c20030701d20484d01040700c0c40e40c8100d0b0100001058001900090420041c0000000e10300c41250388500040c5c0000381c0c10b0703181d0f4000350103500241c2060380c904a007401042641509840000d402110484018100740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 165476375 1250 165475125 165475147
    0x6080708160e1908060f060411120103080906070b100303110102040612020c0c03030703110c040c0c0f0309050a0305030d0f1b1b020909030a0f0e0a0905040804031406071103 76
    0x4209941890040c0008070820503680203010408014240e104d060f140a401c2c0241500314001c02038544605c102d1510f0041d07105840b80f5011210b00203404a285178081c5c0c0b0b952990110341d00031500958100ea02000803000044618500d58403d48503603882c107040d6819030600910200403443c06c500c8c160b104103c140b09154104200c265404184c040141e951601f142030701d4240b0b64140c80c90754051001140383c0040580000e0340120641d2180d00f11500e2202e201d0410058604644101010417030305850365010922009120081901034102039a1503907540740418004503081d03206485035007001c41c12018140c040d002d0b51454840a00c0c3c18070041d00c040c1c245404804100d0070746c070140555031103414046da200c0e4482d0360040d0b0700103040c404280f400141131a2254000b504880000d403403e40c132402505d005070700480e00300d01c0c040d0001c0030107410f005000340105006003081c1e500c000c05100020004400c4d40f844003010a10784082d18150a096a018090b003e2864004816401c1400200c42c81 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 165477625 1250 165476375 165476387
    0x100b040b21010207060c1d010504120602031e012d05010e010c1a10090b0103110301140301060b0c0703050d08070215070302190815010819240608070816 67
    0x1001041e1035208106070452003942c0203221342440140010304103d0003400031a000000c40c0c0b010010840000383c1070b0303511001168544140d00070713242c032818012581d02c00b00c4c00030f0b030140d5400326851800303c0900c03104403908400c7d00403d9001e80300340c1d80f40120140c20140c581048110031581483c01808003401c01002a2064502800c0c003410440c01d05c6029003400b0150401c540500d5180b02503c8903030401154039100382900d03005540c01a810f0824dd140554820320030402d032020040d40a40c1143d0808030050180c68456030400c1d419034956030049000404540144a00d004000040015910398602507003419001e41e4440d0501c1003490401600715004580c40341140c1c2951602e00259407aa84240c0090045016181d070020a00c400b0010054025000d540180d00d07900a00e482e00803020011110700c40100d90380403807100d540702c03981c08281640d0801c415800302c0e161485000c02c2185211070022441ea408980003d02402c24400c000b03800c403003c0c03904111081803074411145412006011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 165478875 1250 165477625 165477649
    0x601030b041e1101030e0327030a021504050a0b0f0d0507142b27050a0219060801050f0303090111030415120c02070e07050a031103040302100b040b 65
    0xc1030000300001010401c02c40940380044180195015008940d8101074030000c50003141c103070210f441c140c642e2420f500c0c00015110b240c1c0e80908901410043c84041003400080407030110340602c107800411006941c0c1038455261b803400400c103217440724540800c001d0031404640c0813907040401008529041d685032401c4030342318090400701185903102d86030b0172074007a043c0e08141c1c10b41c07440105448054041d442c6128250001b80241e0200c3c0c041002e50510860300103d48100c008203c80b0282141211f900388001c0c061800781041e140d61440540110311412459078a450114100d1281800100d030810711950141c00705132410000445a000070a9407445411070240c1400b0300c5440c14041d4007810011180506004a03100c10704080060000d01a1240c10002054a504008400100300c1c13000580104407480029401041d0b202c541c0c0a6940d6030143c03692400301500c0d047e91000c4001070400950085200381d009002c40441c2203540022203c0c04400c41d4415420260302c079125540c0c3e0b00011107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 165480125 1250 165478875 165478883
    0x22502041401061704080d0207080c011505210c04060b0d05070206040f060b0d02060a020309040e0f060c0a0c021503090615031b04020d051e0c0a0f03020c010f0f05010609050d05060103 81
    0x201354403681071540c0303103004100d9644006400064034004204803440508600018640240000e80244031030911002c0d42c2d002c0e50307400c82800101c2c0301c8001c08c802031800e0300e84c8450044c0c5400002c03c00100e010790f030942d003040d2690140011004d8500c0e21510429034401200e102500c81414255240c0105052440002d80003a0301d40046080680d5040f030202042e0340e0050041d03503118886c22001c1c0d2203820081e4510700c19460304050851401d408189901840403c03c06015540d40345403070710207035400501140080003000a0160010f885410a000ea0903410010440d100d1600c20191460110010012002204590500350407502c001800b040340030b02402e4607402d21141d02d00464024064481914001030801e4107101c0250490283c6640080800031424440e42c0d40060012803407241d15110400290b50b0201d402607140310f035010741400322a20001061043c80000c005090b5659034110545080e42c0714010450560044055401084203031000c0012510a49526855402c14031000d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 165481375 1250 165480125 165480167
    0x1e091202040905010f061712030135070305010f0e0f0d0509030c0411030103020405060d0f020118150206010503070f0f05060a14040b0a0f0314071202250204140106 72
    0x203001c2110179005200000c2e044241008950784e503141c00d41c454203104010901074000c99002d050b6040601d0f0031641a00c8a60090b1100e0b14902141030045444690000c14043c100001011414030144aa0030045000c2c0d000440c0007031044110808403991498100184d0b48907406451610f00045810118040075091583c0c80d003494802003070500c600203052980c8540b4108518500b1070040d005103050f24000d5070200075944e1580e041c41810342c02d220010b004120b03040c0c4034000661048517440d182c101c2403a201c081c5241e542c21580262a0109003500c00741e0010401404182420042100186a101c28015140c0d03d000c0d48c40d041301000703000c0d05000c0c180000e0302d00e0581d4091509540c1d6400441d400b65607555803a1011100f58000a004e2030001d103030968030701d02640c468000c0020750050440c0c1404907462b42d10082d02c2c01214212808001a0248090501c1b090315408a040c0322286401c1000507503160710400c0200d4400e88040b503101c1c1c0c16070006105555200d04028011a025580c0c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 165482625 1250 165481375 165481391
    0x60a060f12020c0706090905070206060105031803160302060a0b01050f040b0d090516090c1416050a020a0f0518100506070305040305030a030f0506030c0f04020901030612031e09120204 81
    0x10390081e00c203103003c0320740c1440780d0329000034156840802401101c0c6915420010360311040022a154075003552401e00140050010940e6566814000c8410204140449140c01d01d00031215030100c4040c2419009038000000708036042140e401040c820355402d10b862840c24041b8120f60b122402a8010b009168001288140341201c407a4070417013019400204480030525002407050048071740c0d0081500460420003840c89141c06070400e62484554200f80900300400000f12131200e000e6040e0039600e9101b40c400c258050b0f100c4105120113801c1e070b0004000b11b581400288032a20028941002c0c81810000820406d9010007040f05c0c26500304480781c940d6031031242001c403514005d50b04081c1440c08000b68541c2c440f82c040e404501c03107200300501440143e642108254450040c881065082041004050203500e0181d005100120050500003801904d034100c200310598040030481c0402c1801d4551a4080300c02080c0081c510039034a0281e29850925580003200204444001d000390b0710791101c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 165483875 1250 165482625 165482657
    0x4050f15160201271a15010302090420090102010c0215070e0a030804080606040609020a090504050c1e1e0304031e03110a0206010f0801020c12071403070809010305060a060f 76
    0x444d0100f02d0000080b0254100042e2440c1c40b1100b100004482c03951000d010f0140ca6104605000d10424950541540e0110028010760295220180e5144c0c03007503503181c5d99840d082d468040340d544290018041500e0328401c000190031200c41c06107070010365114802c0e28560003461294554130401d03620b4a20103828008012030581540b58100074810600800d012a0307031a40080c85500c0b4140440307050010a13682c0d04080101d00c20b00c0030890004600c04810f009600303041d00010342040060301e00c0703403515503844442c040401403401914810000000c544040d50000500c1c8080030361401951490340c10180d602611030301c40300740c03580c0c450666103082013050340c001d5000c1034040600c0c040030344d80e0b00d8810754000e45512090041450410886401064480052080d80c0180610600405100400101340c8409800c120710446038003c901e84061085281800038040d02c3d4400c03da215200c110140000d0309580740200135034000c1c0c040070001c0000650000300c1103100891b60910000340020030803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 165485125 1250 165483875 165483881
    0x160213020405150901090e090d08190c020703020315012303030706020403050c0102060a110f0702030f0109080d0e0d08190f051602060a0e07151704080304050f15160201 74
    0x4080e640c031480c401c50415201d20f14a008000d080000da81d541c0c61340c1c0d10780c040455521416501c08805034061200c4500076070180c0c00c03094000121291a82c051051010b1842c2942c0e044840d840c0180c104200410440c10108814103460b0520b1405410310340c1405902110b100c468070f0042c4281243c0e00c0715542c3e644050080348d40311078200340306541e65600e9041c101e0f5103403110000b09006108003000500d0311f000078840c90000e1580c0008a500e080b5244400c400b041d0008101641e00d0b00036844982c122420901c0703903440c1644100711b0380e030700e4074400840c0303030220382440049034046e80180c10955800c3d5400750f001c81e400b004c4078907003c0e442080300d89220300801c030801c1c04003d058a8801801000034014409914000240d421910190f07107001c43c040c19100a33a00c01c4c0a20340c0f0103803040c0b28892807038500307001040962620411a9903064120400302e0426502079072080c0c0000240800e0010901c60144031300f0510f0014007200d4101c804052100500034900d004030341c0d41050046015100390 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 165486375 1250 165485125 165485129
    0x9050c0f0703050f03010b03040209070305041203090c0b0c061602010902030604030804031b0b0109150806010b03070c05100b040f0c0207060e04060f080c03060714070303091406070f141602130204 86
    0x41403158403580c4910aa40c00c0380d0040c4c0d800d91007410b03107030001036802d3700c00d01034988290742c80803000c41c4c0d80b0500308080e800703007503000340c02c40e04510961000f04a0300c40c004050709114500740b00801d8142803035100701001c0020028840c3c2103904201810025032400103c2582007541032030305000507951070400311106c100907902c0720700121400103002d0500401c4040d16042e40c03c4c159041204480344100359044280c14881e80d912a00050010000310700b408025503400041d50070010030750f190590741c040c1004a8002c020b00882d56840307962465003003d204094080d00c6861081025048140c40030b995010184102c008206250700354010585550304204010001090381031800c0b034554451a44541c40c2402d80da010340b044d0360000380362500c104480100c1003841c008007031908625440c12005041c1000e02903820100312810204101300c104007071840b8003c01d507140082890380e44030050550700100032840d00608203100c0d0003040c0e030321301c401d02c004182d0440e24981310140d05080c00c8064041d41d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 165487625 1250 165486375 165486397
    0x101403060103061e030b011d01030b070309081201031101170f0a021c05061203040e040f02010e0a08030c0609010b010921060203010f080c100f03091a01150909050c0f070305 76
    0x1c3c442604d25104400402c420f6a1061384d0b00311030303a83c8441d80c0300014981c040031111410007030390040010030150040103802204c24a00446c05040030f0702c50b44606d03484050100034190100004000344260054141000302003403812020351403c0e61201640e82101510b082c05600c103a5000c50f00200d0705038100c650481282c1416200100702c02c034400300405046a01c2d034000c04080640b0320080c80d0100440d003c2d07481591710414581c4035a2510140e03c01c1c0340380200e05205110400320250f581c0d0001c0c900041058170000c1d6680c2112119071800e2180c05041c12209a0406221010390b0380c004800c46c050760b05580041e0b0340e40c1e02c2e081e500504075203800c5000d1301c3c451002001142c00d40030002603c1c252510f50040b500d03410b104c40d0500951a4075840d180001a20b84ea00b00a0203511075041010940d02403045002184001106542c1840e400c0e48845505ca03c0080d1000350607400c40e85410092080e1141005140350009841c06207120b4408000c5803902c1c00070301c400416002d141075070324003001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 165488875 1250 165487625 165487649
    0xb0a090c05040608060604050303040e0a021216020d08010f0510051b0607170105010e01080c0c0d051309060e0112051603030c0b0901180204020903100905060703060510140306010306 80
    0x3241801505660007406510000b460241c0080e14500f800e03002c0300c080702c0002c1c0055140620b006203242858102815180c80141c0821850842039072031440705000307000008103000301500e03810300a40303062481002c50003401051401013024682001c00001240c00c10b540c0e4103001145120100c4035131058110210306c24054020003108010300082d103620a41007922010180301c80e88070f490321144402d129050005803071011360091548941110b9421640d1410b03c54100303031303460090a0801100d002a03030001240452120b6482c03100e160840700610081d0401c1128a0402e03c609180440c140200c0f500400c01d02419001c00004100303030400d10400f02c0d40c441849440e443c0091044035020000d80e8440d01140120340196410f100e2903844140e40e10408030000f00390740c01d0001940006c8842545401600c1c8038901a02003401400c2615100b4409800c051a1200c0301600700c80264000780e000b010b40c0f0883c400283c5c1c010b070703100d205555140c0c03540d03071a95502b5004030040d00403908481c052200d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 165490125 1250 165488875 165488891
    0x16080301150801170d03090c0e0906070806040603051b120706051201140d0204150504091a0901051b03061c061b020f07140a030f0c080c04020901050901030b0a09 71
    0x10781e41d04268080310081d910010141d0fa210300d07000d45252421024200e542100398510b081c01e0103030740400282882003602003041551105904041c542c2111030b00e03400d0b046202040800b0794041c1c3d42c507600010843d010031039103066881d05540c5400c42e1032050184019274549400035658030104c0048800514112482581c40c0c0a008000d90019034031004501400800418030418203601e06d0380d041400b82c150036610b409502004050700c0d605070800030b06100070701c010440d9143e6000d0061018040c1118440e5012020044078202100a03d0380249900d80800d0004500403104a800044c243c038046949945803200000c420b00c1d8002441ca014903280020390301048000d810103402d10881100030941424511030a84e15400510100c1c3c107107400140b802e100e1030700e000c2e5a050035488043c00f03003800b82e80c0302e43d038103e040d1451140035a0500f10091041112440070001000e112509480a6050032130f480000b804a02441c0c26030b505260326201c144009890f40b0141030000e010341c0c081401121 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 165491375 1250 165490125 165490139
    0x27020402091c060513201206010b07050c0d030807081806070806031501060503390c07120b01031101030b040c030209040e0606060f130b04090f24050616080301 70
    0x442c4004446007401e080004d95907100c40300000784039580003500c041d000d4294050502200c000743c0e4085501800d6510000031401d81040b186005c0c0c040700000c03655034400347c1040c40c03038aa00d030307400f4a101c3c400003c9880b0000e03a100702c0d0a60001e0039801c0c41146500d03502518805040d500c030400100d84031351030412280540c814126405400150103603000c0d0301d801140704000719424020840450400c1010030600340080c1c00d9a0040701d0103812080f958070085410501e220001000400ca40b034010940311110001403001030700400c420908540c9022050741c811007907030702c1444013030060200412040c81e141d00075000310b13810070b0000b0420003117000e8400d0060001c1d0019211140034074039000c450f403010395000480702d001e488010700c05030500c1c82c15505032403a80c0c8502610800003031100c00c0040d00c0b81c21140644040c1040040101e11040c40c000660b044400c0300f8402442a02c806413041241c0c4450108141680c03010350b03030266245900342000e506100840310041c913650001000242031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 165492625 1250 165491375 165491419
    0xc050f0a0303060b0315060319061d01060206070f0c1106070606170a020102060c0c0a080c0303071803020f010e030c0a0306060504050c07080a03090f02090a050a0c032702040209 78
    0x428402d880c00c101c850389440d550b80c1180401c42d400300c2e1114880b0820f01c001e1800f2400340d81d011404516044640132031280c00016141280c1c0804000e100e030300d1302111940341d4401c0d0305024140b14401490340380780908006107100b1200c1581014040003074901810f01074842c03014040c7e000d018102030764132a41403404000800480c4101c50008802c0307903410584101c00310305d5000540c0c050b03004081e581c540d086110290b038000c1d4410022441401c2004c400641c00703c0107003d40990700409541ca903e81041c003d0203841b80103100b619803201e11201400141e95a500c54003002d030382803914082e00c1241c5d2020a103040041440d16910220490002040010350307003042e000c0e01c07001e50342404a6242c0418400c1c15000300c03400100702c0481842640015442580a4100716005401c0000c61029940201c3c05d000310a07151850b41036210800c01c42034040034096840281c0031031808000e40c1048000b161078104220b00150300d44901c0e19000015980c45806a5010240003001e85214156000100c601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 165493875 1250 165492625 165492643
    0x302120705030435030a0605030706110705090106050a03020307090503010e01092901170a060203070c0506062d01090503010c0c03090e0c0a0c030c0f031805040615030902010c050f 79
    0xb0744e641010210210745042c10b1300074900003011400007580e450b1110440d010ba080102188941c65032900009444d6504010140c02005580c440310426094001240e0801c1540e03040b25024040c0000100700d020b0780070048407901c10003441c0c0140c90b5120718078200c8000c00258800c41d0301d0b608040e19450480c1c1c042d4006010588505031240c00c0d555016101520904100040503400c104040100b0101e0008043d80a5413401c0300c043d14281c2060399141c40898006554000026041828000c100700003040200d81051080b26030182007030903644034010980a0301d800b04203052641d44403c400d43d0042c0c2612029090040092010b4407000300c0042c4110110081a0006010440300061552070802000c0c024406000078501c1e04484a400384c9032101d05c00011010131080700c032a0f6021401e85282010820300c80d58907400242405001c20002c61890b4000f6846580307008810010400c0101c801c5280248030304020070602e0150005842074000660b01078014001c0c521034a0307401f0030200d9443c0c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 165495125 1250 165493875 165493883
    0x50c120c0f060609040318090207060218060723010e06090f06061009030303200d1a010302160f0c08030f0405030712020609010e0f040609051e0402031b0103021207050304 75
    0x7510406181c000b50785a50075030b9500d800c000c2d550003040109106000b880c03071100c070030007002440c507654001010490f400700708242e4941d07602150200f402c400380c81545030b89003811100c031400e000d865114007040301c05c5601c95648805403003980d007244c07502c290000340e00a0380c4e44080c1d0f2690f29200c51441d41710703a10085074941900540f00010071500d44806440048160b540e256007056045030740c01d600600030500b50340208029101c0e0b041401c042c1c1f2005109884039014041011080071055180000b550402070b418140144000c5590800c1c1002d220314898208035181034118260406903614079154004004034000001c9240380c03000302c1c10042c0300b00c410135004c0300d10b03107503580d00344c0714480550383e03c000d5105008018a5840e58070402c40c1c52245072000707041c903054501400c0040c00f1559142c0c4840c2c00035845904200141c0e2141d00c40d4603103150345c40c1405c06245800c2d400a912005102501d41203120700040c0c1c92502c0e4420703819141d00644613203903588541030100c0003402d60382045500311 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 165496375 1250 165495125 165495133
    0x307090e0c04051006020a0b04061506030903030b09060d0611070503070b0916060507061d010c030f0b1e0d03050c030a030608060916060302090f0301060311191410050c120c 76
    0x110204d0008000f2012290f4a0f07000c0c1c22071801756a140c10f84020040e000b901c541c1c2d280c041079040292519901001090251000038446c161881e0103030a0300c0c503240300280305100480c2000342c01d48a090b044190140c0c0518005000c101c428130790851801800340c060800e02c00401d0300803c210846040ea801408402c04480c003076a5070b503036001c50340d1031030b4062000050401d000c403100190320b03074121b0b403001c0c0c0d034442c18030309c1c040404200d01d070031210080ea0f00c200190711a001030701d03400c1c01841804105242a141140344100100c0c1c001c14803803540138140e0084025200306800d041c4540b050301d89061054094a42d034071140d1400a024020b14000d0201500420001c0b5900010004481030f03003442400e0f9603080300303240140c00d03070094002551064004064200c00d0300155000e101d00f00c060340c454254541c40b650004240b00044a5648036045d02044101c42449003e40400011259a100f20707885604004000001c6419005624000724240308082c41c280c001e0300800003601c00999840221 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 165497625 1250 165496375 165496381
    0x608010f1e06050607290a06060f08010b0a0c080409050c13150e1903050105091b12100b0a08150f0604090c030f02040608120406020d03020f090f0307090e0c0405 71
    0x28080b01c80510445034000002c02c1501c0004105024900191000d0619400b10343c0c103c895820103560308503040100c040c0d84030014050540c00913400722240407603280c411400d41c10b00703807058590721661842600f4411100c0c0a44100280101102d002e00002c0000303000c203007440c01d003c50180e08038000d034081d04003001a001c101409140c919441d000502d0781c03144050315120051004511000104a180030026078020020138000d008040c054003040b0003e100460151085881e01c07800000c3d0f141c411900c40c1155190031000040c003180749165800000f0f94078924400041034881c1550120215000c0e0114840041c404400f9283c0315420540d40401680e40c1d04003003004464280000412200300c1040500104038000d50155081c0e2014000042e007507100e000c40c600c0c105a010240d42d10040c00135040c052581c0c14400c5c1b1707a119006060a50405008024258003405a540100d001c1c00c4e440c0041e05096504003e03e600400b0000c504105406014a5054807040c1222600340030780c1c205804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 165498875 1250 165497625 165497681
    0xf0c161d060d110411120f010e01090e0c15130603060503070e0a1d0a0312060b0a030207030903060f02070c120f120210050708061f0e010e03010608010f 67
    0x10203820034009500c8409969a204105600220a034107031540403a0b1a40c00c540398881e8490449030400e843c245076241c904500550840a0b0014500012003020b4401080f60003e40c4250506407091450301103032030321801000b1440c0186000c4900c0e40820b480301c1c010070b8003080c400204102c403503040e000b0150302e403505010340035154144200e83c1c041d0b001410800441543d00d01058102e203030500301081c64910400500440e51088080d104590040d0000c54201508500a00c038501c110301d0781403050328601903003000c640c09440304804c01e03da0001520000c06102d111040055680980308010700d003000b41c00b5400035081040c0c1201c400c2448480469109800d200306613000394020f016400c840f10760380d03442c0a90a96601c040c801c1d8407900680c0c9500007071500031b451090b034035541c41d801d082c641002005181074114030712801800419200c013094590084414811310007c0c00c00401d801055000303c0d00400b007941c005001ea5180001500e4084008e410141030011a0180c8400180c10451 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 165500125 1250 165498875 165498899
    0xb090406020301030b09120a030902011403090d02070e070906030c17011502100231080303010605120a0506010c03140c06010f0302040b102f0a0b04030210140f0405030f0c16 76
    0x3052009090180489480f0301c1c400c2e0080e03007009106240501032400c01545637501034100340d0b00a1301c5038000780c008519041c1d041013003c00030b05140c1020382040c141070074081c000d1f43e5140203242c10141c07100040f410490151689030030b40b022005080303149d07694030322032001d581e9641c1c1c0e41c450040c0241c0058500a01c2c40f8002d5036680100b668600800141d5024013800103000c035200070509556480c400500b195052014500a04881c1c0707079142e0303450a4018040702c00794004c0001012510700710034031807035076408501413200f07035814206800c001c0b0b5070801c0703000d050160164a0100c1d100d2600041042821205e801c421039100380e074180442c036039450402001e02c12501b801000284e0341c041e044d030205200c01c503030314040c00b03a11824910380ca000c175002414124400e07010740304c15002000b800101130381082520f03100a05540d00300441c1d42c400038081544100a0248015908403030003240c00c1c040c0510031142401040c00d40340340d8917120f4618481e1035018064400c0718800b0700d80800a80c00c50708035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 165501375 1250 165500125 165500143
    0xc0702370303090b09120a0303020c060105120a151e0605030d03021e0a1407050c01080609010b0d05040203071d04120503011404090609020307090204140609010e0909010b090406020301030b09 84
    0x62541e1200c942004400d8038075805c0b40002c594020f02800042c030f112038041c050610064082c2d6400340c1d41d04c1c1d040c0d036201d1402d80103070b02c200d01510a07180480082200441d00300d05c01903004006034010207100b1500d0303016003048a8044800007141205010301000c944c0700004468055044e1142a401800190204d02a441d4010413202c02030708031000007103000e4000c14005496041a00ca2402d140d000071616030402c500031182944212520031b407035a08002000e41c042800c03281c00e03d0541c1080c01210803405420076100c0c0f8580c80d0000300e800c564060142d000609000004c44070713918001181c0e003460050549080e0789031001180c0d10070130144610300b12416141c5881c5c1901c610940c071003e1100a1141c0030081e11000d68510b01940107a9060010308024080300d6005a00c03542012140c0c0b00c241196048144952410071a58400d030743c0202071003407800c4040310f0741d8200380d4800308124003502e1200403807a8051071802c10002002081d602841c1680d005160882071651000142560b03040c8031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 165502625 1250 165501375 165501377
    0x11514090103140a05011505010809010903050412030e09070201020304200906011b0b0106030e010b010c02090403030b03030f2a0109050a021504051201140c040f0e0c0702370303 78
    0x3001030001c02c040c001c014418540b10001c032030505199849590031950420301512410030012000c001e1582d10128043c2c00185010007005042d04030341e005081441588030703500d8044801440382c024075004541a0f0352402e00a8900703074561a00303100090003940120303422111500c6090000d412040b03030030400511076402819850a03a2924401580c84188007100122108111070b5043d00103206184003d00809080c4c8020506086800105081d50152390b44541040300c43c0c0d0f034050260382d404607107d802c00c1c0c15040010300d40305500b012034290b10508400c08a1004001901d04002d01101c0070540f040c0c801111041070080075180041c2664008240a45260700800b5032101500d4880b000c40d003401c882c644464036043e81d40d80070030142801c407011141c0c0c507555144800242c040c4d1034030f00b550210358422014986400e006024400703a1007030096481c2e050560b80016000021501180c00c01d54005007070798400101c007840140c0c142c82c0400d20014041041c031420864070031079103503601903a501d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 165503875 1250 165502625 165502639
    0x6060b070506190e010f0603020a05010201090b01050d17030405030a03050f0106020a030e1903051c050a08010b0906040e010b030402040b091909050c06030f01060206060306010302150306040902040e011514 90
    0x1680c01041e00c80e501540490880c1a44d0302070302c101c076000074414100c02d07685100300415410328500403ca056007203a80450306590404101c8000212411107080c1174907001c80e030807191110709081074400541c2000c280d1109403000000c0c4014003d0010150201c070300710341e8040c03145541e54040446105000c2c0300321800342e0721600420b400603000e5011002c1107030015007041c1e90814103480d043c005c00307403d84c8150780640015952210460507500320084140d283d0518901e001d1101d07e0003440c144051103480c0441c0c0740428511a141d883d00e044600500c0100341d401d1075075840300080826940142c400b20300c100d2070606c034181039040c600b03030040c410034281030400390613451440b000003e0300000b0310444060084e100640c500380d580e46c02942c0500340380b4012030072a40c149580645040c2d00036203140e109034009001040185c0c1c03500380101d01c0b0001d04400e240c4070b4440303001042c09080c1040b00258800c1c00c01000070003c490541c000079611100380b025582080d581d03500001c0726807244ca580345d00822 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 165505125 1250 165503875 165503881
    0x7120b070e0114030114150a09030b090106030b0c0904140903090f2b12020f1002070305090a0b09100c20150d0212150a0611070317030406060b070506 66
    0x100803110300d880710006041ca200c03e8429490001503560090300b189044030700d03640041a80341000d08403110300d22103c0745000c2c54107541c403101420904151000070111841140003400d01c41082d00302100659004100081c2c500f0000c8050380700d03030005d4070058003075403405136244582d80007581c0c0030b802000750f000511311b4032148405115039078000050301c079001040000001c003204807190b449108600c1c000003504c030683e07017850001e0804d01480018030455000f5164401510030103c0c1c0d001c4441141500103a86200c18902560980142c0c40226840402e080300010240911801840211030450b009900d021ba0404240e44240c144036003e003c0180c64188007030a0b0480c0b017462920328000816010151040d110b22000a901c2000c108aa454021402c04603d604000400381c101c84010104082d1aa0032008910000d01e03910801040040c031969410881c2818480540030356040300720740c1c00312003030854418000d1340290b500b00c444502e04003002465001030002e450180b035114026160b90341b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 165506375 1250 165505125 165505127
    0x4020f090f0f09010e0f03120112080406120b030d0e0109090c080a020702011b030c0501050a05090a0f022205090705010504030201020d050906130306090506180312100510080907120b07 81
    0x2e03402002544a9907a401d511100c4d000d0401c0b0700d40c16140f40c2d04c000e43d0340b10711420380d254a041047c0d018500800719a20040e00140740d14051b40c041c2c1d011440d01d070503c040f948000300c000c3d00c0380000303030358150042e80c0c1c0f40c0e0002944100c03003c48901003a21400c01155840c1c183c201160340f4a080d0000182c50a07011135001407664000388186801454100c018046042d00601c0740f1144007012004075280710000c0c0e08002080c0205503101844200401c09443c001500d0782c0c45919925000300480c051940900455450172400102c040d03000711b0740c03603904800044060060038142d8404086108448000456600c9801250141c0f64107a01414102d540305170140c1e15504043c9050340e10020a00100d10480743d6030388004021402a0008100c0c4049402c140b82044400351003075010070340a03140074444210000c11151469040d241d5510320fa50f840c0d403103062480d81c5401c610350080340001c448180070b91221080b07004010744020794034030036a00e1714030003201800c00000411220308003000070456 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 165507625 1250 165506375 165506401
    0x1501090308090d061803020706090608040f050f1009050709060b040b03090c0d030c03110105060a120f050303040303050103020a120b04030e0607050a060c1704021e12011404020f090f 80
    0x30603000f03094601c00d0340003599208155081c5d0004804200444000281850b50400514009205504201c18210708095004200c448001c00c040c00f10608001000100402084039070111481a0117035900d04a0001420010f85440e20043d100c034072854801156541142c400ca1040b2200d0301c11040c0f50900d40004129140c10091000e5014001c001c1c003c94252202548950214800c0c0e81d601003001d910725014000086240d03810040ea80b40100300301240c0c441c20030400c1600c001075844038003441c0710b190014080c074040c10010407900010052104041d05034120a040e24401c44000d104a41c27034901e240d03520760142002810440018021801007401400d02c580c400da4090511881c01a6945a00340b4003103402004079a4141d590008051030b90340039056014949090028100074281030b0002500d03070354040306043d00802c2c4000b50144907940c03039091203004a4600003d000c1c240b41c880c03c050050000703c03000ea00410b54200012090b1a0010f00c2e54801e080c0304648802079120043c0c02802c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 165508875 1250 165507625 165507637
    0x41d09100506180712061d010302010e0307080102130504050708070e060a0e06071505150f04050c070c090204080d030506060d0905030d09110310020c101505060301030501020a081501090308 83
    0x700c2d0805901600c200d00c0c9801d0740c800c640c41e44840c4854502080c1d13140c1150941d9114407988a26007c422491003400481281103d0702440c0c0101380f0a590400242091440c0d80850755035840018405280d5200381c3c01c0c5002c645048800704107503078542d0001c0e620f0203402c80d00c0200103180301403a404180742c09000b628850b061454a0440c1903990000f00705154800c0c04141ca00c054080c0c07403403418141e1401015481201c240700d01c009000701c1d9012894940d04902e0a5210710385400000b140011003c5c281c8081c550072080301d06034141e407035501d94003d501c40d000c0c02c0b10314010010007401c540e000b402104e000380320260409182c41c41810000005004071a01204c10b40070802105411048038007581d2940743c01554500f900c4e1140c0740801d40780800104001c0c61f140e006101110662402248548a6461050b4081540d0115483d4268090151f8110b19072103a404000070060050560281880f03807000c0c0c03078010031074650640c1c50031009400101103000501c0360358103200080380c40000c4d0131 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 165510125 1250 165508875 165508879
    0x609060204090204140406150e01050c010f020406111002030103080405091504021305091f150c02040c03050106020c09010b04060c020f0a080a05070b0406080a0e03120705041d09100506 81
    0x8200340c0c442e088a000d0740d2041d4040300107011465030035026440c003486124000d2400490f255001400048094220603440114905106000c070f42c4c003403080d100313401c002c20702d410b12441150340c2c41d2a1100070304681d00c0580c1c5c4200900c42c0d4594988803000754402c4a0507260046012802d0528000c100b040c0c504008201644490b03022010300e2180c0c56034005005030440c41000b11031220b0074a41030282c448002002c0301400c0b810a260b114410020200450654110800341c180580e11039800303652f103440302c007002504186401d90310024240d055009c98141e4034550b0a840c90803500c203081240040007030080b08601c40c2c04102c108041800350248542052000d0703e038003032151414000a10014a942c8844031681060110030100b020901121001d84130b00310780541810300b0044020a1110004c015020840da80e02c01025111820011749a5103001c4500c41412440c0c030301c90050007a00036118802c07805d800000100908550205068403440342c0100405030f420b00e445c1804050900030f0142a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 165511375 1250 165510125 165510127
    0xd1112010b0901022a090f060f010203121602070314150105030307021807090b0d02030402120604110103050414100e010506101e030902030f07051507020f1201062303010b030a0c0306090602 83
    0x7409506c031525130f144220750021042c1440e00e42803003401200d81003c04c1850441d0410400440703d00c2210351200e81003140b054940e0b20018280707605a2a101d000d410103054440b20b2044081e42e00c03000105040404d8404c050411141d9071401407503524050172400075440b1036240f401c8481605c4140302da5500c48024503002c1c600030b6031070302c001d103103540845402c3e45e030b0070b8001041005600700f040300d5108810401004294070314107034540015030b100c1610304074101500c8401160502c07a12003d41100a007514096400c50154064200010301c0e520b4109140c1d54203200c002051440d0261104001440ca80c440c2d21038803080c14160101d890300e0308002d80c10715907503001c444050389040018001001c070800007081e0260428040200c0d12515216802c07001d6410481000144c8803c03081202c1d0a0080d1851002003c2c0060002c1c0500f44c50b821110401c40301c40104020141004200300b0920026002041010386400c24513490361212140504400045541003001803040ea100900041c0219401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 165512625 1250 165511375 165511453
    0x4061b210f06061106010501020a02090a18060f020309070621020d18151104051f0c020907020c01080a060b160c0506030406051504090b0a110d1112010b090102 70
    0x1507070440c0c1564002400240c004901a000301c0002c001080c0540024001400c5000081d80045c01c98900103140204850b10342c034101c104440c01581c0b01c1d0b421a4400703020b004114101c08a28001d4000f01c5582015101d82e00c0300040d4180140c00824484640503003104541103408000000380d07111443e400d100f2076441d09003033800703000c01e804621414860000d400350310054442c0708056461100340c840c020b840400c0104400d50b15200c1034080d4030484841c0c40e909440d03921007076a459240300300180d04a100c41c001c10000c59404505086015003d8032003416070b44501e44100c0803186103004100381548100300e080804e05032031041c141814451080c0c100080e0b101c90209505800c240c5040366a15100c9080c40a0f450390820840c0070554140c400700812402c0f41c441c5901100090804000c41f5647c001070500b148400040310711007010404c3c00e1040c5034808103e01e00c05c0d40000c4103207012001010000c6010b021070304c1150322060059008000b240d1000c80c003001010007860360034500314241014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 165513875 1250 165512625 165512651
    0x130302030d0c1412090d0f020304060807121d120705210f07030801050f100c020418020a0f15021b10090e070e030c03070501050315040b150304061b21 66
    0x1303124440c051442d12a850401c03041280c40c1002c4000355000340f202120918020715400004c1c0c80440e400c520f400d070620349a030507041e11001d41c1c0d428103088803820031090ba0070301c140c007080d040800300c43d040881d0a01040b05e8105240c6004060005001d900100c07501440c3c0d028800050444002001e03502d443e1148940402f10150f209074411800320700f4910040240d07203000800365502000585105414941d001c500418034071000800a04c80c581e41d9409030301c2c1d125501d002c2240f25a020b4116078802d5155000a078500c450f0b48a945040b007160000131850f544003040b002e0b031030140d008800c19100c801c44208800810030a80311000c201641c0310004a28a000d80d28501412294036a012550615018035003020b0800325030038041d41c80443c0c10004c40e43c0c46404c481e4000194207040700c208616400180140c510303000302603484100c503620340131200200c8c002180a0b0b841808200f2041301001007108561020321420004522039141008401030300c4e4101000f00711071b000000a0340130203122 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 165515125 1250 165513875 165513877
    0x52404050d030810060516030f050c010e03180409020d060e0102070204050a1406041b14070807051005090a02060301050d03030b1f03150510110106150804050105130302030d0c14 78
    0x1006500182c026804c2c003001300d40b8080da1501400c0d4a1a109140141c2901400d03447c980d2500001d007017085122080c100180300c2d40c2540c005901c070b00b000380031410202d0407840d9a41c0041d0202d00358000542e840c00c10603e050b2003140d45065000d0800304001c03406841314002000c07090081c1c0c409540030041c24005075640c0c402c0620581500d000064507038621580c50703011000080c181c0c0d00075480c00004000c2900c1785024804880c0c242d203018480ca807000103c88042e801240801408010081620f204100010981072403000d0014001c014584d21a030007141d85907001000a500302c031003040180325a00b05015140c011a019060100707013101d820000c00d20300d16a80807849442c144d0344210400c1d01c0d81c540980d5442510a541005440703080c400052408482c4054a0b0244440005000030041081d0809001400c0f10b0518150300c1035181000341401c00c0c01c40d0115aa540f80c500002d4007182c50000c0041416050b84c010340c28150f000400b10000c101c1510624140185041000c0002c0c0e1303644 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 165516375 1250 165515125 165515149
    0x20c07031b090609020315010c020f10092c070306061b02060903060a02030910020405030712021201050a0f0c02010212060f0d0203010f0e0706090b07021504080f16090605240405 78
    0x1080041c1d4910300107130038400751f0344500c40440c10055500d4421000d40d9500011141b04041101c41c40740212048000340d0f607041031640700c01d040c0034110210580e002c0540d43d9031102c590103100301085903611790340120308a403e0350043c100030440d50b1010304090b0000a9145643c2071001c1c1030360345800030210000e441e007071013210000d403190303000010021043c10074031901c00c241d9210751003942000d0a042c00661a41441d000310800182d00300c0840003507540b02e07075100440b8074040b00204000e081040b9000c0240400841803d2411304103003100724031600c1442190b1025516018461442e160344082208903118001c0c0c09a00000c88484000503903400e00c6484000420150001095152645030a0400e2f59690080061004000042024041010031a5200340d13040720f0b03411035003584694001c082c1c0070300d4000c80d001d0300c0f0307202c442c5500c10300004a2a10080e800b0059005030b6a0b51500f220584200d40200d6400000c0b01425180d41000c00501d0106582c1055005060580310707408540c40010320 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 165517625 1250 165516375 165516389
    0x5060c0705030705041a040203150a09050702160320030102090402040f031106160f05030d0e24071d0f151306030c051207021e07090b04020c07031b0906 67
    0x504001c000925081009074010001540e0501c81800c4141900540b12400c4010314021500003000a02002c0c00c03601d03d48041c0f40082000d541c9a46601341103005001c01c4440c0d0717000d445910a903500c0801c1c00d0714507000303d940c011194140c1016171040e481c03054582018141e00756400340080c0303000e60350b03d0018201421556090700003d5140d400c200c950b1000d0495a00d002e011308014040116040050814095801c17102e11003240704186015441c52258400344109540707171000401c020b5101041c0201d01005e80516203200546606c10400f10403402d0b078042c0c0c0400e81031402c2840c0d41d18134192108170211300801100820410501003501000c0c442030340c440e0b6003000030f4211503005020390450050409440c041003001400e0402a096104040d41020b12900d45000258002e03c204001c04290a08200d850410380709041c031984c2c1c40150780100d002c01414990400f810b800c16200380c45409841c0d8000742105071864031307492020130050f0008000914814008030307074980c450140c44000c0c850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 165518875 1250 165517625 165517633
    0xc030618080f092d06030c0c01051015111f0e060901020304031706030a0311010b120607020f0105040203070302040e25051825091a0408070510020303041b05060c 71
    0x340d010400c80c107280440030307a07201c10460304d035442e81241120603004110080d5191a41d0b6201c2c803140031200d028507000b860044d824642049a43e4150341030a00454100e503250300d80090072186c060301c182011071040c041652243c4608444066074124965400f20403034800552005010a1a810b00601322003150260b90000280420141e02c144522000d0101d41100d2940e810940002034483c0c2c0c2e41070340641009240d1340d00d94031a80c420741c08203c0c80d11004103c079002d01d2900441945a00040324030f10098060018102c840c8281805181d200d940e0040180800d0760865003080000e124220036496688a035900c69005095540151007039030f008030701c1c0a00240d29107010402c0800310440316640c1208904180f203112462400c07150211001c51120201c6444007003400c030350340710281d1700030011030396141009900c05091100920554034a041600d98158a4100b4080d4007503600c0d200c0c100580c410000100400d40f12a2116415002c40340c0b007801f2250350b2400989950401003100041d604 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 165520125 1250 165518875 165518887
    0x17031f09090b1f0603050c22061103070b0a1d06010b0403050d0f08040f03050c010f0203190501150806030a0c090c0206071817070e011d0f040c030618080f 68
    0x41151003581c807200d10200800300382d01c2c000402510003c03a01c101c3e428991a0804141e080c41c1d01c00c180c3d440c00c03088100840a041c0c0841c2030b158030703a84d21700c6400c0c046205284c0030359889401104031280b036600321000072a05d8540c1c60b81040102491405007107405a0a1003480d134401d42403003c00d000300640003e80e9203031811820f00b01c0c10305040c0411001400844180140c9042d000b41341d0355803164003d09401c414031028203050343ea80c418203c4440c2254649001d00307000c01200c4c2c0c090741c000c24008440700201030b44200720038101c40003801910035040c0c081060180e000d10a40d0140c2d030040c0040c0580304a4842a91569404000c0c2c2c0c00c140c040f203817941e0811030415070400c85039910524625080050075503070301e140200304800f030040b40b20181241000e00b80f20901001000300400450703c5890079503a650040b80400c0c02d03200c0c078a920520546000c1180706400e02000c5025035000020b041d04180b450f9184001842c80c1041c403411025401041001705010740040c0142449038102d05076906 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 165521375 1250 165520125 165520133
    0xf0112091415060f090415061502160e0601080105060d020403020310020a020f070612020a090506181906140306130c080603190807060203190204060513050103020717031f0909 77
    0xaa8000c0c0004d02890b0340c050850801d50740c01100540281c0c0188050203808460b6050401400f0290070000c5c198103071204d00460b43e907000a0001c4030150100128015548888100c4021030041d50001d0024403990018865071420300c0040101c0390300502c0051802c0d43d04c0c0d003c0f07400c181c044005409020350104181002c0ba8060109480360710040b8003406100c3d00b00040900100948607501102c0b5a01241c01a606405400705001910000700540d03100c4011441040481c0c041192660080c0380440100e01da030041201310b041602c02d152a078450304200c009a050007600f00606003030788001140803a088401e035030310400c0c00300c032183e40d5201c00525050f024180f4040c4070030300041c0032000c504411008103503002e080d256029403015015030389480710700c1c0003407010b0503400f50f1401e40b620016000805a400c0002070003508004071910891030b545200550407030040403800b51400b10300c08500315076003000c03030011644600542d110001c102d02c114000d24401800d500701c1544c19075603c0468040c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 165522625 1250 165521375 165521413
    0x1b220303120e0105041a07110105011212020706051e160b16050f09090901060305030d0606080115051603121509061203020307120e091906080c0f01120914 68
    0x44109903001340800c2c2081d694074503100441c0780c048103009481d000451000c0340304120301004030058000034020ba5849d001104541044000c0c01c0354080003040400c00310740d00206008048540e20780710241000b0200781c0c4c40c05646520007221001510400250dd4654043c0245000031409509602a6032404103d883c038a0045400010300b404000d000803119002c544044681010040da10140252680c508060152416400013071240c000401c0210700c0303c507a9803100b0b0031604141d46d58104c6990300c40680e08203159003028080001d904010740c9601304002102189000e100380fa06801c6c4c100b07406084001c0300c8070400919404c0303100c03050421520120b4000e000150448a107421001404d60358065520700c20b0790f00040c1064034130310181d1039a03400f60042640c0d2020103071000c4c005140c41d11802620310074002d4509840782c07503c000880d8a0f54009250390007540090001c012404070305005607070040b170491498040307075103c50381a80050100c500401817142c1c00740042c102c401c0c2622140c051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 165523875 1250 165522625 165522641
    0x60c030e0303040b0a110c03060115020c01030b01080c070c0504050112020102060901022b0e0303040f1416090b1309080903061b030610110d020c13051b22030312 71
    0x1c00c1d070043c40700740302c0b94404600300c0d2005405428101100c840d40003111381002c64160141d64540540d00000070300840c0720510800e0400036500f0f4a000070002801907007140d103203000440c0001c81506c00210549207100080074000c0c001c80400209a030b0301c10000781910800d0708036201c4452048540710465070108101ea40004440700298141000c8060310403011001100300543e6691030100706108120952000400c402000e00344c9680c1d260904000d01e0580d01041c08494030342246030b0f2004020f8000c90346e4602d002c03000001c01e40c400c1c13402c06984d02400d15400050f90042d01c1807402070320340304c0c6481002400c611880762142c03248c003c50201810090700511020780020740031549000302030304404a981c40b100461700c0d145e10301001001214003504801c49028a4880c1c2100e9000b60b580000d0343d07440f1050202d44404000c1403441c030b50425213800355a9041d00c25549010300950340207120140c901103100c1124405c0408145100d039001c010140d109402003821004119000320307450081c102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 165525125 1250 165523875 165523879
    0x6110606060702040207020114030c07150203070c03030e070819030816090e0a060e10030b130201020a0f1403041d0106050a2f030a0503090105060d031b0516060c030e 73
    0x29480c500380010030050300c1164002845240d001883c0000c5a008105480040c4841d040c0341d0b0700c1c0d00d0321542125055001180903035803101d031800002404081402100c0c801c070401c0d07071541342164940c0d070150041c1450366240042d900440d20301040464040000c41c250111140d460504603419040240c40c2c107034060316001042d80030001e42140e994000d10310008903056110301c0b10107036503030600c1000240041e401c403a4000510201307000e55582c83d12401e10a480c0100100041500c075120243d00c1c400d001d2900a0140e0464050b48001c20542c010120f289402410510110b0494281c140e040d5446500010003101000b030f2030a11030721031000b00364007603d1a030900d01e10f00307590b1020150104410240c059403100e10a4940b20405142220503c2c544a8600480e601c40d075072100080c0c441c2e04225a400c2840d8038160006000d890501d243c00300158041d103c65000d040c0450480403000300a400907945072289404002001a01c114900000d0450382e5403441031004516000b0040b142c1d80c0c0c1c000e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 165526375 1250 165525125 165525133
    0x12110703080a150305120711120c0f010203091c060204030b0906070f020c0105031602210901021501030f080309031201030c053d020f0708011d060702070302010e060904090503040611 80
    0x80700046000411106d815000da4003e0340300c40107480c040d441c591100399013503000511075504a81443d000101d000b032440c0c040b2841418880c100340126a41c2c040c80b01c0d5903510050050110458072a542020a00ca40c0910b0300581361a4403074448905c1c520050b12074100f280d001c1401c0003240c0d82d000c0f06c041b1010103544050301c20010440c000a1460001400614102d07101c40110700c0550300801030305440a00c1c2491400001011080024040d0420022117026005a0101801700516220b1441c1600d40c04244c81d543c0c21080d0300c4e40d9126070070080c50120342e40310403c1030145062150105900946c03048507840f03c01410403081c01100440c0141491704034010410382c1c5000c10140f09003044810b15130403a0101c000c51400d04a1425040c3d424a0360540902c0e4804030350f02006401815100040d2449560400c0c04005d41c1640d480048440300d005801045051005611440b45100d018134000d00c6239040c0203c24000a00701c5040d620300702d96662000804205858020210440070b086c918050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 165527625 1250 165526375 165526379
    0x10051017010911090718030503030a0e0102040305030f03040206070b040503191817030405040914070602030f070206161220240a060b0f1804020301140112110703080a15 74
    0x2540d54000d02c00c00f921038000070001682251049032041050800e001c224200141d40f410026117a600a86152800360704001d0010440c240500841d003c0b00c0e88100154078140a140355503600d50800303131080b40d000208100080200e035441c00f8107405240076002541da00d1495000c45010f2100d0200c0b42000d1142d03980b10341900c0104420610f046507007604001410714604007980e4290305c0f440e00030b50b46c09440d113080201404000c40d248240e00c80310004860460b44ca503002660399002d1032080000444c1d08200000060902402908800c40b40441103084a00e81da690b0107491401c40a40100040b86103442c0d4440d611400c00b1000450000e6025001c00052444078441d0341c1001003d1480b180074000100352524034980c04440240300f031502072a1540c169208255480d404080ca00481d0076441907103450b43e00c2d20380700f207034100e5150792203003103410b440e5038019140c4080f00c2e482c0b981c2440d9243c405079441c00c2c0240c01094170502c269100141860308502c51000c8440548601620110340002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 165528875 1250 165527625 165527633
    0x302040f0b0a02011a0d0f0519150b0111030f0d0f020a0c030f08011a0702030a05030a091502031c050406140709090501080105160507080d0908072a0b0c100510170109 73
    0x40076100e55001014001100d1160030501d00d4140079005050350291500c0d180d005208500122b106145031089061004c01e00c400011204800410000c2e9840d410030003180c2c5010911b00010444050140f1022070a0141204c88a04a80044400d0b1000c1800071f00395904141d8003117250308190041d42050600b40d418844480c015441c803800107120500002140410340d6010041c481c0b085903c00100d81c2d580b051844024030f1840c040c8544810040901060b01d0003600103c265201d50a240607602291410801042c024100180041e2012580d42c100603008040801d0880c0c0b01d112641c4400540ca40341c0b0300d039081281c405900102c016407403c03062003402c071041403810b4129502ca1500545990003410300a40c140710b10403e041302c0c14601a0050200409400a4912070f0700403000140c3c50790400b490021510b0400080102c00c0420040a1200e2402c0344050001802c8420071203c0303540c210796040701250300c1914006507482401008104140d07a405107007004c440e0601c0248602c400c50340e9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 165530125 1250 165528875 165528889
    0x7090e0a09200a030206030a02040f0e0903030411010c021509011b08090907092106110304030906120f1a030d0c1214090303070b2203050403120302040f0b0a02011a 72
    0x14045a000d60b03140740d120000e6844000d800d001d0b54008100a075241000d040c1d01c3d000303600c140300d103259070210301030300041c1d65800e0b440c0607100b4210b140285203541d48554401042500900300c49050261110300f1b103001d0384548062046810040512503956016003001500d003025660309a600840c6811809001410000c103640001b201600c2d89404c6454409096607020841d0304003450092a002c040d5401107a881002c141090062000300040500c0240a201500c411600540420610441000610b11503e1a0880c0c035440480000e03003092840c0d0854103607220403021804000d000fa143d1485031400b0711400c120314007281403d20031040355035582100c400c42c400c2984180940760144110b20408442222801c900040036a51740742441d203003e0091200550740824071088031925034402c10244c810700c0403040c1d01500c0e5a8101031450307448414181c40503165a04258082c440000c5e0421442805005403045460007501c0b09403100c80282141c01400c0003e0004207420204c1c074454071640 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 165531375 1250 165530125 165530153
    0x1081221090c12010203010302010305131e02040b181e0f010b03091606020d080c1e090a0e160212120105010e15030a0b0a170d050c0c0907090e0a09 65
    0x54545001e6507124101070422086400940e0044500010214100c03019030040d07068034802d80b800c000035281e00351403c0d2011805a001400103010a000c502301c542e1490107071f107200340300400100745088250041804d1a980c00d418100c40c030558400d00c40394071140c6131511010040403c101400b403902ea0345001a000040c42051100b010006c040b4620b210244407100301510100741d48280242d903a04002d55400002140100003505540403814442140c0215a8041e241c0210f2080c560000a584145036000031482136001c40c00a4000607a100e41851103441145800ba161400d400070400280c1040e41090039411030003c00c118070001440d40d002c01e541510005c6c0f8200c4004c802940c041076aa1181007071401550601200304502c0111981203964500d0b015a564444659250b4003007008540b00d090f0300d6071326000a003982984901c11b00180c002804c074007048510b491854170114142071029124080064018182840f8111741c01c0644c81e00500c0640041001c103420752100d0900e10218 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 165532625 1250 165531375 165531427
    0x51903061109030618030c030406110c0a0b0910110f010507080901020717090105070b25050301050a03061116150b09040c26060a06090606020d0c02060d0204080312010812 75
    0x80d4417a06659080007501c0100000004903543c40c2d444223005007043c4446440400a0701c0b07109804002810200503060407150030022050510502700c00b002402038540c54410100520083e5692010303108121501401d010180005142d0600b84401008804024030a0085a004000071000a11590208100303c030f11301030700581391080c0d038004070351034485c1c5403014043e0a500c0003071242c45000c5e800700280aa500001d02461039a946e501510740e4042485880e41c40143e080040011a10340d411861401d4654403140c0e20784000c80354401501544044d040c5d548000c554880451601c03c0d10408188071011286441149002d07605c0b042d40089500075000003445481110102d1841d40d410300a00000403c142ea1443c500580445d00405403403140b01c10188c24114000744641c000b2542d110307122025078034144d40034200d809004141d4003a00d02c882c035a40e400c200c00070b0381c0d800a0010b00090f001c0c2d00c201240651628212518007038124076003ea4103103003001b0810001d40030440341c4c0402d04071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 165533875 1250 165532625 165532651
    0xe010b0703140712080906100f050d03090509010807290a1805120f0610243006170c120a0b01060809120414010503040c0519030611090306 61
    0x100c0022a10901039200000d0540406040134401c06802030180c80c0b0481c3c0900844041e40d80c0c4411040700d0310b601d4416400b0b8025024001e00850424075502d985040c0a4200b0010103650b51021a031000008da010b04040c1c0c1003080140640000070608009000392181a49041c400e0780303403070141d244900c24a440522a803095aa414400c021038003000604008000c98104601041c07443e4464000302308000d0b0a00071580050458214004c19034245e401070000c90701e4103401c0402e0481da2803658180d407011701114041d00c3c4900c84c5015045c40c0016100c0c1c051516000c6450806415242180c01900041610b003100303440c800310005841101b2202101c0248142d980611547c0c141003001c0340107006401030200102e0b0b90740c2c20000990013003c801c0102e81c8a42080b02c1030034954010790007014018881e9440c44840c940c400d00285800c58011464440c180b59100300164a10100340b09080c1035031240442001840002d2103604012210741c040b0380c1c034248a1600294980700011314046000341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 165535125 1250 165533875 165533897
    0x1e09010b06090906041d0f161a0d0e010c09051201060506090d060e0f0a33050411030a03030b040b010201060e0402060304170a050405090702190303050a021c020901090e010b0703 78
    0x5141d401021713410901c17001b40404890203945c0c460320b038511035102460768400d03408061403100b51240b400c0c04544400b60350851307042c0c0c02007600c40d03551320001e102000c064480c850028910360a00c200981210f41d5210001314916000a00234494010f6802e003800f6403419804000540790001150f160300303000c40d12504005103900c1c2060090140d9090300201d0b110303403000c500524000040c2801c8050040da02c08144070002640740ca0010700271505c00c1488400161462808a010740002d60440d10071403500100401c00c1001c00e162002d90340e0240c0021b034450031800041c0c1000d100301c40700c03803600f071000b40301c101d04100040440c0000944001e000d61310010004007406021400035480c00d080c07030b51040d5602411b210040c103d810601440303218041000202e8422800003c4070f07101b400026100341840007083e00c0650080c14018121a45150208070388968190f100000900030401d0420040c0c60f000030783c1c001040721030560425610016a14010b00060b1080e00603500d110344e040c170f440e440c404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 165536375 1250 165535125 165535129
    0x3030c07050f060709060908210a20101b0f0309030e090f010303110d02071e0e041103120414010e210304230d060504080f0d1b0f0905090612061e09010b06090906 71
    0xc0c09039002f074800e221030304441211003c0049900103e20a03003950074032054103801d4444945c4440251140301080001800d00803440c0a07410140b2480e000303003407600c0749010040c0854850082121010301d107110314401802015004040d0746070745030a6400030301080000d154040d6035030b03016000781c00100030704900d5000e62070050712020340500b50241c0c181d50a030800780b800c0d0494080b0800b86d24442e0181101000d480f804600540e4121040180e200083c1b40202005441c20310000e191240c024002c80c0c0c070403424040340f0380c0c2100d210f02000c0c01143c0d518a0444503880c3c1c0e0900340340c202d00c825040115118156100b500c107190490300141c0000d0070f51542c1c900046188209110188400800300d0741e0304110105902c48450945c501c510000b66440c2110100c03040490040050081400d0513000d001504080c2a0f45501240180c60818251203620b008c1d440e00c42c0c11140c40d000b01000e0502c121a0040c2051040d030001c18120090000d0b2040400082090003800b00392405583c442e4000fa40e15 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 165537625 1250 165536375 165536387
    0x2010809010f11030414010b0a09020919080f0118020108011814070302120708060108010b09033f0309062214060106030c0e0303030c07050f060709060908210a 70
    0x90707100072420050300b100c6189030f1016030021901a42c04294541c90008000810300503010f0201c0700a003006142030901c00803400a420410449802015a4402101c0010b04510f90400350007800000c0802800a14406080d02c9202900d9034481d6908442200180d0300074103041d041d51110140035000e00880381016000703010116680c10184020002e1145841c2c041c0c0c024518040203148910999071030082c02d0724400c20581b4180d0014804500402c0700561000161829081c0201540c0009220048908815070002c00340391007a28008810f45040254150030328113414040e0801e0704524105018030f0701c4213001800310100708055140c0c0050518503000220b40c032030b40030120940c541500070b03840c1d6881909018220110345040100201a4000c8040c07800c48900180150301c1d554a03404074001c50b81200104944d20b10605403028980c1009004440c4542010358402004919040006200d00c03680c0d4800301c4143c00407420b86888680c0200e104214040140040d03a4881e0a0701c022504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 165538875 1250 165537625 165537641
    0x71205070305070605011511210c07090203010306060f05010f0f031a10020a0b01050d020a031713080a02010306050111031207120c0509090604060b1602060d0c03050f0c04080a0201080901 82
    0x403041c500000422465414501d070321001e0569039901c10508059241155220031060b02401d04811408031212001c02e081d00a0ad44260154280c4070000d41d184112800c0c0c0c1c0080c3c1045412035181c00041c0a440261103811006103800d182211121245c0540600301401004400041503160481e1400300c9000340c4618a000c3c902500709040800d4180c0001e4549015550844046600600014041c9000014800b202da00200180c103001c0c950350b0307103114101da00080300041c0319040c4104190b0b091542003410040c0b40070ba0140680d40031502c00102101e184d0f4105c141030018035000b0414111001064404500012072121125103540005644a110113a080317001c281c106102c0035407141d8818003912505400b40c402d0201c0307403500000c10050b10154000c1c51007090090210485943c1141108925a2f0000e00168940b891003402d5000390764503417404502080d155014085031800000540d5800003490440c141458208903c1d04e40f104c105a401078100840720b4042003001500f98082c0035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 165540125 1250 165538875 165538883
    0x809010908071202060726040519050703030809010501270b040e030d0e0a08030415020d02070303020405090f09060604020f1c0e0f01020c0304090e1c210207120507030507 75
    0x40c0b641e0140c680401c01d070002016071401070040401103005603015907071500b1041806e840d5050307a42c84504020b00a204024002d1303801e40b01d40705074042c03400e000c1340380050183d00440140000e81d0444c01c01034941030003e0440344503a03142000400825107917040c410140900465070b890005038200342d2001416880302110307030280c40c1281c0c504151324000000d000d00e0b000d80d5414040165140d452a485203481040604941010400140040d00000762400301c0f1103060390050911035109084012604200d000b10b000c03ea000034248031525003170742020b6101030300344c4480d00c840ca001031005480d0b0801400c40ca0180750080307103a452400080701607441015203030440d0401d06810250340d03c098400c010f00380445016900e0001444035041c000c80300746501ca040111f00d02440d020084004000c03079407400e50340d4010002002140038100f00480c62469042c1e0f07456030b01c0c0401c109038158001184031004001803040001d000000d944a1040000c24030b5070900035190f800ca401d080d10507108a0f28028 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 165541375 1250 165540125 165540127
    0xc04060c080c10140a0c02010902030a030f142101170a06050604180501061d151905090411150406080f0a23041e03170424050108011b08070809010908 66
    0x1041190078504200e102c0e40140c4814024040e1b8514141e080310005800650541c00641001c0d011034084c0710407900e6400d842c540101c0207400750041600036040300701d00712112040340700719126180130840c800e405000b43c072240c441030700c0b0402141075850704848001807140d902d40b4000f94082da1160b020071031049031030111500d1b0f04071f42c2c0b03855030080469010702c44202d0707041c601c51240b0400684c000e074030920541c064181900030190800a100e02c0c2079607820711076114a903000c07415481d1120b100307005a105400a401c280c2c00b0f242000400442d0340c0c100c103c001402d01003000f0090748920a290800d03030300c1c0c105108a1712486614400340941e035080d40071006401491802a49021480c680f09034051050f031180e10220310710104000301e080341d0240c0041d081c1c031084c2c0e403082c503a14007454110340b041600480d4424040304183e070000b038080e0262007465031a0010800e088081c0188542601e0a61541410030006140a40202005400c00e030802c102e09000820b144401d500901c4d005400040e12 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 165542625 1250 165541375 165541391
    0x90613150f08010603170a2a12050d200f0d0b120318010e090103062309010603050c03070303140703050702060d0b040b09012301090302040e0a05060c04060c080c10 72
    0x20b0380079002c0703844200c0b04032150540f5855500c0c10701059428078000d603629109640c41c00909065140b00c412407541615802202c0340001400a10403400070700301c1500ca40380c55440d1140880101d80840c0400c200c01000a000714800300c0c451000c0b41c01d03101180f50920303104c0140f0000c142c010f0600d0320049810142c02c5041e00c40b1048004090314030b49003101da5190100124000444681c0c807000482c54115031003000610005459803c4044541401c0c6076240c0c01d0003800c0c029001c003902c00d58000c426659100750920034030005201c541c102070001d8005000c11851a500100020880c00b03d1071104440442e042c41010711440856205540040441d500c1c1c442400410004000c5d003c5068402e520385002e2040034102042003c0c1290100980c2403902d02220200342290185c110fa401d04006a006001c40169203910910488441d00001018800d015241c107d14008004d8080e800d4110280020061294018110300c408e540c0400b000d40c036650031001d918a040c0e40190209019030a110f15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 165543875 1250 165542625 165542639
    0x809190f05060103060e1002090f01030903032c0d051804110c0708010203180d0207050105090402040803041508070c0c12020607050d030b131a0906030a08030c07020906090613150f 79
    0x1400d070300d1303503501b055070a003000207900f0800301d129000c141074000c884000c08905c1c80d8081e501c00040340d4003a003408281d010311504400c07040b50442401c40c44210004101d040e461408101400095080b0700702580303014520402d900d008180500c0b00361040b501d80c5011001e0540e48403e03940d455401c2000c89492035220f210340c0b13010303400c03ca070048030008413010614030080e0009a00c00b00c1030443e801501c1a036082400446841e40034850658000f0f80070480020760420030030040c4000c001c0c1201e440c40042069100030039403100a0110001c00454041690200f450301804078100c40302a405200d000d040d41c0b0101e14280a04070000d04503019001c01044925015042590303862007c0354805107480da0000da1204854502c03499004058039039001543c241001e01ca103076001071000b01120802c003410ba03a040c40d50751049904d01c5078588042260001c5090410071140c10010441c3c000002e4600203000ca031030505420080b081003501c842001041080d8241410060107090900c00d11550300c3d42d030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 165545125 1250 165543875 165543881
    0x50403031709280605060f180c1b010207060605150a121b030905071512090501020c01020f1c020a052205030f03090111010509060402100207181406010809190f0506010306 75
    0x40141c0d915401d007000074025103445c100c0700700a560002e12923407441c0c140e02c203800468440201150119001041401d40c0c280039041c101c401d81d1011400540e0794a100d207040d00c2a200075034000780c002e80c0035400b9031901e05015015280040c2044c602116028865a1018058001155075002c011412450a40070b9549a080520300300d0092040764840c2e5510182c1402260b00b0750410320010781d43d298804442600d03034001c407440300e0281c0b0007d4100002041001c1c01ca91003440d03c1c00e6000c1700001c1c01981d1314515084102111041d5408500300030340e0b10005006485180b60902d5000800407917080d4480201102d00041d01d000f9040f030703008c42914207000da0360307900c030048080c04180030006002c0f07800307014041c0b188a21088405820617807940d0782840400c0746848181e80c10740c000e545012890700c07440101226060300202000c24071001c5503441d03003900b12000c0d0409040001940400445101c0082c005c0c140103406200c417000407209040c1400152800b2800070203500860340000188140c40d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 165546375 1250 165545125 165545203
    0x120a0b01120311060c0a0309081209210909010603090807061409010b1e060f04150305061804030206040803060f06030103110f0306070c0b0711010c110c01050403031709 74
    0x3440303c3c0d440a444101c1960b4030101180c500550031030400a00c0b0005100742c01c0100804d11850003030b401c00100a81c02041e001e01101c104009501c18410b5070010030b202c00c4160450f410300c1000d10b240400800216040c481c050143c41c040c0b5840d5082e56040244001c100d031310035a0411010841180076413201d40e02550191500c080c1503080000da500545048444111801c8035480885001e00c1d00c20300303101141d00700c00c03008040ba1105110020341003a048511029402c10ce0b6030024031864403400b000302c104600d284001c08c4420792070801000940006005030481d812203805520382d9110000100c41024902c1c0e400e80015011000100b004003c075055020110200c62840c0398441c044141552510119140300020b880c8484640200c1d101c4110740b0b42041d040d18100c02c521515040d2030342950070143c001c0f0700040c00a03000c001c0d4190280074070035080304240703015450640b442d1802024015030031100c81c48000c4540102d040340004208201006404003030a232802141e00030b05845e07001102d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 165547625 1250 165546375 165546377
    0xa050601050612130201052203120906050a0309050c042c0c03100e0a06110307030e030315060d0b090c03040b010e0609040f020f090a020d060909050c120a0b011203 72
    0x5040003041625224050302c0c0e0b00108a4010b20540d51100b0700300c482650721138400d906000c82080185038005910205c40c401b03c59400c4500207a51441c1f500014003011125814104007044006100e5154041c040352150752003440d010072250b0140c00e01a041136103d0582d40c0e03005240035080e08804020794210300d5841160320404d611070b00503030301c0b05450740032050aa5a264000007a0100940100e0b4000d094140e038503011500d40c0c207020366a00341160280504401500000700401c54a04d5041c000c07043c1100c1e881010f035081d801e00c1d1075410507071b91004a5261092a0204448001c00b200760311860400b1001403c2c08a07030305003030000c941c0560003a0b8060b41c040021000108a4110500b94140140000fa108170b1180c2e55948440510241c6902e007260302c0442e4821a414590b01c4442081c05a400c80c4801a66040901069800c4070f003540c0c00701406505104425010880101326201b542c241650083d600000424a2508000c144c0c1d038000d0034590004004a02e8100c9813000c02032752842 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 165548875 1250 165547625 165547633
    0x91509080d02161505042705041103010515030c0f130204060f0207090c020705040216060c020d020c03160905090f0a030302130902030f0414030c102f0a0e130e0a05 72
    0x215561000c44c0c3da103401c03200f00400c1c42003204004841d02e10014000c4e0034a0038140d0203400390540c0d50b5600f41c0388159015032b040380c8401d00d641c02d030740360030710800e03803c03004141040c1960085040403a03143c400b48140756119200902e05d6444541760700203002403481c59058110b50315600c0d42000b920703100f811010a0010f119281c008155601c5900c143d040c01176094006110700d41c0380004002c041d501400e8205074624900c005880001d0107409414004039058018000b281c09000000749040040d842e140c0c0300f03501001038a0320f0042d82e03034000c03425600c0519001c02c850382c91505c0c0c5450500040300401162040703608c40c1007810303810350107000024031244c00d0341d80d82c27956aa211810b038041501c414240c0540701c40804c00140c00d03196014200c6082200b40c1c1c1c188058104c00c40d05110009555204050320303903203088003d0320525801302031100c421980440440407510040864050104654107101c1c41215103511a9180c41c030181510003101828005a001a1141c5807645107442e400c41d004d00c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 165550125 1250 165548875 165548879
    0x6210106020f0c090a0608010507030c0816120b0f091302030114090c010f03060803040f030606050103200d06050904031205090d020c060d0207020909031b0a0201091509080d0216 78
    0x110100e01d102c1081d001c94020203020f2404420011a20304c0580060100e540e280000581c0742000e000ba680f09034038a07200064410714109005c2c19001e0010800441c0607002102200c0c025040306899212268282c0000b658403614804101c403070200340e40d5113034002c91000030841002030100300b000b81284281c00074020a0801641400c60003020f981513515034000e44030b4040340d940704518003040d00d00c6901d00030407030310b640c1d94020f800c60b4066000302708101c40000c420300c05c0c0300706e84c091900104401c0c42d0030840d0465080b418180700e01c3d102084241e031000010042401c044542099000d040000c100b00700a0405140c003030010150411800161403c00c070024091440100c1d0056030a01280c028050821170242000740d6580003040b00c032000755081c4840405a00c0300f0303000d680709079500c40c0196a9650040a13804000f04110620209036010418100060340e00c0400740341201c1c1e480400c1ca0031483c9180090394064002d03000305178188a10007500040790342c00181c00740d80d00510800c0644013a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 165551375 1250 165550125 165550127
    0x904020c07090c2c0102070902190908030406170a090b0705210f0a0c03020c0601031103100605010509090c0d09051b12070311030a060e01050f0a021207030e030906210106 75
    0x2130346503203007040340c210040620303407124000e205400100d070307014416245520388880c4a6000c9070032003010145114140000c249803950021441c50140c255140154102450709600070b201040d80c24000861800041c041041030b402600001061030380a1082e0815241000c0c009041e5000314034a0311410400264124111200d01039407070046074080c078111610ba5603e6403080150003203804d00300404d50300b000703002040740c401c2c425a8040d6100e01d01c2c640b800c0c0100000c1503e00b02e91402803417080f6103800002c000907a005821100050030a985100340d560710744d4100040350240c408880c0215007005480000c0050105070750000003086040070316002c1c0c1d11001d02c44c3e5510501141c0348140e102c03140138008100410b038510600b0b03100a00300d4680c2c680550341e00d41505c00224515020382c1d1605c080c880b8120283d818550b118034200340031400c4c1803164801005180001d0604001d00d03586003450207005405008035240040c0103400503550307502c0440140d0100301d07002c500d442c4c1d503d000381c0003040603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 165552625 1250 165551375 165551387
    0x12100218041404080a12060b0c0d050c07050f120d0306080d0e1e0d0c03080a0305070519080601051e0c061b300a0b091515030c0904020c07090c 63
    0x100071a40e01100543e03195911070035560b122413a60403c1c000300c43c0c1480e900e032440f4019540078003920300b8100d0b29400c00380c92291030110114880c0c000c2c80003c0c440e10702201e10004c5e81a040b903008844040d04400c007040400c94043c21890311188a0081070a0503038640d0701604814116003400c0102d521414400100300c0e5292813010700c980d480581c8246440c0000c1400450a54415008104159000c01c036602c4403c008242c1d4800c03240c03050045583c05441d41c01d40706640d4049120305000d4030b800070307000b0050340d8110154020b005014000e0042400e691240050320007000851005000c3c8504000b004140e641040d908040c19120304400a9000340e411103100d8425a903074100a400c0141652036400507407010000e401846e0f0f00d40700c08141c4001c03903442c0c440c0a049240c80c0003561041100a02c40000c00083c085008030320490400c15440e2102000001204941d180e01600d90300d610f00042c1c803910600a02a51290001c03400000c450320100341d640464000c103c081000500701c030000c0e112 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 165553875 1250 165552625 165552641
    0x216110307230402090d030f170408190201200405030105011401050714030c030a0306210b1803070501150608101203030b0f030604120e03070e0112021210021804 71
    0x1071221003200b50034210307400d81100300480e2006002604044c04c010110351000104182030340010050700341d07800481c0e04210040e00325001c540e01391407603103415150038140780304403041190240b901c0b80325100c1080c400e51003520f01d600e18802860b00c0c000600e11400d20b0350007034000c2c90710135445c0100014810140500e54543c0b0101a100d042c00c110440c0c5400c1c4552000c10f168101c180002c2280840490040c40200101e02140c2c500144140c2407400b004804c0550741c60b1001c800440f03002010205403601d44641d80107007074640500c4c002008420f0306045015100004000c0d43c2040082940505ca001d0b0f664151120380e07a58652503540d00d51219400c0c8060310500010840c900480d4000c68401d8206000304400075002e81c00c00005440441d20340002110103032101450000080314040c0d21110440e42c01604900400d01c00e030526980c0e06032a02d0611528050131035582d807500c115102c241000201800342c40c10307180e8a000c00b445050181d440002541c2c070007030901245545914045c0f141170740b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 165555125 1250 165553875 165553889
    0x90204081902060c0706030f0509010207031d1203040e180303130206090f120d0f0c0503030105121603050303010e01060908030a030c03060503030c0c040c0206040228090216110307 79
    0x501e40c0c14100d0206004181040c141e0300080d00300295007107110104840002000740303680025202d80241042000c84202038402c1e06c00c2c0c2d0040121501007540f020300700d030380002034204c00c582d1101c1250004005500038012000300b0b0001040000380400f1451805100b10030084003510050f2021200742d8491000b01c0d407406240c501c010001016041c072002070000020040d00741d0034500018000035103e4040300e800d00300180d0280046000da1a80560311400d02c140600700b120700341101b980c4d240c0d12400140143d5005050101c49204944801c102104003044440d0391750f0501c50320382c18510b4813903109010340d00c1001482c200000c0d1903032265001100710740c016409541051604441140a0000c5005000400d61149004121581d00340000c0c0b09010541009240c104080010b002c01d4510f41a907940c150b40001e0301304800758545001d07403041580000307190507002c10b240000c3c03041040d407908921103107840451700c1c0d401d80c95054800c4018a0003010050900d60000040582d6143ca500400c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 165556375 1250 165555125 165555133
    0x50c06010e1306020c16030818190308030a11210606040b0f0c100f060305010b040207050c28030c05030624040c031803020705090a05010506040b03131a1009020408 72
    0x400443d229a020f8104401564203441c2803070400b855000b100c800d503400aa40003080001c2d09219030400030180e00c110441a600c0120b0400d5011100001501510001d09000000000140030a240e42d005a440d43d0f01d6800311074640ca21004103800d0910003580c4410103252041c04120146441020340d01101c10460010349403031740341a1200500e4000d81a001039178416061411118400c90203950180e84c00c640c0000303903030b61030342c1059400c0d100e607840c2141c0560300c10040407002c43e20102d080300a440e810783e544102650150801c0400d1075210071000c681e07c000d108040304018940d0500002c44800301c040700c1c0142c441251030800e01080c400001000982d14040d00c819003869008107284071030b203090004600d1010324010403013400003041100180c00801c030a2040b40741803002c1603041180704008010359810103000c901c0600c01c3d406a0664044003000240580f40d40380990043c29600c401507448140e440380100414500c00c3e14100c48000200f0302c00b00c4c1c042d10074400d440071030b07040200070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 165557625 1250 165556375 165556411
    0x60a09022b1407080a0f05010b0901030507021905060105010e0603240303040e041a0108030408031c09150e010c02010c0206040f0507030b0c03070219020303070b190c050c06010e 78
    0x192103244148074845807140301405515580c1452280b18458940b90984946402c03d1410204e42d0f2000c1e030030030064a01001031000c1c64985050303405440b002e083c00504c0b500e03401400d07881c1c0307050400c4040b0b815a11014210420501080d01d074100c42d42038a81450a0b0310b140e08020303d86c00211a10f07101148045980b1800100e00205400800c80150690345429141e140ba052812400c0320103640c0c0c02ea032801c4c7c11400f105582c0d921801002942c000d1070902d818410940e0710707480703551071000000c0d2000b405201d40109651000c0a070542c4420a466060010f0402d400604440c40764400c140d440c00c03a120407614010701485c2842085a4050450380d41e55543d0982170540801068400d8071510202000003000c0640280c02441c642c041591245040440240340028035181c0c100d141c00c0001c030050050702c0010641c1c03506a84150b01407425074454031680042d200403450705519502305101c51007001d400400401a48864000740c0703020307a03280d401d003000c80307070081d0b60352000701c16a43d1030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 165558875 1250 165557625 165557677
    0x112050601110d0315050904050d0509060f1803010f061203110111030916090908250b01091a031b010804080409050115030e070602030a050a03020f0d05060a0902 71
    0x200d500c80c2050514468541840181d5450070341101a030341d02103542c91200803d40d11503084030100070481120410018039056984d242c41c0c540002084041c40b0000c506024180d8501c019242c48800300045a40c44001b60007000c0d8144d484010070034000d5181c402482d00d15400b070b005680948003480700010b41d100c102e5070300312030145410303040c820702e55070360525003c80d0700c4000000c0d80117510240080c8410800c2c08088e5886844c9a030000c00309620704160a00000c243ca0f064451032190219140441c80f84803c0c5110010700c0c1e040000c102080d150008180071650703502030341b81d60560b00110009486598207241d541c1d01c16a9a0403a000d03081841400d5039032041000303c0c1d020b84500c001c94203140d907031442e03030042e124282c11002003020300c0800070241503410310640c0395105407a0b0080070040d00d8400060740300e02ca038070505000c22a00154245215001e601240d0300b41070085071140e5546801540003000300320076210144101c2d81d90707000040e05205402500c0d02d480e8044a403282070b40e9001c3d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 165560125 1250 165558875 165558881
    0x30115031b0f0210060905090d0f02060106110c12030c0f03040e15120703080406110a0f17120a0605100c08040b13030f0f0b0901060803030a051f150206010608060112 73
    0x2d581000c40c458820303166000c1542d8002c40009200140c0003141a050110704941004400d523044020010390b1801303000d80b10b5001500c00d044807814101100942104034805052000c5a001d042e0041e010300d441c60064100080200a903100311000c0d55a0110401c841980f82c1c450b6104d06a0b5404481000c110700b10213038442c001032210014080420745d60b031b084140341880829401170741c0410340030a003000b016030046041e10000c002c103c098401e2941d40d030354020038424031810141011252603807403001e8803000d1007103505c01c401421501e2094600640500f001d810140502c0e401210a005101c00d194040c0e0700c0111150b900001c0a4102820502c0061454010b0085101f101e401400000041903022507000e0340f017406142c201d240e201040c1082d4200c00d402030110782d001d0385003031030030052000e0120980360042c1c040b16001c503140e00c501000c590398001d1054035043c1001003010010740d0864048002c1010111034003039403180d0384c2e00c0006482500c0c04960960128904142e1507480b04a964 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 165561375 1250 165560125 165560147
    0xb0123090d05100504020112020733020c060117060f011203030f0c03021b06090a03050d060302100c06060b040501050d09061512140f1e07150302030115031b 69
    0x60003000e036a6489440d620301c2c015600d01c1c0c0c4583e10b075544050006550703004c1c0c0b0000016000000542c074012791940c3c4c506240c43c50405034581c1c2c40400494400308088560040b0490791030b03120554230384100d1442c143d04c5660078881c0440088485d0540340800c0f0340420780502c00d2401c80110402caa1030410710811003581560218101540c400c02c65021010a10074100d00d2151a0b40060300c6041031810000d040d6507140454402d0390110080000004000440364a403951502c2c206803600180c8000070050700b403640000b544000640000a001540a102c003440c250151800b4001c090792000d8281c040c0c0303e1405a140000ca08120403000504150480f009151160030000381001c3d0703048200081581c1038129000105041c0c501805010584980c2c0751100442d601500788241c1c0c030300d01941d5422080b20499a0080c541060b90020501403100e44002c00d040000c07440c070a410114000d0095000340a030000c007000222201d03002d64441d00c00d903451020140007440d403000349220180d59040f41c0e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 165562625 1250 165561375 165561379
    0x903020606091b0403111c023703030c1217010510020a15020406030e070f0303111509010504120c050a06050c040f030c060e090f060d03030e06190b012309 68
    0x100f80d120641c004084001c00c021805003100182250302041044854500382e10008011444030f10b100c805652403111120018110041b020064144170190700c2c1050076040003540600120329000044c1900035a00841c0284034040044d0858144201682c042140041c001904164240184203d082000c1d40c44400c0300e00d030044400c0400c03a44d90f16004000710840200e0040d401150802426405002e45c402d1042c142002d000320f00d0612620403201d004502c006401c0084848094100c1201031205164001c4145101d00040c908003115901810703003590f003211010346600107015031900ca0302e1050b2145131311002601000d40140c54031750180c480031f8450348001604000008064a50400c0d0b00000c41c454040610031074500240a031000e148152864003880b02c0e80f0802050075100c41407150300141c126040c85403248541001c070b0041122019114203846000b050000100e64401c86010320b035003a02d818424180e02e5401101c211511b5151100504800402100b0000c02880903200d00180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 165563875 1250 165562625 165562651
    0xa0807020f0409030306050f0d03022a060a030b0f060a02060f0415060e060a090b010c030c08070206070b040510061d18060103241104030303050411060c030a12090302060609 76
    0x52040024120f4402c9075049021903610503042185081080d080740040d801213070041c40220040c2c6000c1e494040c60b400460040144d11609041c03040e2110301c010310300d0005080d05441d4203560300061b00602401d0724861148412020030000e61420201b01d40d080e00096010b050551124074580c40b0080024000b15560040c0060040c2901640d00c5420300914002c2050700081c10008244a5050b403aa000142c01038140351100407640d8000082401c11070f81840c240d601d0784403038101030341280140e01d4005d41c04140090802d060120345c0d4409802540078400740c941d01c400d403d140d00e08403903080c490160000c1c0c1582c41c0c104840040e040055011500c1802c6e480e9410300840400d040c09002d800c11508103c070768035440902c50701590b102d080c020500c0410817260407000c0080e445405503100007410140c80da0006420825120200000210050f0030b0540b1982101441510b94120555541c0011140b0020210162450283d05155501078003e0062500d41b0818230049400c0100702107000700e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 165565125 1250 165563875 165563899
    0xa05091008030a050d0506090112030507061e0605040c0215010611010e010f020307021902010c0609081909080d08040206040b0c07120302011b110d0807180906050109170a080702 78
    0x1030244001c0c0030343d0f0007590314140d4550343e2800c4282102c402900860142400d0343c01449051000c120107217800f50181045500d030240e034904240500003111846101d4250322085d0000300d0302c036030460019504101c80c2170011400044080780d0b02c482540c0b00c660000c50041c010400c59018400340300303000c42c80100215800040c1582c81d420348010a0921900702e42c00020460019418004168403001761040d0380360011094000030701515045101034001555542200c08008801e0300b150000c0d8042503005402d680c1e500344c0606503200d584150710441c060032a0220685214802c1e041c400c0f68001c00007401c042c1410161103068110540300d1805100b941c1c4003042c2c80040e01c8200703540078800ea0020505109000c18407030425009d0300c86009202c074020344010000008141c4010900c002c2c038100b1490741d2000000c81c0d40c0b181500c0c0e400c031140743c410030100701c2c40c0d43c5401c4541541c10030307284c1c4802c00e6902e0b00404004e42c00c02c041a07620782c1118640308001150317070004001e004d0000b0181c0d0b1110b2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 165566375 1250 165565125 165565139
    0xe060303070c080307032a0210030615020f0d0306051f03060b130807050d02010f18050a08031b03040b0f07020f090a020304020307140a05150c01060f1a04050a050910 73
    0xa0f03801981c010361001c554002050b0b44580c0c120000810384400b504890402c2c0f0038100713817241007800203101d181c06200c0c1d40401c503c241d10003401004031000f441018030030541d000c3d44486c3c100038000c900d03000d2202c2001070a8001c2c001c41c1700329480502440e44040d81429801c20784240d20324000109a00d4140006684903200081c0110241d50140c07880d4082c90201054500455944541e006001d54042d000260b078110501c0900c0c90b0f144e04100004120492031317010046a00d40105500030443c42c8085003030b010001c00b81540c180c1c1403014140441c0b00500300395807406140314002d51040f0403c12500d41c0c00103600502045880076206202400404001a041c1c502c21074a0400c0182e01004100541c9030400c00c0f64001d00310740881081030784803000442d41800c124040d0381d015515000054900c0d41c010f80455503070075031800c001c020b00c6454810086040c151403080c00042ca401c451840130f100001c408a90803200000c2000040d2071808042c040a440002d003040300050740c4c40000107141d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 165567625 1250 165566375 165566393
    0x170604060f1a370305060d020f040603020307060c06240510020708011d0d0c02011d0102031c0e060907121202010f0903020f0d03090804171015031103030c070e06030307 74
    0x19403400c541d14402180c041d100081c0d50038560f2803207801c15040c03c00340b11058880298181c141034042e078107040708460b200041000b60119a1000303406104036440000c507140e2204028031507038441c00d010300c084000c8400480f084091880c41c065440113000c82000180340c40b00c034080300c03113103540142d41c160399550b02d81c103084034003416121042c1050480c4541d001582070000d403040c0d20403403e100304a64000c1d000200090620b0f9442c4005003a04c00d80304603181e0007081a2080100020740c00d81c4604442e1852402400c50f4140c100051b100303c00100341a1180400c0c001c040c3e507a000c0e020ba194010640300c060300c04810340309280540d542e0754110480c0310074502480c4107843c082d400070020401c1208100e4600b091420341072003054907003004000000c3c00a0200c80c00c0b54403040d0020060003030980f101c0d06114000041004191510465120039140501c0c00000c0303d01134440008105100010f25445e841205102d0240f50007019052020841d00c07110184c000034007600322400c3c0999942d0300540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 165568875 1250 165567625 165567667
    0x20a0306091104060602010c120c020a17180d0305030403080402180f040c0501020309010e0d0c0f1503050c0a08040b0c0d0c1205070e0604060507020619170604060f1a 73
    0x11100e80d9402e01c00890909000c0d1000425091001300004554501c00500c02c1e4807840c0e10408413038948003400e114500c200305800c04690800c07001072418506002c20111076203d40e107040e88100203039842441c0d80c5000c44641c00050b4041c0c56143ca1560f89175811608000000c10407680400065690b400030303423150072a90720608050107004c2450400d0308000c0b0000c992035001070704542c020481380c050313039912030100c0002c0c2c0c1d000d0783e42010003a4640b4200780008001d03000209d48004e40580040e202c5015802081c00396000e4608001e55102c1d1900356500d40306819428010540500c0444d001852503480746070302c41c81681046003844003490411040c0e4031844003410000b2110906e03440464032910485400c10700b5410240d41014206000ca029400b592044606014011411000355103e00c0115170044c008110340e010382c4400b2079409000d46000d071013082d240414650025085003080d100d40c0090b036070040c114102c1d19140c64141061140b0452281b5030620081c04110151a40d081404070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 165570125 1250 165568875 165568883
    0x4060203042603090f01182004020c0d08091504110109090507090807080604030906050309030405060a0804050c01080126010908040305070e1015110a021206070306080309061204020a030609 83
    0x140d07a0800c2c001c4117142440b404001034090345004406480c0038444000c00e02015401070100c8055604849800c0c500c508404009801c10300010b07000c2000316020450313012000ca541c4a03114142c0f1181802540d900c001505102d61610000104010030014000c540c666101490302003140f648592009055420135900500421004401441001c0782442032001900040004040500d000e4500500200c2c081c400c182c2800800004964043e105100320303000740401a0000f55500c00316007004040c40c008503025649030003240900541584200b09007412144041003009001220000101180302ca02208100f03a660781c030203800024405102130310003140030304050001545000e0408002c01e00081c8801d40d440c900e003c05000540d4004c1d21810b1000d11071408200f1352841700211407030000d10308806507021030785001c80c014981000403400e100b8080360ba020301c03080341c2c4c0d0310003e40d0b28020750544030340c0600248116190703030052000b4180c0c0540000e10302d021a03070350713501d03158100e5864100980f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 165571375 1250 165570125 165570127
    0x3080d0207020a140310050f0705030403091205100c2309010e09040b0405060106021c1805040e1b240306040207080703020102071b1512022b0b090103030503040602030426 75
    0x4951440c5c140540110040f540d1000d200a1604d4641503080030b00050a64003070050220106060601c03455403a0301404807003114515004503410400d07a03e08114401455050034611510203181c455510021203c44094000c50464204401c0001c103030030214074a030402c0050f01c40300e4000d070b45200c012401503010340d1503c10300c0c1c2400e0902600708a0140c01100c1594088e010000301c4c2000100304201642c014070b006101001810f86040c4034503681d51145031312a05000224441440110320b104817440814400c00c1d50204040910480000c5031341d004502e541040b45180074114840300844e03000c00700420051904e11a55038010340c94200d14001c0d03005039808210340003001842060f03210404050401048164a44041c0d410110b10b5454000100000780c0a400b0a24a041c0c06032040700000070322442c0c00000300ca625440b42450b0f0004440c4071810b106a071740880c10490541c0303058070340660f24146140e03107e13115080607510262085440c502c0c0c80094861003da489071402c0540d4810b2052 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 165572625 1250 165571375 165571409
    0xa0e0322120213022505030c0c030708030d05090102070602070b0901060b070b0a0905011e2f1e070b10170706080105040b041803080f0a020c060103080d0207020a 71
    0x6aa4034202070300124900c0d202500000c0241c3c2d00e540c8189070b0109450320142c0e035281c650140211014188010007421465240440d08200000c00940007034092001100d28441102042660314030240c03007608000c4d041001100040324243e0000d681c031949510000d440e01800e503483c0c0040b80e100b01c1c42900c00d07102c2c41c0280b041c5481e081c00f4080081c03844c101002e0602043c3e8550600000003d1304510034185d03184050010050203401c101d48500240111458090368480184c0180114180c246824a10384400200e8442e1254103c1e4610f000e0382089070800690001415403c2040d6010000c590002c1c4050f0001420710648984038507006044000c01c1417501d05004040c814501d049481500821000d101a40d402001241150b00844001c0382e0300740480017083c010030074600081d425241e24080c0c5c0f418150007141280c060081028800000c0d0b90312580e07130342240150081d0030b800e0b0304064010804500c0c01da0103070007296021a4018600741c02e5900044a00365160b011001c038006a00003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 165573875 1250 165572625 165572677
    0x61c0501060b040e0f0a051603020703020a0f060c0311070f030e15040308120601110c040203070309200306130c0302061c02120108010c0c03020c060304060b03031206040c090602060f0a0e03 83
    0x1032038100012070001d010b107048c050f0403148014101c9615904050780880d80d502418401c02040c42515000580340b80119594200200a44071b1118410042414141c0750010007245508403000107070000f440704081c00c0d15540884162841031b0241e40c0c40352110309005e0480012100400c010740c40303404455035945007455906010003006007104d0510011031221941003030b010820f01c08000b801c980050750f0340d4880d64180c0040c1209107000d07100ba0401200c001054000800201c007208044046902a60700d410b402c070401c40304200000c01c0820031800820050a042000d8099007d664410b00d848051700545032040780c0040321010515151400108503181c800c9c440c00204e9030030b501e0284c0d003205483e00d001e5664460124001d014480c0040050140180d0b648800004000141078076500c0f440c003229200c45c003006407411442a840e090054103200d014040d25802c5400f00e030003803c81036549580e01a4150701c000d094243d140d0321000c04003204102400140040101d444c00003144c502c0c0045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 165575125 1250 165573875 165573901
    0xc0303130507050a0503150601181202090a1b0302030403050f03041212110412050c03070b0a0306210605040302010f0c020d0809160b0a050705060c0c060f061c0501060b040e 76
    0x102c054061201d0040505c82c0e0b440c00f01e013003540030750b41203004510b9466070401241c04100c0007000b2880d03a603246001060b030f12a2044001200c0740202c50520f059140c007034410302204c4449208171a001441c50b00c0030f00b598065006540c0c80343c0a41030032410140894902001c0d94002c5404565512a9040c6415465041400411681d0f42e640042100c200600340042c0c4510581c090150084086040b403020400b0401200c00c001c00041d040d02d449690b11841110396810103d00213020034100320740442c11041003c143c42540c0314404448900a20a45800000f8080580181c0443d501c4041004201003280200145000240d008000c1003940b0f900052070604041c0c58040103811100c800a907031003c80601a09464044010079501c444c0d00c4016151442030b40c7d0003d04c540160820454184144c0300901500545581075030801d9a40c0c80510b0406e8030304544980e40071803001403002065111010710070300944a4000007419640f10f44100039907401c00d502c01104044070740200000c042c4248 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 165576375 1250 165575125 165575129
    0xf0405091f0b030702100b0307210206070b071409010c0f03030b04090b0603010b040504050607080c0c060c04140405070819021201080604030e1c030c0602040e07020106092702150c0303130507 84
    0x46c1003000010f91107c0000e48860140c4103180c1c1142d1405120000e203494290b401c49001d81c020102079540c071491034007001a65044030f1000100c0c15014107940380081200854200c50710581d075507454205140d0792140305601c1c100c0c068080591300d400303a01841d15079208541406011394080070f55407900404050948028080c0c80d402641000b05020010388005103050700101e050401038042d179142c139141e90690180e00a00c1070346201c1c1a00784025856543d0003001035514800c00e40c0e0119148005003c15aa8165488000159440001041c280d16000d0040c54401090310240c68102080d40b07200c4072010a1b000310007280c00a034144020903803c00419503014505403804a80146600e5850810400142c0c001d014000904990400c1007440c3d4100c502070f006030003842400d4140400000e000302010b0160071041072601caa1210a40407403500141c5012184600c90045030303e56091041d03c0342924044041b40c0d8092101103c00700051000c5d501c0340407140180c6490401c9230a08500d040703115 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 165577625 1250 165576375 165576403
    0x6110634090302131802060306061303140601050a0b090f010e0a0f051e0d11310e07120303110c03030106081e0106120c140c010905120f0405091f0b030702 68
    0x101c082e400c0104490305c0844a0584c040b01c0050301c80c4e9604010407081e204440c0c2c60748035030710703c0c0e4404000c20403410001000102800c086986507078032102408a13900003801140310519092144004500d000764486144e40b006250640100307800c003001c2415a2580c2d0414170f81c1e403203221400d01203400d041d0a00d40c000c007000c607400c10302c40c3e1440000c070b15000c040040281c540c185000f0dd4294940f2502006101028803e800303840c000b18000f2500700c040c01d52480d1443c800d08144000790300d541c00164440686284c402e0076a078041c007564003500246422004415059801d200340c1c0c0403441c09001550081545846402151504400b41e03401d0b0101b0030032448121640790018030009502581e075002c00000038000081c0062198420b5504030000a034204d5110b800040440108206401c8182c95922039002c07150b5001e50b0958450050050541016030810140800c01580c80c062001a8102d800492170b41e0000c0e0241813442820341c9140c102c540119030001c01e004c0c17001e50410600c1001004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 165578875 1250 165577625 165577631
    0x609101b1704030504180603050610050a06050c01090b0a2f0a0c052b030605040932030f0717090f0f0a09050f060108010611063409030213 61
    0x8901000e018840050309800d003079200d1400290402d4000c8045038043e15100e1041040c801c0e100c243c80f03018050600040b2414000c40c0d000c503004030780180804080d144001c00400d003c5042c90000c541d10f80208000509a43d00c07203000b0004141000c02071405000da02d480400c16100c8211210703064040030f44115001040503c4d203a150740705543c00c0c0c40040e46203240c032032082c00c05170911501e401c45560800038610a030014108207403018011a0351402d4403920240802c0d9a00c90030001110074042c0088d18100300422505421041040d440ca40c01c0c407120100018407144c264510701c0c54220704000c0514140c0001c040c1c050006006880888010f0300030076900d44920070010400c181c81c011032042c005d24445800c15065a1074010b84005040c2c28a81000030f0310346800032407044d041c15100e0714080340c6a0700000c9940351180384041c1c403081c0400028810b80e240c2900c980780f0b0004a00411780002810440c6c645100051804164113081c25510f90003810b00790300401080c5203081c0a44010589 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 165580125 1250 165578875 165578921
    0x601050c0d0302070609050319110109080f030402180108060a050c1c0906060810021902030906030705030a140106020d2a0206070503040308040308070b010915090b0a0305060910 78
    0x1001031101001c602601d000741e120080c2e1700c2c002c00981907000300200b003404041041c1d005244a481c0c141400308a55840c0b84000c440c0032420740c22200b800402400c10b540400c250b1040f00d00650045800030310141400c4001c55500281c0f044020080e0444000350704044240112008540283c070f40015580c006d1910f410300800450000c901005900c044483c2c036442110181716055200000524030101902c2c0d0101000004030000d50005603a840c004001c50441c815151001058601140014249504e107403031340b2400340c441707410080100b89a65299500c5125403400b0070013040c002d10840d001052884900c1c04080e140403011003041c0d001b000ba401d4054201210441d003141c1ca9038042c0c92075656800c680c10241e0851156800180142d00001400401c11a10310000e001c1035015004290b042e07600c0741d550382c1c29100903441080f00c00e0f080090074041c4c0b0308140c0c0702003c500350042c00c4282d00c5989036079240c245581218400d6558000039840b942342c8800b80900786030300c00c9800b00161001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 165581375 1250 165580125 165580147
    0x403021011181c0b150118210f120309030807020a1101050c03090904030c0201020f0102040e01171f150f080a1106040b0c03030403120b0d06110f0d060806060105 71
    0x15020b581c0107124408509256103d806083d22042030250080306880062408040c00d00c500d05d00c031649180060041195948400d18841c1d1100942d00400c210078800c40c0701c4106021000203d51040d1004010b2106040000d602016403161101c01c6407004140000c8030b04002c1e2100500901c1042990001c1d002500080e0301c2080203590b0310030900301140c541c60610042850360140c00b01030b6821801d00000d000505401c00c8100d412540300360b00701d8245840483c02e00e03083c0d0190b84101504c2000d0b400040c043c480c0000045031034185580106c49114408801d61440f8041c4944200c048039a40c04024a2103034000440e800600351450030025041d2510340312503911201d000700a081c00603c5a403090056942408840042c9914200d142d140c40c0c010760490f8480c4c1c03081e0380440c007140c81090440920304d401d000d4500c0895004103c12121080d546880b4007409141180c8035400c4400c010b21201130352408007810300c103805000c00041240c1440d484a20700b071b10140c140e44c140101401021196 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 165582625 1250 165581375 165581407
    0x636010e06090f01120e071205060702280809090f011809080f0a180303020106060201060603060518040321061502010b0303070f0201210b030607090f06050702060d050403021011 78
    0x3c0300702840c020080324104e4480c040200301c000c50059031401060f000081c7e40342141d208060325801103042d074913262140f0070180c0c0e881c070380300d04c43d45010402512860f1041300c1a40150110a00880446240074402c50001d01c40450480b5020b50350303064440107200002c0455240121756080c8402003000311995110055107005803581c1c0742094000041c9100c21b40d12034991031408044080705961415102c0c50040c0c060110f07801244010340ca042c5000500038401c1c02002c003107500c0a0a0941014501440440c801c07100801c00d038184140c03104ea11403c04031041407001481125800054000d003401e003030320009100040502c0c21681413980d04101660007004454041e0f511940c40c249222107840180d89441144621442c41d00541461106800e850b0304610340c00c1c5400c800382e40490307450407000d40d4881c0050007080f50300c03070340c908040c07001d43e001d0001816030f00c0c0000d0440307080599180e0003a080e103030102c5003200160003072a0a888182024000d9594911141d1002420f00c00b03d001e548ac40c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 165583875 1250 165582625 165582649
    0xd020f340f080d020304080d140103030f11070510030b0909010c0801051c06050c031e0405030f0f160c0816140d03030b1e0f0603010b090636010e0609 66
    0x4801c0300d40c040d8004004142d0111002249250002c0d9101d1400d4100f5603281d070003013200105400d0400c40750100c1e440103a520356059940c50340354041c0000865908582800462042240a10602c0f20110f80e584e1401c01141c210b048503940410b034205c5030024820520b1000d800110070382c3c145031f10700811a4015000d581034405c10703601128001c2c09420300303000e01c501410010b01040d103041d0500141802c40c00055210300c1071030030800591840c2c5c2c1d000d5821400c040385c000d012504144900101642035600412082002c505e2007030400c203c0c0011580150f000020440d480482c5400801247c1418040300b01080300c056444d9103040c0c031780b803901401c0101e82801548501d1f01221541d04050196101114101c4090500d09014020015090842945004403480b03100c07000a01403440c03906108903410783d0301c504404d40c1006810300c144080d03608589021440050358030b200c2c140e00c58a44506c000810800c03a04400c4014400c4000b410902c20303140311902806e4204400b1030992141e500144e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 165585125 1250 165583875 165583883
    0x1503020d0201180b070606060f12050601111e0705090c09060a1202120609010506280c12080f0606040602061b040504020a200a0b0408030702030d020f34 67
    0x1291040a200403980d5000198454220900d0036001040c04c94003007014103011071107540100130039511443c0958032559944502da0000e5007218600300b40c1800c0c0d03000aa08440c042c18501d80064400d4045810141840700700d808120104407114103c071010410030f001050240c6038440c243c203054421130042d115502c0d4080c01482c0001302c607803c3c184280e00031100d40d04032150454880b03d5046d202250711909a900c98860a541c070f00100b580d00d00308044403280c2846261030f0034110000c18505840004c0311040c50244000c03d4002804140300000421403942c00d40c2e22180d0914128540e0803d606000e0710f0b46000c1c40c001e0005211184d0000794154001030801140c12025080502c210028842d9400a81e0000d0001c12175916090304040c042055420b54a8250000b25100780348030b6070f0355104640544058421404a000710300e90000a6070810307600d00c141e900c0d1040404c441c03001d991200208140b0300034009103541c0340c500100e0380c0d20710075103141ea00c01c640001c0e0b025003c5c1c11030400c40e0f0060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 165586375 1250 165585125 165585139
    0x30f150605011707050f04080102190806060912070b031306050108060c07030e030703140a030327021e0603011403060a0e0304140102150702070302090a0504051b06120117010e01150302 81
    0x20313064030300400594000300e901d070040665441d150743e00301c0d01075041200c064040c80f126000d04d00c0064041d010b120300c100c03400340c400d40c18125105c0030442d098800145882090080c0030303002c035000520300f00a51052100d5030100300e929440b40b82080450300143d02104c031540100041c400a4018030013182c40483e00761030116680128900080e06080803a070008100d118000c80074550303013802140d034500460190f103040003c2003a0b203c0c141c6544002d40d000d0101c03695080039000040c5041940c001c00462101100940c1c0044a00459410792080c0c2000a80c0c1c0103640c1503940034541007003504c0d8080c4010701d00f4044c50f110100503a9890055016604074603001f040042507e07407007009190b045081602802131141032283c40a0349404182c003059020340c00c5040000e2915599020b2103000ea98050300070030300021350007001c0c031140032103150f09580483c081118120071941e00013502d0192010650b00144004c04c108910b08545128411110f40d0b41050094001d40c4203580c1503c1c01c84e0f0301682c3c42 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 165587625 1250 165586375 165586381
    0x80615040806181c0206100e16032705070e0a09020102070306050c160b0603120a051207110a060507030e010c1407020a03080a09150302030603061b040f030f1506050117 74
    0x10341001213100d18050100c01c0302d06200380e000d500003045401041e002503004030080d16400f4010001100300d5a440c00e20150411504d1102e200c3d90000c007100842025559400608102c4110300e002c0610040e40c40741e1040d40203220f102149071819410080409003048100c0340c41d0300107500c1d501e96100c00f6262507a00c00024402003050f00c1200e8103000c0840368007592126624081c02d001e20182c0c0d0113802031190b0442150988400380c2180c11903031054580c54100091010365801c000001000032040003014410441c0da01c8040140008142c0b0451020503d4a00260002d04595220305203088584c10034101c100071981006000014a00c0d01800399a04d280500120703122908903032008181400c001000001c07030713600004407000d50b00404c0e014008034129490881c181e020070b40301544d141d00580c3c0414400c55030443c8041c2d6001c94103c445003071590314071850600308913541c000d648446244803800c0801001c0c00e03058004a00c02041005001e003058002850904800144a0f0101844c004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 165588875 1250 165587625 165587671
    0x8012315040e010f090804030c0510020a08181201020c151005060d0230010911030a0903020f0d09170102040e010302010f110a23010b0102060a1802040507080615040806 74
    0x4c44400e0030303d009028490710311249004680b41c1c0c00b0344002ea0784914150380c04101d41c505201d035450350309a29802800f08101b0f5440301111355000f100b01c1c400b518550640c1d00038507101c0e1f03500060005100c40005031a0220901d4050034402030803d50010701d060b0f41c01b004100c42005c54014203682c801d480d10303a20398030540319000013842154440d00e000d01d0411540b2426204849807039040805042c1c1c0c420260743c0e42c890300419a40c2c0d810008188080901c0049c2e941019640800101e40c0680b04582c01c80d0030545c4400d051032100f40c076801c00644541414031018074695006480c0700c032403000852906107414025400c4000602000b0304108401440b14221842108280344e00c81d103020540314020540d01d4040e840a501c2c4405071500038010309032040030103040c4501712115006030083c001320759a1078030100007810f408406481c80300102c00d111001d600c40e44116807064a40e925220000e0400408011805c1e00f46126000204000c000c1070292500c082015504243c0341c11400310350000300d8803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 165590125 1250 165588875 165588881
    0x1150c06150b130e0609062206090b011803050309061303080c06040b0c13050108131407081504050706200303190b01030c05071b050303030108012315040e01 69
    0x10a40394a000c0c15400864040d45800c02010f0703055240703090729159540c038980d40c04038030740031590b00780e1080d01c80b40091840d0420f48041148644d080341c0c808800001c10248a04403a1a5001070a01e03644c0c442200c1e000356000500703500c081d0041850900d00394510ba45489c1c0c1e03071048050460081c0c5d400302c0c00f61a00b000c07031607154003d1a40020041e03207840d0642e0708550780745000c980039074100c3c0c000008a81c00d690824200c0352500d5001c90b104405506080c015504c10714090032005c41c24000201060101d800f4216038401c0e000024080d00e089442c15454900c0c4c100d041298038004503440003070000080000910004541c400c1c10002904110b0031800150340c10681c001c540d0038000001080f18241d80744541002100134503d00704030f004800c8004400b141c52800500000c1001000100c012600e5080c909042c4264041c84114103526034000c00d046400aa100451980d100c012800c80070720801b100032508400c0501c00d010034070309034a071101c603102e5003803900c1d00039a80d0701504002d40b00290 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 165591375 1250 165590125 165590141
    0x4032304180b0a08101104050d0323160c15020714010c02270a020a050d021803010903020304080601080309062a03160b0603010e1c03200403110901150c06 68
    0x8000342c1c2e1403540c4c4c82c0901d407a080c4959404040c0d6241401d1000f04c921130a0a40e015100b024225601c0040c071a0f8058443e80245a02400840d1000c4807100c620b4800c2c500601c101d00c10880300c02080c050f240380c081c1d40030610740c000150641080c1c0343c10150513030014200017290070032000890100c9280c401a200360f0791842019400803400600e4401c0c210440c410034002407100c050b0f56103213565281610040307006501c1641c000a20802425081384100c2c0c02802803107071200d0583c1c0e0110281c100181c00c55034410300440143e08041401c000fa100d090180c1e50041034410081c0d441c1c03503400c0d00019100d01c03a0b40c450f411640344c038107007000c408a5803658800112401004596440c90346021612200300240d1341100d54844c940d001440d2130906010702a010ba81034002032159010420508000410a542b198101030f80d9544924030559144050016000d281410035035a505604080f41c048502440b00f50007480c0c01c00041010303051400c40402010a1850030440e02000303803609102400ca06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 165592625 1250 165591375 165591379
    0xc121308030a14160207120c0b03040b0403110105070c23070902220302090601030504170a030b0a050415090203150301061d010806100909020a05090a0504032304180b 73
    0x4010424820400ea0101159070620248900390340d55890000c0928104e240c200c3c1c006030403100d02040001192018948a0b0384255209200607490304103036495604101c80555110782c601003848140341e0490321250311002090003d004904d44040301400ea0b5000500081c0000c1014141d43e03001c4c1486100703003d000040c10203843d445a40c0702981c40281d00040000c0d80031041d0781200440d00108040d141e41101da0117031030708032030b5a00e20340103400501c40144280c800000000403000d0410038038000313016480c81ca84001500405c03034814003001100302c0c1c000c58090b0745030110f80310499801402000c01c880c8500c40140c0c0e283c0c1d48411480141800c0304c0707503a0305582000804546c0170400c001c220101c110705148015103a07640c09031a580c46074243d403802545240c03041c1c14071500003075411000d045400a00403d8104e0f603114040750050300100d503a1803a0580c0ea0090004040e42302800008044d1035a02c0c0d80e0425800800c2c03407100c5d1007140300f0f020f22174540080354041101070b90400c10400c1c06c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 165593875 1250 165592625 165592627
    0x3030b03010c020d1206060206061219150f0207080316021608060103170f0a0f03060b040e040b0709180b030f0a080712090f0303050c0c060d0f0e01050c121308 70
    0x140c102c081d540783c1c0650040d40124074400e0406002c0c607a0b034460035080f81d03069802405261112002d00c9240707040b0b40c071110207a0003440a0718103100d07103030940074010b00d2150006141600039100d40b802107940c04400140e65500404c078400224407040240c1e034100700c1086101d0311180c1001e4080e89403043d5601c5500780d50f840500c2c0003501c20800b046080c1200e0046014900d812040b200c82d10592248a12070761003580c0901c9454121846051780780b41c1c002281c01e0000701c2544070794640b0381c60780269021210f8004501c041100300003441c144079812030b9207800e00c28803070343c1800d683c02c1036110210f00c64004150382e604411051382c1c08001d034180000d01d0034107880415a09050030001c56112942c243d6004021305452048980b0401c5454200c0d509801c0703288800703045942c2100c0a5000c03e02c81e16241c0300b018060415a5941c000801c160b24a45100007542100c10001c2d50984d8500c40c05081664905404c0081c0c1ca03001070100c4411205911200c070596880742c5402040c00c00001000e4010a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 165595125 1250 165593875 165593891
    0x9060e0906120615030c04060501200102130b07021f0509060d020712030203040507080c0a050409060e0111040815060d0609030c0807030206061f0c0308070e030a0501020d1d03040506030403030b0301 87
    0x44c0729400d2216000b0150255405003c0c100180016507a01e44035550000c0c00400c0c080c140450001440868602644009442c10501407081c50300d03000681c00601110100081e40720451600072140b0741c0320301e2a400c424090056045001d4243e0081c01c2d0400e0240200003014050265994115040c0c142c4c4884940800110b0090044c029041110100c415102c0c1c1c010108240d6000600207082c09002803500756024103000034070015041011088501c00d1701e490b542c0e443d903c3c0c28026810070500349210181c403507280100040c07a1049003251810300240d40c20900c07046450b2111840d2169400580c0803039804840e2030200ca004400040180070244041400420940d0100f11680201002c451018621711800c4d90100321900a0f10207401081c0380100c0c220001c0d024580a55203c0000c3c240180cae2208050086410104007080489490f54001682d4800d0403040c071902d00c80400d009a407941100da480581036070780c869030280070300c1031101200141c03c051082d040a424004040c0081c44001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 165596375 1250 165595125 165595141
    0x4060801050411190b0415090302120c1318060c02120f030604060b0301050607030c050705060d02030103060e0a0c09020d0b06070b0601020c0334050d03050c01050709060e09061206 79
    0x2911483d540c8036801481309141c2c08401c007200740042c2e8070414103c0d442d0030301d844811543e00c00c102c8442d00500c0101e0000002523981c8241d2904e003892001c0c060f0070895070030001c0107074092007000c008954610b8080904c0350b010102c0c0c141d0318a580d00207070015192022580036803034401c0300d00f904003015400050050000c4110000313140207800555041c40010380703580b09405180424010550000024094a0042481f44440b803054500850540c1c02e960b40350707400f0070901d5100803a503003002c680001c01081004800c0c415520038400c3c200180207000407641c0d600c1400c07035541c41104849500403642d80d113080c40c3da522040d0982c80050440740e0b076150a24240c1003e5104842040c050701032840308040604001c12410340721100c3e18441401038403c624081040d80000d561519551082034003c102900c5010000d608070b401b0f40c407159203510b55240020f003034400003022541007040300c41d010070500c1d400c120b401e102103408560501a030790700d03000400c444038501d5a45410500c41d6005000c401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 165597625 1250 165596375 165596393
    0x16060509030c0c0405042d020405010602010207110d12080717010f03020f0d1707031205040b041b050d0303020c10060e0108010b010908101d030c01060609170706030b040608010504 79
    0x40982c2820354000300b4102c1c007000100c1e0310480b4003030207800352200038201c072803104900c81c08946a2142d8141141c00070b600800c3c210f07102608000c0241c3e6000601c101030050510b00b80303039000e5084850500c0107409546540c145400c401d540000e0080c494041080c0ca0f0145945540c0058036986140017980c0d14480008041001d05c0306901641a840321042142085d031448000c40c0c0d005400780212660303402840d0035641c0304030700a80400000c0c0e41c0c0c85100b510903008043c0190300070160900e2074105414002c5210140c1e800c00380b64070360f5040c410059519100a0501442e41600300140c0b01c11504074443c2c203000d14072030402003140c5490f001040008003140350906851440c0000c02c8004030350f0005443d03245107400b441180340d2000300d521011041e190820b6101d1070300002d10100c030001d000c18161864112140641c0141d45448003880b015500000e03200080c100ca0388204c00315805020210745900a90140e8010585c030f13403107842e0301c07504c41360400001028414000c10451407d17080002d0b48d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 165598875 1250 165597625 165597637
    0x7081207140d0903080a050c0625110c1c020d03110606060408030418140a05010312030912030c020c2d0a05030615040605040509010203070314090c061606050903 71
    0x5a1441251107410000000440c101c5801c415100e03500010300390303224003186401802c00181007020803c411000101c0070704c05a4044d0b090305048180e680380c5551030300b41c00d81003e80344a082040341d0303008080c90400000d920040d10026500034001140502c03428004c450440e001039008203900f4803600401d0790021229020b00c40c180180d80c0e06441e02c008203c01d511981c4580c180e40e500c144014400340412b07000005640141600c00aa13808203551050755441c0b0480e0b03070701102643c44c4010028842030b4990f58511080c686000c000030b841c29926032450a0b20164440201030b940d02000e010580208070490b0f414400034088003900b40500c0c03600160007881d00402041d10701090130b1443c00d0400c05140b805480300100904080e0348c9a0000c100c4032040150340d0781e030cc161a60780010340d40d02d0340d10903c1d0183c02070350009079580c641a1405004c1d6049109011a0701c1081d900300f02c0054000704690620500c1114001d5491500200023548a5018000505010f29180c14803800c514000003c00e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 165600125 1250 165598875 165598883
    0x20d02010f050108070923040312050603030a20071e03060e03130303111006030305030a0b0910060c060f02040e0906010b0414090405031c061e03020f0603040507081207 74
    0x1015070140c0d01c0c003000380d800a00c54103845610800e03081c0300da4180c1e900440d000360f100e4501820011010910403044071000d85054000c1500c02207921504500760103140c0d407144040d8002d51501c3c50300e00000384801000464101b03403004c01c04a8000d00c05050200c00c0041c00e903004201011031810200c0500d490142c0700032901285007089900c04440003000f070750301950603001150b0500e40303503407402d03180420074555442640c002c21000140d0013071036201d8000030f18041d5680b02d40741d00c1d02020302000c5800d50049284140c0c00c0a0230132029400400300d640c140c078075500e0418581d12084c501800940b540c0700355010403900105000c16001644610540b24502c4031044800303503640c0f0201411180b25500400d46801c415819000080c02d001d80e0b4540c000d0f03c85c200301c07480c0c0201c02d1044c1b42e0301204000d100c9121900e82101300103540c04040203800603900c0311040084585144d0000b0b052444004c00305025580c08000902800710030702c46d58008080143c1503540c94001c0c80d40030055030f0310a201c05c40e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 165601375 1250 165600125 165600131
    0x804050406171c0c0506010608070818070302131103041506120819090305060405061005011d0904030c0b040602250f032001021b0c03060603030414040902040c020d0201 74
    0x418814120410020102c0100a0310300407101c000b02e2000d00c89110302e01c8003481010024200015810807185000f00a10342e180401410030300b100402004020304a02c0c041c4d00c01405090304803202160f6007040f0307641103c1944461a0002c0c55038040c05040d503511400320000700421040c022048900c009204078400204005600c6912481041c180b0800140c115030003446030b804000a849005c0c0b42d00005410007120842d6295525450301400b01c0f021a103a81111003030041c02200101000301030070003428410035410260b1130318808100c00341340b05846414440301103000d041c06140d041034001d030402041c86107898141030520107984035920380f032031041d44440300005403000401d40d030102c1341e0b0110040c9540401b6880c00c481c070001c0c1050242e4020090b0000107400f04017407008000f51688440c0a107031864500c40e00d2420303c500c1d00041c60180e003144080002c0c5950210464095810780103610b5002a82003012074000c0a1042001b5007143c070701485012286e070005442c2e040501e40764028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 165602625 1250 165601375 165601379
    0x60816031113032112050a061a0a02070509191805190b100b0a0c1a09071412060105060309070315290102120705010b1008060a0605030f0c07020102010212040804050406 74
    0x1083c0d00c80b40808280d40001c5e9070920b00300e01c0400582105401c0086c40001081301916015400000345044400052039140000c020072160b40520080006090884905485e46001131115028500c01c5c0800003825603030380c100403120700c0f14100301d203d200e07004005c8504800038600901031942141c00c0680c0d501e00058002100c080c401000c1406448000c03090f1410843c00384c50a482c1d00340345e098100c1e0340c080d1280c034440208000303010003480380c00c1c80b0004000d0140b81220303034400c003503403420a140112400e048504282c1000103286044400540e045540c0755a8515914100300031a0002000940490742d80802d030b01050300b040300d85002050b107824480c2c907280e6403500c0400034081c6007405a084034004070400455180036151142c040c2d4004560f40c1a036200191130907503402841804510300e0300038400b9909014400f440a007a41d4101103155023000079031082c180c50010030907141da400026280c811a4400c0d0180c0f402518100d00031203190920745011000c68005000d1075000383d140000c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 165603875 1250 165602625 165602663
    0x1c050703080903090117040f020d0b010f050303090904030f020304080a11040501080c011e050403140f0111030f0f04030909020318100c090e10050d0302010209180106081603111303 79
    0x101d0b004c40c001611400900103003e8808441580014016a200204100a0805604c80c8900300c000340d8401c4050504940c1469440d4004107450741285000b80e200f40114480c1c5e44600c1085078010b0b4050501c801d0324841008120302d9480385400c00c44960141c0480c907020050003120110303c031541104c01380910385c0ca0356651580d03540840d4006000484504406012501d0081100c403000203c0c5441858a907c07174886401c076840141d055a440d07480480d08400660003845080284060310719264614102a015000a07207005410608075840013000f241c01c050251018000801c4082801d54492801813842110075400c804181c00500038480c03c1251407006105070b8464110644842410606200140e0000d1038020540c03819a60f0070500420035580300c02843c402d041c4a0390026a586180700d042c00028911410502011409000140b155940200d03180d9400142100c040c00038403100d00e0200c002d8101c501c1d0302c104c41d02000038a80c0c1c00d500805100381c00d50b0300400c0141d60741d00303180320 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 165605125 1250 165603875 165603877
    0x9030f1c0c0b0f0c090a240e06030c030601030f0504050d02120c03040b070f02040203040b01090b06030103080a0c030309140a0501060e151e1302030f1311040902031c050703080903 79
    0x1030014404460b40740010764080200c000c041e00300000018081c01d000d91100411300c40c000310780014581c699400c05000310907e0314500c4428040051420b514540041c3c0c02143c81408080d0075456446e0300440001c115902c60741c80300d81408070249052040d401c141c1800354079004081d015400501131034000c43c0c2034525031422106403400c00b20084d45824540032080109400103001141c008180151030070140e5114005180030f90b010300702500703065241c804500e0803940f004c0103160045009100400100d801031003910940700c03903800c005202c00c0941c0b03000c8005000d0010000d25280000074411000c2d14002440c1342d2843c80744008100c200d46407a040c1f03404a00c12600d5888680b51500c03c00c095040110101c014400c444841e1564605610005100b145099110142c05917001c0304000d5120960200f40d0781143c484a0f2113951110251600c1200802075480140110b40390b181c0d01085403400c0211000c80240800407042280d085100106035034460802540020541008503801d890048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 165606375 1250 165605125 165605147
    0x121b060c141005042d120c02031005150109080c01050403030c06090507060e030d020610120201020715030b0f180a020f070c030602131a09100302040e09011e06230609030f1c 76
    0x2141a8400c05c200c00046aa218000302c0232030f090300407610843c0741c240440c0121806503c0d50546030038841d2066000429006066100c21056070140400a001e80d8001c0c2c102c40c156505440c000b03220060604102c07014140348080208548206140010030940c000d101008030003044040e00e00d11030400904a030b580405070346111190328450001c020110001c46c00d040400c2c81801030703c2c0f000340c0c2d8070781c01c6001c50701c542c0d0f00c207010036140d00d00c1c1089882c0c1007c400c03821200171200c54021008003890304006285c0100090100c40c3e000402021304003030355007a600c05580c080c001c0c107002c070340b01e141640c00303500190b18408001898001c08500c9803c4c40011000c0c107000030023802c0c00c14000004014481112211440605034204001302d901c0d83d01042c01440b522440d40042800f00000b403c641d012541c406001c02c4e561310341482405402410103402800c0400034032554404120a00003582c68414820305ca58188201c0202005440000c1f50400f04447c01074a900c1941c2c0944100f034400c1040c070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 165607625 1250 165606375 165606383
    0x3060b090303161415010e0c070b15060408010c0e0a0e040206030a0507180b0a18061d0f0a030b2a090402030703110301121b060c141005042d 62
    0x2400b031100c41245681003410418000c0d559018502c40c004005814a1700b601000c600c5034000ea801481413441c84011247c1044613080140e01d0310405403207040b149070000d03005c20000c40121480140d282d8079502514050014503000b000781403038204d0094801111804018000c0c40400c00004554420200081c881c580180034203286503606a424801032000400500034411803910048111000c44a0a1301a140c041c0c009591003403c0720003d00680c50901d182210040003043c140001c9034021015641c80c40d2000f0160182442c0c1400261400c001d149856088800e8540000a01c807103601d44500605a66205008060712401e10b010042420001e40407100002c10108080f4100340e801164040520303d000107020561203480e0b05540d10a90100400969074500c0400b40b050008107980c4000d1800c03c2c1141c482d00e007001c017510b00702c3c2002c0017900401c01c200c0100c2e49810240100840000c04030010070840c80c262528803d940080c41c419810002d81e0410007400301e41c0e02d0b07500581aa00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 165608875 1250 165607625 165607627
    0x313060912050c1504030609080304060b0a0609050f011101020a02010203220b040b2a0901090603140103081c060609090e0604030e060c0c1903050d0f0807051308030c07050103060b090303 82
    0x2a550a020050440113194074131308400300400000300b032261191103960b5103d0720a480e03030780c101340c100301058031029802584600c1d030f0414100b01e03568020000d40c0481380255243c8604030800c10068407520280c1d02d004225500000b1021645a410b5000358416401c040d014154078051620f008841d03240c0f000d0040519154101180104020f2100641c0c45042c079a8140d980e40c00c01d402c1c484269501e407485201644c2d010407000303155030300f1400c0c48020b8520b92a00700124242c030341640f41c041ea03045c880506041d0740019184190392100900c0c0300007000411042c088165a007100420703000c0c561256020340c1e0300c0c200da88040007002003109809950036035a030307040c0840311700e04100d8990b011a100c3c400c1e42c410100004543d0f2201120392041908648050640b0741c0b650415600b0314202509500400c25908012000680c104000503004001450151f80300c0d9403190605080000c0d40d003024595200c0401d982c7c154441c005151019246e003a070301031200c20ba6503814090786010b100d103074580c0360300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 165610125 1250 165608875 165608893
    0x803030c090607080f2a0a0c0902030c0903060709032009150301021309020918011a07051501081b0604080a0303020c0a0602071419030801050f0d05031306091205 71
    0x1070b00390003500c0300c0e5000c1e1200e40c0c43c1158945070103c030740d80a8403540c10a1151a10710f50360603038000881c554183c09082c007405075900240d4420003158098000c3c2e900f12a40440070501410070794041c0c5001e08005000c0f503800d4104010064100c42c0e06101c12240000c00e504002010440c0e03110440e4042006080903c064990301e41e62100e05141c52070b4141c043d903003417001e442440c0440c400c3c20b00804500d603006076a107210b0014400c03220694220035a5500000004001c01d0f0409110086030300c115920140d140d201c00e1134800c2c240800409000c101000035000403644d2000400c0d074041c1c00315250401000300e6496401d01226001d50303c10042240c018000440109000b0380042c1071400034003081e03880000d40341d620030049070403111081e18000c1d0440e10000748104108071610380000b420418840e048201d54000308401014000d003406011020a80300207600c6019041c440c144d0301c8003e0304c0e110600103e00c9a280f891700c0c4520000140c0684002401c402c00c41c23208000c15400c41d01410301c2c00c0e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 165611375 1250 165610125 165610129
    0xb0f0f01110709021308030414150403020306010b0d0b01110606041d0d020312010b0f04030f06020c010e011b0801050310150b0c01091208160e0d020307030605060a0803030c09 77
    0x2200100903040c89501464481205000d00540d005071090100043e1500001541e2001d1498941c2150306035910410040c0040002d06c07211240d5440100c3c1c04001031140d0060149a50203154002500f501c12600081035260014000c1c3c901c10224400c200005007020700110b4406032501c022003034580251011a56505154110000d8a450864890103150011145924007034014090100580022600e0707444e0b0340b01e40d1050350041850300020360828031101a252954400d9200081c040c030f0680415404001007038066442c6911502e000304940b181d240d0749240a424007042a030700000540c0303169000140694422410b030b9001400400c100c0307082d400c0083c02056114103106114541000001d04170300e03c03000030411414404000300b45011546402c4040b002100c07802c0c02440710304010002c403910800103048140d0142c1c03030044200d565000129082d0221450702a4150191440200030300180f5001240075120a071340b42d10a080e0343e501c2903034680c00143c80400540e01d01704900e408034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 165612625 1250 165611375 165611389
    0x6130227030a050a05030a1e020d0c0c1509050a0902070b0610020c0607060f050f07021b010905061206030d0507020a031214030f07030b0a141e0405040f05100b0f 71
    0x4000281c01c480010b60541c440910f070141d261000c83d040d80c0009103402086030300c19071803594401d03040c1401401e29071501020752640c260f04030403020401c0a01c106001e204401580070000c103009010b81642120f04400200040300c2409201c2c003c03032460a00284505540c07003140c8607250012111a40c1352155001c004440003070750b01d11000c5105240e21162207544e141c0040a118ac410380000400c401070803030400c1954001000210451503030000c00600507008103400304030071400300c00074900051000043c3e415890980007aa000480840d1040090305400b058501801044040316968803907403004175690b1040100083d04180d49000810029512540360000762200d401e040700221020214404243c10403101500b081d21024184070a46800d0f100704800c1d079205403518520603003401924034403c88140310450080c0310105040c5c000b00194403034500350020003030042c04282051b007040c6502d0550060251b4050141808250b0464102c0c403402c400f42d007011300100710401c605400c00600c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 165613875 1250 165612625 165612697
    0x10f1406030d030f27030f020c0105090907031b09030203070803071e060207021503040615032d060c0e03060c030405120306060706060e011409040503090d02190806061302 75
    0x1c4e20780c4580044845a015002c5e0100c5030042d8401800c0d42625800c00401a0007003030030003030035500a56150380381030340d01000f00d6003000015074003200300b034840c81811002000440780c90341840c44002c0041048651203001242203900031030494250603107510880d41c40e441060310083c0301e0030302221128645002010114802e81c003881d001810800141c01007652103030400410000010000100030400405100d00c0c2407008604c0710080c581401e559a40e4048650b641e08001d0100720b444855210660030301d400f44102d540000280150581e003c00508aa0144500076200b8050f03c80010100900102030ba132281e40c03c003001f0f184c0140540d801540030b600140841b42c102c00104080d00c0440c4441c01003200034504540e45a40c0d030342c58401c1104600710300c110b80901c40c002407010701010880010550b00468400c603007000759150780707100150b0780401560f00b6989102d04440c00152402c4081291031007090b05603005051014028103072000c074450710b01e185010001e101654aa1003c40d40300d0144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 165615125 1250 165613875 165613901
    0x100f0516030c120908090a0603090b0a05150307080a060c0f1b02010c1a10090c090e090304030b10080106120510050a020c070b07120201060e040305030403021608010f1406030d03 78
    0x4480c465003e90205484012406864140340000d00140a007060720940c8000c21079880c2c20801220940e941034000302d00541140c1210761140c011400c0c54846140501c5826401412111000d0759550916241d5000300d00075200c403880d1403c103001050049540c075540d00306541d00c0b2103907050b50072950425821512000d82c10007010041c414006405403185034103411140f252405945403c00b002c50701c0400b030360030454403a401d0590960342c0c0c81e00710f08084180c621200c486000c5945e06402a031850041c0d42c0b0140030130301c3d01410710490091011406080d225040024410320b9195030038507040c190140001401644026914410704140b40d101355041905840d0240c03900400c90000ca203446416000080034041c000346410401040c1120042881c1440c0001d00c6524904070024011800040006d4284000040064109842070021b0001082d140340c80c507441d03940300c0140b18028042c00c00460200d5280800340408000c0b40000a403085e48018010144460960707811405400d0700c043d074030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 165616375 1250 165615125 165615137
    0x150c070314040e070509040606090b07060203060d08210708061f030e0709020408010614060a21050106111005040c060e01021501030308040c09050606030a090807050d02100f0516030c 80
    0x10a07180e24810000c0e00808150b542c66445400286c02c00c0101c4d0083e51044c428000700ea001008401462410345440c0d5401c00801a16652100f000c06c0c1c00480c4000b008000550000c5c06403034100d42c00e115403925044450b4070a2240d6500002658954010744d6000e43c40207070b1030940761500f0201490000030007080d280c049038603100f454400e03192110541000030071540125050004c01c5091244c50000c0002e11403500b40c11281c00c0102d5501c2c0b1800141104004880900c8000442d0032004907601801c01202049190394a180040910003110401c60541c047c000505c81e40050500030340340160b801c045200062482c20100751611103003000078506500455505130081180b69151a000318003a85580c040c9103400e1801552424081d003120444c545084140300254480d08140e81c1e100c00c880c00c0c0010100201c0c01c100c0040d001c2d840c4024030754460f42c0d030044141540482c8144411010310414000303064232140001c265101204ca0000840325101c9949000f8401e400011008400381495 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 165617625 1250 165616375 165616379
    0x105031c0e130c0e0102190209060102070f0311040b030109030e010305180a06050f070f0c02060901270602010b060a1d04060b1206011205071704230f150c07031404 72
    0x4074040c141e0766150520050b983d031001011050f001122130884140910243c019181c0b95a9003036050780e56920040e000c0c980c0c110000d50582d0003040010094070000076900300c210781d2490b000680b0100c5141c42c0d1b01681c2001d40c40c8400741014000d90002582c56161500700000d060011401010010000780c40390303951104908404400b8416000d002e030103201c02040602c1c204980314606080034000504025445240b480c00319804800104800d904682c1a0f54540c01d010040701c41c108180b00009102c0c0301c041c80741040e4019010030700d0031900c0c00c1d0020310084082008012140c01003c200002040c00300c040360010940341b0b924160a090000d100242d00d64031070b000b1a48580080b81d1403007288240d074092101940c0c0241240302c0151000d88203020303d251614000388401030740c0051040881114022034104160a080d05000d0207030310807000307400e030050702d0310580d104440b42000071103025200c2c03400a56a070fa550f40342d20908100284d585480020b5400b140c03480c170f0501c3c05a10911040c440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 165618875 1250 165617625 165617629
    0x40b0f0415090903050d0e0c09180c060f0a170112030309051504050d0e040204030c060c11060c0a1e0b04151b050d05310606050301020a09080708060105031c0e 70
    0xd8240e0f22402030361000d48030503510481508840f0480c0c2c030790003e41e2000700031101c00c1e5150740440b54001c16510005400d011128250742c07a1410303008071075902504c041066680d00314400c0281c24041516a1200f6841d082c41d010a200c1440c280510746001e00f09042c424080b074047d80103551040d1140c4100d6610394421400106035510940d8211411740015420007046540901a0b504194003214110b19040c55075440d20300c2003c540c450f0b40b06100d019061002031014029146d0209000a41003d6981440021b01a1034416860b82160141c8600c16a43c0c1a95a4605280706144d401031071a481a2165210303ca40904030600c051805522405002d0006020348040e86803070792030340c46140d218062048080c00303844000b80000309004140c6940e0f00a44000124040319004a000c185c203412040c0c140721000d8010340d002290550300002e00c0028003030b8000040300c201e41c0f40b5401c1c0c03503400b6150160707030344c0301c0d0800c0c030699074075601660510328401c890391041e900912860420311840405080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 165620125 1250 165618875 165618881
    0x60d06030b0106021e0a0f0213140105031603050703060b060d0609021b0109050a02060a09080f0a0611070309050405061f181703030c07050c0a080a0203010b040b0f041509 75
    0x700d9505501900401c00190100b0480a4030001914002d081d003140400700d40d916400808040c26a01e05282c040303055441700108501c0004034560107100500c600d9408044002082c825039005c0d126100f41e40510f907209403890700075668081c018001952560702ca000261984e40f080c9a48000c2c1002498a42034003442141c0050001820245e21003181d011f40c46070031001c544089c08964103100100700000e401040c4104800c0d411a10070b41c5480c013a0704101d41c41c01154201c1403482c400c000b901d04540d000010303540300c02c9100720414400c91612101480c400d0080404c010040784082e84180028502034100581c0600d024140c0c100002c4200011145180c0f08844d400101d01207420440c04041080802c20180c2a0050b441803a0808240c40c0e940d03e1000410243d204400880c01400f0440180044602000700408880020781c458a44540740c0d0015a000c91285d842c0050940304c90805020f02c0158075801440520314901c050144006070544c841e4507450b80001900200b40112a44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 165621375 1250 165620125 165620129
    0x23009030c0310150603020906120a020c160e0601021f0902040b040203040f03090e1515090901030819090608010621150e010f0e07050a0912080307030b010f0518060d06 74
    0x5440882c003500e02d44000b00130000140c00210425004010b8000a5211042240c0d049083c1c0302520f545a503810a51100a000d8030002c0c01050290a102c3c0103140712a241443c1606d903540d0840c041500c58800599885000c1d02005205010410303845d0f02c403940355070101141078006400810301c8400c90001038100e0344100c504580c90384a880c4a1424154054207000c00341c10101c01400711401c02c000c040840048d11040709104034181c140b503145040b10082034944101c8007800000781781d42c4903d0880d01c26005004031082c81c00c3c40c0b450341c02245108a002d842140c0003529126583e9080060842ea00600c00300b114019501281c1c940b541c000b00da204541c5000ba504041002d454149a102e80c042ea0040e40701e151915035551091251b00202911107070440001d0034000e0f035075111030708280c0e20500c1550021824120754804141800544001140f1900c2d4030b0383d007003004006401c01510a100304500c01800140240b0101c2d0507590800034056115400411481c10034844440c42d4065900301d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 165622625 1250 165621375 165621403
    0xb0709050a03140c0103060803091504080706020c1201090c0512011407080114030604150e190803070f020105100614090306090703050607081504090303110307090501023009030c03 79
    0x1035022800f0719441840a4550070307500746002e1224916002c549540c0e4002c0301401e0380300ba900c82d1080904800c1c00d02c100c400610005094881d096900d0304c011303464980502d010380c000c003040010386a5001040c401e410540c0c0d4002e4484007481d05080501040304203004c030310300c081c1d036940c042213450400b900000c5108010964030f070f00300e07503041101ba6100c8035460f100841c081d81c4418144030001d0032061000324090540d480004882d07600100051a2100d0300c0355900040401441c00002e000f000001584038000503141c07001c0d2081c10300307012422114102c503048003c6078125410300400d4816800300c0c0c1203000d07000c052800c00c3c12901c0000d040040c10350ba000f15591015404204100c02440703101d03440354a5007014452460101c2642c18072200c45000c5500c115505c0d50300004050080c2d002000003482d404003603440c0d1801d0000500520700500459001d8401c000a843c0400c018003015804180c2c1349884030449180c807410b005050700174070b1105615010307815501503d510108003420306107044c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 165623875 1250 165622625 165622643
    0xb01090c260108070501020a0c151701060203070303150303050a0c08040906080304051302090a15050706180b0a06050117060d08120a20090603060d061109130504020d0b0709050a03 79
    0x1d00001c3c9498420542d10441c155000400c0300740100b240d1040c02d030100c886074a072503140402501c2d01202d02541c0c807914619000e1445002103940780e400000307031842500c02d8504102c0d000c428104031840031154480180051001c1040c10030992044109100280c89a110349003026159405081640c042d074101101e02d0384003240801c4545800d8083c1e85d9420030704a404c5242042940c041034140703210b809501c80c3d00045001116513640300f00c04944280b500500d040258240400c800740e504041c20105540000c4524003094044981e4413444044441c142c50f00b0b117003000810710304000650300500050340444c2280076540801d440c500205000103c18038107410515250300000b00f242c00724519040b60001c00184031131400a62030444080940403500d540e160394a50002940800440000522a50a00482400303520011014280100d41100c100158440f0f1038000004c94500b10b030042d41c00010001203402081d07540040c10303040281c0789401a5074617214404651f46981a40c800c43c2c002d10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 165625125 1250 165623875 165623879
    0xd0201060f15170a1e0608070308070305221e270902030a05010e07150e0603150d0c0510050711060309030d051905090f0a080d02090a03060203090601050a030b01090c2601 75
    0x84031484160117003440710070030043c050034904036668800f094000140761450000d0740d042854056401d541d451009032092800120304503840c44014881446040e014032002100600e01c440719400707110070b5070078030601400e80206004400110301800f52100b0410303640d411068001d80c03820301107019058042c000228201c001345056078940070080c3c3c801d40121b84500ca0101c005544088210103030320080301c43d1a00d03501e5040c0340d0030004051031106d680c46003000c030381601005501103141e0200c0c2e40458405050000018040d1454401c4150040207a008418840000e1030180061600b04504030100c86c14203040c0404401128801c3e90260800a25107a24402010242c0107881e400320400c0003910105908140d15a03581100c203400806549000c2090010590b10360b054a403107480c0109041e111554030b00b4544000c0d40140d1311021f403070103204004201402d0001d459401ca9070700c12002c10349a03107020b8188000740240c0c801202000400e281c00d0307030020350500c00c82a0300b1101007800d0301154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 165626375 1250 165625125 165625151
    0x2303010801152421020c0c120706050405012a03020c1005040f051e0d030e0f0d050c010305070e03070609030b0609040807060519020c010b120610060c2a080d0201060f15170a 76
    0x36008c0c4c1010345540680c0e024009540e00c40141d4044031002c1c01c1051500362581d280d1410420300f10f1506540800c51b1803a00e041c1680001c2618401506035010502080d00f22003c0350688038500443d45090180345040000341030080203803404e205803000301d02d030042c155030014440800d000c81c103a0014110451031400c03403501c48600e50340c03008120f9078000700c407078103945042d11148000d0883e414996524002940715000320850701c105080141540c1d6861341710103000e000780a1a00069801e03005c602d001031105c1c103003a02094040e5030011032407810881e180c1e8605025060081590b0b4288001c00f0300030110744214000b50000b190b50800208101d5608001d010501180880c03041d40e5a200c00700b84803964140595180c2554400d180c901c2a01e0789038144100040c2012003085550751000c044a4911920040140c0075503001d241503565004220401300c0c203a40541c0160803e01030071007000c01101c186c10241c20107041081c103040128680401110030840d604541c00c4010940b144806110a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 165627625 1250 165626375 165626389
    0x2030307140a0c0f05070503070b0c070e0c220513091203050c161a0405030301031704030818130e0f070501140403032303010801152421020c0c 63
    0x105084101c02400c00481c000000e02540441401805042c0f68400000034450305110305005031002504480c80782d640e0f00d9804070750340c0c403031800d103003460080784c4011484000d550007040c000c0c2c180329900d81c1003918404c1882410080c0c04807498178285a40c400198940320b020307600c00035520203c4005800c03041c0782880c0c1400c442058030b0408040ca031000b040001d103100000e03a58103844110885200d03001c54a420f0384100310001030741d07030303154030940401c030400000200440c1600d1085414480319141b1110414881c0154000289482005d022124072070f18920754154981d03500401948809a1112014007110441d02e00780302643c0025050800300541045010010542860319201ca91810204c1158500440c00002d04114902c480440a00e000318801840c4480004801e9906d50b522211707280208800760035501081041c0c90300255048520100602800400907200c01044804500700d0b00300000c80c41c800c3c40308090b0306011000700e103284003824103194518010f0203021901d104003c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 165628875 1250 165627625 165627647
    0x60e0309030703060e2103040c0e090c01050a0309080304050106030b0106140f0c01141602010501062105070212040314010509030724020f190f230903160602030307 72
    0x55510400c4189400d46001600904903070304200006038121800a5003030070701c4221500c0d07441d0100303000403c0c0d0300600072900440c02a031080c44001141c035a102003003060341c3c030100e40c803c4003034001c4e48003012154050300082c440401c0f545400101412199101c0c4100c1e00159400d03107460b95280b00030f0003002521201103015241e141000c10b4981f400907401c0c5524414005c4440444902007070201c810300c42508005090b000c284000a1035152818241e12100e2880c08220300541c2081c00000d500344c0039000003a0214501810352807803c407401003002c042c2c60042c00d04011407090080b51400346100c45e002e407001d10f01c242c04550614000300b240a0035214058480e0015800400c80c440c005080380f410203c025921600051b1880748a4100340002d00030b4003660103103a040001d0041c0d0440c00c0907910b0a020000d80c403104001c0305117403011100880b840c0000d202100c000345ca055400c801e02000b500d00b00500508884030ac0030107003c1e18525069560018026a00c08014400095040551002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 165630125 1250 165628875 165628901
    0x9060c0c0b060915130e0d02030d060905010b040b070201230c071409043005071e11010c08090303040608010807090504080d020d0f05160314010e04020402161703010306 74
    0x403060a080c00c0c00e4180ca031199804c144100c0d0070240500d00c0309a16042030201151800503207080040c0948042e40302c0d40002c90380c10542d40307040e80119841c4098443d6506a60358030394201d04090801c842140c0e25800113500742d05100304250414880c040107400c2d11000840344071201e0701c1d00c1e1100e080c41e10700301c0c1d1500842e91666244c1d802074000d0b25501c06a0f640990408608524088070b044038400e100040d5291001c0d11030314404801440d600714000b41600c0d071041c01d00c1940000c81c001c2c45004520781000c0244060000c540101c203c0d0301c20b01d40000120302602c1c8a501d0f081d44000085d26641c490b40c4030101081d0302100400031420280198001084014824040c6243c59900d0315510b124600c841e445041d404121554880b1460380b0100314032032552400c0015041c003a070111082d5402030705400c00203051060002c40300e110b070540c85048a102d01040c2c109a112076003040042c0d00490181c80a4444040a001c0461135200d000a4404281310689640c0d505505059042c0d440990a9103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 165631375 1250 165630125 165630139
    0x50411090d02210601030c0611030a0c060f0b040204080c010e030a0b0106031e0e0105090606030a020904080708070803070f020d050a08150402043201030c05070b0a09060c0c0b06 78
    0x98141c9070105212001981161010215001c042d00c0c0301e00c2002c03e0603c02d0b058491134001104000c40c1c0340700c1c10250780503a1902403075104130b4028241c1e41c2c0709900c050350000310344240c400c0020300550840d028802507180301260717a100b00d10210b4202e8000342d21030b8507240d01000c2400301d1540c2102150660410690151800c02c80c00c1e00c42941608040c4504000c1581e1460201103107402451480e2140c0380c0c0c82d400f40942000c0c8864280689002d5402c20300500a9101088a0345800101485110ba000d0003075000f507035031511034600c0342c0c20455081c1d0b04a0400c1000d000000c40036001503124104a4031010010000480001c1c40c1c25007900702401405810060140c05641100c00950b1040400c0d1040300781c02c000c1004a406800303550b010b0511a01c0121200c0e01075504154450007028a128180542c1c6007541d004406075071802c8030540205004119a00c0420500012a0351000b10642c0c0490082e1075665150304903003014007008000740780302402004201c0100015030b00014122100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165632625 1250 165631375 165631387
    0x20d0606031413170c01051f0f091d0a030f0f0c0b06060304051e0f0f150106110f150f09010509030d020703020709060e09060a0203010b040605070305130609050411 72
    0x3120800c0e0060301800c5000145020f6004203e0744250300311040404440c05074466154074810b80c06001c1c00d0310700d0500d00040240740035510301440c9080341201c4a030b44030b0000340d41c07524003158000c08a40003546000340c4800c0d04141900b1040100d407400034031a41c3c95041140100307078001c00a944440c2c000d410001c0410315080803800940f0b00d580c210b14216141e079a40d4072149021403900004d40c1401c1d201030807001c1d04000708040450130030780046411041c0da44042018900700e44902c00f942c83d404200c0d242100502640388111401545070010308200c452003101000240e281c007900796815400070315524100304542d58400c10140d08000940000c0c03102d410900c4007035031203004414401080300e40c04550300041c0b5200300310220041140500800c0740c103460340450300c000355040b68418110700c602d00101d50504503d1007124100e4500a9886c0c1c00c060400e0801c850550120009508004c01401841030320070341c101041c00146442c1d150320549515100a100c20344408034420010100e082c406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 165633875 1250 165632625 165632651
    0x60f021e0c12030714062a030a0903020304170102030a0608011b08071404030506060907020703031d010309060e060411060924120405031210032a0504020c01020d060603 74
    0x21420981a0842e41401a9606010040d245000c1c070b24014068104a0f5500d00c181480451040e014415800c250140100b211908090803c03100c03441042c00e90040002131101001a409903880301c0c07082c0b05507032a00396540c02001c00c43c11185121007090b50700005020200c00184540c000070603250b0300910030301060500d40741c528140c7c01c01c4141402550400120b0316480f60714081052080488961340b03c6807a400d00c20395a03902205c0d1a4080e50602e40484e45141c00000d001c0d0489905a07103100501e00c0c0c00d00c1071981c03440444c600d00c0c14940c444210340e0016240d0b000e460084405107005140c549413074208940c2c140820658907024090400a50049407216442265180700100140c1c842910041c40990070344a4445070303108101d140300c184402c00002100406103211000c5240c0056100c01c1c1c90606140842d20000b060315004042c624031000d4241c410590580e403400503812107030b40e10300c0070909981c0a280e5601c1182d40c00110010042c26074400c1d500946881d1808004000717003011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 165635125 1250 165633875 165633883
    0x10602030a03050702010b031e010c09050a0b0901021014091006210212070b0406080f0f040f0f0b07020c0301050a020c0619091a2d0a0f09050304060f021e 68
    0x1103940805490b03c000900c1c5034000d400c11810054068103c60f60304080c421500f5841105061070700c0c5035400d0410040d1003a22070440002501d500500700c1950600d410761540080d404101b0072410b43c01503441910010f0322a100d4000d00310308074880d0f004e5a04d4500105d0303003801d041c40901c3c482c00f46843c00030700494818011040c416180c0103100c01d0071080030300000b904a02c080b510000e4a200d50040410700c09a410060021140e90780c03038005007503c9540d10313100051000c51303505940000d01000140415030711103012403100d000c2d100c0f07501031181c41d48940f01c03000303c21a259000b41e40420507001660909201e015031082e9090400c605000203640070320f03110300c0040c08032400c141b50305203100740d8480550b001400469112181d4440d07003640410207042d540c0c007100d940c4918114403c0c5034845498145406042d40901d8408500c13640da41c040190080a41c1240309012955508000d40012020401000a800f16480340b00c3c142142c800c00030325001506d1030300428454050110702c000ca00c005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 165636375 1250 165635125 165635137
    0x20124060e121b060409020c0312010b070b040f030e041b0e0f0a031212020d0f06060203160303020f0705030315090619330c03030605030c1f0306180c0f0801060203 72
    0xea4009200c5a01e000000c0075170199800501c3c40d00d20000c0d240c44405030000c01030494106080321040c0580c1c2e145200c003020b0055407406010703668050006800600d18802b921402c5100e810006841e00d10705002c141101e407820310051a5401c030760100040e0320380011104801680484800040100d844040341400e50244002805003440710319001040d40200c0d185401e4400c809811510360f41e94800d602e01410660b01202021071270a20040394491000c000c45a4880402c00781c01c132503041c1b80d03504400940c4618007207080c9000034050040010f9003440118001c40014401d40b960100c100c3c100912130101421861042d004074241c03030180d1080f8610300702100c4c809218100c1409081000101c030b007a6444841c0455074a074801444a00d4010701c0c100c070f14901955040203101d4503070081c566602000d8401660150144541d0b224060b080c401c442c0d80030026141c046581942e03a50b8001540e01141103450016842c0e050f440501c590108119500d0111031030004a29450508003a44a120300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 165637625 1250 165636375 165636403
    0x507082a03310201080a060303020d0810050301090c0e0f19050a0f05010e18030a02030f0706060302040c050d05090a0b0406091a0703020a0210020405030706050a020124060e12 77
    0x400020b01d503203600d1241104024140c005101980e510704802d989105054a04034081003840c1e0104910700319921841c000d580c0d050700140700740b6030190740550b00c20f04001c0001001c154940b0000c102c030f884c00c1c02407440172481030110419042c1402c40401501c480240801c0010b50300f10204044082a04a005090309900c1d00c009602c0d10798068801c09808110000e081141c281400000d60420304080d0318414145024849001e085404600740c80380714010ba0a401640300340242d4800300359407401080c4040c0300d8100022850790300d5000c50207651807100020702061010445528459080c01036581c0020f03450040c02c00b80c0043d5440804401028101a0256075208005410080b00074030120b603042c1c000f880800d541c500300400030040d510140d0f9400040c0101500c0c00c01000041c0296403e8410050140000600307044d03007101c007500045820300466480302c0d80000900000005040102481c0700e5001859042c41c0c07016191030b46031341c0003a01640800d0b00740201c0304800b01d1914012491 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 165638875 1250 165637625 165637627
    0x613060c0f020414060102010e0105060109140102070f0806010501021902030618010207061b0908070b030604052205010f062102041104080f010902090702060906071b080a030507082a 80
    0x1460420700400c102807800250041e150807607905800782001c030014030400d0264001d01c40180c0c42304d4114243d40c3c05903241c0740841d044003414000e1500540900c24900c1040c4100c2e10300c9075860b420b0004001c0321b60303c415003580045c80140169603042c0822020004074030700c00d03c40c940965010940d00d000040c0401c40e80c1503140a00700d000b15080d012201c54641000c1f0900030a207989090081002c44414124007144641d10009050500030810790110340184030003500f95a00c10003808040d140c000c0610350b400c00c1c10140307005c4001054004911182c01040000703404c0c0d0302c400c1b840c0300b151041e400499401041c030200c00ca07510300502e00c2c1d400c6241d050750042459030580e01d4041480c001c07a00b00c10454000c202010b88603200550011418500865010300d45071a141c0060340c550800b6a50742e410340c0c001000094a0f00c1c00b41c50043c0844801e1519107103116410f44881308035800040d0744400090700c45c0148205036034403112841e004400c1a030090380440d903000b0380103150290b501c1c2c03040c14104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 165640125 1250 165638875 165638897
    0x30d1209080d0e160909020904060504020103020909011404050f0c0a0315050406061805060304080a0f1b030f03050a0203060d0222020c15010812161119060e061306 72
    0x1c11003096038030850003824140300c2c0d00020f04580351182941403880a00c03903000340700052122100d00034030344003070b401400081c1251a07546441024080c0103200b6030500d5020002c1490715114292207a0091140c170f000d11a5281d030350020003042d0342d00500707210380c008244412700c207103d14207000329900c100700740c01c00180401010709400541c9400c2c0e44100d600600d40740340050351580214840c4211001005041e900b07946030003c00416020a0798040c00100080c01460035041c02184081181d8a0300d00f030400c0291525880c070100703540142001c80000700001000c0410a825008540c0c20480011065040d4075001c0f021a010b0b8a149602910804503200303402d040c00d03e445407158002401140a654a030145018113603030b00d610000c403050044410b0000112240007140b507440075180c10740d1807890101114940d0411410051090350080303020f206034941d903034407241d01d00b54424140c00c0350542380e40303000c3c0050300007540200c1e510301402e002c000c9400032505498420040e0f9505007807a1140c80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 165641375 1250 165640125 165640133
    0x12090f05240a03020702031c020a080c0115120b070f021f0b060c0708330a021c23010803030c0c100c020a020901061115060d080304140c030d1209 64
    0x1144081155580c54070004040299950680090104a00a4003203420000740e08000780000010306542130f0058200500c810001030010009001100600002044018106245105620307841d03000e00400d90025001c6070400202c0c51580c2c4e8003480f217040c25081c950f00500081d480340c4002c0c24604541d110f0036080300211141d540b02c4451258041d003000e403034106591036281d0724112802039034000d10072140841d210348a801100461940d40308607518000b5850200d15415440c06098241080e400f442481d0303646100013842a5403603074443e40480c0b22581080e10b04000c1540d0300480f11048003443c0184440e150000c22250841c82c940c0348640e0301c10794000d0700c03400c100b104003001c5062410405030364140b59000585009290003160482202d0340d940300c0564140d810000c160b201a004009040d014020450b2100e9000f04098a150072203125035640141650044a04880c5500300516000041d003042001c60011078090380100b46a600d0b1003800360261180705a048403103611201854104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 165642625 1250 165641375 165641419
    0x406050f01080c0a05071a0405061f061b1b051009210614070804110a050f041a220506032802030a14061f0b0f180907090312090f05 58
    0x743e034111fa041c0c80f0ba00070070002c882074a00142c8050303846104041c08548220500940341e0034100c1441e60342810741d1714040059030311400089032000c5c001d6540720103401082601d201c8801c0d500b0300a13520f44c0c007242044104079440500250348420050144800d001109202c9416001401d01200075004050a89025005011003400c07020780304d1154018007a0250700201c402c0e000c0c41c851018400861010000d0100030714251003016845030b6003680d00056410182d2018410101c5030700c550030360300380c8000420648603d401c0c01022a480c00034015110700985e20425803c0315084002d040b0300300301041c100c460740c624000c4803161004503101007011580e041010a200d581d11880d070040030103047d001c1d1a00c0b08001c84480f00d0081d007000ca03464860107821907241c00d8940589115081251b515900b100e541c010a0344007002d0241344150300c0031075039612402c0d4405e0540703540e5440c1590662400604440c010390106041c40b08007401486111f050742000000ea8070190380c0390b2040d9030070690340458 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 165643875 1250 165642625 165642637
    0x10c1b0206040f1e0608061305090f030a0507032a02131410150f050d0b010909021204031704050706030f0b19050f01021c0c03050712020a020406050f01080c0a05 71
    0x40c404418070000e04d0311441c080d0500c0816912546083c01c40d96050b09580520040f500fa0707074403910441c1c1020218050b54481c0d600138500c8c40c11112145980c480d680d01e07507800581100089100400d00108150340480880c1030060311032500c241d200f200544070480f1002c0f140b0001d00c078680f2100600d0704a80c0035803000c07100b1510480c02041d28100300001c030007150701c10302810110981010b42c80241601461000c001c1c00744a646041c540084450064000c0c203044902504101071000d00082d540c4982c00030f420111495a820303482d505103440c1c05804041003c034007640b0007414204100c0031038008500d00c01128020700f000b04130050a01d01c100b00a0611038802d40e4800c0448901000c0b5000310031010341075034002e03600911140080310042e41d071030f203100e01d44120511140b519200d45074402d90b1003003d6207120b8180306082501590300d41c01049107240880340164410b061050540c1b4260290304014034080e602181b100380b520000910701a40180a8240c0799400034000840300e105808a0ba9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 165645125 1250 165643875 165643889
    0x510050c0d0305161b11031504080d06150f050f1204061a0117040f020d12021605010903020f0409170f0408010e070f1203021204060509040608010c1b020604 69
    0x1c40300c18241d0000d00241802c1d00e000404011a2410000c0309019071040110b400c40310a60b105c06000c0356a400100c103c000c6440ca4250003065400c40049100000581c0124440c82d000e540310791404072007508951103988418844645041d6101903950130900b210741541d11741c9840d558903240d01d949906e044c86620901603410310301e03208010901200380e0000042e40c1800c103c21042403100001114001d038060303501c0c4080451080494001100000c0c0c4402e000e04c0601800c03030302c4280340c1341c0400024013002c0010141c1c00c800341d003604102414902c00041c0c482400e1240f89941950007107031181c656041a170740103e43e1204a0000c0c411010b49110b044605ca0001950380d9503141c82e50a42da821070700c40d80b07a4960a05488405c0758102003058800e5a13100d90070b20070014075050300c450783d5814a80c0190198000c03040800e10300b62240009001608150311000d555030070807400c0c40100c440691240300a0b914040e0398010342644a1600c0031942c80034121003122102c1c1c0d000054651180d640401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 165646375 1250 165645125 165645133
    0x703060b16170315030d0513090f091202071d0421141803070b0910080a0e10090b0f0118110d0924050408032e0806100803130510050c 59
    0x100c4100710503201300b10200180c00790b401c854144002a9018060a69030500402c0c815005000c1e00301e055111411020382d4540c0454540455180d003407184982d012800c005800c40e8a045c031008085216508075a1803844181c691403400d40c0302c50b808401000c000d00c045964150f207086926210f058480d01c0704e2544502140d03640341c495000764100c58000b48417400380c05a00d000090130031034081610785000012704880c580c002610000c0b80c2c46500101a01040d0f42d41d036035401440c8000300070140e00b071506203100040040d1941003194841600510b043e10885003100140f1041c3c1f207100315520794805219001c2030b070006010310490a40260011150001d01c2c01c0486410b000d02e0071041c1142042180410a1188504558500707942080310090444007081010911030a03c4c5800c40c4440d004005488000540560140002d0b40f20755010300b5a0703521940620002c0e200c211030f002d0003040340200035850402410026604141c091060324420f80001e03002d074045e14000d200b11440442042c082d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 165647482 1107 165646375 165646381
    0x1180804090b130e0a0309050405061008190203041101110a081204030c05030d06060305060102010b01141303170a030b18040f0206040803070302150703060b161703 72
    0x30780081c1003402c000001a07003403040719102c088131400383c0300b100024200100f000d038180d0881c1e4840c5260000341710440e070b9900e10080f2074181c507007084d680560702c0030000c40c92589400110752074240004204000c20015651000d9440390988800507a01258510241d0f221140c3e04000c1040b1020011782c4801400720340c03501da0051103440c000281c12042d640c3d460079a00300b203c202c003010751958400c0c8030154060050310b611030020b1000f001056041c1000805803045401c81c0c00e94100006800c5080d40114000a009036030407205841c0001e000340e2900340507a0080c060400044c2c64003600941d00d00d459400c811040f00048840710b2191550781b11482045004001207038010010400043c00880602c050440a80290003a00c00b0741c401d04001c000d804401040030703041514020b0103001c001405011341d0603104240980d51a1407505143c440180032a40803000800030000c010 = true := by decide +kernel

theorem cover : BRFrame.Cov 165467625 165647482 := by
  have h0 := BRFrame.cov_init 165467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 165467625 ≤ n) (h2 : n < 165647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
