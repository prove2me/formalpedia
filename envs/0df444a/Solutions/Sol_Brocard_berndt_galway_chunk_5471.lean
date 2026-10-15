-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5471
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:58:21.875089+00:00
-- url     : https://prove2.me/submissions/8022110c-7b37-4282-b9f0-30bf09d9cfbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 983812949 ≤ n < 983992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 983814199 1250 983812949 983812961
    0x705010c0806190b0c03070c06020703060c110d080402041122050f012106090e1b01030614040213090207050f1209220f060906060305130506040f1e030f0216030308010504 75
    0xe00e840c403042c0300303000100328008d00d0480203020740d400800d031b028954a4224107882c96540384100703010307034001814410980400c9030484800c6620b00203015540c1d41c0b0004000340760880f4540b5492a010440c0e035241030038803441010040d29185040721056461040001200410400750300107600c0e443e8112031102c0c6c03d01920008130b9102400710359141c6031803c81c803c035010030354014540e902400e400150740d02410b1405442c03000030f2031300784031081c200030788040740743c81c02903015009a038000303001c15050040c041000d001d000300706801d6556041900309541d48042c14091080d00c0c1c002c80002d1094181204100c0c3c1560f24007800e243c03849840002054803145400f04a100e6050311100099807400701440740c0c82c080e09404100060341800c00c50000c00302c0b40010200e40c07044c250ba010304004110300041d09179116500c00704e20041c82c851841c09680c6014200c0820342141d00c0c0000340000c06820015549000305d0759800c44050140c6c0340c1d0401d00300c644510015000c900444010b200f14180354000e2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 983815449 1250 983814199 983814217
    0x5010c03020c030d0e0120030412030e0603010e06030f0f100c0c020d14070501080c19091d010302040b030a0309030b060607080403140f0d17070e060705010c0806190b 73
    0x1a41c00c200b00d101c042030070860040886000191000e002159a44c0c000c0300d003042444610005083c5844484201d1350307079128070300400300350000ca1400142014400c01004400800103440692696910103c03200d10310400d0320aa480781c0100b40d001a003103c80003c10b148124160300c02050f080c40c050120384000c1100001120801522044140160700c0b40c40d070340c81e44684a07004503034980d20082c0d2800d0400003560400c904020503901404055090030055607a92009c000f000202c42d10011002d452554040c1d011043e640504440c13403540e0304d80105a241240d00955060000c0304d00c1c00101030312a01a59001404224600c40030300105a24200442d071050001e00040e24048054071a4a0140c0140e8002c59000f811040d000810100038042c0440700114a0020314040350a03020103482168508191410841c40c00000303607003548681c0341c1c031440e042d001e0011542d0302c4050410074043c02021285e03001141c01640071507031506050810112401314440f062150609000c242041503204400c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 983816699 1250 983815449 983815453
    0x10e030408073c150807022e0c030216080403170918091009140c01080708040311120f030610090b040504090f140a111503011401020109151a0306010b0405010c0302 72
    0x1004c07441608614103840300c284c00307490700719480c03416070b400926255176005084100c000132004c1080107001180340071125552403c010030750b021104400c40090080c0e00968401c40b0014401da400d000803000180262401102c0b6007442088100745c4040510444545540009031030b665102c1c45414a0101500000c00a0035504101c60f480c036018255201c9a00565801ea07500c105450200e00400000b02d03010400c3c00d21125520f000c0c8409080302500800c09401d1108050346000140e10902140300031883c40c035000d0b511510448d2400100d07420454419004103011f0200c0c048090099100504171040408110303d014101410310000e007203410b2045070500c0a01c0220b000007080e0b4034007120003480e000d0040c05483e020f81800340c4030017205030a4030300480a51180960421125007100d040d034440000340300c0c001051400403801402144c001070030388c1c8403090300300e811400650010000f8408a07880d0281c010580c008043d2030701020300c10f4800164081104001e554014022550030b5406401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 983817949 1250 983816699 983816819
    0x120103020d05120d02040f09090542011d01210c0513020c061e07082206060f0503010e030712051c060504050c131412010e03040807 58
    0x640b40f40541000c2600380d80207030003040c180711800d005264040240208507085c44444466141c1c19212035000d150f00821103c0e8000c591002204010041c0c00c004601d080042498460104888000b200b0301811900c0c102400060040741e40c80b44003241a100780304582204c0104500c01c00754441c0d1030740011108541c603240000361540c0c0d00922042001356081c4d025a0716114020760501f0305c400140818912814800400e0030440540d5825074880c1c11818070035420340b280c031405010103d2043c40d040c642803003155803004104141d0400422520440c41030004251208205800d03545151035202c2c0c103074420311000c0d01040c1101c00c222082100e9003000780c90700b0701300f051120504480b04242250346884040801050034076205160b803040310b00c1c86103070400803c8400d0000c11170030f038400e0383c0303907400c5505440b042a40c80c45944000040d4160082200d2140700039007646a8010b48600f50703080c0581315000802031410050030032230200001105200108000c406034081409a44101c001e0901003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 983819199 1250 983817949 983817973
    0x1e05012001020c0d0201150b030408070309050603180c0a120b061c0302060603070918110102102a0c0507060c0314040909110a0f05040f140408040812120103020d05 72
    0xb10081c4201250600a811102c1c24104007a09441240445000007003080c241044804451800d490b0020b9100410590796410790804440d8240301c0e40140e0740c01080002440800b010151380d15600010750b030f0903194800000c01c00c001c82900984140012a000540d000300080d001034080e81d44460010012114125000405805420740040032005a8858005c1c070448bc94100480801400415400c2c048410410a012080034800300c0041102d03294071080350460780240301d40041c2505041c42040000702c40c862294000a1100190680c507110f4140e4a004c1072142e0506151207810070000d01180d0b00d0074000300c500d00c0c181c3d1810390401481d907148654441c003020061006200b074440208481801d8104013020500000036184982c1d41c0070002c11020840d41a00000c491040714005454514642c0d6039000c0c1c001203070700d40c80e012058003c110801454030045c10640d0019411a4407040001d103800c42c0742d00c42c00511587c01c1300800c0c0100010300d8000b543c4c02003c1e2140069442c103000174 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 983820449 1250 983819199 983819201
    0xd1103070f030b01061e1704061d1e12090d0305090a0e06010f0e0a060c0f0b010b1b030306180601021501080705040e010515150417060406061e05012001 67
    0x54208543c052050401004400d40c8052600c0c100c0450319081068002c4044001d020340c4841425414102039140c005414001c0a40c0038000ca404100084030390050740c80703101b9440e1900c120528031604030400c01160300a40010310721500040010900349000400c00c10441054005a021420460208140d50003501c0c0c00212000802000071803030340ba8180f220016054441c025002410800303a41c480045c5036640e0201c0000312003441c10300d84c02222140c10f15002d0600c0e0b014001d046415541d00001d1124240c6006084b41000640c101c5501c08100080e55120301c410390340b6560040910282c00010410102880e802c40e805004030b50b5440c0c984144c0040b2844260300c1441d03107800aa03010011030420740182c180d01041c2a0082140d40307440004004202c5842040f180944070044c0010b600700008811900984201079a071200707168100d00156450070112011190700341000000200c41183c0103100c1c0d00d40b60007107034000c1c2c045d040000440d02e0480003070590354010a1000d28060990b02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 983821699 1250 983820449 983820479
    0x18120b0c070f0510050108060f01090c05270a060903051b18070804120f08010b07020a0b0f030a0f02040302010e01030e03041a040312020c060d0213150305190501050d110307 76
    0x81403028180300c1c0800c130050421a00141d02c4041076410410030405016003250655041d1214441d00040303007409800119414054030080c10110764a201d800c13050008621052850301c5d030101c0b007a08c4104d0711200100c030111081d1200505650198411100c1c811461760f4050503490301801c3d5140101500d010001c0380441542c10780007203003484090000341f00d000c01d8115801000750074403200c00c1e0300a1000401240b01441400310591010500710115901d800d03402000b000003134030303540e101c049902414205500503610010220b01c0c0125051040c03941c0d00a50b42101e4050310341d4240490388a00540c09040a1071101a09010030040802d004124a080c94007042c0d01407800c8d500c07039056242851580780b000c10000c00b958086003102c1a00d07a11030040fa0303956404268003684846154001e00a40321907500410041000c0f41d0000c000b40d54907030f000c1441010762806103005004604091400c484082c0070f100d41050b00c03032147e4404150902d441e00281207000d001c51b17601503943d200c46494001c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 983822949 1250 983821699 983821703
    0x5130c0e060d020a020709020307050a0c080909240a120602030619060c0314030f0c07050f070905071707021b0d061a180c07020907270618120b0c070f 66
    0x39001c0340000310313964108190000f070140741c2d00440c07171410030302c2c809045401030524003410412070b83c440a040000f03400c1558008200580000c3c0030f801c0c6111584810030002408400d440c40511b902d000b00d2074580c2c941011281c0c200c50b04001080036403a41c80c080e510003020141c00c515178000c0e07007001c00304203075824008104c99600d0715280c064600d002400f005980030003125034801802401480c014100c00650056681004655251b00701e04c1e0060400030316102d0030103540200100012402d0751504214480d80f9140e4a80030200c98540501c0201001903034454010382c84155100d09044030305502c10030500c0300914904440103203039070344030541c0c804021091003c00d00305040c040340d01340811031028102d400445040c0510f056101943d040c061500c002e80b141e01480c02160390b960007103400c094841c0010682900d505103542c02180255402d1048000194600040104e584928000c800596204601006541d2920f403203040300c64602611100c082c01040103800c4c0000c003001c0e000300a9038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 983824199 1250 983822949 983822951
    0x31107050a080c0d2a150203150112150b090d020a03050a0b010b03070e10110a0302060106140a0503010902210f0a11030906073212010f05130c0e060d 66
    0x40b180b40100d400c02841312402010b01c0622021594500b000400008400e11504514a920300050402c005e0001d10050f9201081d44000140080050f0a10302c05024800a0320f901624604140400d4111400c61250000c011891041440f41d1740514005001e640c0c0003d01e03641c030f401d000da000a406009070b940111150f600c444059000c2001484000f80109440c3d1002130035441e0600307000c1d0440700d090030700d00d1240d000395041e984868010021a20ba44144104580141a582c078001c1d51303170300c000c0c010040410b1420400c0400740030980c0c1140d03442d500a5549030708591074550000040c4d041000b4036035034100350170980310300600c089010900c12501c10300400710900780030700c10408031501c0f48001003c2d00c4040080150782240041c0d03403500200c11345404454074201f03601100c00030440d40407110131550389901e009003107190880584400c8030b00d07203003000b516640c170b8a4550751184030b880b619800000c40400b0b00941d2449500c805520402424000800c07110032000806a602c03200ea070400d11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 983825449 1250 983824199 983824207
    0x8030d0e0105060105160303091a010b0903160f1a0403060c091a0304030804020f1206090d080612250e0a02070506150a05040b030f19210f031107050a08 67
    0x4032109008154120000307003003503480d000703001603002c000c4100d40a0240a040c0c50b010039504016801c030200381034000d16003541c0f01c84d58440c0300300c160580c8400700462003031082ca016002d49003866402d0724201c42d052008a4141460003140d18054900c1022600082d1410311001010403114040c542c030707003500c070fa0b030741405541040b55410303032181c01078203190032a0001c0c4100b00002e6000a5410b0f0850340480b009880c9035070520000e070b11060310807403904070b5002c0c603810322504400004142c850071015403100d091590700d600c1404111003140040e60300903441b11800140550211038aa00c554030072020400307a1a4690b0121009800c4c20340d2160001a800034988003842000d00c42076801840c213941c50b005501c0500000781003846a802040c0c0b01c0c903900c141e1100705603820002d03a9030880c1d103003080e05c107130507014402c8a04e0507541e0030099910010940d2401c01c00300c02d182401900981720744a050984a000784100d00a0804110807203806000304041c20100b40d00708002d80707a41d4800e424241e51 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 983826699 1250 983825449 983825471
    0x13b0405061f1520070e070e0409050a030804020a09051609060e0307140a031707020f01080f04060203040f0807120306060c210201290102070b27010908030d 69
    0xc2c2140250401d542c882038290184070700544441d40c507028140d98649141c0200060043c2041005280003410b4503220f0300200040340400301d941c8901c01c515544502e651600c081081c40151500b0341c03402451600000d05010003c1d0151000c02d82040c000f500a0f0384032520741c06003200300e41007958680664120540c01520141e030100004002c0c24152034661704085c1c81101203a50340341c0c14015001e0286052a01c6410b0743c0304da078080300085401c00300100c40d214041c01000c984c0d0b801981c05902070480c80e81e014009501a400c2d00d40a03130040407003003050381d40e1510381c14025000504125a101403d2614401148440001d00b035264000c0c800c1d85206040010b0150403909182e00c00c2c000c4c01640c011140200d220011980079603500c00303103030b11006521071900b01e00403e4030302c101300300350058035071101644c0400554010031010207800b2100e0454035001074014074065960f1030b4402c05001d1020320321404400e103500c91015418100b507520340380c94103981401d5400403101d08180030794071151043c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 983827949 1250 983826699 983826721
    0x60f04110406080c150f0d0207060f0b090106030e0109080a030b10030e0a0308040c05060a12060506070b06040207020f1203130f08060c0a09050a0b0304021008013b040506 75
    0x1400100721820400d1900d05aa11500c611002041030b2142c40c1204c6500c00802080c411200c03000f144295042c1d44480c503030f80c21402074011070800d59584c0c2c42c1c6030140300f450806206503001c1c240300401901090b0718100c1b085000d03080c4000602095521101d20b840020350800281a02e030300a91000b141c04070111050201811803020350310f0801d0b06000094840c0f803004030700300c1c0c2c2403901b41c5840c00d0107541364100a010141d1541c48142c02c8030b03001501da20780030350012240012100354001841865616810440180074600000c1c0001b400d10000c6a41c0b4a001d5004104162000d07102c0c241e007000703075400180000c1c41000204040d400000b01003100003000700b00c20014000100318081d8290800c1c5102e503031501c000340525045000041e4162415000d050b820300101801041054403581302d10054500790000c0e58101c1c0101424526558914001c0c0951810f85913940d940f034154403056802e50320310541c242c400c841001d1040d400b0b0003040354101882e034807640c000c0d80104454104028070710 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 983829199 1250 983827949 983827973
    0xe100504260d022217120405150d0b04050408030615030f040f020d3f170c13030803010501020f15130804091a040e07030206070b0a0e060f04 62
    0x5400108540782081004000030554018020320b04005841c2c2c00e48401441003a041d800548644409034040003940c0104038a80c440f825401400b5500d104144485042940c0550b000c1d8940c4030404a1748104008201c402030107902001000118208180780c0205085600a032015241c680000081006c80e04100305013450314100390a4003890b40c0391040030178000303005c041c10007010404007410f00d20641d921a1181c040c455003050403c880800201c88804122030014104241100c106a035010225000030b40714005801c0d0f034130707105d0602110601c0d42e6020349006104000c0c5075418008280c050003076540b0326000c1c510a14402d0b42c0c950400c0006842c004000340240002d900242850f404040070a86060708200b1842e2800c140300001d02e044805c038050b540081350020b26040020f0101d506c4548211030011065500300aa0f4160700c002c40d459116a000207508980200071440008130920b42580d13200d1200d21002a020841ca00c0442c01e040701a580244a560031070207110502c440302c2601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 983830449 1250 983829199 983829233
    0xa02030c0607020f091b0c0a0b0708040308070f120c0306080c0609010507060b010912060b040c05030c07031b060204060c030206070503062d0a06090810020a090b0d0e100504 76
    0x7007030400426a000501600909a000d40900400130105c0e2800703082d9908118490051280c41c0d40390003001003540da484e14038020955001101c82d001c25181c6008500c0c603030007150540d0f80e240b100d548085050b01c26039030501402040240c08260030410300c070039205860090600350380200e4400d240080303151030b11108645152060300c04000c0201c03da0f0b01306084811590380442c022400d1036902005031468081640040421402110401c0802c003031a40107101d40107040303800b000400100306044900780001c854419041400b04440d802190098006c8541c402c41c0c0f00303c8511210315a61034600b070b600aa800800407840d141001020550113101d1240d000409c0d142c414118607050000441d250115001c1e03075101325401c42c1042800b10004003e00000001a00d90001c8550704c0d000104807400340c0c82415000e0084c00b0403030300e0000c000e00071030320b102d031203a03880090032418060402c19aa101202c920202a5604030510006409101d00313400074880010004040c40c190902c000d04051082c49 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 983831699 1250 983830449 983830459
    0x91710110901030e1902011202070804031110080105100c05120f03040510090206040504020a0e1206330919050403020c010e0d0302120d0603060908190513060f031d0a02030c 76
    0x3c803c441c45849000e21845e41e02468514100c0e03500c01c0d41c2c0700c001d11440401400c0200006804401d200d410003c840040d50140c400c8035903524042c0003150003400030301855902200c00c1300303911486807103103405001c8140100195040e00c00d0103000c012051388502d40e18a0041d40100800c0180203040c09980745522a080303041c0074200071a40040c007039100f10f02502e132042d9808141c4420300d034442c080b07582d20010701504030307007152400751001c0d0b607500c100b10b40e0302028196560724043c0790b1002020011149a0038901e00c1307803241d2500c2c2044801f610003443c0c4030124a0110820003ca0101d000d0030340101d000360090107886941134001040c510055142502800c0c81c0d141200c00250300180c1100300141c40000151109030440c0750401401e840c0d407020700380c4bd01741a861001c0c05103150081003210fa880300e08842c2600d11070410707541401001d910340d20701d241070720040000324003403c2864100341d1079103000960f100c4805074500125140d481c001407190710040300c490031400d080188520100c2c0450b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 983832949 1250 983831699 983831713
    0xc0405030a151805030306041d011530081803030315100837020f03150d1505040609020d05011529070206040f080a03140307091710110901030e 63
    0x64039030360f0f4400a40120300450f90b441c1002700c01292040d1100b50f04031104000e2100c00712600f080d82034240c2324021a924a00d06400e4454010440710b003030f61a00d0740944403001e00240988a185560301300528402c00d11032118150092540c0a0004612030002d24098400d54440b80092100d4048107042c1e01c0c040c02a064140a03016200014503084d011155103206110800812040302000201d0701c0800c5150011071105140000c585c0690720606c28000a10130440c4500c0400c89a08020764000e070070503014030307411030440d00c4a81000d0342c094007620f0007041000e815804600c200f52187c40c1500d030750b50b441c21040d040d03480d0701e5206030040c407802030141803012810201c03184401410015000010740050303e401191a00800d4600400804900007047c0380d981200c40d480300e03003100084001940c400800c40c243e45c024400c0d2801014190303519500e150806101f60a52110200c0d100010300c185e10396040502a94003407001c4560900707000030b803140d001c0d000142c00d0301c0c42100c50815a4200300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 983834199 1250 983832949 983832953
    0x70b190b180a090302070e010609090b0406050f0108131502030a0507080f06010c030c061410082811040903030e0c120a0206090a0801150f080d02060106080c0405030a1518 75
    0x1000e0542081c0b9007040024050514035050345090410360045007100c04007000000c07450b4000384034030b00b01c420443c400e105410401e410041203803442c1c000d107580a44260600c59541d441101c0300707540580c15080549251102d0b07251a131a08100b9030f170700c003081a0004204038001c07800d400783c241c03c1a41ca0504188a0620560320903030360f5002041c05041200030403089003410300c200c080501080d0004d60030060000e0014040b649100200c0d20602480c0c00300600040e22040003c40040c07981c0a500b009000100e0f0700040356010540940031b03141e568011220721b20304e1741d441c41202c642502c01c1c0c40008000d140010380034240000c45540900c0303000340e901c1e59000c10742d0214110400541c125800781e0344407914000601e48118a4001c1c408030340ca0082d40303080f6013003124142c00603552103510303814200340d484001036520201c0303180f05401038001c40d0040000368010030049412002d8050030707034203054031000801c0c40c050800c003081d20f040c02ca00d030000c075503142d05104042580e00d5003101c010b0302e07c44507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 983835449 1250 983834199 983834239
    0x203040b0a051302061c0b1206010e13080a0903120c0203030306040b01021e0a020f04060b120a0b03010212060a0f05030a0803093c070524070b190b 65
    0x9041e1410541c95200040300021402c03001c4582940c01031001e03885101e440c035a0120340844800480301e091400c10424124074000030b10102100002c001840981c2c01c251300b260ba5441c0c050040c44102c0c14024899000805150107049054825030303034408030381c2c950708090307025644407000a02480400310f215800358501104895024806035404100c840031100100d18219011498012807060126852400d200118103940054001c1300c9005518581800b0407003154a28850560445800c000b500c03804e00700499155030003079048400045e40c59500d00401d007664019030102e0f029040740d40c00c002c100c0c0742041c6a80702900c80300340110710b01c50130800441c2e6660b2149a002e03010400100004006142c104802048000e40c00c0f5040c01015001c0000398141c00100034040071103400c4085c40c000b0314400555241198001000d014000030400320342c1c904004400c1081e136885030200944008140d016020900400d0007140041003005904400700c100c0381d004c44c01038071440605240100210315 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 983836699 1250 983835449 983835451
    0xa05120903070e04020a1d0708010803030f0103060b01173112140c1b01020c0d031d011404120512040609030201050d0b03010906020901020708070b0d110c0f0c040e010203040b 77
    0xc5002a0603c0b600c03140000391071016140e11049030110200004c5174000d04020f01103001c1d0300b0300d1b102c418959881e151056142d010441e102e03100c1c48800c20040000c902c0c03c1d04501a0602c060500ca0720903107202c0d54000c464481243c11070704518886074a25440710b591412020081c50300c101020301d007820340e6502d02400c045820f803c02080440841d080850501000f01c450070036200c1c044949100020030b170704030380410800c490383c054028000741149a082241080c1f900661559500e010201c00c900c010603014846600c85040080c0700c0c195012260344400104050b0445c10080881300d15140f0307005140541c00b04e49084980c2d0144010030115070081c0c00e41c800d80c1d83c2420490b80301c0a00440c0074000780084100b4540c15800c000c00301013400015401000451402c0e07080d0758074507840740502940d8201d03600c280c042c5440100810380030000300340e01004540c1900c040b11460b140c1d914a8251503d190781e050040700b50012070f403404562a051280d40c4000c00034400a6066240684901088903c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 983837949 1250 983836699 983836709
    0x210b1f0e0105040e31110f04090c060318140a020307080703110d11030307150605191202190b030a05070905061b07090f0504020a08070e1603110c0a0512090307 70
    0x18810103920080002c1c80d4641440d040e1908020401c680355003811b82c083c99041c80050f024451101080c1820b0505001e41d45003280c200498070b0080e4500350742100281414104540c15640d8070000c40002105034507803880030400c0d88010306002e0b91350700403d400d103041d0b603005030300300d80c0b120303a040001550100c10020020011143c1d07521446c09420001c99101084070800d6040c00005012000c010303404102c039001c29001c400070010f02c1d46030000d1000340b9038006402d0780b000c80d06032010020183c00071911900244060898030303268249203485c601e00300b071030b4200c001020030101c104070b2200418402d484d4085003c1c40d000c83d0892034000811410301c6840c0f0381d404002c0c150603034411a601d080003010014902800100300340d80f82150310100500007079600700c4c8651441c06002645910000b00402030b90b502c42c040001c117440c0d60322109589003d5690801c245603c505c4c115240d00a000080c0061043d08405170034880c0c1c081c501107003440c4240d000c1c035030740540a02458096440021301041681c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 983839199 1250 983837949 983837971
    0x60103030c0f170d0b0f0f060913062418060f090b030108011a030606030325020a27050f011206150303030204061e210b1f0e0105040e 59
    0x5050b0408400c22442190041d00c80c02580700c07060040d0002100802c0c12003460842003015031100401c21200c0004000c0186e80910003203410251b510740310005040010008000c4a40e28948200072815500c40340e2140150410f1002c21035555000c1c0250040b03102040d01c1c1014000042ca80024895440d6001d000100464072004d40300c0300e800303101040e0141010500c6140c17290780da15403541c0681241c29030800c0c3c0307070011401c00107035050010b00f0034000c00340100594200066420200c0161082c181c80f0202c040d041d1005a000d80c903912031000140002c804a0350071075240d840d074202c1c0301020442002e2480d140c00100a15200310b04403040c190362411403045000905070410502912140c441051511140c031000020590561b00070003c881454641a17120840007290801610140790b02e079002c40c0c030388070982c468400d010045211031200364800203281d02c1c2080111f801d494103500450160781c601c20401030301c9900704007090042e02d82440e01514207414041c0c805e03a0fa44025000c12804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 983840449 1250 983839199 983839217
    0x1006050a0b091e120f0d0207290c03120403020a110609090417070605010e010503120c0a030309080c0604061410060e0f21010c0e0d1a0702071e08010b010c0506010303 73
    0x641d48000700c01d1403c0540c0c0003251005d105801c0090b0301c80480e01840f40c09441400d01c0090624458604035201c04c0c02c0280c070140720a40346201a040b503100000e01034843c041004109115010150034502440c065401054554000d141010072041d419103294030441040c8450b60385642c4402038164016072200c0c40e0795541541d41c172030500c1d074022010001c05150512001041201a2030b800b107041703820460890707501070540809070850340f04444c1c01315525017011b030003280420b0081e006200d03e03510400c4514900001803a1003824184292011030783c41da120748214580001d07444099402040c1d4480d422015032400343c01600f640801e00031a8007580c0308140c14541c59940c0600518150201124501170650103803044d802001c00ba90300704007084019071001c403c0d040012060411645c003028640000c4c0ea02c1c5080400c0c000c0c001c00e000c0851250f42d8000ca9100c1d580b002840100769020000c200e203500301070003207081d200c0241c3c40d1810403002042e094049000011460704480d0142054000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 983841699 1250 983840449 983840509
    0x120503060405100e04032102070506041704030c29180f03061006110114070513080601031703090718020d0b04020f0f070602040e1009051f140f031006050a0b09 70
    0xc02000600341f80740b01031000c5201c00070b000c000b250303c3e031180f0311941e00007601000c0801a80e50900880c000039000715032202d41881340b0203d50075107200326004c04003110303030269441c03185a15561004031020410702d01000ca440f850308001441c88641001200a8013480c607004184000d44000d038480d0302d040018602c00a240000203502c09201054245100300b42440c22079405482c1e030b0b00014458050407080140001c1d24140480d07560b0507a50300900c880c5507110071000c07070400c980001c0c110708a036010f052800a190040414446040c404540b80582c07100c1640310000308032210301d20340398000c60040102c1042d18900c50201e621940d81548026103401003401d0140080c000e6808c04c201b50300f469014060a8800081180103c1e1089030b0107200c0384d504c03280c61031900c7c144030403100c0721036100960074440024590318240401101400c580c4000814000080c9040702100e860036115980d1042480711341410030601d800b401c0500801464074401c0800703d00d00390102d04030f943c0507120190403241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 983842949 1250 983841699 983841737
    0x810050c1804060b0d0603020a09020703020607081510110f01020f042706090506101e0818060f15090106020c0108134722120503060405100e0403 64
    0x42d04013a80701d44e84035091504108010110b60005034840c030f0080303400251841c2036000f11610940c1c183d010348403d8807010b205441014010380344080d040204048080c842c3c5945943c00624603d565138045800700c111300090500403400008242d503401040344d41c01c040060421603003190400c2c1020a010060a40500d0a080c00580000c6c0e4580c182400083d44000c0d49e0055070040750200e409100b0507188540036201c00e203980104007481481c4c0d00255041501840b00541d11a504162811403503030b41038415418481c003203841c910a031014100781701c10380e1440050204021400d841650f200d5043c15000395891442440d00c6040103204400900041040c41d861010140d02c1080e00c88041d03800c840024500001d002d001040b091128214800c2280d0300c03805443c0d98110b107008201549840107142442c5600030301640c4000342095121000030808014490480700c96500c064681c28418204000d0700d4000d030003401804070341c00091121407000b00c0c0d056085585403c04030090406285192 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 983844199 1250 983842949 983842961
    0x408071205011e05090c010c0b0609061207030302010e0601050909030304140c0d030e040b01030209010912020414041a1b1c0b060f040608181e010902090106090810050c1804 76
    0xd100c3e03d0a80456180d078415900554003c44070801503074003503290f0800454051a4045000c1e058070b00850105d8428202036070900d82108015000e64600d12003008482e1078035000341d00840060f0b66809801140c800c05200031405400100c5005a103030400c6017016649000c043c0c005007001c48590894030141500b001856070160f030152040c107151083d800c010304078021004c00c49016904040c15107485621030320031100380c802e0507110440c0b02802c000100c104099451402c070b801695414542d120410424001d52082e8400c0746400850070308114072a40c0c0702c8014107108807110010000d5010790718000c050f20400d10308100d001501d07a080c060740300080d00c4500c1210b500034000140249901e403d0300018400d64006444802894560040086c0f104290342120340031500003280003e101b0014040041003000c40c0c000104907120544c00040740c03d08282d0108010a0107440100460b0100f40000d00348603074218010000c514000d15a5011440351040e0302e402e080096081034a0359849a1040d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 983845449 1250 983844199 983844221
    0x4030606030b180c010207140109081e0706090602150403170711010b0306090c010c030215191406030c150f0d2a020709090f240c05040807120501 64
    0x24080d050340c0303050890580c02d003074443d01039021066500c46819400026030a11584040e0b000300104c92a000c0c80c11444005401e6560400642e02c80000d16281c082090740c8052800004030401c11700071080715403400c590b9500c0b40080c8608440204209600440e400485000760541c1043c255118a4111070400181d0049410003a2001c00d10035950780c0410b146505c0c0e10014001c1280c01e442c1001c142d1744407002c855030400342d403101c449219154895814800d034103209004407001100380168410046008070b501c00721003d405044819400d459014000206d001c0c19042c002a04000010039290181000707a01c0c01007003805910030280c2200300480d10600c0d04426074544524020301c40317801814002c06049204181c840004501c01014248401d440b0341c16001001040c0c603105956018000e07012007035a00341c52110f000004a03002c1c840a075a48215416034519116400380088203c410b5107007036504104041c0801c0c0f016031300001d0420107881c244402035a841225142440c090004180300d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 983846699 1250 983845449 983845451
    0x5190b18040f140a090f021311070f031818091e0b0f070207060206040b0a0b040f0203040213060510110a1e051c08070c0f060612020a0504020f07080f040306 69
    0x2e0784000c4007103035120720722030300b03d10441c00d035551113007019001500c05655000c0c0400207550781107001840c10b98510710940c81c1802d0302080300c06810030140d106811076101954080ca104490380e0806510021491a449070342c8011a15182081e950240f031040c03103030004418079980c4410340180004010b40e200c41c00c0c45001a22900c4401e880d0501105400fa10526048079070715010039101742c008241c030380594003554008c00302d9954a8030303544440c44004d0908108590ba9040654087e2149c0c041d48080341030542001d6983d0038244103108840012580051400b4135015041c40031b5595100a00c0400402d4500340c26901c02c80c0318114140300007681d00420f5800c600415440780d07a400c80c521445240500c050705c80c00d403807103071060039204140c0f044003001a9400c00081d405900407058804042d000301420702d00d61020340d880000b1902c1ca034220203000140011480114070742000440c0103407506850a60030290306100d64201e60268030300085c420030740410380300061985582901d000316003007a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 983847949 1250 983846699 983846711
    0x302030102041d0612030909040c1206020c0d020a0819030f0e0a14030a0912110904060b12150105010c0201111504030e010c1101050a091a0306040605190b1804 70
    0x140444010401140383c241c0c0e070b5400c1000806620f080c0d12481102004c0381c0213540b40008a0080024541008104075031403280d5400103d200186030300c0c142d1103030b48030350001682d40c64044a0589004c0620583c1d00455018050103400603454005841d40c0d2080c00101c10a2840c8241d030a8000d0700b541e000102d07000d481d00c42280f05c5840300041c41507213140213850f0030183c084c800d2000c40c3c03281b2424403100007042120000300100d0740c020503115080c40c0104280703c904111600060302c48903050303800b42e81858540c141c0c42910324104070310102201000c8001c000844401322a50350041c014410707141440488400394080da4020200400c02a11110039544201d040e643e545c0d11440e07080c0c6050b0009a01b24404051075405500c20300c0d801038021034005240b14103074004503a01d030701100600d410401c4007000000d2440c150158610b01d00403103c041c645030302d010000e01c002c461a5900c8a07202c0d09c4000761150b00030102540311303001e40c0c0034016155036541d85400d06060b00d0107a001105d4100307207000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 983849199 1250 983847949 983847959
    0x3102031003020f010f080f10030203010504060e07124101090308071b06110f04030b0105030d230706110412020a08070b1204060e0a1a0a29010306030203010204 70
    0x49800e0540c0d108841c10006140781d4401181e5a0301c0d0a0a2140411004004a143c002d6180545c82d807040c19114448034031502d95001c01c0c250340b010b0390101d610a4981c0c1e07165010290510110000d0600d0480c1a40b40c000a130310342011400c0e00a035403d00441c0c0702d010780d900c0304d00300b03c90240021041d203144400340302408130030078003d01e06240190300040440340454a114406c070100c5042c0e40040007205015400f070740340e61009024031119581600c6c420001d41e880200c04501400003540205410182e0390315040525003000c0920000508120b550f49010321054400c102d00b0515100c401450341e00c40a1a103800700040c5242d0020510b403401c04140004c1040c00900e540100920980300319822607035594079250b176641c0c0b0f07028a6180520074010468420140300c2019880b41c00f6800110311800c0c070188650828003440400d441e180d09001c0c00700d02803000c000701250040020002040b0402c202100b10071199002c60320314070203111224007202183e200b50404805540c00800855030303542c6d50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 983850449 1250 983849199 983849221
    0x5030d020a1716030e130509010f06050607020a120804090f050a2901030207030c0b04030e011b11090c0d0617010c0504050a03060506030a0c03200906310203 69
    0x41403080b140040074105100c000e40074903055a8522040d19818a24204940d4003640c8000e440081681c20800140c4240c41c0c400060140707500962081000055100c818411001a0360080e00a03500441040054000580b55012840c1c102e5018034406020a03469142c600941d22803640040c001e1410300718200c07031120030b6501560164090383c40400001c0c0b62401000c5011001d01d1040c05088601c03801280654042c0c0c0042042c0c900c64a4075a0304032001d56580040300800355002e07400100249640d81003960400c001a02c0c120880c1c1d4103001c0f0400030343d10581c840d9040c084484c010010800410302640d82a01a0713402c1109004d0180000358a6841c03200307030f10301c904007034a416600b003800c52a02d450040080710107544010b042211500d0441e1200006044082c4c025509885005101350202d03058106050296100c3c1e07680c81c2d4400c152000c84003003c0c0844a03a21320582102c000c1c003046966060841e6040c0c402100c00740c1c07003007400001c0d0030b00d2032034454912202d403400001000003100c06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 983851699 1250 983850449 983850463
    0x518010e03180d020d030e01020a14010606080606040b09100507120e01080c130905090304030c0b0a1e080a052d01080111030c07113c09070f030b03010605030d02 71
    0x42c03031811002012104002c0d9040c0400c0000c0c0d00141c441002e0800b01303114043d940c0c810101801100d0307001c2280e0f82c2d58802d43c40242540000c59550340c4062151560180d4885d80210f811901c0f90300b02800e14502c60102d01c213101040b48915000d14020105034010002e4409040d00090f5a0807179850004024141d0b01d008011680000e03404400248121904415220300040280b24191158146002c8030002c2001812440580c84280000400103c02d0040c80001e0146842a9521000d4100002e0300020701d16522480d0700481c4002c030114a503101c10364a03809242c1c031b4030101d034a0710b8242c0d0340b9200301102c410040364031130281d030f43c2d04c410300000d003456040b9480c0200810000c20150701187c800e0005a0f00c0b9841e0410410110000c1210600d142d592005c00401d105d000340c0c082d0146106000820f48031074030488809844d4680c4d04040c0c09e007142c03c0724040d2404a46454489002003405001401e290b080c55a501c140c1401a1025440807000c0c2201808480c482e8030812006591125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 983852949 1250 983851699 983851717
    0x2105040b04050f121602130c020f01060b1603050a0c0506092a0d0201050304060608100b01020c15040b18120115060c0c060305152e0e060306040518010e03 68
    0x1c25a02040d00100000a03804404000801d2550505003444585c0e056025440c40076a07001c580035110440c0f0200360720585140c604607400510350114840001070a4075203543c4000e0081c141400b580c0450803002c102e5541e00c0ea81482c01c1545c0342c51b140d106031007220040d0400b6001d4070402d020010030841c0018602107402507a1002200400705c0d0a0800d514500303810455081141c0010000055010380d0180d90130a2141e100443c246484a644929004103540880d504540b500344900c419601441160b41c447c0d420b03205514041c1c00303400b402085114134400c5451b640800580d0540828040c408000109001001340d0480011080c075030f806050340c002250110721070b0020004083d4010303888485190362044003140e105240200540c010140100001869200600707960303a640d482c3c2c011103c021900ca41e01d401c08036011410004081e00048816084c4040381800710723503650b5050b042d60b9112030700303c80208090355030321400c002d103030ac0000d422401c0790701309070400c210f082c0b020001e490501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 983854199 1250 983852949 983852953
    0xc0f0f08040b0711010c052212060207170c010501170f0c120114042006040e070305040c1d0106020d0203040b04030f030203130f140405070e09090c0d0f060606020106030c062105040b0405 82
    0x2411400c61160688c0601c9400302c80607504980d00000343c0590050580ea40c0150b12040c0c50310301d080c500c0641c0340e1210f480301c4026552100188119072440ca08083c0c803486050007001600380301c03410140c0ea03038510901140304402c090b0070b480d0720704001d40041450f544420700342102ea052620b000704440d280b140c6441d0b00301c2e00307020556100d030420380156000c85075007a1f0400d03e5a19000001d0300100001781c400e03500817030140c0b000b00350041c00151111128400b1409420300750301d811030080c103040001001d142150810001081401204002e48040d40d402c07481044c000c05640c541a4610f01c034022541040c0031a14400040200040c1e042600b150103c901c01c1c1e0010728084e040000322203003112040042181e80d0304108150412081159004000e003048800f0318480c200080c43c51305100e0021515100d80424406c10807a00e03000b600d0081038140020301c601400c6984200c403449031030081c807007000003d0040484120721649502032a1300b105104001d117080c681411181c1c441d0842e000d039614 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 983855449 1250 983854199 983854237
    0x3050d05011203050a031a0604030f1709031e01020c0106080319082e181509090809130f18021801180b01020708030c010c0f0f08040b0711010c05 64
    0x2c080300d0b40320a03445505945491510805440c250018400c07004c0240c41040e02484200240c2c0381c41d0f0080000d0b41c082c0c28500c1d15212280703803800007804241011380401805014800c415200080c0008090302025001107034506440d461a00900641c21500d045e98202a800110410040300400c6122181b100320401302020fa6016034554006031031840a10300120404c01c10a05400c0d241e200400501440c07240c0b040d40c42e041440114200144003180c0c5613980004d5242d40c0d0080401c5000701500f010900c40e152003600e40f2030041c00307111886401140030307448041181103154081180d1080345030007000880301d510705000e00d240589808a000d00c0503d5030b0761000b034001d0062181221204100e980310392107070f000f03000050025041c80505604c03c184c2d020a2a000610140844186840000904681091000302181442c0321b244043c0094440d100001c154070111069100d034110b4410181d0b41c94000080f11140018603103041154030b004008081070780c0c454020440000540604105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 983856699 1250 983855449 983855459
    0x3010b04060f151103030705030a140115120908040e0606040e0c1903020c07090c090e01030b06090c180d0c0b0d0e1b0102190f08030405070609140924040903050d0501 73
    0x1a181c982200050313140e00620004030414800d800455001d030a1520101d0030394500c08000901e003e00780c1054000300002d004081e00c156000c0d100ca4090a1154000d01440e1035540b202c02e5244036901620001c0d8042800258103502c90700f08590041501401900315481d00c0b941d10700c003d40291140c035a03d14074920840c20464402d00a07500425401d8010f0301a480c030301f01401c0010300302030040e02c06001034544005624142c01c2c20107802140a10019111851300000708440c00f04000d058840c01d41d07081c0801c07001032120782c040c801e0160040d501502c03549424100120b88801682c8054004200040c80d035070603a01542204640c3c03845601101c005040b800181d8005144ca00705031801a0311503070030032006841135025003500304d0040300031084103003139500e40c00c1d45940112000d4440f944801c408200071580003000c94000d000d04841845052845000180c4100000e000e0708001481c030032401c0041902c0810110103606c00030300030041215586409010350300506800820f42e4500400014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 983857949 1250 983856699 983856707
    0x60304051b0f100e0a150804050118050307080906040f120b0105030712061e0c09080f0304050109030807062403020a0b1918090c1218051b03010b04060f15 68
    0x561848014180c0e0301a00c00d181c02190351380b0002030f2066121042c140d0000f1070b2100b03032000c0b42211102d83e8658499203031500b06103081d122540e281c10a081c64083c8060003003003001c4251404254030150807907844038200001280c9000d143c10a000354010004005448071450740b4840301d5038800c526103400d40e0707a100201070304c1e502c091040311a46c6007643c03014400104c086c2c0c000341900f40c040a1652f00d40c0800e43d8004200c0340b001d4000301c0407484030003062007101010806d140b5091003810056181c5410100020903060240c40b004200e40400700d22441040020b0b000b0b031400c030b5440c403e83c20350144004040d182d901d12521050340202512800402c1c50030a000444501d480d4000d50030390a082e00100031201d00200d4100c1c4500700c095401c000c11058554000d0408592142d5500c2899082d01c0ea41c1000f200c650740144008a120b005440c0e00241000c01c4c1e030035045070681d0250144d03041e140c01003405000e291a4840c1c1c41840d105010640740c00c144c0c13084081d2006640c60580c100c1017144180c0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 983859199 1250 983857949 983857969
    0x120307030b0f1f0c05010c210b0310020705010b220b0303040b191106071e0810050103050702030702040f0603030e01140711210d0f021504081602060304051b 69
    0xb41d0080d000b160140298064544200c60054207454280140c400b00e84809013100d804401900000d0300046d04408222200d4607100d81300040d1003403c1181100500c0003a80da05110301035006019000f04001042c03001c2980603038512000901019584440d401e00c40100318104541c00e0401c0b0300d0325411a03500d050001c240c41c150341d0710268003880c0c41c010b800a80c00d01d800030110700d400c01c43c0c01091010405c01c2440403c1c044c1010b5214280390031106000c40c01c01d141d611848600b002207042c01c0102d0074003012586c3d41220310a00700025903459989049043d07114610700690403608082c141808481d583d480030040702c4c000e960781c1605030b002c0801110b070040300041281c190b0b00c0910200700480c2200104040d0104010700c00744404040d00743c40140c00c01d100012041a4000c0342e030700c2403505d4202c1c12446500c100d51001d40562a0300c10250054550064400342c041c1e0400b080710741004520559000556800800340c0380c4034174013441c0065844034a5803440d4078441c0760184071419810056540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 983860449 1250 983859199 983859229
    0x61626071b03120e0307021201050a0f0e0d030e011503030513080703080d1a040908120c0a050a030209040905010e070f090504022b200f06040609050d0f05120307030b 73
    0xb083c4202d102200c16000c0c1c00ca0a038114200e000810a580c0140e5500c0d01d80c05143d00c00f0f00c00030a0914004a04200721510a00e1000380c041c2042803100c43d0100c0441c0c04100d110060800050f40f0841c0240c880c010160544400b50300501100c0c04420f140e0002d001d89000c09809158900031070301e8800e1a5100c404c50301c40101800343c00d00000400784001d0300a000c1e09d1805442640c0741107141d03400601550500b81c402e03604458001600151030900c8820558001032000d20249440c40f407001c01003083c41340854003410903030b010425012a50300d5421041050f82c0200081c0000012819156200c03141807054225444500c040002c1c02e26103801203920a6030001c100c01c11a07146a40a80c0c030003500c00341110304076511200440c00003950200d040c0845540496026054081a41446021014151601d00c9240144002c1003030302d0b4002d10a6080c1d500c1174030080c5036001d503403421035001d100c21038004045020744501c2c507071900300340d0025501c03c503503560341442801c50501c184442081481c0380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 983861699 1250 983860449 983860457
    0xa41031608071502010e060f0f0a0b092a0723190303020a050904060e01062006070e1c051b10140f09040f060e09030c061626071b03 58
    0xb0400211954105624480c9824000401c011016404007410000220303003600401e0303890410f100c00103091903d4903500c03240c115004c01182400310300040340e43c6001081641391400300711015004e41003060700d450f29184210303001c3e501e58445e07161031900426500c01201445d007812040503106240000c001c0c0c04101c000c2c1800c0ca030b80c2c905d910105e01075805402014180041007120050984031445028010301503212418103a50400100500002601da084803036a51204903032a1701c11004541c1c1a00302d000741c00c2410b40c2d060703048042074050b00b25403c1c14052089c20004442131000c0030900c200c06403803010403c82002000b0041003041100000c06400182089002505481440740104000b03154080040c0c1400c6503440010151115801c0c0000e401d0b0702d401c070800c0a485404078054214241c440030b1814a121420b12a0307891070010103c0344d031483c11010348551240581c0c0b0a9110000e5120900038481d01c0041d030079070142c010703507640c40003500c4e510301106400800410f1000f41e40d41992 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 983862949 1250 983861699 983861713
    0xa1e120f060512010e01061508060d0309051905040606080915090f16140108010305062a040e04170c210c060f0717060a41031608 57
    0x404000030254110350444065403484042001d50b2800e840103c80c0c180d050000c00d80e9140c2d40d042509454903540701c15001c03901102c26429158025481075807009055a4800302440f5605086139420100d6000d00d030860603109007500d83d90b10b891030750400c0d104160b6062280d15507074a02150a00006c0304c80c80c0d1540c000d000681c8804c0c0c200704902d038001e0000f13012212860349181c030842c2001726880c408441040144410060000d5440c40504003c0302402c1c0400c1139851034442c4d41d00c660005143d03e090300e050700c005d00d150300c6484003016415021b2021190300d4a4640002006075a03064070250783ea203050031304a91500c00c0c0c54085404003c3c040c00680400d0313000d04c1000780060810003841c20040f070240a2901ca44500300710182c4203011800081d055802c200c0009806c4c0c5841d1441c010003802c141c004c01010741c881c81804001c031071540d407204038415001d0000d04411402c83c0510b0340c14042c1c010a40860034003c4511204942003107050310000c40c1d107402c800b101504a485884103d030071401c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 983864199 1250 983862949 983862977
    0x60812030a020c210a12060506040e04062003040201020f0c0604050f03030c0d180603150e07170408030a0c0302180603040c150323100b131a0a1e 64
    0x74003e0108400341404407149500c16000307000544803251210150711101140d80b5032081e130f110b0b091540041da10a000c22419081401050303640c451405104180d80b15600410b080107031075030192504080c0081d810250382e24044051046901c1564241d00620408254104568003c42c00011111000b06480d20b45850b0206100c1c0a003512520f0070b505010501018420520a0044990004050b9210191511140e12940000140d5084041094541a030050412a00c0f0008409a03980005000060341e500641141d104d80a40d280810029202c1d080c042040700d543c1c0990301a450b00344041c0700b00f0700b0744c1208074101d00661201d0750620030003000682c141e0408000442c0c010b4043c0d002d04010075200e0310000070100b603401d515400282c1d02c600101c0310b02e1400d031100d5410106440c4040c0641040113140c0c3c1d2001023402614030b80c050000d044c50310301c2a40703800240104042e660103c1c05110b03903214191035405c00c0d0000c0b4081707551800d14150b804c2c1c016003980032440b1242c450b010610409 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 983865449 1250 983864199 983864201
    0x421080f150402040810020a02070803040e0103060f0e0a1b0545100608010509070e040c022a0a121505040303020909160215160c05030403020d08030109060812030a 72
    0x503220003600302d9800c00012440d001c052190001e414507007500540e5a07602d00c400249040110760045169030014842403040092a04040c1c1c110b80c5c010780d01055440c07025080700000c0c10201c0d840105440303205050000c01040607035000068052000701c02005980380280005802c000c1e0741d20784042d600c030400e2000580200031090300040180045080d5001044560b45650405e56428010050000042060603400b60850340905010b41d04940f8608210101600c3c600464100300d104a8a90244060a074401c1080e0080c030400009000e02402031080e000064a180e242558082e482c6607902182c2c100000403903000041d44103003034000400018400c0b100a200c003510031010140c0070082c003c0030303648500c0c0260042010308907000080c04040c0020b0300d030110308180700e002074800b803040005a000c4500300c52003403c130350f05040c85101c6603441d25a046102d240c10003075001c24407410400510801030044c60588078107860800c62562038501156a42002100c2050300d8401000010078010300b0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 983866699 1250 983865449 983865481
    0x2040621060f030510060803090d0b0711010606111b0105090d03180e090607020606100e01020102071e020a1706190912210b0904020d1502030421080f 66
    0x51800036049440b806601000c00155009403000e62041d40300c41044401446410000d01040008520700352066011480b0648402c00141000000c9000035800b50f000d892280f0ac40d5030302e54001c000c11512410040e00942c04060554100c0c400ca00121121000c0b503140d003801010140c56103400c11000404100c400c600c840701c100c08014880c4064851410218071840143c002e64007400c10a01c1c04580e040c1c03500e40000c14080865002900f80010794440c4010341e4003103801494846205403103540181e001e0f01c1446002400603030090542128003c4201025100c80e1080b1450720040b03a46851000e0414a41840440b041c0c2090000c512400301183c00022600884c540100381e90320261100c68004c0200050000802e135017000c4c001d05d00d00c0780301c4c041d0040f5010000412100e202d600c0032544883c1c0060009021f00310000b610700501904035854051051044000e561724130b001d24205160b1220412004404030840880b41c80581c001c03c0d0440c0300e41c04000d108030a0759601c25200c191011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 983867949 1250 983866699 983866757
    0xa06120218060d0c0b030105011b0b220c170f030f030109051314070915060806041d120a020d0815040915060e060a050405011d07030b0d050f06010801020406 69
    0x80b00e0003030a00060500e0640200402c17040303c03015125894400050300020034048050220703801015003a0000d050520480d0300f0003c0f060b51006000100311889114910541010f00b002020030000945200e0110404c2c1c1c00b40c00c03050980e4582c001c0705210725501d0040c110302d0100024180700522140d040340d406907602842c20304034080312008540340c030a0200c914490314122500100000d00c803103c0d1602501c007440c0000d0311440540c0e86400d200034080c4801030300e0944070300c1d1a44503411021401d1128401c4503a80401642d422070080c5d1090342c404da00c0860303184050b016208950f03884074040c40c0c0041c403461780d414022404100c0001040300410340300604581c0b000036600c1c4440c6002c0d03a84241e80161900c0b83c1224a035040007401c01154001641c41a1321a40c1010018007072050040e441c18620321b0348000b020b03800d07152098240d000c2d0100540071900f201c0035408100038040000b50051813029424142c500e181d032a0070500e802c1c0d12407030140101250001101c1d42e4013aa00030b000c001025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 983869199 1250 983867949 983867959
    0x60f0f11120d0218010e0303070b0606071202070e0f060d110411030114010905042708040302060a0e01031a030304050111031c0e19033f050a0612021806 67
    0x1580c02291000c64000b0354030107012030342c0031030f8102d01c1d25544011070f05030f9482400e082c03c2015021000036640d2049a00040601006002180740340c1c88030420b840324282d1040c40d15018090780300e0000d69403a580e00c100700b10102d551020900142c0c0c0c000b20103000305c80203480c0d85055029a11590f401c0c0301041d00c0c04e41c00c40d6a072955034a03046041380107075002c0e00c0c48244210303403d9441000100341004940000b88140c0c80c0c000ea941f600c5540995131411071030130460000034403119080c4400c2c0303401168406500b0540016601040ea0342c020320b02101800e00740c80421845504480c04180c44c840112920b80580c410881400503601900c001d596030108001201c0ca040e92580c030700410100903200e03034403d00d03440d41d0701c941c0440000d11034003c0f00200300d0b20075814007400791002040001c0d0418075071000c400d42e07080300781d828682c02c0811503600c0e0030444080b492050005034a0041c0700854454450b14030303010000ca900c1050629030492160000c010005207200b04201c40c5202d00d001e8221513100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 983870449 1250 983869199 983869213
    0xe060f060c0a0b070e01020d0305012d0801050a050708130b0402191706060307060512060d0c030b070804060b06040303020a080307091d010e071b0f02041d16060f0f11 73
    0x20715010f4203d02c50203069985034814004500064544000351440c0814103080000501c9440b08144040c4170a00001000c40403c0001c0042d8541030421030300000880d508000c2000804801030300041d003d00856038909585581d415103072049123511400040480480f80b002c030300503161041e50801c1e90030340d10000c0708429079030700c1d0700b200e4854228884200d950400c0003048101c5c981401064018401ca0821528200d0400040e0107000310092450f840385404410f150180308607050134502a41c1c2c850345503103403402c00e80c0d805454031030102da040703c1c07440c00c00b01c410005051500a84046030b515070018035044200742d54900e4240c10007007889080054409001407001075442e50005e0800407009070021550404801c1e4420f2038000b4192018021555034090a21000718080311500e508030600c2494851217100040141882800600c1c0e010030901182c55100004950500709076211041094125610201608c80780b281421400101e464400507040c00c2d80070b41300804075034072540199804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 983871699 1250 983870449 983870453
    0x3200f030a0f05060a140103140a2406050a08070e15030a12031512060504050114091005160c12050d1407020c09040b07050f04120b040c0e060f060c0a 66
    0x41e0040444082e1007000e9004050000d020b402d00119412261a40d02403000d0782286401981c207580c180700080880d1204400000c4220050111079040741d0312044412306220035045074039100c40c04004e4142190301d4807230001094640018080211081d03440a006143e00c0d003000c0032144507000f03008a940c0f240440e2040083d60b401d215415801d23200b10408811054412402000c543c111813843e1401d1140d40d40034821500b159045031000c1c0e600150114455940b440e203035014140810491403a081d450060283c0034801058016800010b000c00300590b80e82d80391111001540380c003245002c41c0c4041120300118070b19000914002589051107032a1104409005088400007562854003000003024007002c140d05001c6561140400c07201e02469080070b440b00780c0500d41c003071710b02800d00a002452a042d00702e0441950b005200a4540c0c1b0209074207428080d414100459085840070401200400e81034100074640e8021080540a00b80d141030380021301c402540480c0070740030b061255620900c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 983872949 1250 983871699 983871703
    0x2a1103150a1104090f020a1704030503010512010f0908030108210d0b060c03070c0906060224090a0b0a1a030a11010509010504270606021209090403050f0f040503060105060403200f03 80
    0x9000f01017a2001655006841801080d0000d1140c0000c4201002d0041c40082503210081d2819110103d0b00075292600c000607032401003050380030303d0f42d1307243c03c6c1418101400442c0c0301941c104c039440f00a03103101d012030034080c141c01201c2d0711804450607020703c48811070791500ea00c041401e21003d0840c51401c503280303050038034641008600303e034501a921070a02c910421402480024603d81c00244407000c0c40d0558151840c081180000020100340002464000208401d0710b4081e0070a244e2075850030304441e00c00250201c3c94818880b200d019078190864140012400c010640101c6038100080c0c00b10011519035001200850420078103000c003094820015a114000403c01c16041600c4421400514141d600c26400765003076411041100c05900031400441e0122482101d2039040c950b07480c0342c10b076640d02502402822040012032011180445c0e02c0c0104182c50302102210741030b0782c1e1001009014804c0f4003000b407030801c8401c152800d58056140c4c1142d12000109400509110400441c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 983874199 1250 983872949 983872961
    0x204080709050a1506170a0b15091e01020703121205090d0f050f09091905130309050907050f0307020a05240c21072a1103150a110409 59
    0x11031a0b03440e428403440700c0c4148104076090035201c1e000d0380711500d445400351800d0711449842c8109000703140010030050381c6a010081c1c00c00010321603c03180156035236507880c039085903d505000f582c04800c00c156180c60300090b14100e1005a004144503030841e134030b080510802251901c24000d0b1240d205002c00703c1406014801d4188400601d4400310b50768005000c140c40c00c522a050020030801d514100603500c0172140d40300720a945140d200d482d008083d0b000d00031500b568190003403600040c404902c12003884800e1280c000c0c3d5a14218540302c3d41001441d11042e10040d01060041005900c01e500b0903025560180c4140180c0d01100d40c581c41d6181040d0300e00850442d080710007681c006030701d180c1d08442600401c00c074038800d04090082c082c0d101000c982d0301107800c401d80c8101c0001c03452445510310f0440c40320084886194806007040003e0030a40406080b161603110500c3d82d015030400103114201100107400c00d2000740c80c0c101403080201000c0c3c451003507802c1c08100119055040d80120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 983875449 1250 983874199 983874209
    0x304020607172502100f02060105100e030706090503060901060b0a0f11070902030a1415040203062409041103100302150f03040b0f091f0203180d0806010e01020c010c120302040807 79
    0x203c603400565104001918010148034810b0007401910001040d070300041d8141594015a00002d01c146210401d9500420044200d03515200d50300001c5600796008440c101242c401707408880349515040b04003426101c2b83d0043c4440d001c0c0600c0198803d170711401104600820509156408014034800076080c6145070b00301e9000583c0000522020705102c2c0300c1e4040f8083d80f005450079500700183d21001640d101e164140c865070b004000718081e5501c0f581c448158940761724820440400042c040780440e000702656030b00c103601c0c010001c1d034040954000c41e40300c2e243e4590107000c0d0909503420040a90a0010340c40c064100501c100c0b1a02e4040c040114000c5001d230030350b54a245020110b4200c1144002c0205017107401c01e95000d078080a610606641c1c0e02c2c409580542c807650342c0035071082a11401a9100d0461003600d8854200a40040129008440070307625240110710120042e030761002c7d8031040b24000b604041525001c0b80400410701140301d2103203405440c055882d20355510b81105a085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 983876699 1250 983875449 983875507
    0x80a081c0f0504021f02030412060209060417060c041d0c09041a090c0405031203150d030309050d09180f090b01030317090a15051504061e0b030402060717 68
    0x3d100640c6080b1001122040303010f8030b000d01101c0f0b0500c00039180e01851281003440030003503074110108001c07a01a81e003561009030920340c66a0b42c801084001c0ca01c0c1211034807080c0210004144000c020343d0844041d02e08003c9466851004000803c0c0400001042d0806d00c4200f408100700c10741d52401441c1c1034a140038040b14030800190100040140098000301c0031410810080000da03c010814016a4911480854603039a5244515080d21690641c4903885451900d0302c604264042e4007816001c6d0141c41100c02100100030141c0304641d0340d010702410408d020802403050740503a0402d044c9408240c0e0301150011140d1380b24000568283c00803004030392201c4602c0f40382c0141110003a4400c28117401858480059200d1200e041d1416140c0d00311291294005080b11154100000500001030010000e40390f07500c0c400d04e078641c15505030400d50307d51034000081008102e003d403801603400406044c030f42586680c2c2c4200e0340102c0ca0040030511014002c04c0e600d20fa9002c0b9030309150106a607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 983877949 1250 983876699 983876701
    0xa02120a09140a050f010f0c05030f0d1505130906020412081b121801110f03030a1113091e05040b01150f090b0a02070b0c0f1204080a081c0f05 63
    0x22401c2c4905500006a400f4500c84402044140e03155500c1c0101c030142801d200c100100000012640500b040c00e000d4201e100005241031a08044002401e80c0b0603d40800c0020507520007100110800328800c039a030100403800900c082c0e001560013007c4051241e540145041d0341c400c0c8001c42c1c0e415400c0256200c1201144001e41014000d070110045040740340900100292400410708a00500844007558141885640e200ba4000d480c01e52100b0021401c540001401c003d11039620b1b80100d503052543c5081480c0b1100217803058065a039800c00840d2811361103820003254400804e11910f0010042da000300140803122000d2207900d0056000b1a01805c003507050044004094000001d10b1382081600381071591034507848100d00c0155140d9039016030b0340c0c40d00d5020807840d04030380e60030603611000001030400310140001081e00507190404142c541c42480b0745031038802d41c081c80c46902d0507174100c1807000c000076000fa0000e240303101a5414008407594441d04e040200c42c26500c050712044d503960 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 983879199 1250 983877949 983877959
    0x302060106080c070803330307141302180d0b09010b0603040803151f02010b0a0801051b2107030506010e06090607140a0b0403050d0e160302060a02120a09 68
    0x1000480c0505114100714000d814159085078a81c4262031000d40b812a0220109000c01d10f0b107170b503072203d00e0582c0d0020034140900c9a8408210028030110510030710421b980000c02407020210440c241c100100702c0b003400c012081e000f90180d80082c00c50007100102e08854561540ca2041c481040383c020045c034011450000e00301803c45500410451190f20144100000501c0400c00c0300c0e030001d02c558081e0720104814022440340004024284421085015130808483c3d05600400d8a9807080b0364032608581d40345005400c0341c40540e4016150315644c41d83e401c91048900c0104840d05040c000c505800081c1151500c0c4a24141c8012001940740d0703040c0500ca60340100c24008078101203c074140f03040040c5002443c10702c01d64000074040d0001c0080201030340340c11b110300d0301c0351038102000c0040707441e00345001440c59001c11071048a5503d00700d0105258140010924032806105141124590640e000c011080d003094000c5400c40c410262420703070710351150f0041c04c403803941d64640b000394905203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 983880449 1250 983879199 983879203
    0x809102a0c0b0f040807060f0603081804050c090a0501110307022d010e1c030302040b030f09100b0d11042004090c0314070309080708160b07020f0c09071116030302 72
    0xc1d142403040b601c0b980134040844c640004481075254488800250100700c150a0b4004d01107582c806031501c100402c00008503190040344138007811003151700b000980d80300c0100c1c11107802000d111582140c1968030034401035014040b0002c0240c1210101d0b803c250341e941c0000c00400307860b810fa6020b051b8603003600c001e0198003a8041d25900090030700b0012004a00045059005465842c8540c24107402c088000d042c0240d048801900c0d4802c081d55492130b100c071182d1a41e9009540011062298051001c035403036240c0700310000d00d00014072030604003469481d00b0070f0211100031450351082c2e481c0401418130442c00307034544001c0714041d00161210f00c0c0080311421502c0840b010401c1c507007881101700001c05200c00c41ea503c45d007036041c0010003800d42d0500d00518051064000c044010001c0e1880d203910440c800c040416104540450003a0350300ca000b2a12100c010020740c1d45071307010385561141840d2905800340d00c68207a1400c428004061400e0030302d45030344012520400c04040c8801c2c004d0645c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 983881699 1250 983880449 983880451
    0x1318021005270109090207050a051510030f060b2106060a081203070201111c0f0603020d300e040608060709030615050a0e10060809102a0c0b 62
    0x150034200d040050200140d10b4594082d207088080c038080051030456607000b2004400a080c441a0441d00e8220624109940301644c24060320940300e10b000b61001d000111101c14810115042e003105078928696400c8106800d03110101c59458aa0507012030a85900c2d107141d40c1c401421031100842e03400082c0ca40d040005c0a0038090007004e10784000c0c80f4109000407601d841c040340440300c1d59656130b00e41d800c86c01000c0d440e20703d403000000000c0100070707030304a0030000e0a070741003c13201041504c0307015000c4811128a480003c0d00000340031142004601ca008580110700d01d0072043c80c455215144500074004a1040403402180040c580c0496070704040c03250320b002e00940401408103041c80540a0400b071890300c4014000f40d22490b1030300c11341c1e0b429442c0350000c01c006021440c0e8591128049a41c801007119504030b0366a500200185503441046a180224442c801400303100754101401c901800035030490031a0fa2142c641c0040703204d2410986130218141c25990303555400140d00e4180b0700500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 983882949 1250 983881699 983881729
    0x50913060e0f0d1d0910090b0a060c02010f2f01240302091810060311100f0c0609021002030a0206160f0503091e030903010c0203180d02131802 63
    0x4404040c003114180005074210f241c44a43c20b01e46000311000d941480e11003448903090303401500d2039090100901c206556002901c03004501400b10040f076400380b04095040344514030004841650341000b550141c042c4081d000420718203007100c01010002100729110b8030f5800740d00084917422006681c00203209014002805000701003000015560090b5644140e010181c414900700b000700300c0e1f0403420405460070040c000d041c2da9000902c0c50040c0010720341480240c80d0350b120314504030801d00e020302d41c10380136009a8441d401c0740003142000701c801e0605001e0071501c03140c1c1c0d5140702d030240e503a0f00c8128040881a500850780c0b070940900080c20808090900d103450000f42c400c545161350086640d0f0254200780c50880c1e20303681c6001800f4601484a500001c00c0d0801e0042c03145880070100c003c00140d10160000c0c08001e4803814101e03078078400c5405c20506040c0c0790038083d00724901180383c552031500040200b802e4903244e1803440300701d801c41510f00895200e1604034608600b01182d59244000b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 983884199 1250 983882949 983882953
    0x506150103140f3c0604230705090a14120a0302030405010c020a092c0708030304020f0111060a02030a060506090d060903140a05040e01171e0304050913060e 69
    0x11890014001c90503014082d030b0014840b00300007801c030101d0041c000310100c0c1c44000500e070701c10300315800340c4880d071314514100c41c142c3c030040c0080c0c214100b6001d00e103003100c550060300440b400301903110b40010b007001c0d002c0c201b0010708009442c62942c44200d40704c00b815103804920b001a143d03c003041140f80c00380d002447c0c20b8101c8249503010a802000b5202181d0080c24086041c40c0148000b816009041c1c02504503940f60401205c40c0d9001d01c1000d0362201072403800360800703074202c210469458a661145043e25842000024014103242031080300f400e0060400b07c4035810f45401c01c1e03080440c01c4610315403c681c0481048806030260148100800080d60424901003100000c21a45d81d502e0704040e000d16111040042014412400315080c0c8540c4040700f0385658820400621302c1c0c0c42446414a502600f8001103071300c4803031203002c400b00e1240d40c00a000703001c0c0440c482c02104500215030303180c502080c000010340340c55100e0100d200380100c0f80701040e00d402c1440c150741120a8008000071035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 983885449 1250 983884199 983884211
    0x2123030a0b030c03190602090d1208070315052205161b1502071718031e1c02010f0617010513030914151b07080604081219090506150103 60
    0x25840102c5c00342058589650400742400740da0503d04040c0c800d018280d600648180300e02000d00400e0041f619249043d03036217a0850b62a4050102e05071586031818100c4002d80500c200250710b424030055002440d002804990142407241840c00c440003210443d00b64904aa42c03100c00c030703600c1216801d542c0c0c40007542481505954031161050400d1400f0000c60940c009180c20500c810004100e980c0d0100c202c005640d031500c8181c820100c2507107042c02e800b07841800c450700840704c404451020b0003410240200310340d010b8071100c000c180d1201358501082d5561100b40700041c3c4507030b0040e40b01424503030142011210812941c142140c800030104440c0c0b2140c0d0181600180e80900281c0031600e01115014a2004003c0010a056201c210805c9510700000780a1585021300d10400030307521040007a41c144580d142650b94890070202e50084c8121020840051055010304602d41c0101102d841600c242a40f04000b604461a19100351055031040040144031010b04006040400c02844c0c18804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 983886699 1250 983885449 983885473
    0x5030d02030c060708090109051b0a080105040809012019140c01020706050a03020c1624020d030c0e030a030c050c0f01050d0b0f0d0602030106020601122123030a0b03 73
    0x45110140545041105500c085030042d06c00350000d180040d00130069404100a2940000340000c8200c2014011848030700001006a0706200d8113101e079810a000b5840c0c004550011104000c045c6141d00c20400041580011800304210000c1c41c03d8511410400c0100c85062001c0501e1440c2651600ca501289040420f80d901046c11801c40300b03d81010b58451207641e4095003c0e020307420790030030a441010311840c1921140c050f10f00440c0c0e1503d12040e20304188491108825a0ba1449100542d009440f9a1001d6109070301075000300d04e442c0307400221000ca4800203414100e40f40300c181c000404280200f014000d0074000525a00b5040300d10740e20070b91110002a242d4060540304803122580c1d403c241c04941c0b0b503440e00c5030342000001c1004000844520b0040002e410038040c080062058500125240410003100700b60300d0781041c2c0e00d0f8500e10706e00c1720002d4600d82941000c810004d4001e19008881000d000d10341e1400c200c201030a0700c0e490720044940480e050340090b54441e6004a0364420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 983887949 1250 983886699 983886703
    0x937090f050a05040f0209040201120f0917030609010e090a060509030a080a0c020a060908090901080307060b010f2c120d1106040b011a071a0103060506010306150518060408010605030d02030c 84
    0x1c5c4c181d410340d05e000f10382d9a5400103132140d022150fa049a1942003003020941078016600c0500103e10a8401c5480410325603402c207118042142c40a40006440700107100c994441c10710280d00c80020800c41c0d00c1180240e40d04404e803107080d80c0c2c81100c3c1c2e002184000c4010381006c49a58440e002c500c080220309540d400c001d686240e00d80015100d10340d18220b00040c40600310880d112006c0180c40e101865a513600b5039941c2c1d41c0040001e80c1e01e01e250191080f002d611400d0b201c03024261654030000b8541152640303201007401c1d0041d0410044580c00580c825445281200001280702c2010b460000b8a1010140c502d030581e810041141e00001c08120000f440c80890314152041e1110b0381d00d1644015080141c144031300003020b0b04205140c650018010303145424039042e244240010302030350711082c0054080d0703651030003560351250400000004a905c20303000303000b4540d00d1001140c00c08000c1c00c049480f40e4002d80003000c083c4d440b60b1041c00700c2c0c00c0800074142d058240344011803820810510643d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 983889199 1250 983887949 983887973
    0x5010209180a1b14091c03270e01060e030a0b270c030a14122205040509070303080a020412050102130b0c0312130203010519110937090f050a0504 64
    0x355010134085036000c0a5242d00c0d864039200301e4203120840c0000d0039810090300b00054441844101d410803001d40301d1035001e1500700002c86140800011081c0d08140080d6001400021410340501c250122076002c03070000501e140c05260303030240035040b507948003000c41c00407201003000d2005da50060080d409161800200d00070019040f03032244494503004482c2a051115162032004541e00c0422a000c54410720706a692583c441013406030344d40395482e000d11007510800c50f03000885401c861001c00210b805109529400816000010318058640158440500340c901c0183c034169400f00f89080004a18071050000e0001b94401e181001000c1070b005544e84180d440c010000c0000901244d501ca240d0130446880c958014001d0103a032800541441d100d01f107200c01e0060a600f003a14103030704416428100c0e145814040e2003400031407440721000d02c000082110180c211140340316100314076900180400003a006a60340490361a912100c03074030550750042d1461280e103141100317200008105541107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 983890449 1250 983889199 983889227
    0x50a1404150b04030302150a1e050405010b06210f04020d0f05010b28051002101a04090317010b03191e0501080c0a090501030b0c030405010209180a1b 66
    0x880d500604003420400006540d2001d41c20364408070f004410583c001c81d0184111b03d990f40440040c1da29541450103880300800c1191000c0340910000b0660300c000e40003507500600480012034440d1111003c00c07c1640b00d003c0b030030721300701c80350042c12200b000280420b034200042340450002c0d400e054002842740199404c00602a0146034504402c1010a401010039000c0090081500c0750030809404160901207410b4901290a15000700c3d80c0c6c03402261403603500f8440e50080044500d201c80c0000244074100c00c1030000c1d03015203162080c5a60f40d0041c22000c42c800e5070f44049065044106100912040c0c0020210031018410085400d030f0801607040d200d44141703c04203140b0340582c5400190701002c1500004a820800041000070b00040c41e1040080240d030212041590303110700604a400a0000501001003800400c450080a0b4051500580240001803a1822000c0000d03001004590f00c2c4848400480420160700300d075103c2d11001c081150154202581074940041c45d000c1d1780c0442d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 983891699 1250 983890449 983890451
    0x301081e010e0106030809030f0a030203030a1808031f060c15020d0b0a1509061b0605090f0304090c030c02010b010806010f0c021c14150402090a09120c0507050a1404 73
    0x103112090009401c51001404182c0013000f150f6102d003000419544400b120901902c05c0f008212402c0200040400040c1d030168095030440e21075408200c041e19031241941c8112520142440101e104040114050091603a9004051040074080249045aa030220081c00703000d81812021840c01c1a5001d91071440001c0140e0754100c0713110180040003640c480c160080c090140124104c20402d800c000c1480d0580c45d802c51042d66010304881c0c1d0b60480c1404210080d070105d0340c034001501b81d041140c01100c00810f442c070100512524610315040b9a1041c83c1c0c3d1516503003030a8100b0b40600c038101070103455100900a0075030b03e0001a0104c84050030040c100314145041e541840d10420081500c591f00803d003c8042c004104149400c0e0081d600542d599150310b03210a600700000905800c00c22080c20300040940d540340c080243ca000000d12031503815441e225800c0020706031402d181d0000e20313640c40f580151285400c2061030045150402405105601d4041c41421503d1114800351070040310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 983892949 1250 983891699 983891743
    0x6011106131b0b0a110705030304060915020304180204051c0f110a09090b010e1008060a02391e030f0304051501180b06030403090302040509010b19050a0b030108 71
    0x520907409401c0b50f0301808019201050b070550466009100396480c1000d80c044501a82d1511704050f00d0f07102e20300c14400440d03141c180130481c0f12000c504056000c2c080f80142c80c1030503a1060861203074614610710620040c4d0018080c0014079041804151001c0c1c202503043c98441d555640c02070001e0b0100003d40222211000e41042e83c0c1c500100303402a007181c0d801400360000521b05145992001e0007202c0180080c03000091141046194a030700f00d070300c20401882143c0312018240020b60044141d6800c48403100c485007002c8a013080b403580d01075030903201d0a044081260409003444c0c0b001850016600d4081d008003400000001a10510300070048200d03034036160b034a042c92625035440030519400480c2c1000044c1070362960388070385843d440d0000600c1101100780802c42c0c180310845005011501d0303142d060000d8201940700a9106003802c0c00003429440c801c0000344602400d424902c04480000014400d070b0818240d040020b20406550300c1c00c5505040e00140c8400b0400c419903440c1580c06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 983894199 1250 983892949 983892983
    0x607030c050307081b0c010c0201052a07110d0f060f0b090126060f0613020f07030509010c051e010e0a05120f0d020409020405040606020a1104180206040902030601110613 75
    0x30709030302c032851760701c1515695441c5080c1c07030782d0302820000d4501c0c0003552a00001a5142030307a4181c18101c201c1598801c060041c0d502d03800d010580100609444e100c000030025001a00e8a02100240d00e00814189115091500c2c0281c296a103000100e941641002100c1c40e0a4a0b8005800d040d1000c00c0344940c0c103240ca50300c0c82401e01c0c5607809021450300c601410301c14a0805000c05900a14040e542645280300445030300050780701e40042d40351650300c02c2040001191050000c0c1551240525020644000540782d051401802803e00d80605942c1140009011024820300310340b4424400030305000741e0544ca40c0e5440d10000c0c0c483c148859800610700300000c60040c1110314000301078a045440329215440070000f034005024580c01140b8000012984c54000107551003000d51040c81540201007100030300014003214100c01c0b21100381d181e654001a40d40901900140c9001e0400584901c1c1443c0018405140b10401d00c0032600550140415954030098041c001c581101481a0405181e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 983895449 1250 983894199 983894221
    0x3090a020f1822051c1b030f051e0c010c030c030b090609060d05030a030603120c0803063c130207210905090103051f0608030901030e01090506180607030c05030708 72
    0x2401d0001c3c042c1c02286130b41c2c2d40c62141c084410b60002455900c0c00180d50165103900c401440c94035002d40400c50010080e000c1c28440c100806640859030810b41c59140c00a52b145125000864000d500c1e9440d03c801c000900d525204410b01c806482c0ba003800800000d0300401c41203a40034040601940d5000005801c58070303880c088211842c0e2060071655200101d84c0300134002c1000c2e010407107840081070450f80c2c035140300300542042c05170040c00301da186442e440200000e01c11203040183c802c1e0000c07410349003491100c0504d0481e4402807483e515498443d08208040c0d00000196800281d2040c03040704017180f09055042102c00180c24002900ca400c141c00341c60a12059008a0b0311045600011003046800316034495110002c01420800d04401071554007541c0c41c0b4024292580d1003070224082e958400e07003102c20380d0507044d000081d28408036202c45003444422284102d81c140c03007548107492560b0420429034064014a000c0000c880b0240d001042c5200107407003803080098000100d5000f4401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 983896699 1250 983895449 983895511
    0xb0916050903120301031a060f0108070c020d05010e010e01200910050421062319021b0a0c270209030102160b060f0f0303030103030810080303090a020f18 68
    0x15120b241341c4940e5640303840200301002501ca03200c41c6c035044022460b02d040c1190001c01a09050b160b866440c2d071032000440b00e480c4810410b90740520f02d45d21041c0464420b106034001000701c1c90007c42c0744400b0400b1036094581003840c00c5101440150928400c546850680e8843e000441d01e00e038500700e0170a0b00f2113180c001e0b500401c1d02c3c0140c02d000c1408481075503010b00d000a01c1542c05019991301081030368030710780711910407040c00981c02c4006980380100140781c2e400e10304003a40050400300051180c0d0004c05106985400644c44581b441c000d101b00840a1001041d040d4050009900445940c03280520b40c40d11541c00b00e90080348180050b5004e40640e000394881a201d460000524100040b4582040c1e460364062410002c07291010700f410f007060800c005001c0c00031495030346550780841e0b00c0c02004040e66001201e10101080303200d070a1005602591042004180e006074500400290280c0030010711b100c1d200e1075802e110810a0b1508080e4001e074080d1009415840b492045031804003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 983897949 1250 983896699 983896723
    0xc19140c03030103150203160818030d20192109032c01170c2701030c0302030919050304050315040b060105160b070e15030a0b0916050903 61
    0x24046900c01035654004065030490b80124000501502c0c038103a003008912050360030518018101000441c164003030f080107a0004038000401c048000702d1070390f51b030558011a1041098030340b0f0320340688601c103a28400728551200c542e406803900c507580020606554070303032100f041403000c02403070b145c8440c580c0b411150741c0b81e5910606001d40601d5203801842152902c003984000c80c0f9180c9080710342c50f04484801584001038480c07003e41c83c040409030400d0340008042410755401040030701c0d440440582031901040b40316004114400c1003d0006d420b545422180d0010588103004010724041c00080d111480c08030407083c4400c2443d1410f0041c218030554100c46d4051054200d5000ba5500405405101c1d5009806518860f03d500c00111110311a4941c64030658000491002c0400d0004070002d0b0800d405040850801550401003840040b0f10b5600c43c00118000c0100702c121074060090a03002e950440d45844a803a20301e141c500d0000c01c0001010401501150cc05170340c0d1030070801e46001c05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 983899199 1250 983897949 983897987
    0xd0609050a0b010b030a050c0c0c011206080d080106030c020d0e0913080406055205010603030509040b0109030c0b0f0405030a050a02100912080c0a020d051b03060c19 73
    0xf684401c490b0550368801da681909051500340060b418505a0090b1004056402d010b08003143c400c02c0116481d41c0c11200700c00605580f104002462403040000036030920054980c0402036161420242c121020902100d0030342d08610701d006130440c0c0c0080f282e91075030011143d5245a45407ca0900b543c0c90408500406004c1e000070046a40c941000141c01e4040d0701c4059680383c1c44024180c0c00041290521800c40f4600e20b020b61030389101c51100510010441d00e080301500784083d251503007900c040b94015000f06000145501d0740d03081601511206005c20700300b1940c151f00d15580c411101440f4460b50540301004101d0381d00b0f003c019000c44004000060403603003800414201561910102c00c4220302c12301c81c0c3c80041320040c0c02a02c0000448100310070716103030441980c0313840102d42d0204404c40051f00880750b0b550f0040e51111000040a80101d000300b0b503100603143d0421100400300d02a03403080d07000f4800c1041c40000b20b0b00b183c1450080300c0c282c940c9440c01c0b6809903100841c0140170141c0d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 983900449 1250 983899199 983899201
    0x6090d150e010b120a0c06081308040906170d0e0f0105070f111807080a0c121401080606040b030c04150b04090e0d0e060d111b070e01080c0d0609050a0b 67
    0x25441500888410501144c62555020341c1d201304550766000ca640081c142101070408104041c000e000e581e034803040c1000f042000024940e2407040c1580a03400c00c040c2c1958440b414850241e19084541600000c800200b0000c09000d0002d07188004052955220380d040607070904c5c8691082044d0f41e0119031103519081c2021003442d090504621100c0d12034091041000c28034408440805024007900c83c503199000c5a40340c48181d5800740c11004440302c28081b615400c80340d5262503105504110102c0407150041d035060a92a90400401400303283c403c9050a00501c500d54010410903130714041214001810800751061540441103540001d0f24810042400503d5509a420802c60240d4000039203500000e2990292854642a13074140d0300910207010f1008802401e0340b111120740034070742520303040c1015150b038800d03182c0480c1014009504180400c014070300c0310f072501e18054505040074080000410021034400201c103000548019281c45007070050010030f0024011494203c0030b09006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 983901699 1250 983900449 983900471
    0x170402040b1806091608070c06111b010b01020303010b0405042f031807030b01090911040513020109080c150307052a0c150d020d0b0604031110080606090d15 69
    0x282c0c907088440c58043c421103400542c410034118001d04144106880300c10f00c544416004451030103260500721051030355007200140c0800f8080c094840d502d04105403040704030000011901707440e002c20a040c1998001e1005000c80c00d04841a182501c6041d100064240342c1a0441c940103c0a02c8003101c01c5032600c01c00c1180f688208004521a40310500e40300f4088031007219240d6180150304c03001d020003242d04014020000d26801018050380203151002041c020f2000040459030107483e0500300b41c90032031201e0110358201d4005401810b00340042c04040ca9100c01080960800c0007111012003000400540414028030a0384c100f564180300507100c0c1800e401303030210710790700d81c0e40b0780c02141c42a00380070501840c00006001c0b0391940301d44010704000042600d040690400c0000b019003544a182000c0035846003c043c000071402984e540040030140e03014004e0180b0701a20b1503013044000010030400744c80e40c038100e64200b01c0507a21008000300c40d0801c070f4850140e00c803243c0005030405000c006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 983902949 1250 983901699 983901739
    0x150b0a021f06031a0c090f0102010f1a0406170a030e0307120b010f121106090f12060406110720042414060a020705090403020304050904030207091b170402040b 70
    0xd0300c0c8215a103190114400fa12004888000c481c102e0b0705040800c4850410b0030308a03034111f100041800007044088280f250030043e148004903d0040e079509402c1c1000602c3c0c03e001e5400100b05100c51071094007800981c82e92181403411015050041da01001c45d5a0740f810042940141032902140211516034034000140075000c2c46007801c000c04c0c81130042103070403003d48816401c55010180050780303500e0000f407141e1a0400c03040168070040801d50101c06465120603031030415904400341110349030070710303141f01143d10040c9600e542400c14072a41c1c00080c0c4854601640341c106108061000810800240c080c00c51124004400c1c903142201e50b100c0f803040c24800c41500c0041201c1100380e00c882e000c2c40300e135000301825000140e0001d20100980c0c2801403449402c84c0c000c0c81a01c0c54180c4940210705c4a04080d181100164014407040105904a1080e01d1007544009080b034030071a10290010003041c040214000c1c078403090700c00b00b000c44d52507a0041c040e8000140c244644403203c405591 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 983904199 1250 983902949 983902961
    0x803010e010801150510200706110d0c0213110f0a031d0c0607061509090f0b09060f070827010f050a1104181509061404150b0a021f 58
    0x40183c1d800c10406103103040c6405000025074a02400c0004050b101d10000c58041c6100342c410402d82003c448500c010000034050000507140d0b546800080a2480040518050001654000f00000c0c0200800107035201a5500625404080040745203a8a46141486e81c45102442c601030b003000600000c50a4154000c810301d00030280700305403141030312400d154603000d03501180e6600600400985e80014010703803100d007011201013075600a91703403100304050072a10070300e030240c80d533581e5000c489042005404e01590b000c84040c01802650410401d4100202405030100040c011070300001040320031004881c00e0024002600040c7c0c9510015610380207041c84102c00c11428102400038000030f13018002da403204000005920310300f03441e00350301c0e0f10020f01c462a0003903241e403503451400303040c2408086000070785070048001071700741e281c0302865484d11303c8410315a026a06040e0522070003046d01d170151080b90103000d54917544401000c022420300400020b5210071124100392040701c626030764021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 983905449 1250 983904199 983904209
    0xb062a01050f04020102060f0603061f030206280e0d0609050a0210030c0201060506091e180c12010e151012050c09040c170109020703031b0e150c06150d0803010e01 72
    0x394447e0389501ca1603000a04003205c5003901030b0b100720003060455100c0340500d1640d03e0011003842d4599100e82c00221103034426180f000600d0306401042c030146c6942800036030380da5103908100080c1d9002c940803c20003140108041c05091390b41c40039a092210900195200d81d030700800c19a5252886d00c800380c02440c4410704040198a407980100c0c09050880885900040040000105c08880b0000c52185141994101e41110040086c2580b03004461016070140703094a42c1280c80f12114094003001420580c0003036034034441c4405110b03440c40c0c440c09c50800088240e48803007034041c01210a40741107000160a039295403402040002c40d120b0741e00507142c104002c44007402425a1381d00103d42c40d5021237600c20000c1c0103140100300d4a03041e40c0c0180030581c0b01c0e00700455581b8601c281c0c0220103240303030215404183c940b00001103a1603c2d4460320218a1101c4143c0e05144403c1d07540360f0348010043c60701844201280346400301d9640c0106404599030303c1040241d40350b0319054590380444081c0b1407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 983906699 1250 983905449 983905453
    0x903020c032103180307032706120b0103021903060905060901060503010b0c0712080c1213030f170c0f0d021b0607060905010507030902130b062a01050f04020102 71
    0x14221140350100c1c07404000350b600d01110a000c056504984165403000e803035501c04894940307100c12081d0041c800381035824000e8031104172180e080154410503103da250725a4148100e54002d0008a0f00b22404481d03159401c80e00048000c00c4400680003441051031000c0402c1c102c407400030f0780b0307549604140700b91082e2a2040c402a1030b04c07402d0040300c03042801a000460024401070000300040c03c00741c038900c1d10010481d0011a61200704040b901c140010a8a89640c001198042c00c00d08022280c000300440622078900684091002d05c2034469020080800001c03101d04001e00803c503030b5120faa03580b82d0080c2959900d00601440c1c0c0c9141c1d0f82c1080341c0130b00510907900b801c00d00100300039003c0c04014844200107110310003003020540c0400703000c9607015039601e1800c0108500f4410b181c4110980c0d240080d920640340100f05182d0666100c2c0d03010136041903a043d0280e1582d1050319001504070103428090f00c0d4070002c0b00e42170504010350801c250310f00000c00904503030609040340030354000c0c4c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 983907949 1250 983906699 983906713
    0x1090f18120c0611070804060e0a03030210150b04080d0f0203030601120b1c030206060103061e031e0f06140a090506010e0619140f010c1106030c0706050406090302 72
    0x110100c005690304405000101e4401030030388032900030a405840d8611a503c002200c2d410b10f04100b9203038205e407105680c4054041130910a036a080000c91001100c2100e02c6d84c075141c1f46540003550307481250040140c1310384800c40403440201009000c4060a4502000b1751669182c0041c10394540f4517603900340010b1050f0001d56101c074000300850340030b104107969140302c10f0160040c2101802e581b020060300450031503d50840b0b400c2000183c0344044c0b196001d00404c0c00c02030b0004080c0c03040358010f034a00b041c45d2008290254040305d01d52007225800141c1140080540c95845501030f0007020203030160141c040352400304084c0b0307800360444c10f000d140d0640b443e440780000c880445521800040950780840014050301043c2c9070659407044000b03001c0c2c609400c0f59603550809121a0780100c03000c0d100080b4074066031a1172a0382c8900d5503c2031a1840900809443e43e10541410750035140c040d0b80004045044c004040d002c507003095030402c0b000e202a0074580391100080010607030550050140f25 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 983909199 1250 983907949 983907971
    0x21803030d0c1b031e050405030a0c0302030706052712030f030109110c210c15271c0903061b091e061b0b0c0c0d02030f04060c03031401090f 62
    0x94185841c2ea0309a45c800c0c0940540008410b001040c0c80d41c1041440000e11000840c0c2d642003210707240d904d200710202140c0c1c0f0304e94418146001ca15030007034014040d0910001680e0720741d0000b0300401020480301946003280c2440442d540032080344850350035003c009010707030003809140003e5040b03c0340107004000c5500d401d0304944c041d0140c43c0187c0000d41104e51005560000d84040c0100b84006500807460050301d5002c50b441c1800424070002095500820410000103e81089131403221130049848102410800c081d241c079201510001410001100e00030a5882600e2a602450307202404002041c01c00d8801a60212800c81c1c9800003181007001240050f990703008803510300605886115820b041000c00c0d07620403802110300e012070307908913800800310340300d0b0704030318021510302d00782e9a903420700c00d1b4810b400c1071b80322001003040d98010446034000c203450a0440c0c0407a2082e182c4208070066618084000c1d01c5074400c2515280500000424004442c1d80f064040741640f0301c0403c0907040031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 983910449 1250 983909199 983909237
    0x61905010501050a0e0f0402041502121810020307060203040317090d122003010b0304150203010e07110109140c130b0d081c06030b04020111010506030a06021803030d0c 74
    0xd0240d00e0014030f0a00001181c02d02a40c120a150800100081c04180d003805c007040480c0c1051b0301c0700703401c2ca00c120072918050340c05010414044102900d16850400c1c002e844050540c0155805401000c0701c1c1000011503109005540405600903025541ca050504000780000d0190048840e003818101c0490205040003421606000d03003520b8402c81c07030603800640001407a1240400540ba0082113198040c40c802400960181c186424010348030f00740f038200410110204c0d540c1c02c0035244104014001d040d01458090351104241c940160305d940c0415481d4094030a42100400101344071251200108006c43d80034640c0b6025107940c050504003003011010b88140900b120b80003c441107407130012809403c020311840e10000c40521601c0400855941243d030304d58000d407001c01c0b0010903c8115a0b000040c8010124040024040d40c200940040c0c0c4171041903100400403540000d140400c1042081c00b00410b060007070949899403880755621029250646c07000d8000755508020000d40042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 983911699 1250 983910449 983910451
    0x9090609032a0b15060d0c02010b09040b01050904020414040b04020f1017041a0103120e0d02090609090f0d020f0609060708040f030926060a020a0e0d0c1205061905 72
    0x46101100c1035510943c4030a8850403014100c485454107005011101ea19400d008004403401c1100024031200c461a0080c2190408000680b08030342901c00e000200300010f100c14192002192800150388440c40001c00916071404246003003507075a401c00c07050200802805200d1802a20803040c01c80d01c4004001c81030069980c0720000c5150410607403030800c450720040e58881e106810100b03d2103040c86203607841904c01da01c12550140700d9007440144c0c5612106200c1010003d907910810b129880d4001610150000d0a0a0041546a0014066035400c22910a1100f2140181d6040d04004017000b52104580c107203d49040c4036030400328285000c00074813148152450f035544030f100d840d241e507410a00c007407012040e020000a4240440c1d042d414851200c40f42540c1d004600500c1c840189817411310b0300080031901000c0c410f101e24041150480b059081030075045a81000c20b1015140c496041c000f960849248420a00c18142c10020300140f05800303603c2c0310204007005180760a080003030706c0f4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 983912949 1250 983911699 983911757
    0x41406040b060c0a0b10050303040806011e050121110301140306060609010804030f031136010f030b1338010909050a020c010c03020d06060302090609190909060903 72
    0x8008104070000c103a41203030086c1c1010441d60b000c17915680d41d0b0b0000c1c3c0f540e0049d4202c1a401d420050040141004404043d03110100e50010a031f8418035040003e040b501c0c0214480b21031100007204001a04415072041c403086101c107008940b296155040d40046100300d1003400d000c4d110750302c082000761400d00182c0c1c000541c142e54259541c2d03615074044840080007103680040c162608010b2640d0000d603000303010340c608101920901d0030004240140e030100b1007010000c0521000102203103990b0301c64801880c462080c03c6c042600c0904501080650500c0311040345400d1070b10108040130441c0010090090008441d03e803040f01010550308071904800310311070b020801c45441000400e601b50801a8000800302005003000410940d480c00d4580694644000a5001580c446c1c503215521480d006010145821810045a4400300d020b030b12544c0d149078800c892907880f0303201d0b00d10720304040d00281024800034805a0210310f41480508030708001200400c071160f2502a0546c000000f039a1100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 983914199 1250 983912949 983912953
    0x102010c0c11040b120a030c21140f09040f050106030b0a0b0307030519050f1603150b30040606050108040201020c09060406050a030c0f060903020a0b090a0302041406040b060c 77
    0x10240b02c0401004092503980e20380c112214072074000054106009203041c50b03000351600101c0c0411491700458001d500d100d0320342c942003829419001c10794003640c050441e0714801d40d410307a03c030f441c0500721450303001e46900c581d8042e00702081011203c00350307042603040300c03280e44043c400d0301e0004003009204c0200307025080c6024030a000085100d81700c0e40040750441082e003084044401c90a01d00401e0316011160b0790704203406001804803030405015041600d10880c50104a000d8440a94940aa01c180709075052a803001c10811080b80740c090414a01c1e20706034130360000d50410b0b201800900141100c05943c40ca16040c00000c3c254080c2e0301300c83c0300d540e05a02900a084201d410451f801c0006440181c10964940d80030409484040001001d1030047c41c0d4031168030710b001d0103010341c0401504504100b10710110104016121010a0030584140e0f08645440e40c0036000807500602c510f62010f540507003000051885444070030203081c06200140d400303114600a003030030304c64070307100d8104480403135 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 983915449 1250 983914199 983914223
    0xa0f080307060f021209030712050903190602040f0e04060c03140106030203040c150e092505070510050a02040e0708012105010e030a08011d1b22080c0102010c0c 71
    0x100c0d075512041c100d11003c500141408500301002c0d0b4810390032108101d140d80002518000d108182d0081803551040780344c01c524281056007c00d41344d5050170800d4468000b00350a24080100a40646000d003030f05240c2152842d99031200010305001c1502d09450140c80c01600301c0303c0911038090b503034442c082c2c3e00c00c035480c90b40307009811030095000070001d49072409095070106070748016008031814001c00d5035555900b052800208884900090164120030512406120296003805074501002c4e105003880d030744481540c100203040007001c2c0e4070082510b00c0d04080001100e0b5035406001a00c40d24000c0d070400d0f584284040d03602e50000c0c0290451207242015261034500118003044015100b5400440c40125081210385142c1040043c0004203901c2001031003940c0510600d440b0801c040d03001502c00381003004a281e6405036030355102e20441000100c0c0383c261607060194000c641103800e0128143c681d034030501a1595038446046006509040c550314009105d04034102203140c220944040d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 983916699 1250 983915449 983915453
    0x60b0a0b04030b060f180108030904060504050f060d150603050a140f0c060a14030103211706090a06030f120e041a13140901020304151413140a050102090a0f080307 72
    0x705d1006118540d82c44402034450300b40040400803c01d009061140056840c0c0703009008100c01d50781c041d00306500031444d010400801045094003680c00034410780c1c1e1910f043c10079080c82c610300e241d0000c0083d074850404100000b00840000e081070f143e401105072250f204800046943c55415400280030300c0c2e40315442260003450f000c001040e4214150034400201071490700190b00f9908240e005541c05229a0601d0f043c080e40e450798142d090890785000b4440c0711841c011403002001c09001c042c020290540000c405000b951300c540c01840d042000c1c42c8c1680c503180b0309104200e186d00c100c08009070003201154207501782801440e4a42c0c4c14091301c0a051b0400700e0a000d801a000408040969118014101170744c1c00d00201500030b094101c000341c0c2d6440e2504201c11101217402c50b01c0d0249241c020000030004a003690700c3d030000d03100d6840c03482510031420415800f280c4613060000a018010030740042020540c0201410142921001e10a41c0e6410356040b0300041481981000d400800880300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 983917949 1250 983916699 983916709
    0x150e0a03052125022109040b01140a0e03071d0403020c04060b0403060e2509061e090f1b0203040e060f01142803050603010506190b090f0d060b0a0b04030b06 69
    0x2055031040302c51200c040000170905040e01070600c03c00040000c0c1030400d80c2081d00500e50710307940c20b0a0014041884202010f601c1c030030880190100044030b0008441c2d640c0502c0000028043d0035240201c000002c080042d4061003560110090b228206400c4507034100f5014a80844240180842c02c041c55900c5140207060b00050190f05401510a00030141925044100c4001000a089040d40d41004455002c980240d0082d80d81550310302010000c0080c07400c2108265031800d60082032560700d1408010140030785030581e03640350450740565800d150f800009042203a1a0307041802e06a00c03044140101c540900382c1b6140000c1012103080c1c50700302c0200003446012052011051000c1146200846032a0070740e150100003a01d82c018000c1c0b030700e0b003409031a0300460101d80f01195510b513148403007848111841220410317640802e103200d5a070b507943e070714100d1044060201c01c054101c525007440209a039030110b0344502d043c131030b000c0303510740d412000d441c1580c2c0e0100350309000384c03a0842002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 983919199 1250 983917949 983918011
    0x806011101180803040c17030706020705011e0b19080a0303020c0a1203050708181e0703080d090212060702100b06040504140708150d150e0a030521 65
    0x1540e50340390709500c02908180500b080070700b4000c0c40308a44a003018035051a0300c0d45564010078960005462070104003002100b00d0310b080342d0144005907074a1451401e103016242d016030040411500c44084401c1c81c0705600402e24000e4111683d0a071802c0008000900c088113000f0402c03941d00c43c19075200041c0c003e0340144989008803085410100315507503401c05542c4640307801800a0b807500180484650841c24060b00401d45604103040c0544904849075203400d01c2042e00340b0001c0c00011004516800d00c50385024681141815075201d13918020b00b4042d01071080c049025480745d80030012321104c00300303105005107490340c043c4c40c04443d1811003e003e007120021169000034108800902d6980d1442000b01c40130355011100481e1808030713000b900c1d0100c0149100601005910358001c590f031180b001c0d00149a00035181400e04035408002c0c4010f10f8020f01d1010648100740c51523007890703001400341060f40780e07410007800812400d94950303d59070700a507503030f9040c0744a14210034800316030030240d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 983920449 1250 983919199 983919227
    0x103021e03040236010e0702060402100908011112090102071a060a15020a11030303010b0f031308040303080f07051206061b160501140a0503011203050f13090e0d080601 74
    0x138880c040c2d560481c040b064541c031080084180010508824103c16440900d00420404000c05168944910003a4031210010130092082c012000000e5410b40124258800741000000030451001e107906807640507031240114450a05040c4005010300702c0500803114856409400c608a42c0c02c0701029030035883c80500400e50140359400007003441013451035980030441169000f4400141c560500c92034050403046030034080d0300100010b000c035180c6d81c2c3c02c03108a65018410255070365540084400003001e440340c001c00b1f03000005000001e00d9449002240580700d101c00816180e00c0d500000c0e5075611484620004445940000940c2407500d070f4040e0403c801512205003400b00b6041c241401c00c0d10041138a03100501c00f042c00e00c400d50b031140ea00c4656001a80116107004a406d0b805000343c001481200e40c46c45a201100c4200340c030543c203031904000b05003034541e02d4144030440a61180110700503451414078100340300d2818900004c0024070940d860f220704d292600c1c0e05004440082c00c6c4214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 983921699 1250 983920449 983920459
    0x60f0e03010203131b0b1801110708030a020d021902060901201b01080907030b10150512071806030b36060a03050714220b0a050103021e030402 63
    0x50980e84080c0000c51143d0980100b103052068245002d60516600e002c02c0a1480940c1009011503d00c8404641c0e005d404c061345e45042e40c203000012240d00c0e00940420090b0b000d5000d0002e40c411000000c4c14007100c1c1746d0291020010f4621080340c4c3c1d041412030b00585104442e03810f1002d41802c1300106500035040c0752403410340c1c891400f50030540900c1d0150a04a602003181003803418440c9194500c81c0a0910342042c0d9410314000056640c03456001c040d1040c0c0000011076416100c41841780014030000802d08002c400050001c2d1440d00000301410a52400302c000807041d81c0700c3d04101c10600600a8a07140303040c10860104e0003051488225500401c08403a03a20310340014a494075150141741652650511a400d5810712004015010034041d000e0301a05000048002c03a0310010340c2c2d480c02070f85021010300e4000440496120074101c5000e1240c00300f220382c9804541214641c2b80044d50f461100d1665940110124411a884000350b000c0c0c0382c0d00283c441c2070f180021504140014a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 983922949 1250 983921699 983921717
    0x30b04020a020a050709060e040209130212160518040b091006091a1f0f0311070501050714210910020a080406060b070c090b0a0e09030a1e09060f 64
    0x101290490340306107440c03000350380700344500c03020401d040045030003404080206004140c41e01078000d2036001c010340000c1c070a1a18800081c6c00e0622f0f1242c248500c0d03001850f0580a0411030411900c481c1090f04070108100c8114000c601402c003541030361811484150003030b503070361b03036035183c2402201c0050311401803806807080b00003079002070340580300140c507414a002405600842200f012841800940c03402a0b988040150400004203040f0310307442058140f071a896001014120b00911401404001c0850302043c00c3d001d1150552005209035120b4403140ba440461080e801401d00031545864a4802241d4400400c4080c001800341c0080703d240c01c0314180700482c1e000c0da080e030308000c070940c0008194008100901881d0301400c401410207654403890000309880c0c0e41c080d14400d008000c82c560300d45643d902203032940c9241100810302c049402c080c0307081050201d41c50b6800003030710400042407813480000503120040140c9012045071644e0450600c0c000090300c6001d42c0074003680c14007049138 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 983924199 1250 983922949 983922971
    0xe010608030408030d050a0b180a2903010e0c100c050a08030106210603020d080708130602010b190f0e0903070804060c03031404020906040513020d06090b0106180b070303 75
    0x1c082d20180180344007664550101c44850b4048034001040060341604007045d940c015152441c1200d15104403040c01c0c000e0395200d00d4560f0141c101c040e07000d407403032511f048020340d0002c034510300d6810f828044000780014904101c54583d950f040400e0968011042e00c00101401e000b840843e1144c3d06c0741c4191500b031000c81e1140049a04244d1200d0041000307102d40603000d03907100c407603101d400c00c480c14100503941c2580c011030b043c10741c10f0200800130070001a030303001071002140c180d41c0500c100180c81e200031503c585009001e041519a0716006082030f18110b00921085841601564400c10740f02d24042d15050440f0322052010703007d941c0d40c1c0010040d800c04101c00388010409480a84c0b07038100070014a2400600b00c1e50214100c00c42d4501032010b200060ba100d03030007180c000d03404a4000c5207030b407902e0380942005c01030145c009520103c04142881045110f400404203d8094001c0c03255680e40c400c4241c8102520075940080100c0040041c0552218a005041803e0284ca0b00160703101d180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 983925449 1250 983924199 983924203
    0x1201110c0703030e030303040f11010309080a030b030106140f04110c0307030e0f0402030405100e030c07090906050a020c0d0c15050718140d0623100806010906030809040e010608 78
    0xd0381034051a4201640034014960003c3c01e03260002000c0d00194914682615020078681c246800200000c5804103c0d0700355030703c0fa0308440c8542d50410442a55055401005001803502403500b500035400c020740041d00e0015070700038092048014094030140202401008010200c0d034408c0040e1250600410404000c1000a04a203070321988508200e82004020000b8148d0502c00092049004204000004001140807103543c5040a03011490003207020303020b030543c0a030841ca0f1030980b14400002030700c000726030003d11149020f614200310b941c0340d18403030009911030340c401e00c0b00316800354012041e42071044000101141c020010300403014440324024090360400e0311203c001540d48054480865103d0524500401190301f510783c0185000c00803851512101d200642525602e0320300d0a0303180144204080c17100d0440c1c055441524000c500d4912240791030169680d14401c0e080080b03584c803064811042030b00d0304441000e0404214004200107404225815042e954a510002a002d042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 983926699 1250 983925449 983925457
    0x509130311032b1113032004020c1501050a05180c0412060501080c0102010501050a120c0305120406020f03130e060409140f0c0913030807090e0c0403030f05090f120111 74
    0x20b10500d510040600074205954603000c488440c0726040000304565005c00c410340c421281d1100341d11069280800c00e10044400d44420603030814000254424050b10101d02400341240c44160169642d0300c8805000044115029840d0001e01c4034050b4a210b03203843c50782c9a402a18005c20610b001d813a00b03003500a65a204004482003501d940050102c868207200002150034281700800c903540c03401001030207109042c03081540c0120081260001c3c01010745580002d1600103045603034207010350000c50400d90013480703180010701903121340717101021003c001c680814015011007418035041031400c40c01504050a0207a1059855950000041c5070322110040d00c4030030805030400c402c2103c44281012078002c05507104250b181c04000e41800d1118080c0300c10354040ca04036030199540001a5480409a000040b0b03030341c0e0003802c100c1805440c100820176a44032350f481001c1103034503850a803030030b000d01a0026800300c4404500303010b608101c1740b1040072811040011034506c040000104207070740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 983927949 1250 983926699 983926747
    0x4090606020d09120b0c0a02030f072114120c19030f0501080313031e2411031302130b0d0b060f0321030406090c06120501050913031103 60
    0xa00d01e240045600186038800805480e003460b10304034115910301d05c100c00002c180510460000c60030b0400d440c820030a40788207059034540c1664078515030512208100303881014030000c69181c0c440140c034034841c040e164180d02c0540400b0f1b0408403180104001c0c13880052105c291000c007402a41120603031417034143c14001c0680c50000d002801c8000c6e0700b090740c4050700f00c0051b6910410084a042c0d2412013104210ba8004442e46e00e0962401c0110183c0191810b0180c040340184810960007490790164820b89001c8080030401901d404040e001ca9000072911000b414560b601c4520140c00d2181042140461705080020b00381c100400007078118500c1c040948000100e8020000a0305256403c43c6460320210014000382075011101016500360701565050144084046000c100580c2c0000c4041917000f0211000b00e511b0b814002c140f1000d400e60324642c0d0707051000000c0c0b641030404009008050501240290483c2a2801e03550414036502c10f00c09480208000b04803501da5519031404d41c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 983929199 1250 983927949 983927953
    0x503011716060e01120b13091a070512060a031205090d14030d2403150213060f031b020706031e0c0504051003111605032107030e0a02240409060602 65
    0x140f1180010500e00982c00085410351601c050f4072119a80c0a404224521140c240071a080040e86010fa40015000414202e88216042880303d4581c1080160140644481440c01c560791280108132119000380f1024040e01700101410400070300c2a0014003418402400500a0a21036541e0606544914055140741d07040460302088600c0c1d03034000c0c01000d941c8640804d010600c00d4600a0040f0b4483c40010304451007000307403c0d210790450b010348146a0591200c02c03081c43d600c00020b0041e11520513004002403408041012425111038071500c111590350003064190b05101c01a00100101400c0c0744510815400c5d15081403494001c0720101802c0740d484540319840c05041c8a03a05024140d0328041c94241458200c1030381c3e0007070641ba0125265100500d00c800c0500380f060a5105810394605000c1c03541162207000185164464011403d07079804220303507817840e44e40c9500c603141d1080081d40b0400140490007100040b8100540c16508000d54038941b40d51480b00c60110380d0a5440308001da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 983930449 1250 983929199 983929217
    0x3061a0a02030c06150f090423190b01060e03060f040809211c3f0207060518070b0702040207050c03030307090e16020a0b0c1b0a0204050115050301171606 68
    0x7803c1001c01e00c0101b0074180c9801c4900c1c20aa0398480030360040001c04920b51100c03a40603004000e00b000900d448110540c03104103a445582000d80509000f40204000300d8125400c60026041c000f803400d01c00c103070081e945d00d1079403150b41c2d505001d03a10482c08140d0068004003100305008803c90301d1801d840310900148510312204d0301c4601d81450350f4501c1d00500c002440e00034400c07200d400b001005030113420212040c0c001c84600c0c580c10340c1003604410000910108115040250300e80c801030007419074880c0040200c0c2d0004010750307204500c2c0644202003406001d01c800505142c1c02404480f4070420a840c408007083e0082440e40c1c00c00c94400c000038466060421584160014483d080880c84004d820a41c844841c041e65594150318000d03d000b0318400040e0311845040180e484400a44004490700e50400a86075031700c620400e800e13032149240100000304c03c0e0f40f038603a42000c1034154403003500796031800d921100c8405003114540f500f4020031103c407403858081103c801c0945101e444460350 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 983931699 1250 983930449 983930491
    0xe040510090c0818070806150402121602070e0c16080909091507081e37060f0e010509090106051c061a030318010c0804090b01020d03061a0a02030c06 66
    0x84101d818044d40604d1300028000e128038000030400030b9000c030030488414080b205070710208000b442591082465110319506024800d407024200c0c8207184016400c49030381681312031100c46600300540b00c01403198410031010001c4411492822842400f40e00c0090411082201103042040f049490a07130580103078001d0407080407100506038002c145450700200c145443c2654003608105048001e0000091b5000265030404610b42d00103000131109495034502103060000920200142c01102817070b007054408034001c140362074404100c4808941030802c5910301414018a00c5005d821801d480d5211400400c1d20b85a2603c440c0360400100701c11003035089182050b504031132050760780511208091003252543c1e680002911280e40c2016403030f4400313110180040e5804040300340b00900981000ca8001110503642e03111401f004400c3e020b890012070785003011403c4822038001d002078030011030101031020b80030001030000003031107004907490143c0e4841d695150110031280c101081c40030200100d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 983932949 1250 983931699 983931721
    0x24020615152209020c07060c050c0406060905030f030c0a020d050f070303050702040b030d0c0803181005011a070c091a1207060e030d2003070c090203060312040302010e040510090c08 80
    0x10041143c05802c500b41085003080d1502c942e0f0310f114810800c0407403032091017842001c1c400040c54110040040101a69400c00540036040600c00c143c802c1c000d401c00a0030601010040b14034451845003d41200b40050b4200501c56003905015165407089207180000000b003002108061030123521150f40b40d000d144100015906480702c0e80d0f009420150f0f04141d00390304215001c05890f40000c03065180d69a0445a10100c0300d001c110740d2603403240d41c20090818541e60b00c0b00d8180c404051129840c8000e45015488500c100c0000a1441c030640341c04100c080d2241e805031050524149503107105480c04c0d400288480d840c0c0140984582052200b00215034110800c11070241040d0003030028444645400781208640201070034201417401020b0f00741e048207008a41b01e0990100000c0809034079044004000c0d0030864000d03000c0d03ca8001c81c81c03440001403086c1d5003280d505940301e1540300118000c0c4030103032001030000c800e620714816000c02c1c405094014400d180c091a9070f080c5580c504207030020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 983934199 1250 983932949 983933017
    0x31b0c0611180405090f07060507050c0d03081306020f0301150f0315050d05010e010c0f2307030e0d05030a121a0612090a08132402061515 61
    0x2180700201040601c0c80c0d86086114118540002c50340060303540d0303400740380b28107110301c050541210b4010b08002280d095041009000f072140620b00321104101d180341032026089070580d02070081007440002a0f048002c0070f0175044080e03c610009414804003015500c43c940003038124014020340700d0220802c00d0340c00841d000510070340c1d14052000c809041e0144064418034001c02e4085c0c00b48104001c02c0c080250480041034500754001c006480640700000c012440a080d01c0c0002040001030040000c08040c0b00c00819150100c42407500c84959800d460354050400c50a4014078070061003008a0420700c050403079101113403501000000043e043c08103c0302d003072180c3c00000340c44c2c48600c5015119039080c1e400c0d065103815444540d4132164400c51500303c079080010b00d020700c00104003484403503601800084076188c0c0c1203004205003008500e56103540c40c54402c4016072154002520106240d0000f05c5002e0f005000c1c03108840a41d081005640c0c00100351100c86103081e03006102b03a4200401d82 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 983935449 1250 983934199 983934221
    0x203100614010c17030f01170a03023708130503060412030b06040b0c280515060109092301061106010e0a0b0d110405060303090d080a031b0c06 63
    0xc004250502008490400444440c5810060302c843c4103070410040c0b1280300c1003c030300500f21940768038040c1031303500d03406409015400880104081000030b84900140c131890150340368000c2c140038072030344980c41d00c10100700e5007201500000040710450301c1c2c551580e40782e0b990701501615664130400080784c0081003c59000902913400401040082200c0c582c41c4203011104c4c1c900410603903440e1000030701724040c941201c10044000241080c4240c4001113404280a0b03404207400711031a51030516120750b40200000d0001e0300201465507a1402c08140668000814180b2150040e02d45210008a070203421200d030110081c1400c90030103003082030600d401080f03079182140101d5011442951503030010302ca0600042c0c10074020914880113034121501d00030020b48500a840038174241022281010000742d402a490080803402174100801156907080014003a4102c03140160369a44141e40405060320402d559400c03c131990300240a03200c2181c0e945a038866206800360b0804c00104e038054110303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 983936699 1250 983935449 983935451
    0x20d061a09060a12060c09080d030e0c04090b130201110d08090f03042303010605120102070b0c09030d080a2a090906140108100506040902070b090102030915090f06040f020310 77
    0x4c010110802d00902225940171a02007080580320300195001c2c0d0741d541040c125801540340403e003150b496444070303560103980000c40d02034100303400520040b84d61403c03000c1c107071030100780c006030b1448480148007540d10320614240344407100c10f4800c0c1e4101440d0b01da03d403000501100c103000503202e007002210314903041326010f54a46498401d1080c444040b01807100c604c03540d010008503103541c00307600450007803602501c0900c0d20105415124000d41c080c4604680521030400411031061a080c00e5660181028006110315100c590064030500700040c1852529511402034204103600c08500c80545491302c0740301da0701180000005030821a0540241c09458038101040010000012240c0340c11002800c0144850306c80700c0034030002d451150425a04000000f5002649420719402000800d0184034071540c1078480058045c00c0c1d1100356122045036201000030051850464039190300300380c980003219032000c1c3d86009141805412034007965403030000c08506041d800c0c14400c116000000482c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 983937949 1250 983936699 983936719
    0xe030633090610030905030307050c01140910021c150501140304020306070e13090804050a0503070b030412120c120b0303030f04030e06120f060f0105070b04030c020d061a0906 77
    0x4206400402032040d8810f50407000081c0c41240680c0c84110065088020f0300e50341d11703210780040c00c41e900800d000185503180c181100b140c600c2c2110158020030301da1001e080307060070b40d21819001c0c1d0001c003016100d80d600ba5400d100030014a100ea031640c1003202c801012407900c1c0c40005000344400c01050484684c08104020050f44c000c41d946a00058508111410000d04d0001c203503084242200812428500b01d1410b0a01072240050002c841c01201c0d402040368a90301070640301c85540c4590907040c2018804503001412a01d202c501c2c100701c9141020400120b05207203400e845940007032401143e05105002000704c514001c603542942e042e07004529509011030700b0107009100600c007030200200d4503c203ea03503641e0342007107840d0f403041d00740f00343d0b02c506100c1200d00b0700c1c08090341c0191040142c1c6103044030950140081e81d0741aa00880e1989450307a03a86c4043d01c25a4100e4002c9903c03260042104000803906d220b14003545200c0483d4031312071020b150510560940c042e180e180700d02070005c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 983939199 1250 983937949 983938051
    0x120070309090c051605010917040f09240b040e150d0321091103060106090308190e090915010905091015091e05160c120e0306 56
    0x600c0c200459600b0000014a041c2000d000c4038640035104280e581d03502c002110009000054025064640c001c101e8a03110b03918510a155091150b13220702240c0310b010f0901003180c070340281e2246a120f9036202c5516801180700041c5000c403d03040d0411400c034440450303388844a04000059030000340100c5c0c0d0340e03000c1a10000240031841c019802010030140c1c2c0d02c44200b03c00d1006259142c95148001440068154a0302011100d00c040f1010f0091066000000701e561180b00700704102c0e90448140d600c0c1c08042c200150540200300c1c01c2106015040411081c039464518441d0f1141510304040c0c446186107000983d50600188c0c022440c02d4180021b0020100c030100700180307020700200c0009115041130075198540300d075a03880b18112924103030000300312144c96103c2d83c498040c28007040041d41e90b2022038110900740c01034000c001800c40003140000400c0c40170001c006004a041c0790f2012601c2c60002841c3c403000301e51602000040c03940701c804041d02002c0c84010000c034100c0c942d40200d501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 983940449 1250 983939199 983939207
    0x5011d041b080a1808160f1b060215070801120c031a150f0109090b01031e0c0f0207060e0108181c02190b040602030402450402010c150f0204030501200703 68
    0x100c0580c0540d41b90780aa0004c2004107194000c0c043e501505000f21290165800d94000300e42d0b01c03070768015000f04040c520b001003c80540511404140c3c0b1040a036908050001c003421034464022280c03030210300e002001054903030141c51505101820743c440d40740740c81c0d20304c016a002040c81240c01143e11041c0c0c1c00c95a81c0203580d100640700c4c000310009040c1012001200a003980e012503210362804000001505600ca400034039044103c1e40701c1d06280d00c0414812a076840007031040346c00003004000030014940c42050305640008040c0e42030040c14856405060030644106404a0000b20103904041541d1701880b020640180e51b00340c42c400619a0b4a46e2481c01000400003414250300200003000c554540014031003501801e0b01400301c0000b050700c46440521003031020001010f041070809d240340c6410450702d12640c0d041e03480007076409084d03451485061b411110900c9082d12451084050300c600d2020700000d60151001003040d03c0740e0080202602100550704e80b9044040068101103500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 983941699 1250 983940449 983940457
    0x30b0406021b0f07290d0506010305010e0c040b1b190c0b0a020c060c120c030406030501120f06090203030c1912050a050a180f06081503010605011d041b080a1808 71
    0x40c102c00c45416411504848a02c5100804050b005e4076005c100007900c14082c3d48068407642c821380342000580d8895043c00d0594004a42c00c4885c1c680400042c05102d42440150141441c00c003240c0008021440210382030540500c0100350035041e242070141403103100600c0b84011b1902031149440c0001070100203441d110f045c043d01e40590000144040d441d10200803103010301004402041e100c1000205482e2aa417003032240c1070001c0e06100011032032081080050807540d501901c414460a425950000909051141070740c0c1400b040c414800080ba00f071010302c103400c0c02109240c07541512458100d04034402c40100ca0704121042c803000c0e4030303540c002d030448210005509080072601001d404041002142e500190104458400c00054194201211a0044541143e11071901c000300040c1401c8071214400c0d18002085510440c1d4182c0f10600c140c41595009400440c021921143d4160130446100303074180000c0195003000100815480b603a4081c140004001c494100390303403590940781c02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 983942949 1250 983941699 983941709
    0x1b0609030c053a0b18060a0b06180613180b150d0c0e1005040e090601060207050d0609081803210901050906070b0114030d0207080705010f20240402090a020a09030b0406021b0f07 78
    0x100d074101c68403152f4841058940402e290080c81c41c07a1511006a00184610449030a00d00313030400c240c0003440d1030500304640548568402d110304202034400e008010b4402c0c1070b50741051010030643c0030031648410503c00302c0b0326055200c56030341358034010728540110b000078007200a682043c070040c800180c2c00304a0a044070022541c00c0210880b9003081001803480c040300404540000079189401030400e4803e8004200c224251141e01080c1040d9101800141c01c0c1c140202004004c9814a907020301c005e404104000b41c40982002ea90340e0722074105040a33048407013060800003942e540c600d420803c1180c04c3c030041c03014024540c034202c00d0343c1e038a208030700410f0b0503c130001e902d158040e407194145051404000036000303042c18042c00e10a445104013400b10741c202182caa00722081141d1004801e008030360140c00415260380f4504038400941095400b4010000181030000c013141451036100d0080c0e000c2e1000595581131011408109800141c05690941007172062a290380b00110707005080f11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 983944199 1250 983942949 983942977
    0xc060a0905030c0604120e01020a0b0126010e01020714070b030118020c06250e06040b0904020712030212100b070f1b0609030c053a0b18060a0b06 64
    0x100318540a8158020303074514414034810141000280301240e04400361860b01d0b5210740d50800c0305240126240c400f018806800b164212004004424602c2545160701c8086129640c4003a85480824251b951401d1614200c8c0c1d000300301102400b6400041c99480c0356043c3c001e0488514007110240640014030549101000e10303038912100c4042e54048072040510380b82550040d243c0181c00b00c0c21054002e0404034015000304001141300d010f802c44a0b04400010603441c24185040440f031a80d502c840356080c0c10075024886d0381f0024480c04601c103082646520050388a480f4036600d125003090090403a140c2c1c0d80198410000300c182e860403101d000360045405042138015003006200814015100c22080c840780b4000126240d02c22084c40659210f680d8441125546004000d60700a40c41072414a100101d548501c0d62076140c22900d03011b40c001143d2030303c000c07040d80b20040f5940d01283c0c1881016401020702819100130f001040d4400d50b050000c02c10050000d01180940c001c98485200031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 983945449 1250 983944199 983944211
    0x3100612060504020112020a0203121006020c091306021215040903090315060e0106030905150603060c0c0c03060705040503160308031612050405010b100e10030c0302070215041a0c060a 81
    0x1da4841c03100c4001000b84440306569548c80300d0310003544e075400700e1600b03025101032074080340c0442803140403003049861541c0103040400d103c4041051080d405011901c07010b070074100d00d20024091340041c00f0300b03c1a088003074515141040240d04410a03140c2c49a20032403078440201d000a03085864a001e42e50094100e0208043d001e9400d0300810181d00900d8000840c0c41c00090119815046501c20a02ca0401d950006018012a88242d481515250742c9030700b00c1c1c00020360300c0342c41d00050f10f07442c4401412980c01d074900b000420700340b40c2e040d101c81000400000d001d00c282d0400f003059044030031608048210441c60b64072051414080030703200324000055042a0b11110384106042c80c8960860f6504000343e0410b0300d04203000f01070403100540102c006d1802130003014060700c126002130101802042030003084402c05c600034912039802e401815820300501300940c948960100313401403640d040179600c90810361624100c5c01d4400d08054201003c2140c900305170790124010382c00014400c40030a01d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 983946699 1250 983945449 983945453
    0xe0f090d030507030f1e0e060c0a0f12090b0a0c0f0e120a02040f060e090d12050417221203050906030702071e0315180f020109090903030b03100612060504 68
    0x80d00c040e07941901140d0078124101c56001c6201c0c0c4007620500c06c1a0100600c10500151903103492044a01140c0b10106200c012801030245882e0344203400d9528220f041d0b0311b800c2126504840344850141c41441c206000c100200119124208101d042030501c40b1503202100c600400d507103c00c4500300d000d44c41960509081072000c01c01c813030080f03034006d00a1102c8103200d0080401400103101c1c6510b407200c1c3c40d0224008000215080031004400d0f500c40c68180003100a01024100240007110000010103003011101c40c5500609440c1e10203081200013003400355030307190034400150080240985201440c4000a400400300c561880d4185c9505840350340f4244140d041030041d6011600300d4034440d441000c19010350f10440162481b542c0e00222540c4400e8000044800e405400300e482079110140324081495488806166441454440d11843d110f2a07000b00b44c0d400c070310040b004692110f40403500d615060003070110306030001e0307010860700e4502407080701c6414044c1c0015004582c0e50001ca41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 983947949 1250 983946699 983946701
    0xf0b0301050118081b1f0c120305160e03030d0e0c03060601030b030706121508030705060f060a12170c0d03060503030c0616020f070b2116140d060f0e0f090d03050703 73
    0x814400c01071b40701144040101009401210754450841e190003c0c000014001c40c02842101d000c0d40300c0807046404030040030415281c01c0c1e000d402155040c80144480e006031072240c055407c903101107030060501d085441c0281480c02c20040c004a05050500100c010035032000181c0364100e440c1403800040d00c515901c0f0700c0e1b004010b501040001411448000700c0c1400c0c0000052030701e14441c208030303049543c802c030442103d21802d443c20f40c0c1c44505800c00b0400c00c03503003460100034980103004c16a9584032007240c240e115408006020002e40142c0e0310b85074401d416100701c4004040940c061440e03d801d18108507100d0030014400d004020011901d550070310300c00c014446651028104942800e601d813a03031414070740c02100e20480040d00d6a600030208141e4088281d000e20503030615541121650101640d41030030342500705028103000e0055462444060003014000c140c2d41011640c103d08214211540b5800103005954004040050003c5c5200011320207103908e141d03180014103600c03642e10880c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 983949199 1250 983947949 983947969
    0x16030b0307030302030c060705090d02040b1c0308100f0803030705072402032e03240204030f02010e01020d02070510050d020703020d081006050f030606040f0b0301050118081b 77
    0x6500340c803444038080101600000182401340c2500216542e994079090202c882e48198805690011551401000181010303004034990403002440c0645c89540c0158020500e207035044143d000840110174130140403810315056010302503d54142480e02c3c142038116a41b4031000d0545401c1210000d6000c0a0114000312840c40015401004204440300d0031000040c0d0010b41b80240b114a51905500c50002450b0b01031400f13107490009440101d145448003a10900b0800e2803001c0216200300901c248443ea2004001451003400e803440c48005900004006181300c0a41c54199480070300d141040c50b4000503560222501100c01d031401004c1c02d407085a1030b005203d404203059001007003c104058011239194160349056883c1a06691501080314405c030b240d105150209904001000e0565048001982c1c403007006004c1620b00ba540d014020700b0401968070200c2c07031a6010006214030341e4030068074000c01d4001380c00700303031654282621551a4000e00c20110034000543d480c0028980b6010020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 983950449 1250 983949199 983949221
    0x10061112090f18010603020903011a01210f060314060604150b03040305040b160501110f07110f0a030f03021002040b0301170a1209030b3d030c0f1e0501081603 70
    0x8080c0f550307481c14050081d4214501c2d03e44a542849025800410340c20100404e603a0305950304140c1c4580d4510f04140d40f0a0131898258294440714199441c448500a10009500c1446000100d0003e1000f483c18124081d150901c624244801d0488076016104620151401c150035035074bd036211891700f6031780791140b42c0c00005c1403600070031000740c1da400c52002203d28901402c000d03c2290103e01110000303201d40c41411140900034080140403071010401e004034004064189100340c40c180002440300c110540c0100c070144408090041099410304c18501d07501c41b6a0800d605050500007990050300050049580c0b1452640e1480401c0d2010800080001d801c55a0b1341d100c444111402465910b00d8081601c5100103440030078501064020012009010940c03c0c05402490301e400255200e11283c000c004607080990101c04205017078000001000043c084090892415464806408a151620354194004002004a660060803059100c40048804800000300d124160010203010720f03d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 983951699 1250 983950449 983950489
    0x2150408161e0302030303190b09090304081513020103110d0504200319030809031207020102040509010603020c06072609070311120a03050a0c0b10061112090f 70
    0x10020460107101e1200303003507402c1d1454807110000050800920003078244002900750f401040090701407a030480040304021804040070031500c40c4000007501c101025035800342290070000e02000000401c100107aa4542818045051458000c400408140a400c0c021341416191801140801c25400031540304c809698800c02c40d50600e0b0610180c403603e080d0710032404244401c051400b03464000740000c802d44000743d51112044456408981c0500080c1074141c0e10310092200c0d07100044400d02d510710603503495000503100c0d0700d4034082180044041e0700a00c141803041040e0802020040340c0c055100c541801c0030480300900002100b0003140c1e550710034451152030303010301c0090380c00499a181164059900c000c4001080301c10850080c40b204034501c40c43d4818804440040c0c000e0f00945800d01c140d003849582e031031040c2c41e01c40000302c1c2140c452000440000091003040c0e0001101c0304c0d0040d100340103140b0301200c10768003451403103201c010720705c103c00038124400b10b59500c58a8880344441095 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 983952949 1250 983951699 983951713
    0x3020c092206061e05090c0f0f0a2d270f0801021309020313150b060309010b01020706182d030b0403140f0d0c020f061e0a06060c02150408 61
    0x801c01c00078800f900841d16242001d942407820f0a210074540310507034074001c14081c00c42e1602140d03440e241d440410042034815043c01103281d4800694040e00c0c00301ca0304c0d110011090354455217652404a6448198020340800142000c8690700c407120f5165004400790030300900c00341c007260748031407071b21070b48240304031202c554010644002c10340141002015080c1494003081d22840250203031b0108071039901c2400c2c02003507a01e004c0f50039070181c00440001f01500107201d0b1404404680c440e0f008031680c0d4802e82d151501c811855038108280b800900d003502c1d100c001032645104400720080c4600c1010310304455419008000340e00c0f60746e0183c005c2603a074110105581d0303918200013803540883e001c1c2e0100b40e00b01240d06074200c2280864200c0c09404800785c4c0303400a8055080f000740309000c80d1104500c1901001a180d2008001076070084003115424686510080c160b04822140100b501000600f045000c204207900484104210303035044a10b484000b2800c40c500b00c1c075010781d0b070200310588500b403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 983954199 1250 983952949 983952953
    0x6080d0c03030b030109120f03110706230603060112050309060316020f0102120a0c0c050d2f0c360406140609180703020a03120201051303020c0922 65
    0x320054268032944080c007003d540c0d841014225040c62001400e8070346000400318a6602c10003c2d008507000da0300700083d0040217030f20401c0554020603c1210b440d55210354207032240100ca981c0118804a4a11a402c0e603d0040301190303c0701010711621003000d29a03200754040000074030545240a001808541c2c5a251800110400e20b8842c0d140c0f8007d4014640340c07109001040c0200c400414949a43c4070090720b56900e680002c5c80510f1101081090210079200010000d000c401499011542e402c40404508211041d90080309480070404014a0f00002c5000d40003080d4509081c008454403189000340000c5c01c000380318241e0304d070f10004c10703150301800f460262030066600460140708204900c0981c16a15000088143e030302c1e0380c1c82204da000103031100c0d0700c124003080411240c8040d54100e0340e496002c02c40c119010b0b00101d0f0284012603043c8140d91342486007551007250000f015a0180305610065107903034181c607642e0b019240607800900d41d00c0011a1580411000b00e80103000c1c500c0714 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 983955449 1250 983954199 983954207
    0x20c011409131d2413050a03142107090f0509061014030906090c0a0b09040b1302270405041a040816080703030f15060509120d1d040207111306080d 65
    0x12100f01080b10104045803061861381502031701c1075442001404085102d0b01e0950340030365002030480107000c0400502c06240000c00b50080010074103101074202d0b0428000181500c81540c005290482c03181e80c0402040e59403118281d00081c040d0b500f003000c24281c2c2c10031a03047d80d0a281292819000009104c9100c00008215214052a2094072484481001081001201c5100b044045501404840c0051400b5401400a0040145108082c00301c01d0701007000d07600270000160f080c0386030440c40d010702c501c030781d91240c41d05604840400c6146003d07600e00c1d0b9022003801d50754003180030100010741004510011500c01958410b40c0003000e0b2500d1800030003035802250100d00103130603c407894008003428080d06002290424610403514144202101e0755004000e08680c000e140c4d44010700410001d02240b2001e0f8001c0d5a805c8100d684601c407030704500c0e240012140154030402412001c1043d000c8423102401c2d0031110071422017400704c00100944450b81000900f40242800c0030380312500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 983956699 1250 983955449 983955493
    0x40807060603050f0105011401081f080d050c06180a0807060b03100e15040c0b0913020c010606110c06040b03060d0506010806091005130b07090b0703020c011409131d 73
    0x14200240b000341c1e254680d8402c2c0012821415020036003a4000c102f4007520740c0100d4090620003071040309040ea49903c80c40c03500b90100411700210702c00040300c2d058001c0502507150711203004400e142540030360300032042d65601c68050141800c94045070700800c120706608402000f100040403642001c04e40d074031580c01021a51020b4000303103d00001e4810519039002454031a80c2c008020f004044d11341f640c0c6900c146e000920299100b1000b0507101c507254414805450700c410044e000046a0f400d00707001a184804131016400300d54400031401120b65901400c8070700780d88003d0942c503101c0e2503450216500c00d540c1fa400414502840c0000300d01b0110004401d03224200c08011200e805d028000e5100858005a500950b01d86414010402042d03a245c14903812010518000451a07501c0802e1095a0071400b000c50040c1c0000440300c03250341c0e01001ca00c3c00c440d0301d40c40c418644002400010400a05165101030b1552a65034080b144130102803841c3c50402d4a006650010b03541e49003810314240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 983957949 1250 983956699 983956723
    0x510120309060305061804060b010212040f03030f09080705040c0e030319031b090e0601050c0604031205010b180f010203040506120618040308220f061b051606020304080706060305 79
    0x125104c0020fa2900e0540006010702007401c040d84116129034603824044d00700800c2860552080b9840600a48c0c000c2000340010000c01507800059404c41c074000304004180102c0c1010052201024080d03101c010900c402100e00841c0c0c0007a003911406410b9400055803210103500d4007000c14006103220703030200480040d442c9075038200449255000f12810b002da80308642c000049120b0020311480b224044416003004050500c0e0781800e0f502610769180950440d0100e00094004009141c0c010b01c50080c6405050300c2c0d100d1a05010311160441402d4400c10781180c032504100106801c0c590081c01101c02400b009055140e81c1d4886181200103510140d480d0b60007002d00f1512051507000410006020703581c180d50352002900c444075071941010f003240c0c800b0700d0407c2041400c03001a0b80003c40c000181d10600300454184203e510300c0c500c855141051909200041003000e1100700b103200a6030046510600060303c0e511241085580e43c0100000100300c94540100070007400070000b40d400c0101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 983959199 1250 983957949 983957951
    0x212030307030606031e050a060b04080307140109020f010e010c0b0a0b12010606140c0709060603090605060a06081311090a060e0c070804180b09101a040b0a0305101203090603 77
    0x1e5a913130011022602c2e1850070040c03d9440780309060100300c490b00480c0c1c100700b0010020580c982c4440e0689001d6001ea809140c4542c00007c020040105580c1e051000481d0000200548050b50300807a02c4040a111000d040041c42c0309880b605a0007866032025690300025800103916181618074020a203440c07807a4490000c5d17445040741c44505000301010f507621590703503045e041121517208120380c005103a0a9098029801d011420600501c04c00c1c00420203690081548002c900308001160f01c042c05250007028500c2043c0f058a4011803207039009200040314039400191424419900302d0400c0c000c0b94042c0c0c10005200c04641d1396000081517903a0158800c0d840d468070400c0030740d5032090460041070030030188000c202d522400c82460054602000c0c0104290000c0000115000342c100c41040c4000060740f01400302c05460440a01481c0502505502d424100751901f0014020688150200f584074130001e20b05451624001c0020302059500d01c034010f0f09494054000b84403030080c00000303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 983960449 1250 983959199 983959211
    0x3051b0d0f020c15040902090612070903030801080c1014161b06021b010e0d06052802043503070606180c05090f0301110f1c091518021203030703 64
    0x540750909041300c3d003000e001642403a2a240c840e264010b074000000ca5588404240802d03c2c1f07520010b100640704075001c2d5150301420b0b046103006001004180c104054a0780112520503064a60b11224140c0d6405410440030b440640c0032507404a100f00f80c00340000d0b1b1026040d0500308007801d8150b10081c140395017903030515522074508a80c0c403400d60202450b1850908100c0c0f0a55000c3d81140c1c2078000c000d4119001603070305407181d03001d031007041d1807060581d40180c1c2c007121141e85501c4501d00103191000c05600d0945003000c0090f1281c0c1c01e0320102000724080c011800da49042c0800e40c02140040d00a69031148500c1c24450014512441390484ca1614100030b04202d0304035100e503e404440c00d844039400c202d400c0d17040c40754000b102901181c1640d43d0700c243c00e81040508001d40101800c218940c0d9032078441101204100040d5507628203428244000840083c00816071009036403044500041c8800d850744440203211403c0c040a5040300c1d200c50b0999400c280400214410722940d1410701803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 983961699 1250 983960449 983960473
    0x218100302160b04030c0b0f060a09050c0703051c050f0403090501090501051c0626120a0c02090405031e0304031e1e021608012408070303051b0d0f02 66
    0x1c0e0302c41d0000042014240e80d10440004501d0a4200c2c3c0203802407a0070805075030f455860485002040e1204040d0880c03003820000c480c5004a0036102a1205000c1407241d0309012118403041d000790340006050101c0440d8000c0245031001c802d80305412554802d1081c0d081c28840e03d0003440068600341c0016041c0100801d01c0d500440504040f61810b945c1d103460b203100000f018415603184295400c080d925a88001034900711885003031480c01c400718005500380c5901712524540324485c40e81b0400900180010a02290408000102590180c0e000d003030750341d01c1d440d0550031031050b0824100403800d8031440e50b80006660000c0c51080d8466200d440b1ba00d84a058074510600e00a600500090203114500310507040c1c5003080b00500c00c050049910342b1000320000c3c51500144c5d000041680c1d5285815030b0400944003001d048081d03d4000d1000081c28103045688401a43c007010702403001c00181507600d11008050040610354220584001401544000340b060f903658206000601c602200c13080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 983962949 1250 983961699 983961701
    0x5120d0914070f030803181e07091109010c08070803070503341803020a0b030a0c0903080f0f0405060d0618020c030301050d02030705030a05060109051008060609040c0902181003 78
    0xf5607001410816001d0f107155600412588010702100e00c401c44564107000014081120701c20402d001d03a1100c2c466400d0b84042c0d4075055856111003001414541840c0304039424500b03c0b03800c01030a01e01071103244010b05122070319108418004002050000400c410b03241d02070041c502031f50425550031942c0d080402c2000d131100c8040080104544600c8846022034010210f2440e001007020005400a03070303a80001c1d9940f18075611000100c1000010485c0380d84007403090642c00385150400c03103000c506644030644a0b0042800c1c903503c051000170414020301f1440182e0303004160040181d5520141184083e010300704501c00c1c0c1d0445d0744107540f0040c0c0e0500b280266841c0c001050000e5080d6032034001002400d12040e142070760180505000030401c1e4600348510242c00740118014100755141c08004000c40e880141003820185580748240000e08011546540246040310101f000e40c4441c01d001601204a03844040c2080c4001000740140c00340d00000341c0c09400440d03d82c0c0c0d5491000a041d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 983964199 1250 983962949 983962963
    0x170105011e03150915060311040b010201060305060a090c0504181401061d060a0b0a0503070e010801031718100210060909050c010f051c1b0201060f1205120d0914 71
    0x1407000040ca14103c480c250240d0168010b98003400304a20046210000001156980c2e041603035180d40c90901042e183c00d080c0202c001100007840200109407544d11810303182c0c0c502401d1a81c1864903440c00310180200800b00760098100140100104960303951a1100d80411b00403c5944400b104142c0040141c103200d200111507030100e0301d03450001d030701e1101009004001c0089910500c0400086400351880c0040c125010341a100c040d6a401e00c041c02401c41c0c003050354040d041200600c010702c009089506000c84000100078155203c0300e400140b030311a000d1020884d40c2200d140000c00d8601036000074200f1407101e0607601084015290301584c401d42d40f503410003404503841103da003c1d4039485222203040660751850036034103065103034014804c211809440b087e0142d40b1045004001e231200468105903ca803800200203091401c0c1d00131019514901c40d201c0740362901b105000620005000403003403d02080130780ca0b515006895407200812210b401030b10740040d15401d205011100181d41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 983965449 1250 983964199 983964203
    0x5040e070801050307050d03030213060c26070b090118050105070f030b0a05090c1606061a0c1e030c0a120e06070b0604110f030f06030c03010903080103020d020a170105011e03 77
    0x580240d03411b00090001500d250801141019400c01c80c3e058800c1a0a0301000070f043c06965220241105040c000c8110340b00301110641118002411000101000c0c01ca0300503036846604080c443e40d404c003140740140309203e010f207049500f1881007000c1080640c08584907240a8660316203652110000320304481d00c2c42d403c5a04400340c900709009a03e82440c446500200110005191006c404c880c022004681001160050340361003050011002c4086c0d078101c000341082d0350b9810b00c0311703000007d0354802c0c3ca440c1203042e50200c601c1d080c803200320610448149403260401ca40c40a4150329111242c840503065070800503409032140481031400c40221002e16412081302c01241c1c4900d01084000c00b03030402ea500517544104030b264030f880380c024051440740201c1c912480003880c1c01010715082c02c1c600d0458900c80d0340340034410380c000f0360010300050559405030b6a00107111601c0c80400c1405407150003061011022182080c00454150401030503036250b0b82803100700800d04114030ac44408207001c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 983966699 1250 983965449 983965453
    0x5090d0906020303040b220501020903010507050f070f060612050f0d0801050a06270e060907142a16140306040c090f1e060f140603040210091505040e0708010503 71
    0x800c0114200351261a00070a422100d4000e04003030f07003958102e0403210001123541d03075004125404603103021312030700e40d2242041c03d06524041c05026040c8862043d000020210181c0c0700a400901940354480e034098401441da403188502c850500b5591412a03141c0010203100764080202c94074441c00009048031170150a41140c9401c0c00ca0070f442010181d0380e40111141015103c611165000c2c43c104010708004840e290203082c40428041e968a0003400703441840000c029007600915010115610741c1da10701188046218040c0c16144206481c0c4e803030550920503601021000c407040c21a8400321120442e003e00b95034680014540c491004070340190109140c40c104114011054000b6180c488101e0400110000c20920940044982c001c1e242445603442d030042c020f40403410400b1019001044410304410b409400003007040c0300007000280aa203000c0202c00103075006281c400043c1c5075802450384200c4d0020002010b40e04144183c06864030503001007031074a409144080d05888010700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 983967949 1250 983966699 983966701
    0x6061211060a21090f03030e010507030501030804090e0304090e0c010f0810030609020d020904140706090f1406071205120601031a01141e040306061d0402090c040b030a05090d0906020303 82
    0x3c020450b1022003011500030b5070f1a00908000a0740240b603417491070b442a1400503580222032000380c21100014190400c0c0b6103080d0050000c11026400d54040f119041030109106406070803650450003181d0241d580300c3e05110a80410860204c2c40c80c0103e882a03a411a070ba8003150001c4500d058152060780905800c2c0d001440850040d42080d0844c0e030018241320709041059012902c8240115410340d1444900c5151001445043c001032004185500c0c00e004c1a83c107181d14000d1450151041c0e0003600802181569140c440400740c0304080d0700309419101c040c00440018046034003200443d44001d1a00000410135802407150b4500210309a09810700140d408005403005001c0d0f003a80c0f10318035404d04c50f0254803541c2d00d11003221504816070f881d80300c601e1840d0040958449030801022071700010820b2402841e1101c1c4c040e030054044402c01c60341d07100c0541d9103000780b1a80d041009000000001c103c6014000e0700194000c00c40e4030300b1180740c0c01d9000c008940828250180300c0050f04204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 983969199 1250 983967949 983967977
    0x121003030903061107020d1203060503150c03060f0a140a05010302030c03130201110703030c05070b0a0f23070305090109080f2e0c080405070b04050a0909030c06061211060a 76
    0x180c04100482c0070001641d00c0d019030f6400040c0a9101c000089407071250031642304100f10f900d8043c140041404ae401030200380740d40030300102c4082005100360010304002c0000360981e910100222441100030300980642034032102028102410340168501521a290300000c03d940b191080300c0c800c500c034281803802c42c0c83e10800701040349000c030130980c1001003030a50021050003c0c84820002d51181d29010500c0d0a545801c0381000c070150701040e0903100c04d02c07003500803d80001900072844a54508401c102248000310040800d80c0310181da11380b10081600002c141d044402403e6456098883c103540d00d540d16115607852801c100e140420b07411040e1440c1c10b01881c039007241c41c0300150000410f040310025030082e0849200005140c0016110700074030050100a01c60070000d1301d500d034040381c6006d040501003114070445105101e80c46580d4490181414482c0030902d480710350080c024004550303114007125a09000d0b490954801200d2402b03001c2d00c1ca040d1040307404810942d2a0640440001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 983970449 1250 983969199 983969201
    0x6100f051e0f0c061503030406231b01180503090d0303020417240103021f020f1c020706020705030a0b060a090e010516080f010314070f080312100303090306 69
    0x310218000c0c0d41c030010310040030302451000d0450007146080b416100c044440c101440e001c4081c2182c017600070350904048090b1004001c0f201a0380701410000f8052210640c25003100b10456a800c101c6000802c4444007010b00d05081c201d00d0100c2c0c4d001b8412400c0c82420100f68003841da400801c0d80e441046281e107541003504000c24114080e044c01030401e640c0d01e405030b4081c240341110340d2240d007043c03a4680500700c500c6140000c11404082d03091840d81581e0206650320303d04580c160164070001c2954000500c00c0082d0b81742ca090950035101002030806040f00d508895030801d402501417004e0104425100245042c11114018014100c200300c2b900d6087c010a0b000e8a1560080220280414810031074011074616542032400000d403440c000b60703041030510402168104012850b0180804140300106803815030b500180c40141c07500f150180c01d80751401941c4880060100b5180000f40031030044060040c10007202140306103a9950b050105ca014070500004010a605031740601c042405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 983971699 1250 983970449 983970457
    0x50a0801180f020f031e010f090f0b1e010806150d0507110a050321010305060402011101020912030909101a0d06091103060a08010c020c09100308030403080f06100f05 73
    0x1c99000020500c1c1040d50110a83c1e0000b64403c00302000002403001540d10380305403030049101d90208100031b504003162071a420101e44120f010850f180c0d02c0301c0c01805c00f151b01280b03051780c00404420a80a000e000c01855050240802d4041621400040c405003080b05032007405515082440b85001c0036039034003a00409024081c1010002003c14141c02e0450400940e2a42c030f000d40300454540c5604100c101c40948601c021500f4003c0c40c0c001000095800580250842e60900785103100725241c0c8c0311940203008000c0899400f00c08002400c1d010300021008203000702045d0b810b848181d603a0349440c0c0c44070050f8440c80591a07003501c440c410416604001d40541c10706410007145540da50781c01c00e020b59202143c4103002410000500c11a0724203a00d90100500300d090003071207030044141021751100c240705001c5000d0b0010800050082c03180051140c042d560041031381c0d490f0304050900400c0101c044500c2600f1000c2103001c00c0c150b01d01240081c1c1d0b003078582d030381c1d00600c640c501500f2501a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 983972949 1250 983971699 983971739
    0x1a160e19030b0106110c041103012601020310031103160308070501020c010f0c020d030b06041a0c07060f0930061503060c14041d090f0604030e090601050a0801 70
    0x5500d46010002601c0d81c00d6540c002d141c00d6440071140310301c03000300c681030500b05003641340f0a070320305403042c040c160240090b42d0444101c1010192403000007a4004a14151803e0515455100000300709804541544540c2501e0240700b080088510315810705a40704440441c02e44c1303600300000100300041400c0020050988a1800542080100d001c0203007540c02100411842980f2501151140d6078100001c03030000d5441c0c0341c240000c22021000c101248124043c3c80c0d00b00d003e0044070610301e072884040711000202402291180d80d59070368000c20074052450030f8030004124120006025000700c003100f40005007103200c400d02e84010321b03003640c00e03c6200380100d51481c0c40c1e0b11a003a0100108402c00015030042c0c40100c2c0031802c20000400c0031807882c80d01000c160f004c0c0402c0c40071500c1d140c4807851084001c0c1c002412500d07981d0305603242100c0500d25400c0c51041034200410903030300420030022500d054400c01e0b0952511401582c0a00404080d4400201031301d004000c4401040c8001e160b00b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 983974199 1250 983972949 983972989
    0x306020307050f040303211a0603060402090a03060203010f0e01031e06180f020a152a0206030415180b0a150b0c0312010e01030510020903191a160e 65
    0x10076110607004039820070381c0160301103065459464015203880c7e51100c0c1602c1e04050400403c169110070f460102d0714000e10b24024240400051140c4c2c03156070480345010402881c90b80202d0f03980c0381c0074020754003d000c0d1207649108040d0020345042c08040d0503040c1e0b50722400000c2c1e40840010105524200100151b80007511005020481c0100150b14404e0380d018a0808842c0d6500340180218906160300140500084000400e070340d40d44031014441c045c1c2054242802d030340064141d1104843c08034006540031200009000811554401400201c40c40c3c0c0c0e0300340b16941c40011102c07040710361180080e05440c200c4c80081e04000c07061744561005a086203074030200340d88034160782c5002e8101c0e558a5400d5800011000d802040801c0d600d0f004055140d150012981180d40b015110300b070f1800061155500850706540590702884880c002d128250f200012903410b03418800b100b428114a04180d085100b00070030351614100d4101401c07400325848200c01c1d4020381040c00042306404021520310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 983975449 1250 983974199 983974207
    0x3030804020a05060412021008070c150912050703090806070503181c0c031b05030702100905150714010b01081302040609020c030c0607020a0302061501120f0203160806030304030602030705 83
    0xe981c1c1e190181000c1c25484620000b1040f5604c1844030181c8c1c0701c55084203000b00c12080158182e03211408001d03407903001c900350384103c44180664000c0c01c411200241120603c2160030800c075406405800a603010b0369130350340c1241ea00c100c400c2c3c4844080e554000010420000201c0c1860a20000f000f141170070801c5480000440ca804860441415055800204959524800d055000c0c0c0b40103480613103030013800141c00d0750307036143c1d036480c400c100b0003c2c0641c204440f804415406464017400900020304001016070203c40c01c01140d510820084503030742d2115840d042804814412207044840684808609403110010035003510031103a0201e0344589c650740c0206040900740080e02c0e03440e10780002152500e10041140d82071450050010045600600c159004aa8001101d603080000074030007810800d030410040b2a030780c50700d0b458034440c281401282c0c1a409846d0b802035105101c0a1404100c040d4503805c00c030346145051f41c20940c19401400244081003a80e80215007100c01800c00740c0c03034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 983976699 1250 983975449 983975459
    0x5041a01120b1803210106091a19050c1f0e01050f01092007060203040210020f06060f0103091407030606052e0216030f060b090c0a0804110307090203091c020703030804020a 76
    0x2900800200400700c104617100100301036a0040240d50181030580c64822607141d1401da0a2550f004014441145d030221040c0002c2d01c1e4055021624081604410748902064000c03201123070b04e002d001c0c0685607a140c10540300c88420180710b00c5024081070082c07943c0701d900c0c040613040030b008049100081c0c00d805000280b4604518401080e0a41c45100c0250722807500c1e00410503540780d510800020f6420441c08103500403000319215034400002c0380c8006074600c1990040300185603049005080040040e013a149088000403441d085a208032003d028003038682040c00940340c80405039514000404030181403c0c40c81d0072881a90344541c1c13044840d040041c0c0d40c80b91190417154425280441d4461005080c06100e000318443c00c18181c3d0098520f04016060100034403480b07009500700102c8201042c10840300010036810b050000701161155038841903108000d40c01074442c41500d20801c2904110090700e40c050702c0c80e0480a8029082051646d1401e0f900c920005100700c0c0d001c4152240421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 983977949 1250 983976699 983976727
    0xc010e03070f060801081e0601061103040b0705030c070906060e0918120a0215040b0c0c011b020f071a2a0a06020c0d0c0203210d05041a01120b1803 65
    0x43c40c0710340e03442d0150351404a44a080150012036400311101c444041c1c074a076440000c000f411102c0500e0030b1b0080c0c1100c0d08425045020350380240101d01230000d4071106101d4004017802c0c000442c001604c126598480c010b404942c0c55106100c00304a007171941046c1440e03e0001a0340c415640c5818414080e21000d41c3c9082004548140c1c04d00e000204003a00c40e5a810080b600030911600d51446881c1001d848603605030320010007100404d4000650f2803054602074102075417807030f015546a580c40e038001b140603448080384400d410075445181e00c006454405c0e6510850b491100859103071400c103213441c6803146031401c3c01c118105010b07403003101035041c0420044580168000c1c640181c50743c14480b00c181c00c09031000c0854040000184524025940101e092a600225680c411101c214003020400c0741e40610710b40500194980030420051100840c40c0c401001c1c54411071412580e208d414070701040102c000050004400400065001840c00701c02c4502d0410305000c99080c200c06810b104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 983979199 1250 983977949 983977979
    0xb030d030b241b0d0c06090503160305030105030c09010e0402060915030901140906040213050901060b21060913020915030f1c03090305070809040b130507020c010903050c010e0307 79
    0xc40101d80004500b807821042c6402e041c021030f058405000c040c602414003c044181084000d400c01c3d5031140c075101040310400440d58030712450404802c0245e12800c1c046c150350024441d80d4024044c0740c0014906160130317000141a509410943d10860310355800b8045250001181580c01c02c1400460750b2581000704c0281d88070f20302c0c00e0000f051204441400d4a070360400503103100450b9002c1c8050000513642c02020880c40b00f900d01000540717079114901d19025250036071110000e10400940102e6860a410708600122a038680d449001e8a400c4284039903860300325121000740244c1e20080c001440c00c446801c0d080312040f500a5842194070000900380000700b80700340400d6011040280c40c2034808480d0340700f0084036080c10880001152806013141c85081001130618034000740c02e6500340d4450341321522204000e48103900c08840c0c029000001c00c03054503144054410f03a80c010040390f1090b6070010030782c0d5012000d4110a80c002005649800078102ca450f49401502c0000c030741030002c22090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 983980449 1250 983979199 983979259
    0xf021c1a0d0b060102010b010e010c02220f14070c080f070c2705060f0604060305091e0d03050a05040c0306020702211b0402120112080c06040c05130b030d030b 70
    0x10710803410704000286c21241e030210b03003074180406690250460381c1c101d1085048140c05548203d800306900520108030110340c003108640394603081880c1404c2001e42c0c0309190102001c0d004c7d420780e8031582010f80e1500b028110003820349004006550018121030041c18440c0d11401300d00550300c3d2640045440d041640c030000140f40c019645440c0300481d180299600803c0030703982a803000c080c180200b00e81c0d2156000f010140342d02c440225042000030001c403034084280f18003007180d0481040c0c260352222504004d43d00001d00f000c012079014101481902d0081c2e03400510f2400642c5541da5210103034010502c142d901c401070154241c40111f078188190310000944c405004903806154100d500b548000c505980114414800b40201c45220038656040d207a00c0300700c4440d0580e9070b181800452242803003041e114040c0406010412911448031015541c4c00c41c2c0c0c4950601540c51800c0446008a14260b4598011055280000e020b80d02980880202030004402c044280700c0044a8018080c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 983981699 1250 983980449 983980463
    0x306010521240103112208060901060806010f121118040c1d0603031639080c09040201050d0902033003251709010f0f021c1a0d 56
    0x580d100a4071510101554002e0034201000302c0030003448504014007800d0102140401c00e0110f4420a41003149444020006402103d1403890502e00701c0c0d0103452103104140003803240e280007064802000e00740074195141d0400940074500c440c0ca480500d2000c607006c60b900303c1c1210780349000c0c00d401c080d125407081c1c3c0510030360790946181400c0d11031040700c0802401400d024a10512100e5034001c42150a034003110642031800b02c083d4105064400b09048240503401d84551034440e400920030541580c041c01c59500a00050fa1181495201c1000c036410990169030b4000103801903008601400319180340c08800581401c50703a02080c9401d0460440c40400c448034a00d0301c03d80e40d030160920142c403d036030002c84c0c19418003004525142d6540d001701102c03006021000034003184107a00c42c0e041d8070469080c4009908004407a1070081c10a5a0310a000c40d041c401070600761402c03402107440341e44004220309a21800704403918014a0030b06000401e000462a0141040c1d40b40b9100d10304550155403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 983982949 1250 983981699 983981731
    0x61502070510051c1505060a03050f062e02010f1d07120506010e04030323061201060f050f0a03051614030601031104020705210406230306010521 64
    0x208014040c00c6441e242d41c1004030030841003601c050382c2c214409500c0034219002c1103d034400c019203001d288440d040140c00010224403124402e6154001e2802001d8400000c405512aa801e0124158841c620351170700d01c02e0014448040c56900225100c00b4540d0302c00041c001d5400b89a40058603603004e42503440700b0b2071891194003000705008610003003060200e00c4001c0788284d6106522184140702d841c11340030502d00040c05150007500a1401c2010410500f07803120780700c1050302072100d420303200980070380007902011102d04814032a20060b00d14101140413124600010805020000c00109402442a400c00000644c1c100701c6100303402e00a0400c00301807805e00c204a0480780f03032040c1107480303580080300400120300842c40c1d034042d4040680780507030303502100c1c00c06502d0030100f101d5069441a82202c24617142d0b1110000e4001d40e0303042da583d403a03482c10390082280715051440d00014003520400105502e907000360028494903280008449a07100d0314901550034200807500c0880c1d980c0c441c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 983984199 1250 983982949 983982959
    0x20705011407020c1003140c03040b181b0a08060f18030a0e01050a0e181f150c051c0504090b0301020c070603050c090904061505010207081f06150207 66
    0x20040000364486041c58003080d203001c0314025580da1071311529a01880411952541c0284070307801c0074010847c44401500c0c1401d100d07502203650743c001c8030241d41e158038000101c8d8410b41801c0900c2d6801d6115002003940c082e4122040c619a40c5200b0010780c002407100300000d120205018003480351101410b43d91641c600400041000c640076101c60801d90020046504020303000800307651007441c00e01e00107488016580c410b554880340340c02038517071002010562515410300d2080142c411840341407011080d072002c1118040800c25030050512030b00781481d0780503007188034201550780507009604841000680e800407900b00068440c0382000100d00003001e025091840c080d41d01000b40640085103440c00462200b51501c486000380300404d91218007242035030207501c040c2c1c0c1850710020404a0141030901d482d50050a00c4050400707004c0c0315140000f100e60010071070340c044880c807501400c01404c50b44010350b401004107106000e041e9554070301145d1007240740c0c40b1485405881d002891414144 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 983985449 1250 983984199 983984201
    0xd08030406050c0708040605033102131401031202011506031a0901140f03010f020d05040b0c03060303041e03061a091503031804060506070b2a030c0d0b0901080102070501 75
    0xf41190200801000003100040e101d03412101191400d1800e00d403130341c07112241c882804010344001522158030640f04c800c00d8074206007114480d44200c0f070202215044001500a40f8036140071301001d031807031070700400101d01c444401d00320034446440005211720000d103441d40e075480290810800a6560406035008010303010000b00603160481d6070840940c0340c0102110b0710f61464490354060180e040c03030b0900d183c40035000103509101d01e190554403200c08402100041200b03c03000e440c0b60104070007082c0c003426200200e0740107034070240c0030b94500741c1054004c80c18850700800c1080350000301c1a000021641611400316403140e40c25100c0340100c81d14080020f0b13140d01820790400196102c0040891742c4d000800c80b2124005041c0d62844c0710b102100050091102e075100980010f00000cac0c070810840d6003112103200300b60601c07024600c0542501140d81c0c07884900c0001c3c2e040c007800c00201d045505200041d000c20854041d011804503d200f0100741003034800c0e8000041c036900803890100304042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 983986699 1250 983985449 983985451
    0xb0a1d121c033e1813090f12050c0a0309090507031b210e060610090e07050d0f060608070e1905040e10182d0816020d0803040605 57
    0x1440c0a10004041c000710f0305102c031a510000c156a500ca68200140b452280c104540c00b03038030398a250340c0b62011515860000701c01d000c0c0062050107800286a1075190910880a00a4101c07080b180d0586040c1d940d039642032071541d12101484020700c07000200b98010130007921824465510311030228a0711151a0907500050510400e26040500c0b030200740b080c0f10402070316080705280c20324000040040c61360915440990b0703100c4041c240f4180c50000e00001036024090001503e101025034030740c035821200345c10a0b000c1c4240301d0103504080b034801d034400c00150030340c210b03078010009480740029222000c65016134010408218480100000c16402050000d019002600ca80000d01041407201c9405203541c010603100390f5450980032a40b94040003042070103807801d50b0810022845a003100e11200c0480350403a01c01c4001c0041d00c142c0f044070200480048544a400c1307410080340c0d80c440c00740c0e400c9102141c0702084120200380250350b45100c00030f440c601900c10b480d030700d04003810428103680c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 983987949 1250 983986699 983986753
    0x307020406050607150c17011205070501180605031008010513232a1905040501140f040b04020c3319052503020c070e010b0a1d12 57
    0x142402048040f4514414400c4150005d001c0000d01381151070f4180c400c01700000b1043d00e1440280c001103842c4144200401c03035a8060012100407507510001100c500509940000400c10341c86020000e490080000d148c01c0304011040c081c0c001e8441c00c00c242111001c60301d942040c6034039007080d03062200000c1d240406041034942c00c0f500381f00c2e21000c00e07510810350307000300186048038448016525411f02c038115500402031592002041d01049214007945034002c59114501d0100006541c90080c0c03070b03181002d40c019001c00d42d04c9000c401004001c143c0e00040a81103074007007103500e13200c80c8244102a18504142c82d0f00f2944280d030020444800d10030903100e4501c882507400d1040220703448422f618000120840401d096980020005890704894016000040d01030020000550581c02070100c0495402c100d0758510390713515103a40b04100a10500803030200400882c404c092281c0420315510700b050350070000446c2010080f070f190b1050320100201c107030031615140e039800c4032250716800118 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 983989199 1250 983987949 983987959
    0x6010e0604080a02060315041b02011a010c110301060308040f030c090b09180a05030d091e03140d1407030204081902131a040c020c04200301030b18030c030702040605 73
    0x350418609039565155243d019216000110000d800903c000c6c1c100b61050300050424001c1e0b000004202c2000d403500e901200155090405001c62003590704628a104881650b84d04069042034441000c40711a44151540554941101102084083c1e000304014540030800541451a43c200044100b16607003080820342d0400540b03202c1940e540c1c0202e40c1003010840e550300080803411200c0c1c504403d00e40c0061441c0004510000e40356180c4d0320041c00b00b40603808105c01c0020b0020000410300d420f440040100d0401c2d01e0700e0381c013265003002401d845d1208075000a00c0c1719040010403080e60b0210f0306240060340009042c005403005210700d091409001c5036080f90410180c1c0080c0890340200142940240d44c0d000e404a180c0000740c40c03821614018000300325051000e0340080d00c2c0c0e0741c00580c3c680128140503c407940d1946440c5040c2450b00d00052450442c0d00b959904000d10b00d001d80a8180450030000441408509000800c244440300d001035985605a1050100341d58461b030203140702e8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 983990449 1250 983989199 983989207
    0xf0303040f060810030c0b04050406050303090315060a080604150c021605040209010309060c03090c0602030c250b0f0d0c0815090403031d010e120901170910110306010e06 75
    0x1508001001a0964840f810600a2507656104c0f884000c0c000e540064000c11140800003004100c480051065035015074082c454280c8940502d60740344102c0b040c06400d507210301c00a94103108050b4400fa00311390003c4c10390701c0056681d6201440c00b40240d8003620140c61959061003a040d00e4421454200420f0000d0300000028800201442c00f00340304040c01160001500580c84c4c1c8a944800c100c1944940200040404c0745030007801800110070403117020081010100303069000106950044142c040101a4860702c54482c0303c051004c105040722050703a040c0003280c541d2150000d468000d402e121140c1c2c958040100e144160b542026880086c00040780910400108041540148210035903d1140a07143c03840d08030000d08030400e140c1c21311640c4250200d403035241900086146a05441200c0003407a45101c01c540030710900070f1150218030340910382000602e14007803555209040406076040c580448140a00396114000e150085003000810482c07950380140c007943d0300d1a001e840440c20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 983991699 1250 983990449 983990459
    0x120f0603170d0906180c0602010203060a030f11041803031503150507180f140406050607023309100804050d11030c01060b04150e0319052401050f030304 67
    0x60240c00d84941a14020700281607004a51036070807a00752150310034000c0102c4000424681c0d00100c43c00401c940040455000240c5a07205000362809907000400d9803901c24516500e0180d2070703000c507500b00c03000b003000300d0908101e40d80c034400c54200744044e540f01882401d451034010704a482d9020503540510f034216061020810b078640c0d11100404803c40000c00303840e0940b003540c12035044006940d050b40f000030701160302c0190824100440d5032044071040d006008030100700c1590030368000d01b0742004090000c4005442e0400c003000c26a1140702c038203090801312100303880c0400103030707111480c4601000a00c0145801c240d95010303103903c118030380310703081d4142a51403984816030800200e04122144884203404a13090049900d40000b00000304440390384c40400341c0060700248070710001c0c4103400000d0a9480d020780d0900c419130500030094085207820b084041c2ca1180c0c001d00070b90b8944500d650b0030f55030303d9090f03030320614031545605544d94940c03605042040b5040c0c030b06001406a0018001080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 983992805 1106 983991699 983991713
    0x501020702030d0e12030f070303020a210b15070201020a08090a050901180c260a09080c0a120309021c17070b060405070504080d031a040903120f0603 66
    0x141070741c1038007501506d84c0180700418960500801109000911039801000340d034096007051880480c2c0d04209a01840c0003400040805030b851041c969030345480b283c04c0c0500030070850203525002c0c050340000c1d03d81480b1707280141555000320710306146d5036541002002408010781000c0940d81d4a240300c00d0070ba10f0540710703031f117080d8a05110406800d20030100301e900310b070b201d60b0302644000450008145010000307110768800d61340c40d449500010141350003000d0890310140180b4403003065082c643c03a0500c0c0c0400d04400d140ca481e04410040e1184c00031400c0b43ca02c401420f6104040508203100c032a03407410b8030b10b00c1e014400900f12080105902509005210075a000c204a40c0c03807103030960f4030388600c0c02200c2040d4011070a4045962094110340707920000d1420340c18500c08440089010f0300c49241c2c04501160b4603110414007002d40d481a6911502c5c0b45009020480c40e540b1050 = true := by decide +kernel

theorem cover : BRFrame.Cov 983812949 983992805 := by
  have h0 := BRFrame.cov_init 983812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 983812949 ≤ n) (h2 : n < 983992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
