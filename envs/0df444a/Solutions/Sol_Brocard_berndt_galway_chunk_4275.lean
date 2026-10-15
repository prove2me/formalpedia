-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4275
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:05:32.972573+00:00
-- url     : https://prove2.me/submissions/2fb2dc53-c91f-4d18-9166-7b595b937abe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 768705035 ≤ n < 768884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 768706285 1250 768705035 768705037
    0x2e0501060c05010b01031a04150e07030903030e03030f01230603042009240a0f09050105131109010302090103241d04150b010917010f062c0709030501050903 69
    0x10101e40b50b500b060f04035102035119118003c192554207188008018405041c4002030020020501a0702000310021400c800d02c1101c8500903107841d07400040e02030660a0040803198403c10080c0190010004d1090343c280d40d801e5541580c0b140c002d50500078401044016400103140741d1242c2000001c0100070070721080304040d108041c02c50481842d1461420b04100b6584411201d815141c8680d0303014000000e0040202980c81e840a42a0086140c9a00c21007010601c903500c65442d03140c4440042c406400c000340040151a00c41406010411003040041c0701400342e002058109a40130980309a82da100c3d07086940fa00008107003074601420905180a0403180601841d852450206080e980c40120200201c3c4a160003610702d030303c010056907407030b405015003246050401003801804034888031244000700e80750b4101000010401d4034400c0744000c0da00594802d00c14a85c02901744c40103c0449103070040c5a11200008003619a5400b2055514143c01d40020781150306c0c1c03004003c480c00c4008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 768707535 1250 768706285 768706307
    0x111b030409090b0f0603151602070810020c0f190f0602040b191d091f1505040e070c1a1b040608041109100e0417120a0e0606032e050106 60
    0x184c1d81e0b6810380e5154180741d5160f00c5000d1102401e00c420740018009414414600100f010790b20503907141076a9a041640f034861552501200b480c1c0c00602882071840811110712140c001801410100d120945158032086074118040c0090100c0d09840c02008002c1d0b04940291498071541074580d44c0395078072079003d04043d5201e08041101401c04034100d002c006251400180000c10094556440e00032406044004101d1403907248944900480c4500c00300190082c043c4543e03072800d49440c90b0540820f540d001c0603041074180480d9081c0c4c100401c45040300100805516060007422341c40d03500d11040c101c001594940792500e00854041250740d48080c8041c01a401007404101110310403081180c00c079410344843c507501180250804c80390342c044044a40c4240038600b8011516203460150149500c05900c0d103611064420800424003210302c0345640c404005c400a18451800304086940e03205444002d02c04003c49404002c40c044202c041d4520b4103903408400c0c4001d50b0740b0440a04542503803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 768708785 1250 768707535 768707551
    0x203090c040b0901180b060f070311071508010603180c06090509060f030d0f02030906161e03020309060c0c130212010803031b09060d05010e0910111b030409090b 71
    0x403a4030240b4040f4a00790503125403140482032a005c0c050303a8801005500441a00700c18140050749180c145103003d816018041c2e04d13554844148000240e00382a903e41020110348001128500d0099014030a02c1c19070740700341000900907540c106c0001600c484810018903280204001040309540860a4011940c1c1540d254403103440c1d04080220014042c40c1e4260550f0200e00e41c046001d00c40e100f110280e01690060345d01d840c40c0b21010502a910008080320200b034000300d010304000e82403040c01840000b07802d00c206c0c0c250f09540c00079100c1c810404103e100310030115036000c2c100800d00c00b414110000401030f5036501c0c621042d40001e50064411046043c40880c0009040e00d030200c100e078800c2d0003020000011051124031044140c2103842d0785604200148007541c0145d01034440c0c907000e0301071852401010b20b0f15041d4a4076006048500e11080b605140c0c2c0300c00d85000c140261222a03000001980700e0b5100041e5440c0365001e1030784003500107410459200140402104514052410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 768710035 1250 768708785 768708791
    0xc0305011e06080307030e010c060f140c09180705120103150b01140a03150e040c03110a06020a1104111602010f140703030f0e030a02010203100e0c1209010f0203090c04 74
    0x240d450a02250540d110750f50464004102080019100c0c82d1304858107041410520400003035500d80c9021210344104040b440c507554005244041c600302000f651100c0c01445252800d541d20001c03c1c101180c40c60001081e40780e50000c202014041d0094a0b8542d0b03418016510a40e541d0a141c0940200820a50038852800540341d4155100c3c1c03d516034401c41c2c941e9514980f0702d034100200c008040500e80011828500b50022038505680d07011705001d02d0007030050700401810750901c0c20014208415003803146100c980204940780d004221629840d8006210588641403c4c0102c1c004d0b0109108040160303400089140d04108000800300d880d070f000fa42c9000c7d1a0b81078400690b030a8a004010040400040c882140003900c44e07004005900890721012a840303001c64281440d5401462035440940d401108001030f5104aa2020008109090244a290510044000b0300c1e210b650b2020060701c42560001c1c50b41c000035000840480c5100ca01103541e0300e050811130351034400c025042d505c1141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 768711285 1250 768710035 768710081
    0xb03010e0a06150506120c0a140d02090f011b02060903030c1905060601090b0421020604080307150213030b10032009090601081002090f030d0c1223070f0c030501 71
    0x50000a85480307441c44841b0307200c035441c2c904d40c000c903c1e00324019050401030044a01c1107100000b4001d0468107036002c0c401740c0c540b2851410802c04070041e101b01810801c07040020f5003600c00300b09401d02100e8040d06c005a07103c5c491030229055100380441c1107000d106124002c00c01c00030000d24101c50768060400d43ea160303111107004443c0400c1034071070700c036600e5020b21051000700c8281040e103044000b01c0400d1180003c1c55404240540c016905c00c1400c1d40010504409209080d9482c0041d87e59481c0218a0800d1498080e103900c80300c0d000241960030003a00007400c107a00c400c1000c0207150401408804c0014005070306913412044440140141400307408101902c45c0022454143c40200020300031011000c01510000d40220000d281e026a083c0c1200c0d5050306d081c004604450001d98400003110440d05204042070211010318040184c8003500c2c500c001d9080e04000a40880c00f501c007a0354018600b01004c40c00c1030300c04054800b40010100004000056201e964040000c440380c040c44a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 768712535 1250 768711285 768711289
    0x804080313140a050906061e180a080a031404350d0206070e030138030a0803011e08060f0702100902030703060203071b05070e100501120b03010e0a061505 68
    0xd080c0c0312402e5000200c58006002500d000c1e40c48135031011014059074209062000b222010b981d01e80c42c035042075600060b81e0450303030102004e91003420300705a4480c80c441380350051310f80d9a00d41d031100103010003071a401600a51205030048030300030416115503001e0940b80d4041d01003025103246441001c5081d403000701460b0440800c03132518400c00394000c0c00141d034800006403014520041000c0e819560b8a0007500c100700d4141e4000d00384022031042d68403000d04110407040310100740220510a502040c031810014286100712815a0700039243d400124101c4948910a00b029400c000c1a6018800c104041070240c8130310148208010b50855040101841440c0c048800c0940040d402d034000c524203101261060b002190850700e1450410302c14800d0007040da03060407032940200d4090308454000c11003d800c00303503800e070800800c1b8a406c141a00e0701001030720702d150400070000140d8441700000c1d1155400e500071181c06c0c98000903200b0700f00310b5141607001410b000202201c0c94164900224041c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 768713785 1250 768712535 768712559
    0x240105150703081801020a020715050f18180a02070b0606130504090f020a080d090b030f0601031e020310210302032d070819020a02030718090804080313 67
    0xc5021091040c03400d00c260b18112a80180106002c3c5259001c810b0b00070041424801810840b841c0d502400956040120945001c09408400001c0110034131440b02d900d403d1800329403c00d14030000340c104480d0400c0200d101c141c15400000c03500361000b0108021210b40350010040e241c0b2480803040b06a48501c1005014002c1141c01844170b60380c02c1c020b000a040035400b1140c0ca030300504500600e1580d43d0300041c2104482c1e04601d02640001d0000c00e0b407240c001d41c078500070380300c240021411458150b02280c080c081c020700e513604264451102098010303030b1210030302402c440d1190a560f6440e102454400c10306440c8500190746580f020024030500f400301c0070512182d41603010318682076440c85801004070001c0c5440c680c01060f422500c02605c059002401c2041c8605080c0e03071524080c0040442460400190311b007550000303440e13000140d42c003040d01380685290350141c4840e03075141d054a600820850000070484540050003040c2d1442c00800350000e80e00401d100c011282c3c4500a10810f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 768715035 1250 768713785 768713809
    0x60f09010e01300b1504050102150103021e010c2112020c030703261303030c02150f09070b0309070302040b0a14220912110f031e070203240105 63
    0x10300d03203a040300f90b038622014040b595080001e4400401d50040350b400182d19410703000c82003e2400b4000400300110f58060144940c90340d6496210001c40d072668000c50f0305444a40c44022502d2205451003469030700030000300150a401000d0521140b64078000380713038004405420800440e4440440c2040c0018034021070b0b1540446c0400b641c206a626641134840008061b0400840350588a400d00312503c4442424840d14041b0201d2202c0541401d0150444000303600650454201100311411070301802d810039040140b8002c00c3c034040d41c401900d03034248030254102041444001003071141d503035000226007040d41e00841d400c0108003442004c20007803c009100d03c4018280e0754031a01000e182030240d12616081401c1000300c001e0100e40c41200322029044111542491401d041c01040d5011b82c2e610460313401c1000400150284810981c2c1d60300a2440024810596a02c08801e402b5150140c03122503034003a0417984405a0340c03000040140016050b00c45a80004000003079504d000d40c44800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 768716285 1250 768715035 768715067
    0xc01051513060f1205031905070c05040c08150f1008040209010602150c07020a09020a0c061b0c0b04050f03030103141b130b040b0a1205010b0d02010512040c05060f09010e01 76
    0x1050b6450030400340e402621181c0145c4440c0000d00c03092080c0d180c1070100c07140d500720130f98442d9074036070302c61500c40940d80720b41e04900d00580c0b80160700024190405031651b04a070503000c1e103201180105000620181c01e402c0c6040c0c000b59042140c44090341c0003250580250303c03c0703a054415070380f10442203070707588000601c40c06070000700004241c0c0c011244000b4207055001620700c044080d1620191002da9000c0030030040054201d0408a01f48041c910032400c482c5d01f03010201441050f0001d0003441c290030048090240c1c400100482c2c05c2120030804080e03503481003010303079459695030708201c000c2c04c9070701010b8105405a2100324001c840c001c5405004514014903208035803040103c100000c1c8821351031607070080d0740e0700490403050fa20b00b000715008160390725210320010001d140581c2910540d441c0d071b03170080f88103440102c010303030700081039514148590444040c155150b0038a5542203a075588160b8210b100000d5a00311702c5081d400400c1244021b0303c810702e403000003000458641c0c1104031000c2c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 768717535 1250 768716285 768716309
    0xa090c120b0a0b0a120f17041d0106020705040e010605030a3f080910050a0b01090605040b090603040812100906082d10060b0c07050a1212050c0105151306 68
    0x11100c0c40080c045c003400280560624501c0d00a00c1d0740307148080440e00c0a00c8002d42012038100000701072201c121040e40b4480da01409103500d002d030040d650b00c0a60041034495038880c82c0300d804881096128034020701c1c1c010212482c4407054100010b100c04180301070703154044c2c1610080e18050394a003041410104181c0c0c41c0c00649001030742100e20040c09070090089010741240d00f00031891a000e501c3c02001d40c418009001401c080025001c800c40b98003810500c80c060108100d00c181a0b42518aa0074081c1c500c40d03038aa84500c0c01034014440c0110301284045148140b103401c100800c1004143d0704003820030041c80e500d80700616940c0c240d120078004401c004e4a5040c150040360446504d96100640842e250040c00700c500905440b003680191070310650200d40da071168041001280c00402007500c05041c2d003800d04800e4080c00200c820050441001a1086170f030003440760741160040a00a802006142410911868050402c02141d8451640e04070030000b03400e024811b00c0222901c140f005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 768718785 1250 768717535 768717539
    0x120f0c0330091b181501030507090f03230d03020c01050f010b0316030605130e100e0a080a020a02090103050a02150a02281209090513020d0602030a090c120b0a0b0a 72
    0x150b01d1070a218001540c1080d4404041c19a14039113210b540d00030280481c41c03604800d032600004044441c010110350030040c81d05401c0102074960a14402604d8120384440b0075951b80840310880c160f03e900f18413026100360508141c5195059010342a2020804001e01a50f290440307051061a001c0c0100c1200401c204045010f42d03010400030025820356040105502e0781da203000804500da0080d007030b0fa555031100c10b0580c18500c14400480030004a032000c00242d030924100796071703509000f40000e242e11030015150014a0080040c2808242d0044c503200311980c5919150340c6650440c1c4040303004502400c0050005c045102c1910701101a55004000c0c0c01038081c044029150304210440a0790708007201c00300801c1000d840035208030a20313240c80c1d0000d4074086100c1c088510051030070b0002c0c065440107800594555048405486e0030180143c3ca0751502010070700146681e1100804003665124000740b44411024011316080c080d003007841c101d070780d6003000c8410303a03800450041d8054170520003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 768720035 1250 768718785 768718813
    0x50a03020c0f030313140a03020a2405070c0302100501030305090d080d0f02270a090506041d010e070e06091602030c07030501090c080a0302120f0c033009 68
    0xa0100c85980d01c0c01c84451180c104802400c5910aa40c0441e00d10712801411050040083c080d483c000030703410041501c0e07203464a001391075800d102002402c0c00c407801d060402c0e0080c04540c00d07003a41d201180810150070308040c060112040e54800300c000d402006040510b00c4524171441d03049036010b031a4107252014903010801c840e5040102110701c80c909108405101109108806202c49403210050361615501c074180c16010100b0000b0840e94900b1001032601d8403282c0e0000111556480302041e142c840303d00003000382c842a40d07500d04411548850f03020415054000d0412140110305403109280c55911141d6042d01c11200c0c1034000d064900810000042c0b040c60140e0f0500d1031054038144840b000403982030903040d40c4299056911040442c0c02d0042c07101c4007100429100d0010081c43e0b290f503030080c1d2259640c44020070641c00100c5c10329607401080003103d01c500b094009403951449003013100720b010307a80c0e05d0090280c007107003100100c40c1d240c01c0103500d8000c98a04000341295074480d22 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 768721285 1250 768720035 768720037
    0x1e080601050f07050a230d0507020108060411030a090c090608070509040c1a1201090506030a0f02030f010204030803090d021f05071b030f02010f021306142a0709050403050a0302 78
    0x70b40026611042041c5000701d40180300a1901d984a404d180c80c3e015208000780000b410349111210241c3c100c100b2158520f80c200c3c0860711025030a00301041d60f0355a880c0040c00500c205501080002030001c104290f021b0258008010035204058500aa40e1a81071900407900c00307000b02405503008082c02d1005240162005070300078400c48685030f0300f43e1551820010201c0b072420400c5061404034400e07401d0190a148203001d8040f00000b0044c0d494044002503603901840405001620858103440030364906011049540c0ca070307034009558071540c80c908206030b0750080300c01380f80074060718600c9481c86201013584103035840e00d450268102e25120800c0c42c0200b1004d040ca00a02806280d01080c081d21424101d039041e0094941c0031806000c814007a003500e000d5890030801a104001030441c9901c947d00400039903c070ba01d40700070903005180e000ea00c82c0c0704242d003186003694140468483d010079200c2c181540f440060076a1509035607071f000710f4203440040c1c40040c0464018402d000509100358 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 768722535 1250 768721285 768721297
    0x8060a0509090f031902060109090c09051801020a121532190509100b031303050d06030c17061006030c1e021b0a05030d0e03070e010b0a1e08060105 65
    0x1006a450203108140c107113195900414001014550300a000c82e101c035014007d8900401c620310b0b0502200742a035545d1241c030003480c05a0380103140e441e00400c0340d007522802c07002c1c00c5009000007156a51102040035009210070b15030f000c038841c00c0c000702203074082540032854100c89011002c0050501051b62070b45903003000400c2c86996880340110413200b42c1c2d520b40c41d004080030341c804400440e41414140180010014031021182e801584100a14031680040740e40c084960417400542140c2460110307011300c13440101803070755400c18801100348005000000100c0d50b04a04856581c0001d040300c40d03c4010807100c1c00000c00c2a4441004a14040d0300400d150100d0741c41e0030745503080504611819080b2003aa140c00591216401c89000b40040404c1e410701c007411581940620b2610000a54680340040b100c010400310030398030300c0c00d1789040240c0009041d40c0070551180b0342e11903218082603041080700c60001601400741185036407400c418213415000c55660042c01e580c42000641c0d4941c004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 768723785 1250 768722535 768722551
    0xb03062a07080a0305150310050907050a0f060323060f01050c0d02010c0e150405040f06080303070e031e1e071511010c031103042a1203030c08060a0509 67
    0x181a101000044200003803001d60b200b51412602c4a0103a000203040f01d40042c01c8003c01c10714545c0b40c10941d600026024a600402400814140ea42c218201d0800c8170a03071000c0e41109000c07202003012015210090b0688019540400c00d08449030340ea1b8030134950125407010072010550215849040c6050445601c0d54107040c0145030540141e001407803d58001000001070f5520401000300c0d550010a804503140100e50030407042000b0320000003c1c1c032641c80340030704c1241d84449603c050324030ba0b0000c10003044204103590312450701c0c01c405840020400540f91090240c0c190502d0036803140242010310b010088014007410f04940c82c803407440328804000590a21403a2701c0052207080300707521741c03001800360b070b031440b1550008110113429607000c07216031014103003490084141005000b041d40d0740700b6044010400e441303a000401030140b0340b9202c280c800c14460b40c200895003512507100005503034401d80d41000f217289480811509000241c44884d032007603d14404106500d44016119049503071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 768725035 1250 768723785 768723841
    0x9030905120c0a03060f1d0f010c141c060902040303020615190b0c0a02031b190305060c0307140307031d010c1b140703051e0705010c080d150618090b0306 68
    0x80b07d00581c20620b9115103082660780810380c0c00304001000e0050703112102c020b081c0107110f07000c1880c107940580240140d020080700d0351540f14040d03440e05d800082c018a0003003011542c51382c903030800a45a8400f1200c406111044001080b81410031407a802031442d0140040200c00c1c1c00c0c410610b400c0e610a04c000e00c441c0c41900030b0311b00903944c1403260303541c42081404050048880c44041c032480c400c0042020300c801c40c5503101040410360200d100c1c1d0703028062008640d5203075541602601c0d15594900d00700b44044021003003000654140e03000d0321030303120142408040e9000f02d1041c9800e80d60710700401c0e000500181c07069854840340c0c0c503a2109544c403c070340c00090900350302d810900c0e202859000f039440758000d083c07d1820b00c12084c41c9911a0030940301402c0500d04100000c0c003851100413000707042e00f000280384c08a003030b01c070b40c4100c1542c0078004814a403146d41d600014481d11f8403003408008102660800241c282c4a0b20074460500300150151415030b440c0841c000c0440000e4079a2100091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 768726285 1250 768725035 768725051
    0x100614070209101809080702091f0b12090a110906060c0115030b1008150a110a08010303110a0b063d17012603090409030905120c0a03060f 61
    0x19641d040144581508102c51010601e810000c428003803d002188211510b00074034400880c0c00e540403110940d0301950070027800d0b1a281c907403817002c01448079003a0344000c100c1e80100c0c1c5070400030010b100202c41000c031101a51101d814054503880d07044001442c0040490741c00410b8209104800c0c1d00242c010401401e000c07400d8199800d50f100205104c0c59820509814010031083c085941c1c0c110801100343c0d5865414442410b65844103000c23034030604031003400010042c4640360802d01907003000042640d154410072802400c99402804201c000c940404d00000441000142d0003801982100016070340d44c0390384050000c2807040c4c1f4804000c103000c1c00bc1090326400324000680300300048445044d002942110000c10712117459182141d51382c0c010004000b804141d14150303089212100d00c14010741c03040c4000614611501840c1500203050440300818560400c41c010200d45040d154034101c0f0481d419155250082e10710440c1c1e000d80606000c1c1301088150b0b000101e685c0b4002d800150240f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 768727535 1250 768726285 768726289
    0xd110417010204090f060b030c0c03091c031e0e130213080d080108010501032a05100c050f01051003120c0501050c041d01030b0601052505150f1006140702 68
    0xe21254804000d07900041c0400990b50301c1d02c42d4154009500f03604100340360508455410a12000e09000c0078171401050007102104103108640106034010541d0608204045e60802c04144c2c8803400d4000c100040c110180c0b9006240c00d00c18684101d0f03940b00c1083c0160303810021242030000f001c01031907174203000c205a004403200300c1c2030107440c181004003480001900000c211060507003000690f6410300c001000007500c200030500e9010300710350000d43c1444000c60000d0408000d5404140c0c018014400b0108898111640e204403034040c03819682c00101c90100c60382170703810070b80ba80d5820a9440c00c0030004140d8151074070001e2a01f501e040c0103001d1154485d1070944200342c1344544001e00000d401c100d81c0c00908071788002010441c20102c6150726640f0f0b11003180c40c00403c034a041c000005010b0741400100040400c60115000d01301901c40c0032400c000f507807040440031002030700c5c08c00b2010031030b90442c0412151040102204900e40d4906220044810074103403005a03070b00f0300081c04900016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 768728785 1250 768727535 768727559
    0xc0819020319021f060305100f090204061502010c02073b010603020a0905040902030607050c070b04030602030402270c0a14030403030b031011040b0702010903170702041a03030d1104 80
    0x1070020380c01026101c020301c0c51104080136110f00798005514140003040000d07070126414041100d08072000079140004072000014200054000798458a80900424002d5645140702c0c201d06441d070080001004084c800e80e0f8424150007540d0f2240e1055001d890311402e070072203031003003280032000307448149451207909000c8000030f17002100800d40120b00d0011855101a10b1401410115401e103d40301c51500460f84600b40034107140c003001303400a0301103c10a02040006d004024005d003c5d56207940d01c3c00c080c0c009401c20345049214030204c8924289030905842c003860070001c4151112256111600c4600c400e82c0f0400c05441485450742e400044074801101952049010741c80c0401d54a41c070404060805907540310803410546442c10500d402110241587c00741c1d5541400140d071900d40d400181c1d004060356000411600c3c0d554010030b84410002c0190188520a0707406102d07001c1108a5002100d01200030307550580e00610495001c1802074004042c104c2c400b003038003480c064841303040d8921 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 768730035 1250 768728785 768728827
    0x15180d030c2612040615030c050a0801050c1209011b0e030f010e0309040902030705100513120b07080a0908040602010603050c0f06070b040302070504021803010c0c08190203 76
    0x225070100554001e01901030052203500181d590100c96000d5503480b02003036401020a01000d00380007000040410070650302250a0051210071022450360342d00d840400c3d100c2c0c07409040c0c0038403610f11000828000502902d030003102c40c416160b040806c55540038001b107030010150300140d921624020800e0100700f500c1c0c4451101940e071020304802d84018589003400c607403038000b03140e0715020092030580f030003000340e80c4107038000c8070085916560350000901e4262290061039224100740e80e0341280542080c000c04500c00110054000c00380d8803c0d0362210b81c0000300c80a01040c103003070001a015807045150940c4140c44d500c0024440c0344039102c07500180c101381c21010250303540e103109000b07020301005118420802140e81180090080000c101d40d40207094000340b00710303002c1000c501018001d000030f0307000d0700001d04210749441d01c0b201030105842d8640b0b8124007a51030108684822841106030007080764004100e14906180143e0050209046824500031404103200c0d00e032600300e20034030001d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 768731285 1250 768730035 768730037
    0x121104181b2a06140f0411151e030405070e0709050904050a0c0605090103060e0103120807050d021602040513030e120309032505092404020c010e070608010f0515180d03 74
    0x180e0360016600e001e03001d803000b610417181900311408100008441508080d1480425a40501d40c0c1018440000040c011402c4910480314100400c0c51450303004c0000d107210703500800440e43c0e0702d692002050140001a40ca20300021205081404281080c07030310160401d01c204c0443c0c1840c0d00d5619412158811030308000006600016440410344e41801548041c04807450040b120303503d0341e654088035449482d01704083c002c50b030000a2055020b642900d400c80e02c40101503541d02c42c119100c0c4403210944038120712683c0340802064030700c040c00c0088148140c5c1034680d1002c1c0d41c41001003000d590003043c000001484200030075482514240054540e0813410008403016111103000900c0360034003600a540103850100400c0340c1c04603035100c10340c030101c043c905104c1025441000304001e0302c00d983d240012907081c50b10058181c1c40005104c0c0403141075036a0801541d894403281c1e84d40b040c07684242c65100300824109107200da41480102070b0803840104244800c2211402314401c14980a400e070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 768732535 1250 768731285 768731291
    0xa09060909020c0c0f0d0506010303170a020903060403031a1005040f171b150c06041208090705040f0603020901080619090803040b0601121104181b2a06 67
    0x90190401041405010329120039030415840142c0d45039221041d41007503105d0b256001d02d0820701d4680d0440c0207400c68000098501568490030054151080c9004803030003400030781e0000f4010700320b500c2a90768601c401405015103403156101203001c0c0001001e00c2c68152801800c1640695940b2120b80d0741d48181d03140c00b81c40394a8405200390001c450790110301a80c40c40c4100e1103007010007040103400034101280244032404844041503d60015800c5904c1c0607000150154a0980004100b13214a1242441103003100b0300481c103c0c0d5002c004e481c07012040c1c0c42000140814900342d040a900c0d1004080001b80c07040e501d8002031034401d800c0c0e004248c00e40201c8107000a20340001004818080300080901055585a8a0032013503c8010f0014080a4266002c04c050303a00c18480d4134002040381000f4071080d0b1032151454030302d921070b11800404015039050300b010b124450007100141016480c0552412844240a0318844403010340501c030740300325880c91040c000c0c40b1880718001e14001c003000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 768733785 1250 768732535 768732539
    0x190515040b04050c04050603091513050c120601090e0c060a0f0f141c0e1002040815060a0b0903100f0f060b120610050c0106031a06180a0515060a09 65
    0x1020031280314000c0c442c0100e040400300444509000d045400b04c0720305585c2d080d5030359648040903092203406c01202030f0801e0b5000a01c02621030405070300c43c00b50b0060068514680a000030004c9806600d008052181c0000c1c00411040035564080c0b40381c080e010b000c0d41e41c0216007200007071032035001c03203103500104000d90701001c0c915911021400381d0001030308109002088071002000c0901410202082c4030b08001c012000c0c859007038011308801a04a002c840c0188038140419020b5001401602014402c425844208400284109000394405020070882c1418403050640d40e40c0160361031509403094148503203140e0080e102d460491860250005030180365400346109444060344002603000d0240a40c01d59010218035940d0000c10484030254004843c00c0192040d0140c4000e8800a500e0240300101b0300c00750004e804000d1441040140e1280c0d542010003110f55214050410207100220015234103441070f510250b00a1444901840031020900c005282a480784c007406c9c0c0007419852701 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 768735035 1250 768733785 768733789
    0x70903140d090b0309070b0d0b130b03101103040b07140304061b09180e0c061c0b06030c0703030b0604180f06090c020a020d081201062003180108190515 67
    0x2050b015184110909207035084c03500392255580010b00030718908000000e040080100c8070b0340310044660015044803c0c9290001214008244898202e80130f0b01502c1214124a41c05205012042102140c07907800c646464580c00740a400c01081501400307400d6900d11040201e80c805144120b00c1510007040800c000a40d07504010b5401c151f801c1809484102400701812201c1c8251150000d80c038000b4500740d5480c480e600d0f028400c506503030865000550300031015800c407200341e011100b030001846961002000e004141c402100c40705414003050160f480002e00c69003044540d06801040c2034141a107510b0032100c5130071010b41c3c0c46040781d9036040c851241d03a418007802006080d205c0c001c0045102c800704c0a5119001004028842c0b4400000070080040d0107064469010510801400568480c680907010070b0a862400071114001901c030070548400100b00c07814000d0450f810310070f541d540d40054030b02078405840c404030070041041001400d41c15100b2503110703182c040380d01100b482c00d40302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 768736285 1250 768735035 768735047
    0x20d0b0319061404020d060c090504060603020703090b0307140a12051302010318030525060e0c0114040f030209060d060e1b1503150a080613021c030806010503070903140d 75
    0x200320f01a0800c0c06041102580d2990403408000342c20000208120201d803104584a80503a003010f0f52140c0303009004640c450f0715078058528107200317403682c1400d071752522a80e40440c04211400741c0000d075181e0080c10380704400e03405001110128100400031180e6001000c0c140d890440d404041c80381180c441e0f505541e49401060034500041c2c145800f606419140101241b141c0c502a80507e00c0006003003403511110b5803801c2189030092000c101401c5192003980c0c4800b160403203039000500000344440c8140703c03a400c840842c0c00510a40381e01d0303440e40d800d003c040c0310b0050440c2e503c411400c2c03c400101d8641e00a1032014560a0083d04259003c50b006a0143e10300d110b000340240104c441c0c4081080c140d4040329005803580f400307070b406681d1850000e200d10450343c020070194040c0c10700b48007075942412241d510251086650005050b68146441c40101c0c00780d4000d40000d149101059880d40a540116041440b502e8000b503010b4882e161100c0f401e01012454075168004154582c13011b80c404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 768737535 1250 768736285 768736301
    0x30b0a0524010c020907021203040b0702061015030903090504090f0c4103030a0f090b0c0c0108100906030f1202030304050a141f02180a0513020d0b031906 68
    0x100242407842403500000c15403190300c01c009000c0d44650000c2a000750081101c192200c0a00d14015501d01d824a491000d6140c01d4403810050303c0354102084203221244100016500500c4404200c00d02c00c0c04110050100380c0300c20360a000d00c01c0c0d00855030781c0340d5005040c003442c0120014880341300141350110300b0030300a500441c02070500070b0b011b20405211070b00700003100443c2c130200307581c8040d9070400c2d1540002d0208250303414400047e0030f00c0882d03008445480b24110320303120341742100d41e607401820b490710030361000800e45c0e00000b4040c40d80350300841683e9004032002c01116809500d82d00c4600440d0207030307001034425100a100034402c0002410302e410140c0c82c544061801e40c101991002d5803050740010007050850341c17040c0501003600c20003150821420302d04940c2222203290940300300a510500e06840141c5040c65880003500701703103e201040361405428200d2010760b140d0a0030084d0009929581004d0300c1c3e20800c0b040d0b59081105c140da0880381c1609008501582c68180110345840e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 768738785 1250 768737535 768737581
    0x80f060f0601120e010209032506080f0c030a0902030304090f0b06070f0215091c1511031303030603020604080c1c0302060402090705070c030b10061d19030b0a05 71
    0x10204211481c2d07071140c5011611454083d01003072181014500901900906401c00e03014440c51000c0c4003a0000c5455803518545071603080d1240d583c0702c10089502d08012039034685462416004210108841030095500001c80000007509007200c2d40040d003594856071240301d03015100c0700b01b00044529072041d00007130341003200d216140c180960340703d4034500a500c5003e8400c174440e0b8148220403040804442c60100c005001064030f03d184411410300354103c0c0030a440707100421003001c2c1110418841c0c1307902c0005a2811030300750381c0d071000c18050f070040e6540e048041580b070f07203400001038403250040c2c006003214101a00480001d10300303002d80c030b0140c101d24401d4020441800c001098001c940c840d000340d010340d255900c46d500e00c80d003a5030600c038841000b0418007200f403001003844416035040b8007800035001070b002680e40c2d03030500715070390440b120480ca11013104020745200d40c9811221109400000c0d0055000035075030f9142d0340d00390482150112000341d00d40d82040240040300340752011400744 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 768740035 1250 768738785 768738811
    0x224100f050d0620070c06031107031d060409021b0d09060801050d0f0b190b10142109030913020703201207030201140708060d03121104080f06 63
    0x1400c000101240b901e028040d14142c0c0c0c445085840c4140d01c0c41e41c12221180800d0640d580d60307540b074021502c1d00603105034000a4685038540008100c5807045034a05605a03843c9401c10740d0003c00c00d0302180d0b070740780758a0303000608001c00902c0503294009084c0170401050302c00035091465a503503007803140320045081040010703041800541d13041060941501d10a580c213122848980c68010445140540302030700908840080115428114035405088600c44c1001c1c8a075210007818426001d10403886100800c64110306540c0014541010b0a07000140c0c1c40020b511070800c4040071b2000c1c00c01d440e078065541000900e400d89041141800040d01c0c1c200808620b4000c180c0c030010007aa0065070003245001004500c000c0b240e00400408101e40d040402c1142d81c1d0b610340c50040d000305441d41184608802160028041502444802c0d205400c0607000c42e40020701a582210761072800c04000400c0c0f55204000c0c403c00030f81d9805480a0a030071340040152540c0c0c02841c0e46030800081201203c01c2c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 768741285 1250 768740035 768740039
    0x1e18010e090c0d03320a0f03050603070306090f02120a0b100e180f0303070507020103060f0609180e0a0b01080624060f0c0604080913020a1b02010224100f 68
    0xa4604850100f5605450010b6010040c4103400c00902c20700541583d0954104611a5110784664003c002080190326034030a402c144446c00e40555804590950f40358001c040104041200d540110764200e00c1040e5840d03504c0c11544c00212041014007104070603500c0510544104002400226001840c0c2102a40103a00d071502144c03800b90014003c0040089181c0001d8500e041000716500515915090344e41300d1408801c020415000340034141d0011b07050190000b12885012644801d070b9502c4e50f03502c0226402d0a1410303076800180300380c03814010341d40e03000e05002042c00d001310321096104080f66a415450f1100e05484e088002d4031103214012452003031158010345201c001124081075411548a801e10001d0302114000d011662515004400c02c00c81080b250500904440004650001c0b200120011020807030250003085008078074203c1010501d0028030f042280c2042c41481202d0b10030007441c0194104031641c048201c0c003595038000b4410b11910031482c08001e01740d40402030f900d0074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 768742535 1250 768741285 768741289
    0x10e04020306071d09090c04060b040b0313020607060509030a030e0c0d1e0602030f040201170c0304080d0207020d030e030706030b06091002010b030f07080c01050405010c021e18010e090c 82
    0x403028103e0743c10300c030480300d100041d40f40620440116440050540419140c848000c5880d1281015001e20942c944140401c010304080f0a48003990b500c1d8031118210303504da005420900e00d0043e4142d0b440602400f030403001407450f00801d84203d49090265484451450014050780c591820503e0660042d415035103a5444450005000700c3e080091041c4100f200c000480c030fa415400c1001d0300d140e00003c10445021240788e44207010394402c0e642d042c608100c1509142c0c0280099421807004002080410b0101340d00b41c0292154083c0300800615007152a40003c840c0c0095503811404a0182000f070f42a80c58180700c010014051030034107020b6441301a000500c1d910898000c2481002c0b08001c2512140c800d6001c40144078010301140c1c0c030220500c0030a6543c80e81c501c00c2203894441d01c06802003552003142a1011030b00113868a0a2411a43e400c028541c04a04002c9205c030030f94201200b204c1ea540c020042c103c0d400105a4000703035041c855500e940e40d00c0102024080e50045200500f99 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 768743785 1250 768742535 768742543
    0xb01090504150504080d0609050108121e071a0a0b041b050a120603060c0c060f0618090224070203060c0f07020105030a060509010609180e331509010e040203 69
    0x1042c602d90009459079075171400741c016008122041189602e00310003c10941c59680c0003034165103007030040340c05040e03d02504d84414400c900034020700f003003403181042c20030b9003200240174001d2003240100034a14072500103c50130b40b400c417a200c3d100e540314031400c2d4003410944542c0c0030507100380b290240300b50f11070034019040e8400c600c1c24404022101072034603601000c41e84020003541e031081c0c1c103100c90781103044010048544210b003594641e01d400101c0d588a84544981811240d001d80840320a24820105900402081d030050380c202804401c50391280500d1040342060249054001c0c0e111042030051500d0214000c00d080f107400307000c00000c8440303451a000e9450079542440c1803540c0c0e5460b02c0040015018a034030464004454900100d01d568229070500700f5900d000704100d099401c4160207030140c4400b010420b8440c3c100b4002c041e22500c90701c91510307107003000983d001c10410040d075010011a9044a071a0001c078071070b850b0f1140f940b0b4010340c01401480d4208200b0918105500000d440d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 768745035 1250 768743785 768743813
    0x12020a08390a110a0501020306011202040302030a030c06090b010e01060e0a0302060706110403050123090a020d0305030901060807030c0504111e0a0905030a050a030908031216020111070f0b01090504 87
    0x80c00e4001c0b41c1d00901c14403601e84040c20400b4041075520a41482c80d01a0203500190382890100f8401e03520081c0c070041c030b40309603030499400030000d003040300b581e4505a43c480d69140054418a40b030f510898041002c940f0031030f009000601101a8961520900070900fa80901c0341c58801c50480714104007681d90a4103880c0619000040002c02c50040c40544801c3e108036407006260b54280744490754070503480345aa01e81c00d02d18485040080d0b4481c1e60003501c0e0491110300a44c840210754011011074456005180d10021040002a4060701d80b0b89003413408495078022210f0301d000705c405208a050ad4001c40a88c03203103205040d424080e0700030b10240740002e2230f050280c0034400402c00d581050320038841c03a402098041c0a8854070709890428035201c1e12240e4007134010034000f62001801110010071910110f0540d8084107450321031400748000301c1040400702c40ac664a42e04020900e0080900501c5468400c01010301102d106181440481005074002c600841c909803c2002094483c41c204d94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 768746285 1250 768745035 768745141
    0x614130b0a110f01090b22060903030f06080c03010c0315031101050f031524091905090702100b010804031b0f150e010b060a05091012020a08 62
    0x10321444841c204803905058000780d054588145011040c19000641c8501c00c0e9a00841040102e580d890a110400391071801041c0315001c00c00c0c603858007048050340052043c905c40d24012490b6204c1c1e602003000d40b8629000002581c0084040c003500e407800344201090100c0c030381000d01c10980c080c046100191124400038054070030f804a9849107038410800c45409282408000362a4280408042c502d8003640c0038090242160201c0800110500e880d00500d054141c083c1c14a407080c41410b10034019580300c01030103040040c450200702569080051845210240e000702007000c03540918005454280242c2418000c00c4018840400c5e0700610721603048803002108001c580151615040b9296003002c0a0007c04410410341048a01a04100300e00b04840000388000030355142000001d22894141402086040000d081c0c04e080c015036609280386c107800e002d0180f01c4040c1c403200580c1d02800300e400000e008281005600d05000c071074640410214150180901c2c0c41444061050303660081c2c1c52 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 768747535 1250 768746285 768746287
    0xd02060117070306062d14060904020405090c0702090106170a0c02031b1e0303010f050904051e10060b070b01032418110105130b310614130b 62
    0x107200c46410001c0000035503002100700000c2e65224000d615040f10280817040741d10f0703200030050301c000414071440150f82c15001102d10240f4054100001c03030b0f22645140350040d80910001541d6a200c1d1920703840344103041946991106548108540100160040c0c41403140c200f07200b6001400f00700300568045100c550005800c0113510060703186009130b04103408038518018800c0e0450f000400c40d002c00f503265210f80d0ba08810100000da480f40824043e203a514025084c0400481c5003010005400074041c0c420f840e0317003400d03540c10303c0305c0325404481c5d140040c0c0c89180b11405030302042c4190802401c602c545039080002507620b40114400620014108161581c0c40c0c102d480c4e5602500f541312004400208058081c1002c1d0020100c0c54580544401007299001c2c0510b500810843d5042c8402c40f032031100440c14107401c2c10403038015442c0c0140d0842c0d420007003108408261070188640d0410f814520010345044801040600a4a514160712030217200d003400341c0a2840382c42050303a840c4030485e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 768748785 1250 768747535 768747569
    0xb0406050a050d0c0903020102011a0906060a0509031209100804120c02030c1c05010b030606030307030f0530010503010b06180f0405040c060806030d1706040914010c020f0d020601 79
    0x44425008600103660b810f03142890301300225070000e400c03500700c91003a0000d001002003921440c0312035418082d400d401190380760000f000c03858108010700238440e050405604040442d0003080ca030010302200a9444200012002c08901c1d04160400022030149040142480d2564034104100c1c06000c000017845540c0380580110f5a0074000000c12400107000e465a00703104294968903003503900e4080d0741c04e500c2d110081c005410086080c0340716640c042c00961403c807040d40c0440e06450030601031000c00005012107446410360b0040740d10a024643c0041b44801480c14012844d09010390115200c0d030301d82101742c2c04584a44040da80d95501c0100c1a03811160900085a400c1c0c80b0203201981c06031500b820001000541034043c401d640c81556103c09a50311801415615469809a0b074041924400200c0340d05042c07442c01a44a05c000e800428141c040e90703101d036038001c2c40001d80102651140d404200c3e042c0e040180c00c03075000c1540d0040140001c4c1100281d1200c0041c068621150001024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 768750035 1250 768748785 768748787
    0xd0206120411060a020102070b0112080417010204080604062315040c02010b04140405060709050d0b0603010e010e01050106030c0e060304111512042901050603060a0b032a040b0406050a 81
    0x600b20b18035201815007030341d42c80c41082c000d00079400f81034126840c40f6418008a041c0d040c80b01c1001891303500060301032520781018800404411000148404c0d51340801c0081010141488410300403489030717a0104110400348201c202040b03000360340e80006c541480070858001405202034560200a5070005107525902030124058440f04202030b410500b000340072100200c40300256072240307000f08140c1e013580c2c0740e041040710100c840340315543d0b203c0702440d034042c0825140e880c681d4100500074000103024848a0005d0700b5564444841c540c1655600010400039415008d644036030360386e030724050884056280000b0094000904058041a105000c1c1552521102a8100904004612a601c421a400080c3d0940c18100c40455803d07621202c410380b690415078064200000709680010030340c0c02e100501c842a0401407005510000d042400210084204000d6000340607a9114400c0354403940c0c4000603035103806482d40d04d100c200700000c200110b0280300341d41c2a9505032800913501c0c851008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 768751285 1250 768750035 768750053
    0x240f020106030b18010c0503161803020d06050106080606070c1202040216051b091e0405030d090b0a0b0303090a0303141e0702030c010305130807231b0d02061204 71
    0x8020b0800000000b4800b20800601c0c65120028145000b402004451842100e09010984103030005142524050341d0b49d500810480d24516014440d104146503640c0000d54120406001a00c1080d170382d90041c81510b600c2500187d11020940d00c40d454118542d07038142c000c0900348074590045e07024a42407011035035a901100d2000440c00140d030503100c49400c1c134075120441d84400113103900041c40941000d080c01103a892256680c1d000c02035030240d915407502c20605009100b00c90600041018822a10f040d02c038443c5818007543c8080d07550310301101c03407900300c07058044201d201e42d00c2848180301ea9911180d50702e083e00e0707051a1120b01105800206101d501582c0881c4040c4212040407082a04107a405002e01c00c1c0206d0869404000840056048503025a6209000035154101d0004101d1060050042912903101405500da059041c008003100386c81002030380d5085041495416042502c2600c10320200f220100d8005c00c0b2540018020300c511144005400c0c9050005010711000398 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 768752535 1250 768751285 768751289
    0x8030919120804080106080a0c0b0a120c09090501080f061807050a0b0a03050612190201140a0c050d08090c092710150810050402030a0c0f0906240f020106 68
    0x840e014020300c06882c0c00d51554000c0e002d404d40c20340c60803500040d0107900003075400150360855000100036091a0005c5010741c01021000d05000300c01c0200303c0361449500c40c1c0c001001e800c0e9140d4000e141450480c07070540b85c041c0c3c8010001d13404801c0304c200c586008610030b600710411603915100916015201400c0000c240d01190703018022682c001101c503040ea00500745001c0039641044196528010403008008107400100c0c0d503444205480031001210744d50f1008c26005040443c8502030a0200b18807036480300310030308002030f8410000000c0081c01c00990481e14030906003040300c0d25044102642c2c0e10100c00d81c4134800c90008000c241880d01240003e40300c41c0c3c548041c00e040d05014a0620340d00c6155040c00c000d0289498070540301e0410b01c15050040d9414440540801202c081480b006800b003e04140da150103004004070004040480280040681416500e01c0030710300715910040381d282d540140d600d0b615031180f4000e5000405245450f4084909062610038074040d001c0b40140815 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768753785 1250 768752535 768752549
    0xb0316110f0f06010315020703020a0602090a050a1410050c1b13050a05070e0d0209040b04061506030504060c030e061612020d020c010f020c03120415050115090501080108030919 78
    0x210321070500c0c02c40403425a05890003401c9500300e0000316040541284501400680143c000e100ca07030f0005210342c0c00a104000c1c0c02003c80c0e00b4961600009040c4801c1c907401546c155074142c840e290b960038103450001d4030040d01e04141d8140042543d4042e00c40b0405001c2c0040d0701c89404200410365152480389003800d00380d4208004614148605000070401980c444003c40d208088564491600400c5c100b41d081c1c0c05812030080b6110b41d51403500c5664081e004507030343c1d5228030b0b0b841c071001d1340840c3d11300090045070b50105050030a41413043c2102d0f80d0005000c00c044c1003000719500000d0003d80c05400c10b20440c0507038030407089208100c40c51101c1300c0140300c0c01400001d901044882c1078000e044121441000bc016009032006407a08900c1044419402070f04140442c4401d0000e5500d200c1e80140030f042c980030864040b24008080343d001740c01a4032a900f07400b14802c06142c0c0072070a40c003e42030031308000c4215414402c14503600d0294000d045c1c03040c00e000d9000c40c125107200a0500042c500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 768755035 1250 768753785 768753793
    0x1b0901091503060c050c0c030601060507150603021906090b090d020d03171005011202041a03070e030a03120506030f0c04020702130e030714070501120c0201090c030c08070b0316110f 80
    0x3c2800040c10366010104210451144000347c00b003074903001c0303107007812544180c440c581f82440550710341a0130000210101c1c603039503035200b0000244e1524944140840c80d00e01051403141d05004028146a0490b008540c0290701840004015198444500d44251b01110603003c00c46142c83c00315540c04102160030a03014001043c8080d48c10011040c50a032007098894a030780c289564000700c1240514450750310316541c50505444256554401560004d0305807034060b16283d400d0000c03903c0c00e510a4012000034426209403c9130811511904d50040800c9001d01104140600f20380ea036111400e144500c525030014810046503a0201902d20040c01c903802406074410042c1e5094890700180800d840e1800078080340440c075840440d42d1400da54050311182c40000f5441d0004008105003100401559a030751190303008280b100030b9100080d1720401c051142d49081c1500141400043e0744500e000b40c0c0180140610720703113402303018031034038405180c0341140f00700d154000780c13500c80120085c11032805 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 768756285 1250 768755035 768755051
    0xc10051c0906051803132616050109140a0504020a03020d180215071e0201051209010b040e030403050604110609060f0c16030503031609090c0e031b090109150306 71
    0x3000d500018032540c0d1300c41c032800c1c0b80c1501804c001c0c1c0300e100e4446149200b1014540600c80c8040c0c9240540000842c20038108950b9085403c0e545019040548080c01c00b0726128200100e44c0d01092030409000e000101c0d486060070030703010030410380b41030164604c5150045602c00e8020b2007503041d07071024031481c2030a012002d1400e00b0807101d404072000aa00a403120300c088061903000e0310031900f100b030303000075242018070b15001c111b20048803125080341007103010005203070310ba02c529145a0240d000381000117079a0b60180100011103607060300402294005000400104201003155913005400c81c100c004080501e00005a007441400c10030f55200001007101030a0b00030083c0030b025602c040380300300c40d92410703008448501e5451503c0000c105510420001e405c054a40d80f0310014440382d13050104005441d02e803004150b8440c00c0c08003000815141e42c003c01c500d010407000010413402a800395500c591800030035103942050044c0c100003600c64100d4030500c2c4181c28628021604454200300d145 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 768757535 1250 768756285 768756293
    0x606161709041d1002130b07050a0204091a090607020c12010908070803071218060c110d05090102070905070c0206070c0e1e0a0605031b12031b0f0c10051c09 69
    0x180280081c0f481c140324429900205405070b200f00c8502d220039841c0e080d112031030032030351082d9a44088422211800fa900104005072030ba8000c0441c42d5104644019140010410b0390b07107001d20007040280d895100f0018004aa0303004184c034601c00c00107549450441e0101080d0a0250a5441000348480030005102c02440300351f0002c3c5026255030394802045030f0405002c5000e035008280000f91441011024800055a55000369101030450401308006854103403003904040d0004c100001103a80020000055a8107008130340140c15541c00400403401c14040040080202407402801518000340c0e50080c0000445540010030342c1c80b4142036036207082004407840c3c542d41c800c60144000d0075808200c107034420380500c8055403c064020120300190000243d2151454898290000d21180c0c14507141281400100751f100600d007040100c07586541581ca107440c4a071244040035400095440445071384a201100642b07020b8580961150144100c00c05010000d10b0325501071440d00521400b04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 768758785 1250 768757535 768757571
    0x7050f070f09060803030a18060507030c030c030e0703080a020f030412030e062d041d2521060e0a0f06050a2612030703090b060616170904 61
    0x614071011003500081c0d61a0210016150f26000c1c80385203030403c0c40011034243c0b450340180902c064400640d0728145080c5c5412007264002d448400c00079171280f44528105406000e5507400741e8061a00b04108940001015142d140c0e500004103c0540041e40c070455038400c10110485071072110540b603585070340b1800c07100d540070004811004244480a2052285072050550f03402a0200404002c54000e20960001040ca5400503030420348040c00041600c0000781c21781d40c411f44880307200c65118100281a41c0c140980703211140b0040748c040d00d1080340389034030400c00002c8000080c00142e801d2842b540700f80281111340c1151807580b0000003044440085c0350040302c42a5004e07072042040f551107100740441e08005008010f58070340a49540070b100c4042140f80d4041c1c000301005d1300c6100c1c46260b05058198400e942620000b0348600d074882c01c0c0b041865502c0d80011049640c00e1400d1114100240039041c0c0304005802da80101044090200001c0c1c2221015003008008210108582145101d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 768760035 1250 768758785 768758789
    0x30f0813061718061302150a02010f0f02070c031205210a0c1e12060b07080403050f030711010c060b2808031602060a020106030836010909090807050f07 67
    0x5103188440070503a400c40c14180186180040ca01800881e039404d4182800e00c119407004a03046903107881c145581c0c3d447d0f503000c3e244010721135001041d0801800c106000b0344006c2003241c000c0c3c0348100f01001c0003800185401c4200c80c2d005403d020b150800b070a058550340207a142c00108900701d4099070100c10b00c42941c00d4820030301c28500704020000744004691080e01c8030010803070b0142d1a1044d030003590252108900c01461060003040854a881103118180c010f40d60031101d03414042004c2c0200302052010700d8480b05080011414903c00b510391012202c10741d424103040c082d100b4541001d201c0160031641098101030500201e9004214180c4900110746c0e0f0a6110b0804042000c209140048115564000c1010101103800c9207a000c0202640c000d10001081d0f40d41c80c0400000600820003401c0c00250340d142c2c1c00344003c44810501c20440343c0d00d680c04000c40416042002c281c1e0004015015540304040004444000d403030b2011003031103114406402480f0b0305440f1110b80600054000c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 768761285 1250 768760035 768760067
    0x204020316031505101202040801060b090a0801290d060e0f150411060c28030f020c01120507110f06090f2a0604031505060f06040807030f081306 64
    0x10807001107034900581c160f60b003e0250702c05200c0c200c8500952096480c1040700700d09200041c40c045d40e80c0d591608403001d59108407a84003000c40c0000c0107180201004009184020007401045072010348032010503003c0218040c600c0104804007015224010088406540b06034100000090002550703076941e00350241d894203104108600e0f2980c4221921140155409100411600851001c01071340360001901e001c450b220b00c00700c2000f00824140040500206800e80300c038030710001e04004100281154050b001d41d8050003030130340d00c1d9902010440c2c03000801500060a61035041d0201c030488140452104103110382da44503c100080440c01034068503200044030300303210a42d12455203030400035580ea10410f1110142c20495410b4842007168100c004103507034501522541c6030410100821100e41741a9651010480141415000307510903240c120b5400c0e00b070914146410340d42c0d085074080100f000030128108800c0006e92015540c04840d449444413f40381c03a2003000b84a0748080c26021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 768762535 1250 768761285 768761291
    0x1030b06030d02030706050903160305030412030227031c030e15061c0606030b01090903030c02010e0d05090a0504093c02121204181d060103021c020402031603 70
    0x2000c40c03800081d4803410503001d030055801c0200c25280d038001021f00400d1000580010401c1f161520340281f00d081034240b0076150300c0c1d02e030308190410441c101d4080a4044c2072500c1041042c90b414a0105c82c045070a45c1a41e001141c020480c010a0804480503407422500083c2440484443c1e090340042d0200e01c0321500310780c01a00c401c102c5041c0c501d0113544654102004500b5026628852002026000d0007030f400812256901e68540010761401d90102e09800e6583c84103204043d818091144601d03a507100034050350801a001540743c40380c4211140a00000080c04503407034441a01c82c0006000041c000c01140c0c2042c00c043c001c100d814540007043c00c0241b07a0704090041e80000c50200c000030400309001d41d01e981d81c24040304101c11040041c05103d80c840f8243c1c1011389200a1000e040c0444400745402402c2160205441610000030400d1b8601c00840c0103040000540c6c9044036011160100c0d42544050004807100203000040d4100740000204090100d080d44482410f5419540030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 768763785 1250 768762535 768762541
    0x1b0f2909011403130f1a090708070b1e03010312080a1a0f01050d0f021b0a02091f09020403050d0f030e1005090f0a0c15090b09010f050903060f01030b 66
    0x14024a11480d03956901103240741c03040140c1c0d0101580610303030010300010303900311207030607a01c401d60b9a040d48903040310001d500041c26030910039072840c00c58000c3c4285000300702e1030b42030150704c5449842500540780212000f00340d00c100401032031710711704011038038461450f42c9585a003060b042c40211141c030311011800d03c40200e000030040307101d5035403441011030a980d2040c0d100410420101040500b00381041703000d2103111441e140510441000021401d401070b235501444102041c580c40d4008802c440b44c003d0010310000da00c0d440c0160740c2c403440d5820344400542000c0310790060704005400110301c0038800300f000b004202c130003c0c4c0e12070b404146844c0c02008943d8910708406030380b9400c03008a07041e00308800002030565650040da80001c02e940907103c031145614421072802c3d401d031034143c502450441040004120304040008440040e213048a54141094044086803283e1034070350303042000c0c4196400c1024801d8065a140f890028160380356800c2a209100c1144400c3c0019a00c0f10001004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 768765035 1250 768763785 768763859
    0x409050f060102160f140f0612060306010504020f031602070f0e01030512030405150402060432030325050a020a0e06030c0a080a1e060c05280c1b0f 65
    0x1300d00071550080301c2030700700c0c500b4101e00e6040e2000f0300c0103103500003046150780303500c955595020b4015a507080c2d02d400c5031440c0c014105481c007039041e803006015920401645540d60b2001c811254490400001e01000f44402a41207203846200c1d400800c80c91840360340854140005180c040c1240d0080007100e0342d01038240084200d41c48152001007260b4410034a541494540242841d07100d80001c014a08040e500c050035004204450303248440396442c007408105c00d086488451070f402c0c070181c1c0254107121651010300501c407141802d0f1300080120100c0802008000c010b003082480d409845103000581d03685a000d410300080d10310714468003440d14003020f00d05201e844c100c115102d040082107108403030340f02c0c40c036252035401003150840c4040e800c003004a1014052496080304030f42d0f949a0710308241c5500341d6141201025072000d80700a03503407100300c1c81c0c0c00209408400d801c400384001003d400c000f085907074401984000c0400c11080c0c0c0015001003402c00303440000c0040c1c84140c218002d2005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 768766285 1250 768765035 768765073
    0x180a080a03170c1c06050306090d030501081b0904060605150c0f0a0b0c0a030b060711330918091c1107090903051e04170d0c0204050703020409050f060102 68
    0xd91520483c80900070440407052070780c10591082d1440c0b4001402c9a2680301180c200041100e100b00300e0392042d68a440c903030354107200300c41c0101070703c2026020000c1100603844030851700c4c2c58418414003200340414140021540301c1c600418000303040c183c3d0542403460f846d20301c0d0480100c0c4503480c0600202c4201144001c50107140b00d90740101d01d94000c0c0c3c7e074445250340c0c07038000082000c20960303284090110358841c10024402e2500417000b41e031200c80e0400c00c101620f001088002103040b000e08081515021081c00d403038800700440c0499403181401c0380491004001003185102c0754080d4000e02c2400d94010540c0d00c0d104140030b400c44070142080c101614010a100c2a54590742c0c040707003041140c84100e40c46003042503ca443e0403407030310b00622100729040c012408180c4020b07800107010000000143e4000f40340554000151200a070102d4016101440301c00000c0d008507100c4c00007603c10f501c264120340150102101c10842410000c3d020740c285103007100c119025110b45c0c6a40301805c0d034040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 768767535 1250 768766285 768766291
    0x140a09180e0616180801090605060d0c21021819111204020a031a070e010f0203090f060c011805010c030203010e0117030d1803090b0c030f180a080a0317 67
    0x140148203a4650308140d1180d41907066011007000074241044201c41e080911590041c80c5c840004038015100341000000c4403405045144200ca04990101c00160003000034401c460100391042e000c0b0300a9840d480c1c14106590300254001c0e481c05914a0603680468841d006010202890481010071403c10046541003000c00111a000744002000381c0d40401d001da5010744050074400000d0384d04d07070711202d45d00000c0803070040030100903080220300d540c000c13103000300341000340703007811000c0903095019440b03201d26442d103405018000e11011568403014215490300b55801c00030000c0f12600ca03249a4030030921102100c2c15420649004000e500c03c1c0241c9060340d40504580003564a001800c04803402030012186c00d501003448002201840d520420240d03400c070600c0c0904030780c900c2ca00181101d001d904a03004803d0144160042e0140c00000e960301d218506040070b039116030300f0040b44400e0011070305e80c5500c03a02e621404100f2142c04604503056500c81e4070b81032440004240c160000c00011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 768768785 1250 768767535 768767561
    0x5070e13080c011b02031213020d080c120f09040f02090907120e0a030e010215010b0a0c0804050a080a1b051c020612040c29030c0a140a0918 62
    0x200c0e4080410000d00c010010802c100e0b00004844500702c01c0c1042010141c550a00960030100c2c510900440441d076155205a404414035a035250950014814092620028028010105040300d690008105004040b9180d040c50340d150401098900c1060b48101c002c0e40c02203080c40300140c2c02071414003c1d0740f00200010226001da980340c0b80119202482e0780c1c04001e43c00d861f01e185001c07241c401d1102c41c0b1241d010b40d84020849400d0340019140c103202042d08d40c804090744004000700da0340e010641f00d0700b817003030f00c0c1c0034410320514280030781e06014680040c0d40c0300e02d600350001941600000c0e61014a44a0058902c40701c0c2c2c1100300705504000c3c0c1c49503c2e00115161442803050b81c00384c4c0c05003a49131005120509203180101e600030000e02c101e5084811541902c010b1040c0302103040c1c0209911200b407440300c0d82c0c0c125002d06083c1808050035680801358041041641240982e5540c1c800c1d59160700300a4070b400c00c03454028000409403103811000c0d8441c8032205410030705402800a11580f07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 768770035 1250 768768785 768768811
    0x18060e040f03030209150301030503070201030e0610290c07080705150d0f020c031303030206090307021e030307120306031208060d0f020a050607112e05070c090903050705070e 77
    0x105480c2907002c3e41c08411703401e030f0010503500c2480b501d207003443c091806503005400540d10703000244009130490709030003010407c0741d1003941041074280321111440180c03444000c4295601e43c62a0300302c540c100081c210090541c101150708043c141002504400b1a56424100d45d025661030052000d41c0d141102d040501f50742c1041680b07254400354000001040200a00520b08213034850150b0070b40d044049105154055000108103241d410002543c1186180d0301452801a02c1d6001415800003003854101d03005101500c64001e82d07040c42910100f5403c112200355400e0581750080080c070581c0012510741c3e01d00b45c0c501c10000d00c2020014403a00002d0800c0071250a5901c03074481003001481c00301c1e0320501420300401c0c3c0780c03500800fa1910521a00340940300b581c0e00700030004030ac0c0f51644c41094113511a18804940320b2140c6e203000d1415513506080341d41d010302c0d090208203400150420368000342004146e0b020140c1c020020011940204140c8000544400c086845000191414201142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 768771285 1250 768770035 768770063
    0x10206010e07050d060305010203160e0f0909030928090c20070f091514030c10030f09080913050c0306060d0b090103030e190302060a0807020a05060118060e04 70
    0x201c00c240d0940180e0a401d1075401c00192241c8401a1240c9170012a0581d401000740a600380320341610340f40c5104242400c0f091120541e0101d0b9541c138800c18a40c0c414080d10002c0340700070b6810b00480d00001030203001c149407181e09401880c111080401d614504001d0600001040d110350b1003080110f00e140d0b80c5403031400c100040c0800d0394003002942e44100e4080e042002070203175a61a010001041c034044040f13100c441800c121204250715038411400010681021240c981d00481e160144510454181c0b1401725011070441c000c1c1850805241e403180b500c02c001040c4800c01e8080e205804d000c840e030b00742c2412000044c500b9240c0c161000c542003030090001c40c829142003009465100c1103808002240c41c2450009408544280d000780d0100d10040040d4130941010790800340048a14003001241c2c0e0f1959022442600c0340c45040d00c100040f0a000c01e9903a4428000142550b800604413884c558440c40000c420b405803400c400e02c10b03482d0102c00203814444101d0903102d940c0010280340014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 768772535 1250 768771285 768771299
    0x15030d050c100b060903070609170102090d03230403060501050405130201020706050a23040306291e1e040612030503011505090d1103010c0302040b0d1a12010203090d0c0201020601 79
    0xca5110150b04c14400d1100c0c0750140c5041000350b0042c01b16039201c3c808103144c407602c91264050000c4031f019a03401044944629210100100d52090741440c22681041c3d9866070700100e5008910207030383e40c00e40090000284591a007121341610710840701000292130308280d9258040c507400c0000e01682246c0410003850340200013820809645061011030404614a40c144d1401d03441049051504041028800d01501c1c2c4503c0c860801200900e4205180e446100c0c040050012a07c42c441c04108080c8008502c8648503070b44603101c040c04030709218100c0e0801111001e10350990501561800100280c2802f501000d0691181c1548549182d40d0030004940005003038111141c0901c9000c0003501c5da961650b12021030b03c50b00841500201144c0d00e4205801d51326010106407c01d80103100510440060004880c050452107900199040e15421451440c00c1211550399122215540c0c24880c988103400840c07081c10b106080e2144c2d04500a0103640c4140c2c0b0100190040c2e1203280140108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 768773785 1250 768772535 768772541
    0x2040321120e0f07050d031e030b0d0f06050606090a06050904091211010c140a0e030c031002040305010e01020c060402062b06030b07030b060a052115030d050c10 71
    0x940901d14218962952407040c00c0140c0b0070120720402c1a0b4405604075400010600c80d903405410100d07610f00080c000c40c1c50080000311408212940391000351203100c002030090307002d03500c0c00801412002107401d85091141e0001e84684040c0c0d00c1e00e0804001075854a0408100c072110b81c802826800868100202100c0d581c1200140075049036890012002056401c101e07820b458100d6034034034200c240c590350344501303681502900800748540c44809016a00340071b030036144103049500d0300480d001400740c00a80b80142c160006509402410022400c00706950010015a03010f130340203110200d41030050314200d00c00c0080904003074204c07001140062070501c00802d01100c02c80201014001c1c0343c000d43c41e00030391491948110726038440b800c0003000480300905a00585a0408001030640304000ca401882400c00f00f01c1044030009180c501d0404104030b0504140e000c0c80c42000302e16003c000701502030018405640300303108441070000303214810700484100f903a022014054080f1004e5964001e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 768775035 1250 768773785 768773843
    0x3020706060f0e04050d051207081e151002060112111203040803070c060c03020729180a1208070206030a11120a06080d05030c030a0204050a14040b04020403 69
    0x100c241c681c0c6000545885400001c40508441c460301112401d19242541c500380b800100d03101488000d00490044200401d440f9600c1410313800e02482c6036403001000802c2d02500001040c4588122050010300440d4003000386c0d054005850072000200011000d0740d969900b481829840551501d0380000655103000760031240e080a05003c1d641c1d145d0340805400c1d42c0041c0c00030102c070b03840441d41c1c0060002e131030381c20f1000b44082d042c100280c03902610002d4076114980503464018442d861980140e5414404200c548001c5d01000c5031207003041c404100003880300800203880b603002c600703012500c0d0450322500c0314503607444500f880c9008015424031069230002466900034680d210302c0041c401c01c0f41001032000c4054105081c459207840003840f403c444482d00280a82ea01c864001c00340d050300407044907081f104004003192240e55602d0098040d100d10340006802803040800042d020389400b044000e648800c4405010004041062200320300403480007070070801c0d141030201e2035151003608201d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 768776285 1250 768775035 768775043
    0x301270503070804140103050a0c05070605070219080921030417120f0c070b18010507020411072d021302090307050a0803120603032107231c09080406030207 69
    0x42051815100c850300c54116500421902445d0710b007403105580e061080302da020041c99000c000300d00d014440140180200b44000348401e13603420120b2100303170003041ba101e44284c1002c103400200c1802d1411011607000008668020b9034407801c5e514040d503680c14040c13070f4401400300943c00c10b803504000d51840e601880300c0221600600c06243e0030300c22120020400c1d03da8222105654500c00c407425071802410707500c100c110110920901c01d11842e884100c001f00c3c502440d09945400550001800030303c2c1d981c0c04842805800189601001290842d2415440705080b080c40c11050b00b02d544120b10a00c0200254081c10000850050420507805030600744009030846a03a2038483c1c0c0400d4240e900c94014641701e50012954100c840d8002c1645a4422001d502841c00c00c1c00590f210114003212200c900c03111948000010070071445100450800c03880e0708800756010190341114007032036029002158241440452004918040780a501c581c117900004e5540752034a0844100d000750091a8116 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 768777535 1250 768776285 768776287
    0x12071410090803040e0601120e07090e010f1d06160203030a0504081e0423090c09032104060813020a09051801020f030a050601090803030a1109120c09060301270503 72
    0x2c01c0b412000c1010700044c2c05034644940c0070b41400800540380c58110803042c00f14509103580c0040c4507038042100421500700c1000481e4a10320419518058061842c10740310319450044802d01c00c0c00c0e0b0161035006083da040c00e940d8070f0b4403041c0e56407415030303040100301000d64003c2020504101c5030f86d202d194014040c0003044d04284459404480d42d0031500790580d05448089014480114012030b12032401285485400100340030002040034082c0044c80d5142ca002c011840026644050040384284080c2901d080043d80115150700101c0e045030040800284104000ad1aa6080022120002a0014141c4030041d01d044e80d1107028003401046084000072480b03021802d2038007400a410445003071001141c692401550030021200000c008504005484804021143c07010084a40103601c0c80307030114480c1c00084958031640301c1c1c0810f8a0700b01640c0035840c51075035000309418140140485544c0c3c0315450b14002c040c2a00c5802c0081c1004078800e00d1901c96410b041c1c2c0e0300703000b0310380310340152 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 768778785 1250 768777535 768777539
    0x60608090a11220e07030203010f06060c1e08030c030a050a02120a050703060b07050318040510291b0705040b0609010309050a0b010305060702010606020a0c03020105031f0b091207141009 82
    0x100f000e072200700000702d10640c0800018400c5140130300802426039413110003007241610303040005248421036040903014400c0d22036044030088820802010503904000c00782d0307980c200340e25044c481c0e90044071240b401c985420081003040341980200d400e0403180c440c202903a616501d044400903c0083d2209051523504c420003d400944480038100050288001d152225800075a241e105c02d04900010312551030708007003045070a400d00d004001c0d24407652480b800c2000000e07002c024040c007620307000680d100100d0109100040d0054152922880d042540d86240d0f5501c280300590381e04040080d1300c00001d001c0d07046254402d0b030101201c18041e004580c041143c5803100b0240800a810584072500164100700e1155024000c0030010714091004210045550b21601d07030340d00b1b5a01000341005000000b0a00311001c109000b40c0c40142c1030383e6005030b29515411030a59511415500d40100c204d43e0359024540030124480003260800c10014408920f0b040c02c00ca5691050310703501040c01110900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 768780035 1250 768778785 768778849
    0xe03160602030d0f050106020303240303180310090b150a05040f02220b1b030d0e06010519210f12020c09280f0207060e01060608090a11 60
    0x411801855150080c41e80c0e8000040d2500940d50209444940b0605160041161660000480e0f074450868150052540025941020740480b424540f0707616100128080e60742c44c290301e001c1800076900318116000d140e440c86400d02510180c42c8050075064502002030a042080c64400103c000700405250001d515000020200e0342c1803100d400c0040c0c0d010a02410f09200c5003981c540c803c0210007078150061402040c2c0000b44601c4510410243c446540d05c10400c81c200140c03182414205810302c040e08070503000d00d41d40c003400d109a078821142001c2214404031445030794000da407c9803081c2c0c1e0000f0380d60904600d0002824008481d40f0f02c4d0383d0140804102c1104510b4001030855014102c02c150900401c02c1400000e048041100c0103000364500344449554520105e5040000220307452403c444060300034002c03803c000e02201d0828058010b80f1106501c2402a50001d840e81011030300c840c040e596454159900c02001e44240c814031040514201d0064480c0041c02100d944121010107030f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 768781285 1250 768780035 768780073
    0xa02060301180c053603030c160501031e2c1b10021005220803010f060f0503040f0f12020105071409010914031203131217070e03 57
    0x2104842c00c20814a6850b0060000d00406118000c14035140e82080161400ca01144407044001290b0346164082141191900400844403d400030196a260510b600d0f80d26190888240c80401100307000c40f0101c0c081d80688502d8801001c804000c030b00e10010103180e200180805203150403801200f855008841c1c03445180c4030031105889001e0215460301615400b04030150030034451164540500343e0004550005030401c00c501e00660114484d140c0c0c942c048040c00400140b010098040520030091010140c01141283c1e01e00c85c0080c2c1c110b0741c9190490301c0113041d5090000042e402c00221340451040a0440003150080411232140110756030781c18250220b00b540000541d45407030401440c10340043c01c50744a0024502094604143d5400003030000321580035060450381f10f600c1d141080d881c100812112000e04901c540e81d01c1c2040403540740600551031040f111400c443d401510000e10544489014400c2d4201080c041d444c1c60106031450b08240003c1509481000004844020288 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 768782535 1250 768781285 768781289
    0x1a0d0e0c0a0b04140307060e19241d06030c031b043203030a03021c09060914070609050f040e060103200916030e1006060f030f0b030a140a02060301 65
    0x1424140e645103020051113503015840d8000d4403940042c1030802c9215049482480c1c203460494841381e4010714100310003000b603225001480e0100000c1c2e444a81e1410290f410403030000c42c0c0c2c071081b8402038000f200100c2044190205500107505101003560841e9441c040c50b0480e004407100130541e100941d42401c10380107644054a00c0c0d041c004958040801843c03c404071030300c1d4840c4011500008400300703590303101d401500303400c00da40000c10a120441ca81100d0046042840c410b10220f0028140880079003000c24042d030b0440f00d069541c54018600003506011251281c583c0c505491514080010f402c08003410340707806c285c460840000d1031078188007035400b842c4654050341c0c8018407031a211003500e11301d0030000d0042d5400c3e418000060001214108042c04a240104000181c00d5045081c4451038140c180d1060400f031001c00c2142e08401038008011072990100000c050041b0320702c06541e03440242c01d8158102011f1315000c640c2c501c1e08041545048000c0791040d403000c2d03004c138199600036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 768783785 1250 768782535 768782549
    0x303091011250303030b010503100302011b06090606081213060c0309081507020c010c03080c070305040302030a06140f1303080402150d1a0105030403021b130e0c01091a0d0e0c0a 78
    0x30b40803e104254040c402c01d8000e400038a05070f4103500d0490850610341c2014000a41801002c003401302c44085094502c103003041d4400740c1840101e040d4035090025000f280070300b51580c09211800810340d4001303005e440e0000b240da00045100c620303000090716001076540090701000319062000c22901c604205034207080c140b02050006919008100a0030040c0c1000c0141c101b2040c2986540400d03030080d500da0300314034141146d55686840c4c0c5001d441c2849030390b00082d0940a0420b204007800400e510034804803500c00b04d41e14036640c0d0f044682020900485104540080385a016004a88074080d0550300c10300c00341c860320b02d07a01d07010002035403a084030844008440d29555410348bc0003482284040b0110282025030450502d950041c2d1154001c03420328401451003141d40409540780e4403100311035141c40c4000c2145e511065201c980b10140c50f041640890618140014100c0a03500d000590700130f01c004003070619030b0740085800580175040c1c40854511603181e0b400d4281d6a460038000082c02c81c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 768785035 1250 768783785 768783853
    0x16032904060b0a0914040605040e03071109041a060d0b090c0a050402040305120f161505100e0a0c090317130e06011e0c050105240303091011 62
    0x1548081000340c8006030000c800b0316505202034045590041128020707100134000420102c11401c000c50014101030b8499a070090030085552003100010008098444c01540d03010003035645001400640d1b40706690090202c81d290404c003080f42480540c598000400400031088180c054542110020080d00e405119401104884000f46008145403005000c10b807000d40c00d051449d03c4664848040c400480010000000c0d0101d019000783d08943c01c1e03112000308150380c1d0800303040c140020750741c9828000d0014a0100170a130710b112442c080070704541043c5c0c0c281f61541d55000703401c0c0140010518040611054443c003100141c0304200081404003902122030312052000d4095010540300e0b4404880100404140301050741d20040390a144046807621900013199150100d641c00a030302e5024050b5460710042c40198569030040140f000044038203502c00c4010a0209522441503d10496204070444072042c4170074020084141041114010303200070804080301a140d862144600303910506c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 768786285 1250 768785035 768785111
    0xd0f1a010503101a0f01020330011d0c18040f050406050f0403090b031b0a111b0a090b060705191208070e191e1409040305031603 57
    0x40822050f0101e60380c0807014410101e00f541000c090741c00c8030040798014002c985040244c0d034000c00450395030b00c408620f488441c1030325044082c0c031001d0041c6520745440d200400043c140d8400f10060313007007015190300e8030760b561101c02182c101070f800448403a001c1400d180c207103078207941c80e44140a03002c41c040002040ca40380501e00001240c000920903c2000034007020321002c00d070b2000c030f1201a61114141c2a55a0b200c001e401070040c01807080d0480220030000b0a41d074101d9001c2540e00407900b0050440d09564a4201d41c0c0303c1c2c041c3c0281850703421420240040000c2c000a0700070915001c00900040d16048036078486074108450b04400c1d205210458001104002e0215407a4825403054a8060058144200c0080c516000b080030944180c6280a0030280036503070f00044402400c0c0d0401c0302901030b100904034401e81c0c03054400c2052030703a200c0c08105110300344064a80d11450b80340d550315195650f03049154001c3c40c10118035404265850840607007164604080e07040348481200c0d0b08a2005c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 768787535 1250 768786285 768786289
    0x1009080105010e010e0a05070e060c0a170f090d0627031d0a0306050604060f0f06020609010e030708070f020604231e01030905010e1207030f05070f020d0f1a0105 71
    0x240c1c103a10000d050044000104962415121059084601703d480811261140303030301200c01d01030a08034541c3c041000a10074000b4207001400200c0c05100380e0019540740b0000400701080d000d002280040700d203003040036001f280b81500c8900c8119204410000340300c0308844c0f070a03101c035000f41e4403040003203801402c4105040d00400c03c90116118170700c030b4140442100f00031490f142c400f448010511502c0d000031134420341e03551700301c000600007410442200341d99a26905d40301410902c21b06000d409044049140400103009400c00000304800139407034a1010303911807200f5440524150b400f02c0c810a00400182c0e6070034001c000070010812014034500c8516039a070364040c140c1d0507051041c80d00341a14a0140786024001c0754020303007402c000440480c6820300502500390040c0104690007402410390b1000a1000502901c81c026510035401040f40541070303400344112030002d80344054002e0701d00c005103043c80340f4004481c031030246003400030b0856a0380401d41c820340c3c081600e1403940700c005120038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 768788785 1250 768787535 768787541
    0xd0b1302071a0a0b0d1106120f1f03020307050910090f0b01091d0a15080709020a170705031b0904020a090e09010902060d02070c0b030f04060506060306060a0e0f10090801 75
    0x40450450b00304038440e0804c002400c40b500c0307642c005010105426131140300742d03500010385507840f4180c248901d07070389424030707003048a99411145840b008041c5001c00c00c101105445510550fa07001d070007406050b00346806c0101405c40208070500c070107601203010500320b201d400b4940c08050401400310760055644009003402620360020448045c0200e00d440c0c1511905040d42e80244888000254091500300c000280700d1454112240344d21410381d0010b80f04e05964001c00f88204139564110300c450044503080001c481c2234400700c00050341030003c52002d407001107003072103203014850401c3d10301003564000c6400e0313070440d00c425400703e10448410004048050340055110180400800c02006681c1c009030290103049030000401ea8003064003000c00c04d0380d50307a40c1d002d041c04a040940780d1a00b03080d441d203440b8049a0484a040c204404036000e810140203881c0544402400e0390704040740e0400440d00c150301030311030f10b5001103a01c00c030034103035158400055a280120350310754510300e062440460035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 768790035 1250 768788785 768788791
    0x9010e0312150d03020d08071814090c040f06180302210106061107031b080a0f12020a0201080703230901090311121b0307080d02071a07050d0b1302071a 67
    0x1500300050000010707502082805141406047c5250280c44072101201d601342401219070380e031000b1000c003068140c5040d85618013a1022202196030b503942407c21107a9000e030303101b041419003480100744146800707242c180318a01a20b100c544000c2e42c0d65000940c4070042d299126800b02c50858601d00001c000380252400381c0b4007800c00c0800e0b50410b02100303503103806a100c090030806100000312a8001d00d0402d50004000a40403204035005030305226904003800c3d102100e04e0030a01d40d061104070700101d03202d40840c1d0140c4541000e9a40c01d4007e502a0159500f9820030381d880340c00c000d040c1c0c01e04451a07401018070000000c2c6180aa240142c002d840010f0207220700d030301800d18a103070201041708550502401c02030940c07a803030707086030558514008e07810004e0511601060400100241d41e001d01000342c000d000d103160074000f546100c0311300c7d03c060b21208001881045000c2d050801074020703c40d04074000d41050100ca042d540400200d8200f402e0850780b203440034200051139050141100c0e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 768791285 1250 768790035 768790039
    0xb03011a101e0c02010512010605130816050f0d050a06020a090503011a150c0105010b281d03030f07060b0a050102030a0203190e19031e020d0b09010e031215 69
    0x203000410002200700021400742c0c100810084038101030441e4481c40a44000c400d130122606003c4d40c68200107400c5805c4410704d9020750754081c0d0000742d81e0100248116818a00042c070203142810901481103080000708915001148141d0700030020f1020059002250700800340140c0362108514002c00c005081e43c0214441c3e81080241075100e4408015184040c100300e07a614203020400c02c00c0368290042c1020b600d615441c20000040341285140200818180e070100c1d042140e0a10301c10520b5080b40307805480010340e06806c2460410b01c3c42e55241c030b141e0801000ca9040412443c4205455400075034102c030403588510001001c0e00f044921354014100900185062041081009669000c0c00040540703000d04421114041806100b8081e64424080c1c40075824680d4490340404002e16480201d991070705a4406901c005400c0c1c65204600364010301450448050340c0301d1090114000c0c00b0010305550b2203940c40030802040006102103402c401558015141c0b20761003014085050341454 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 768792535 1250 768791285 768791297
    0x204320315010509090a1a061f0c110109050a031b08070e0c07022b050705030105091b131805010e030f0409090320160f080303190b03011a10 62
    0x101c860300500401815504161510001c03556208501c038508020040c1c0505941c0c4201920b030300d00011410301502c210000e0b02d10140884a28006030ba0880c85a020800080ca8007010000000c80074044940044814036100c101680c6480000740244556803007152500416690442101c5580000c18001c01403400a00074562412203032615841004040c0030190100050140840d5074840d040e0280e0003042000200392080e80100c4800740e080c25105403842d01c2080c20000c0c0e14501405000c1c446d04001000e0310003480c2c04402c04080c161580d41301135002c0035052a84454540034440c4203801c0f051481c40c00890010313810702c3e508440030890120429001002488003140c1364204440c01c075061044001403c01e203905048a151a00b8072078240c508407112400380c110a0001101552070141482030384159a842c0c40e003c035088803d200e0705000e41c00500008082c4000d5000c045102c1c20080004602c82d0142c20001b401c5070200200c17400b40d0203007850413820310b04004072105802800d9003020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 768793785 1250 768792535 768792553
    0x40602010b031b150408060f06031615360617010501090308160f05030a020705060705100b012307120305061e030109060509061f1d0a02043203 63
    0x1452980744084005010b1403842d04d5a40c8400d41c1d0908172001070411005588490421103080c241c205c10603162540f09105400c2a801140c68542d0310404890241c0700440341c1c4900000160b8a40a0429044901c00c1035000030b002003607150700d5001c641030a018070120b40742d0300381711002c4d201d2a520038180c81402a03800c0140004c0c0d0300800079070180c03500074403e26244d0050b40302240301d040620030020402c060f040c104800304480040035003240100d64090350140780d15142400403600a80f203003d0708551105840c280e11144552251000c01da041c5402240f001040418401c1c4206403405600b96420003d0301e081031103400b0450040754031841ca01400142807070340001d44200d01104031100b0259a00e001d68135a550254004014a07030f102d20180b12274035210181da0340b100340854454016080012300200c005189401c49416681d258a441c92030410720141e11180c03610090200c101b00d82c0c01c0001190368002114400710950703a010071083e501d00300300d4500c1c1c000180c062006010b944400d0f14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 768795035 1250 768793785 768793813
    0x3110705190501062102040f0f141b0a051c0912021b01080402030d080a0b19090e01050609160903170d0f0612080f040e0108060108010c0c0308060d02010201090c0605040602010b03 79
    0x1d40d891703a60100d80c0030807030412801e1218020980e059006135010300e4145400802000a1000340c4104200b2100c0f00304d502400000c50454428064a400040c0041004031825400e100380781008001c0d69100180003013007555002411100c0c1110b0030b015074841161a40020707800300c1c3c1000140b00070b01e0104028241680801d54400a03031140c1400d0100460000c1c0240e0200d61180c3c200000007030480414600d2000901104071213030140503440c500f06207030030302151014055240605da01822000080e0b6404154080800340103081030100092004008049a10310010700c03558600c1200d1203a0700d503d01c00e0b0440031203c808000c10101801c00e50200703d0001c4500e182d660b80d90f0052040356550301681c140c015107120b50f4008030102451030300041051400091104d0694803204020030141509070000d0b58050b0441400600290503900010083e090564141c0105072040c000030a00fa001680e0303440120141c1e810036000a400854208174541e42401007403411002640900070146801d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 768796285 1250 768795035 768795089
    0x30a1203020318010609060807051503010e15090a06081b130f0209040c0f021009020a060c061404050619090503030a02071e05010606090801021206010311070519050106 74
    0x18540145980440028042084020207420240020000f0015076071100803460081840b401110210320400c0d10101d0349040020b2441048006980000c0c1103038030b098800d0305081e0000745070b0240c2c0c00403924001c96a032903811000340101c3d005400031850900b40100c444c580951040101010303030101c0300100071501c40ba0b10f80c414103480401c0100d072480760b00581d900a480358000d182c0d00a4500700c500c10f1000ea0042e961181c29803c1c0e070035907a0b1000718111010950b5140800079512180081c0100b041e41e007d040580b140c28401d490204810f40300105601c0728010485007a902c0d90000800c00141501881810b00801406c800400800306a6242c0f80d40c1c9020043c4035840407540042c02c5401d2096403a00741c025895071248030003078494180782090203401d46109032404200000404a0151818000d81d07140c08060708403210960340e038100440c080c10300740e0200454800100003420120300d040c06002083d041303d42c0900360000852408a0840c2d17425480402038826410b00c500c1141e0002e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 768797535 1250 768796285 768796313
    0x61107030f03020c0a021306080c0901060215060411030405010e010c17040b070203091e010306090c0e0d210806031e06011202131a01030b030304050307031b0306090818030a 76
    0xc5401601c0340c4130340030038520f080d0314150065407012403a5001e0f40009000d400400594a164054420700c01c250028130010301801c0c09a440580c100041c5282d80352601e010942c1d0141004201003604c1c9007002d4010750590082d02c06840701d94403040d1103a02041d090083c01c098076240c0c81c19000b0301d803902c07204800d0548042d000415004041e004196454820401e980482000504400c1c40094070b091006403020354407681408a400c000001600c240b8600c00c2e0240c500c095100c0210202d12078040001201000c881110607011031001d044604642c0c0508500c045a0b54403141d07010f080420030107181c294858801c21054110124200060b6404182241110004440c410b41a400c5100113100100201d00c040d058a01e40600001c0405601d44008903000c02038804210302c0f1002d0044c107440b803045000d0207815a200f410704100207200791020b801c10400030344035558031a03103a80e1440c0c280ca518010580e0400030201d41c128440e1034507400007081806c220b00030314503002203682c2ca030110b0200c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 768798785 1250 768797535 768797537
    0x5040602190f0921060e070e071727070f06141e0d0b030312011e031110120212060a0806090a0201121506093f031e030603061107030f 59
    0x10070080003404c0b0b40640c0107142103174401c0342030204030603580040307a48001611664072040c4100d404030700d0241c0102c903141101d14440e40b007041c0035030300d1f82412200c0c2ea04460b00c10b1a000009001c550210009100040140042100068880749850360041a99032040040c2038444020080b0207464072007034891a16182c68030001e5900d6000608050000b8520165000e40500001844070030509081051030305841070751142d6000c900ea10080c3c0103088416000085c0300aa290854203041d1402d1001d110843c8503520380703940750154440c1040c0903604844041c0b0b50680c8001d00784695441c02c02c00f0140904124070007030007140b6000c51415521194000003034184148414081c00c00c044941085a1820b00c2d000203980b2180c0c1d80100500c0b240d040d00c24424900075071003103c1056000d5009843d0000c0104c0d22100110300484401429042410400c070140558898088800e08a2400009100c0501d450001c1c0321491410148180d809000005c40c1d040020484400007a030000000d411b44001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 768800035 1250 768798785 768798809
    0x603060604061407060e060402120a020102060601030e120705010b120f0706051e0307090905100302010e060c071d19060308032806080a02040c091a1c05040602190f09 73
    0x3c5942c03a40068454144040e20a0f8200420900ca1510026003940114420f45400c11040b030094404e5807079a051000c000d0050704000b000c1401d5610a4009400d0501030806032a2664403500b01e1104662240000b01c4181e5101c250b10089071522094291081d2855005003c180820710001a2240880d00501c018088089250303940c212a0551104010704000d8215540c0c1c2418800275001507454490350041c54240000204800f4980c442001140d506841e10106c801c03501d81004815001507072034980901c1003501c002202032400c3c10342d844456810b10142868207081d9003448210251000702c03140c090604a0400024404800300c0f6807003c0c401c11251001d20103c40c4260102500c1c54103205130906149000c180b030f500c003184d00303280944215403c0002d104101401c2d00c80020601c900c04031140700e104000c1e10031210340001c0502c1350f060010747c942c4000728121102200c20565040d1045603021a0071000b4400c040c03003485030482d86040c5140d100c406c10758024a0b42005001e00000341d50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 768801285 1250 768800035 768800057
    0x804060c0905060706140606090d08030a02120f090c150d0c090503010c0201020d0b090615071406010e010e0912031602010b03030a051309021e03060f09071d060306060406 75
    0x11041e150207001d80401042c169803074000e41030144c094070340488001c5003400020041407040c90041e04940200401400d424003000040e140c8d17130b8458000500200310640c08006041720b80710003103030070f6100d070b0154461401c05040c02c2108038a4500400031941c00381041c2d864680c0d00c0c4003240b05540d10849100c03400306210402042c221101d40e06940015095800c11075842401601034000d00002c10481c0010400c1d020100308201500707405031070040d0064140c580c000c4100700620001c0110501a030000d00c004c1e041c0c258003d1504200364814000129110010302090400320f1031a80c005c0720f000028142c000c5003100786140ca1002604241e49000c4c0041ca58001c20700039002480c0603200107050b070744c90b00704d07826026102d50301110a8603441a6105008107011503a442550042c65002c4600d600082010b040d8106a1703001070f029035072091105600140d030366904001248a1140f0340d8915202c3c8002c4550364140c4101c91248034840d510520810110340c44000030b5500b1100c10345407680d1810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 768802535 1250 768801285 768801287
    0x40219082404050c0c0d05041401090f1a160b16031a01050a02010603060f06031b080309061c1b121112040c15110d090513050702030d0e0a0b06100804060c 68
    0x48151103e418460041140c49400141c00901600480700360005018680b58182d00448bc1c0006901800702108a05c00c0d00b40076403010240046040c009100c40305140401d100788207220b019540d101241c0c68071852003080340802c0307010120340306d070300c114142400200c5564410345c24103982008841d04003c808291014101c0c401d400c07041c011600004100f00c0f8162484405000d407845010944042d401d9403844990071310300d8072900c0c046420000280d41411120020002507600c0448400e403104c2c030041030341c0c1c041000740c8181c220882c070000c0e021601590841000c1c2002404001000b030030342c13404007149404030441d0203c07500c079a1840000c401035a0745140c00d454504454011402605001030710400c440c3d08010000074000c021001c0300d010010200f0101c1d0039801038014076400106c50303810030b001611550051904400140180ea08002c84000d0650449002c040040517560110030f180042c808040c8042e50031101c00d5500c0b5490269500015040c01409040103100e141d507003545100403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 768803785 1250 768802535 768802537
    0x20604034d19030b0610080405060f06040f0c02060609180c0103050c0d06030507030b1f140406091e0b0607030f051305060706020a110d2001060302040219082404050c 73
    0x1c0c00c1c0c82c103002c00c1182e0320b80c10103026040c01110000d0040d000340c001449101c0c0141c0d01740344640d40c040c0040c03005550300f000062004501502146d0829100c1c8a070a070f0b40c8845020f14803500920364000c1105c1d1a200040000b4503001412002c11a896400b800261030300106040038103003402e080102d5240c507010503200c041c0c80741800504a1501e0488080200034000c5007400441c4e0058001942c56102d480c1d02d00292400b060080c04442c03806c03403041003611201d203c05e282000e4001c0001901d81e5803569954103983c800519510842d03213002c03d176040703110284540c1d202084140d40c62814810300d540c000e40003540740101801800404034507042000c10000d502c41c0a050042c001907144c039600e26046010350014012400841c00041d0203002051000880210044c06540d070f846000c410001c6070b0701c00b0302018803c0b500c55501d80c0302c00310241c0c4641c00240301c00300d051010702e020200350260003803452101414122a4004580384004000e0404d00034410481041310001110b0311451400701c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 768805035 1250 768803785 768803809
    0xa0c02060d020a020f01180308040311060703060612090c05060306030f0a0f0605010e0727080a080a080106020303010303120b0105090415030201030509030a0c060e0a020604034d 78
    0x8840000114041c40360307000d4024100342c21494003100c4001c0d007250200313402d803480030402c81e2001c443c80742c010f03010a10031107050b42c206000e400e00448540000c0b109030300307101d002c880c90008652501d00800c01c06074026800034041010000800202c62240c0e240c1c110315009204203445035034007101260813980c06103d1101980280030440e501c0c03007424901502209585070060320954074010000030420b09500d81c481c412040c43c2d5a040b49142c11401c505003a000f10000341442e583c003c000411150420003500303000500922006494007608440100302c3c0d6416040401150070038001040040e4000742024030981000d82d01241042c1c80a0040b9006d000b00c1d040c050b03020342000c406120340e98030200700c01d0a40c0e000303076400e00c80382c0e0b10303030280a07a42d100740c24021001818120b0844003086071503020600300c4184070705451010b1229000104981c2086d00700fa11507001800444201e09086598192002000446501c141508aa9005041441b81c0050300b071401c007121540b6a6036a50100d0503c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 768806285 1250 768805035 768805039
    0x6060e090114130c05090106170606031509040c08190212150c0a050d020a182103050304060e160f05040504030c0809130e012031080102190807140a03020a0c02 70
    0x4c0c2e40c8c4d40d92005001d05d0105200c1c1184a605e00086149418520212449600814890307202500e46206102546130000d1055514150a08010075208010300c4058041d58142c030880803180381c2070041100401e03024420310340d9036001d0610700d050706503c1440a54400706e01380260742ca03160042e5060307400740705601ca00403500f8400625000115000400d03685101d1480c503140340c45076240c0d0b880003009900c80e08405007aa54241d0000300281c8100300841d8090721402c004180300d8940040c09140151710040308030b0000380c5070001c1c00845001c810f000020802140c0070f00103401c054901402801e850030000d00030500018801c04907844002c078800f610303c506a4100810404400310900805542010042c1b17444076000030452003034038005892010807141078094407440e100801e07010a1a030043d19001c2017084550015040c1070a00c06026601c200b100465014441c00000404001d80103048030705000340404c103034000c1200c50007a504ea01007141001a50780404140540300d1500c0c44900075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 768807535 1250 768806285 768806299
    0x90b0609101508090d020a0503040b0f120c12071701120503120106030209010e01021614031e03210405120d02090a0308092103090d170706060e090114130c05 69
    0x2000554070400f014801e40c0d461094402c0610000412a06c0f51030045000d440c40c2d10a1005110034840d1070002c0c40e950003440710884c03510103030408220641c6011603404110080110301c5502c401540c590540d407052844c0350904011620350005905080c0600844051184018849040200c10000c0795403036605060350000301d6940e00801000f960110b50000c1c00a00802103001080d4000115602409030428050640c0340c18081c04038421341c00546a00e074144a550031180301d040d80c0f115141e0034440507001450391941c0d902c44209240d940045140042e2490741c0c1048082480820b0b804203035502d40150a50b107900c0491104007034022800c00c594014610440082000324100040c000c402043e12100030034400000e1084481040005480c65600200451100303445c0c58000e908111b84103507005034032121191034112564001d140100e60716943c0390420b000b038108150150303900c204064028011440f002d51181110079024104051425089801700200480c556991000c0c05000c2c02e59 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 768808785 1250 768807535 768807569
    0xc0b04181a032b0e030304120807233901110f060a0c020309030a11010203040b0d02030406060506030c0a030e0709050f01060315030b010311011101050c09030f01090b060910 76
    0x101880f8540d20b02e5044003c2c0c400008400358081e030b003110f005100050281d030500d860020484030500c000341045480c02400c004101c006008000355240e9032401c86035030180d5000702e00c4924074040514810f10580090000281b60b80c44091b0902c201e03a8034080340d800b05141138071300140c03001a0300044140e05800307a0079540d04074110005001d44504040742c418083c0d1024440140d0b01ca102c0d60350800d805421035006000854200190701380540d1040c8100da04d055603400741d25400390404003d022240c0e8000061100740302c0613008000150200b00c81141c81d40c1403114211005210344828242416214200510659400c0c000310b4014020b0100030b201c540b420101720194901c090181c6c9010910f0881201c1012a00248000a80354400c0844c42140d0a540301c0302540c0c0d04143c1c00c1410031040444000001a080c0115030050701c4ca42000303500c44070001f007098240706043c0c0200074030303030702d000382c0c041c04218403000050f0460f005445504203502c9514002c42007081c1500291030403e0700c041d00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 768810035 1250 768808785 768808813
    0x60b030d0e01031a0607140c0418050f1b1009031403071a060a060516020a0312030f090803070f180e070f02211b0f0106030c0b04181a03 60
    0x154070128000f60303000c00444607100042d01c1c103000b080300740a40155003800f032040002c5607907110507035a00307030f070021070740100c000400007400e40381d4050f084050b40d400c2c40d03022800c20001300000e06078026924050b1540c80c0310f031140c4041c05554840d6140c4941e104860b80120503000d107a40710301035900480280038407a01c4c021500e581344d102071011100c140c030503000d03200c941e0125403040e40141710040c4000a02850048115500c0d0400c40c2030780c01a010390711100005075038032140030b0f00451044844400c41c080313100010b400c494824811000765424052454009044c05084aa0045850600e688001100e400c201c5036111286c40c148001040c20001160803941b00401c141701e00b1440e5203060503c0c55854040ba2a6151140040d280c00007407100c6440e001100005400780010a03090355401c00c0194600d140b81c141038017100e1165941d544403d1007401026407000d000340c40e15601c00781c50507140c146503020214086884220042c1d651050b03000810110b0a908483c1c03400a04981454215080d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 768811285 1250 768810035 768810047
    0xe010509060d05090c18060118170a1704210c050d0c05091506070f05030f040306021e09240f031510020115030b090a08040602030d29040207060b030d 66
    0x103040282881001e0a0850b64903191400301a1198030004a0071b0a4444000544d0031103501011141c1c51102c044000c140b50826094980908801c58010800c030703060b40c10084045402007180407603148003040240200421544080131020b40ca0820410056a81c00d241b601203446400081d40100d0000d8410184450498003a0513114100ca07a007030740d03407641c40d4100c120040030510540c1112043c4449004100a68a03103400d03140a901581d140800d02407119035254850b4104660340c540c0451012400448104070308809248812460303c0c4c54280c00c001040d0001c44616000c200740003200c41403201441c1c1080d10184251001e240d501e0781040c00828040c88100c0720b0b0345001d00d14651098410354414000d90100c0c08800c40004501030440d180c03001c0284000b01850520b10485603c440000c0340040144000c005550145890310300750b00c610001c0d920342c103580001055400758414400c00ea49001c1014040c81113030011382e20a00c074a8240090181c0c400d41d15494091901c141080a070010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 768812535 1250 768811285 768811291
    0xe030f0403060c020c0a21080a0f0306050603060306010e100b160213150b0f25020117090d0c060e060c0301050a0504020c0703081b070308041d0f070e010509060d05 72
    0x10014014008400800c030380e5511701100c0da80e88188440000c10161100c810f0a040c100c000341012040301d03019440e1019a5403003082d45c1400150383c03400d92801543e144c0303e00000b0344800c9800038a54204580042e07a500818040e12040d590b014001c5a14203e090f54144000e05110707040c1a26103c05035071020201c01d08103400ea004142030748441c02c02012a00c40d846840c407019228030581e6050558003102600070022040c804841004042d200250307203410b041040b5030082100045d41121b10004141e180e03040c403500b003460195000c0c4050041d01286003d9905000c2ca0029001050380c100703100507107500524031181d4041d030340c18820300d40118001181a079005440b41d9548aa4407400d000403807003440202106900401010300008408000525103507400806040700d505001000904244496000300c4003200005420002c0076083d44100320610f0f58082d01080514000c10702c40d401640c020810000c01032b0603a0004010380c0198140d0b41000009008141c8030344005080c02c004100070703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 768813785 1250 768812535 768812543
    0x10903141605010302071a0606090a0305101d0c0108250e041808030a02091f030e010b010504053015060f06210a0f090b1009180f060e030f0403 63
    0x8507602040b25400f0b4000c50b4411540505088902c45140080299004010300b2003031b8081c0c07040040300208c0d990f0100c000084d5000300041e00781105107400d2541200c003200c008503035840d81c1b03045490505002144c0444410b0302801d03c260181e840001c0040140740c204044298009940800d004051703001c203541e0030001003550200480001002122416000f410000301054010000100004102d801a100c555805445e803030f005200ca02c0031904001001c40480d00103503981c2c603096070b001d03c24040d028000380d081c00c003030340307094108408603072050504041c2d1040c012b5482d081d12412904d841307490400310149003e617002c80c140306c0e109200c00c440c203403041072140c001c1c0250b150480c40d1003001c6641c1d100c0f40d002d03010420720981d03600ba05039450040104040e19507844003044004018052600034910400c01885a4a41300c0d1803481d00b443d00e0340000d0311080ca000340d02401031020310032580350300da0400c040403962106890301c00013402507414032500c940004122103007156000c5010f801600d1003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 768815035 1250 768813785 768813823
    0x310819030e070e061005090607061b0206011215020715240f0803031305031606091e02030304050d050a020d1101140f03010b0a05121816031203020901090314 69
    0x140341e11101c065041130390410b5000c0b020300c2400201174080c1000b040148405440c032420b0003400e460740411205200c560040603029141d5504016a051043d2405001c1c4140101d00e1800580c0740c103502601e5000c1607100389680041d0101c14080b044d8040403080e040c4402c280003a501e080300040000340e0020030190008040540851280c01429810703060b41c003010021810b56503180141c1e003c0c0f810703041090300c1a00003080041d51011800446425190095401160046091800783c95610041f0025850704441e02210740c0180e4005c030841c0c007105c90484013882003042c641007180c00c150018400039404002c003400003003084be07500b00c040190359090300d98180300740c0d081001c0421446090a2091510320800c014400751004201500480c0340070300c1c0a81c10106010b111401080068410440760780c203580b00040c0501c0c00300b00d003211150380c41585040280c42c1d99141c02006800f0803100003031503000300d00f0224a910810b8540006c1d0742100f206800b02c2110f40c007854135014058101408518 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 768816285 1250 768815035 768815039
    0x120402010216091a01170403200d08070f02031204122f010b03030301080c0d030306091e0c110307060504020d120c0203150f04020d0501061e0e310819030e07 69
    0x2001d07014180d000c0b1100740346c000c20b595960340d045940e0030042d0b0101941c0d0750240c100182e06841007081008107506a124074510307041c4400040d244900084200c01154810040d95101400002100d90041d51140080c0070240c0e1110066541441c0000c60400030103500501114444c1074408003d0751580b410000c22104444409141d200e100c02d01550080d680507001000c0c00342407000d400310004c0d000c2c3c41c0000d20b440d26115901c003500d0440942e01d000e80384040a0f81c010b040980708050386081c0314109070380120300d4681c0d501d442e4080c03880041c20403659040000c040d52a00700300d4807242c035804844102c031040304910250444254013403d034000d01c03c11440342c0358045803a6000c1d0182144614103042d55440da401c003d402e02c40c0e03807021074695486503000500d13002c0c49a00120010660507900c807900d410101168844c2000a081d1150340d007002030845c40040f08840707034074241e1094000c08000401d841c2007615280c0b20b96070500441543c1428101e40740303075144d40704850386a40c0e1004e8400c55a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 768817535 1250 768816285 768816287
    0x106031104110f030604090605040b19050717090a02030f160e0103030c02130f050129041a0a23220303050d1d06071709030f120402010216091a01 64
    0x1d481c18840040b000c0100103481d40d940514010310350250f402440420043c1440d903c52003a1442a102103901c082d80000384149000513205410754102040000c00040c5050341c00107000710340c922300b44000720740b111003c5103443d101840800582034024013280d144142245449607512352000020310fa200c06284085440d036090402c1f941200d80507030790340008101507020415503520021488c140d00ea51076020090b40001d901819008043c4281407845804c2400450522003c46103034420703d09108100500c041401a142c03070320400f00010b2400d03110183c040040d1055110500342509200d41003030007024070b000320740051402d601001000c502c0702110080f6000350300c1d40c0c4e0000178080b5a00380520210103074564407008214001d1074010900c2e41c60290a1400e115095038040c2c001904403c007603c0c15046020f080b90068981030085180001c2e80c80c04040e6805010180c0c01420207190101e400d580c4208407001d0f034409804e8424104681d1001d90000400c1031b840010380020f150340e01000344d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 768818785 1250 768817535 768817541
    0x312040b01062a08092101062c01060c020d17030402010905062b020403020607120806030f0304051012050a0b09130b1302150a080402040b100507110109170106031104 73
    0xf105020f2400c0c1043c2c0702d40d900c0500a070800090359821014030318407074a1020082003401c105054410002800500301155900030703100e202280609002c1041c0322210700c603c0516514112001841c20700c1e4000340c07500c0081d059000850f80503188214440785038402c014050019030280c1d200342c80d0001050b80c0d81e01444080e00039076151a4240f003a002150a88040c05d5144020540ca6140018134141d240c0d400205c0e207402101d0242c413200d81c6001c101c511580c209030344a421000403002410b0300301c50050072568a106a0080f2030140015200240405014a5100c118221003c005200070f1406401110045c42202d00d81e5200780140000f041c4c158442e803098140031604000034054503078a541d0009481648540100d03000890491040143e5610340c003d0035080405d561900d03110300f03050040005503844820b4192042ca0064000b5044a810104484140b07030721260b901c083c0c00840005072901e0780a50700c0081c4d02c411444100c400c0303400640c0310706c00b50b07031003558203510040e04d4405100417 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 768820035 1250 768818785 768818837
    0x1f030b0603070909050d03050c04050409060b1207050904150b15030717070207030f150c050c0105010b091c020103090b010f08070f050102120705010621020906010206060f10020312040b0106 83
    0x554101b1900000c0c01442a0880ba0740000280c281c87c3c541584d0720701090031201e40c554181e9995940300321180c4949031004665465549500041015600780000250040d0029200030300302c44042c007a8029500f03164002810200000b407c0c0c0c801280310412190003035008840310300c001101c07420320031082160b80c0c543c64001c805907030003020450300399520301c003440004001c2610400104d031451504404180200b403642540c581d6142c0c0c80e041e607140c6440c2920b4060700403600113442401010500c0e1650640c0000040c0a0303041805250403500040e0000c082008024100c8a070b01c800114560198501880407140b0540494509982d14014000444121301034a80140c1020001c41410005c02003c0c20070340303000380000990540c0d910800c0400c1c01c44403000c4500025001000381c158904441c805a004a080c0050106450301d1030008103c0420f401400c0c0c4203502c12102c00c400c19108000b600c4809005200c415080d044c1350500a440304400d101d810009041d8000c840310b40700c0d1240840390303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 768821285 1250 768820035 768820043
    0x250c060f0e03210904020403080409020a0207170a0b0402130507020313050103180b1e0405010c030f0911060c0a0602161e0507030b0a0b0d0605010f1d0a051f030b0603070909 76
    0x3111102c1807000c102141c0c0084039440d4170a80078440880860708480c0100018a040040107a8444d02c03810b020342031032079540c45081d0340c90455000910a07140468032815190340007000e884a41c2d558400a4005854009030740049850304080001c2550008003c010048141c44951401c07030f558801141640c82c420304807400ac550080840380006d00c1c0d90301040d04888640301c4065a00710301d00f411010fa0200719400e0710303169122079030041000d0305407040b0881e0070320700b0b0002e00c00d007201500c40ca040d4003107803c034aa018117400112400103010030720a109550b13503c04070944da0b403a640841480c0d80c0500000c16546080e5030000c03030340f00d000700d40d007503212076503218000c2c00c429807858641c001810780041501254584418009040c1d980c0e075007403101c80c00e10a1f100040c13594100104503071003035404d030850291004070150b0090401a6242050307404102c0c01400705c2d0301c0e5100e10f809051400480768681148021000c0403041204010040744070381801d5003200c0e0f0655682486006888460780c000e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 768822535 1250 768821285 768821323
    0x30809010c09030f0f12050d110a0242010e130f030f020c090a02070c05031b0603190e0706080601140304030c1b090b030c0a0308250c060f0e03 63
    0x100040503a1501aa5076010b20b003050303414006612542003400500301d2140018000080860704560142714600121940e8000113090140415000c2d41c1e5003040343d83c01e4100034016017100c0c4c000c420300e040907a1036800602e46c0f0184615801a03602510802c0c01003030600020741e80050050709070301d001040002e80020703030b00a001540ba00d09440c45050b103c40e200840c01110701c03803d42ca45035203281c0c0c0d00482701c0d10320044c0d48103054100101c0c0700700c49400c2240311f42c100c4004034152004034403194409610885603590349480e01c80c0080b1844016181a400f2181488403802d495000800c0c55001c544a50f1a41c0c1c00307a989007030045410920f02c8002c240c60765014808140030911070740040c800c05204103440710714206000103048007101075901104583e0b840b000c0c400010301301804580b01140d001c0e60000b43d09425039031910705c14000c651548004982001400031005524099401440d40010508000d1911124010444c00041180b14080f480080724000342e0304001880d04403085c0c07142c03101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 768823785 1250 768822535 768822539
    0x23030406031428060801020415030e0a030f0f12090c0312050406050304080a0e210f120318100e01150b0306150c0102070c080c011106090d0302250c03030809010c09 72
    0x102070048480f01400c04007907440002043c142000d2006101a01d0300d90500c4642003c50000282906d5803030350012030ba0f8205850100000e0b40201504400c14054205000255003201044502c4d06040303030b921000314206a074100c00c1c40075a84480041c0c1e402070305c070101c058208000c15140c0303204603c100360001d0020000140807941c00303800381540d2049403400a4101034140c0000f88200e080030f0f040c00c2501c9583c130103032030040c801b00007080542011401800d25030805c540c0d410002d00000341221200e036080c0312050000b01081c40aa111040d0094082040348a01001b140c024891a10080020703504610081940004801580d2094000070320350400000d000c1100611a003288980c400310390340070300c04800000d402d241490301810354140140f0446150000051100c074840c0441e8016030030440500401c8400850f402e4200345881c1005030740c444034400314140540312aa03890540326828a410010803403944002001c5030f009940d1524181c8aa4920b14202c1da03081001e00e001c40d46030380301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 768825035 1250 768823785 768823831
    0x3030810120f1a04140106060906021c0207030f0c0e010608011511030f04080c0405010902031e07020c04020d15150219020a090203041514061c230304060314 69
    0x240c11040d0f00c0b409451460488800010151410a443c11605500320603d217071000c031401d103d0840103240d14505501d80c5840c0100c080c2d2a034005a904210b1803000700d0905816a000308564001140d120300c0c0803158401030f0030101190200303030195000d0b0180420000680611803240700c3d050340d031003030190719038000488000d6400488d81d00036500c40340000d020388581004030002400c014510280070f441071401d0380c820441202c070140c01444c00a4818814031124021200314440300128560300307003c2586551000b82d18280c01d20002590103400012074440700021340c0c0146c0c0790401c907903500254840d11020f502d20301d03041d00e02203003005921182040700303a089102c05a01c656400070b843c441100d500e4880c034500b6030b4821541034501703206078103281d00340c5401480380c40c2480c1c204408589003400d0000004449103042d561207000514500c50400c10b000626207031402c03481403152803640c40c0f8486181c0c15200d800c43c2c0718060203e494543c3c1103040c01e020309080ca20401049003203c140013070b4025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 768826285 1250 768825035 768825053
    0x103050c0711060f2b2a090b03010909020a09020f0f0a020106030b0a0911121f060909030503040b1f03020f01020f01061e12082212050703150218060306030c040501030c0303081012 79
    0x1820000f0021f80b17540000e403c0e510700004501900e114800440c01071058018444010741c580d000b90441481044004c900c2d00200c81580c2d6001060201e40e0350300c644200080340540007a80000d840128010207210800319290b103c1c2c02203911401c401c10120303012500300003102038910600394032900903c00d210203e8500410044041020342c40020326503444540900448141d0783c03080b4007040e400402c1c00103121042c04400e42c00240340c54111000103010000c40d1042c011448001d0298040c0072584103140e00034040003224412060081102c156600e400c01420065003060000213020303020041541151600009455600310702d01c03d15140d8002c1e00c0e140400100384045805d010310003000700d207007a150843c0d5840c00d4040c030f00803c0c2503400e604004440180d62402c2844071441082984504120328bc1d101c003040c8002c5450f035849a4400012034209540032138215403140c0741400100c10054402030940540340a60ba034007200340e94103200ca40d03001c00280035681048184102140c00541c2c201 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 768827535 1250 768826285 768826361
    0x180f090a15030507090f0608121903020403060216020a090902011e020708070b120106171902040b0c0703120302042108190c050c0103050c0711060f2b 66
    0x4040000307440e80c985465041c0741d056003201e80710302d80b154401c8030900110b000f1030b40503120102c0a404070710720054643c18184510950000ca4000c644503815046010f90b047e1030085d50025030641d59280b80d07402c25000c403c410300c0202e1150740e50712404608101b0700d01c0f49041c07281d4181c540d42190a00700120500000140e441e480840c070030316501141980e810700010004144800003907446521220101d211034005800c00b80402c4040a00d902d20444c030040703071b260480482d551412001e1203405401c0040d104d10303041032014940c0091624401000003c05008490040f9103508801d40108822420b07072191303101305201900c540c6503900e901080d51400800503071141300018902030305d8001c4540701181e800c1c01c0d000490401c0c0480c2061000038072020300000000d01e01002240740c6407030700520902400304040c202c04420300070704640d5120380c02100c981401f98840591148207400e1011810140c101130742d80341c44400d52110400c0d9909001700f11521400ca45500703081380308403100f021102e8202c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 768828785 1250 768827535 768827561
    0x1f081f1107020d0c080a0f03020d1806110a0c08030c280b0a1b080106182103030b03121e040e07030209190b0d11130b1c0203070302180f090a 62
    0x4400c002031720110804c07525800e544955401c001d016603a06029090030b482c00c1e20b0308140300c0d10707891002d00303d126580d03040d09a0314182404011034801c1341d111032401c0144cc00041804401c1140810003c40000142280b441040110762010b0182000e15010754400b10b0b05081c2e0240300160480061030f40d11560b9406208510000f5942041c40002074900740303185040700c049001c88006225003a403210791040001544140c5142c0d9602e800d44140040c20050502c0f40b004544000d920b08040c46600000f01015000301144c0e2010b400d000c044c083e42d400040c900c04061a080150742c00d01c0c6c890415103080750032060030781000307a403546000c1c1c0207980922200d0754082907080d410340b48100c080ca032110144c1301c260030781a00da010b00d00440f01124000020590008424000d03480b0340c1ca41e03408104203544120a102d915043c44e038206040d00d516614a03034003405d0021003004421541030703001d0301302803410b0032444100941400a2043d1181c4000239141c001c0d081c1c000140c0c10f041d442d00100840015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 768830035 1250 768828785 768828803
    0x20a0203070c0f03020907030507020a0605060109030c08102906030c0c0d0903060f090f02060a090b03180c060c060a09020f0409051e120406081f081f1107020d 70
    0x40e9155500e8040c1c5401c94843c0070300d400d50600a5007090b10080e079000381c80341020401401c101402a54990350303000002c0042d0f40300d100041c040c0e48240401c80c015940016550307501d03620380c8906d9031240304100554800500d020b22032a9034800d80001c010180c0fa0300e00c2055104100031041c86500d40c0010100e9440304010041454150401c102c2075620302800da442f00f02e440d04514001d8103444241d02840301c11418005042d0210307035021700c6c205d11981d04075200e59540001213402d031003030b2610354049001d60b0404000c0001c81a6090fa5102020030a00156405000241e0400c80240a1070748101250741c040000121046480d03803009104034001001000100380c242c0000d001d039400428111165009507a0f181c0140303402400c2840003c0401000d001465501d80742d02e00c15008601c030303840c10000f004002c103016400c4140304040b100c0da01c0e030030b5060300c0d07450f0703411543d4415804d16100a6008650601100350005202d044510310303813095400e20304003d5408000581000050035100315803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 768831285 1250 768830035 768830047
    0x16080c03070903140a0201120608070909150c021b04051005040f090b070215060402030f07140d060f031202060105010e01030b04020c06100314030c030a260a061509080a06020a0203 79
    0x1290102d5010b482400c1c0005d1026005500c001049514880d91a10b040b41c2059010710210354045080001d955405a000503001c4050906800c1140c95603960b8603c640380ca822600210f5000c6001c1a40c100740640e0300707035407010503000d00040b90001c403204803000b110400306209521303268000c148000301d016401300b14400c854484035455901564081e003da84822229415203559842d81030380070720112011070a500d081c0000c1e01c600c40b0002e00384000c0216501b1400b461011100540b112816880c9041000c691038107040140c501031800103450168150318415041d910004406050710410303520301091030111710041d0080c0c650701d8052980b250f001e000c551500c00042003e284601928480201d0882c41c60420302941d0450210f07000c0241c0041101001c3c0380c5002003144c104220341d2400d46142000305010444e18402c0c0542e242803070301c520040c00012a042e403c00c0080c0c0d2242d09600c0105d072107005042c0c40030402c1d4820f01c0300300c2d01301c801010007003040d9a010304140151401903928045c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 768832535 1250 768831285 768831293
    0xf0718080304080c06121b161a06030a0f0b06132a0203040305030f25141608120a090f060c05010b150702150d1a040516080c03070903 59
    0x5005800000259001040c208a40c3d001080340003448082a01c40030710b00120301c0d20b400c41202c40200910148185440d41801d000da6120132100751318018101d000040150340303000820049201001c4101d440c80c20003003030f0280f801042c580400c035444152040715041c1030b0358154041b08010300540d031000f4469004081c040701802040c0281c4154050324040a002a031104100e03c8200120340841d4014030003403000850002c11aa40c034480e499410703841d000702c1588484000205070b801540408420022804c0050301c260a4115556540c1903c44200841401c2c1d529050a8070401d0020360200d129554280c0b440301c000c0070111020f2408482c1c150b107500d0311074407403509a03208000140d20103c4140a12501b1712805030020812100d856014120901580d00d074007503460003a111f0000700340c5021110380c04c04120340002d620100f05101c03102101c081d4894904408100328042ca050000098210385961a51448003a186e21011400c0c0c4581019000e1500020904001d00c501a40044081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 768833785 1250 768832535 768832577
    0x11040b04090f020a06170f04050327090c090112021b06070c0312020306010503150d0c17010b10022a0316031b05010f0e03010b060c060108071d0f07 65
    0x340100c60b030000380a01441807142a400503417240d802c00544400c404500c1d109030340480c3d00582001400210b071344503828031506506c40c00c4500010f140003119103140c43d40801c0c0d8504103103982141c04c4100d0b41d40c0d40700c44503060310481500c1ea00241c0031422984014800e9405850728040401038a20910a8645100d20701304040d210704c0003040755146124101680320086050340d180c061419429800c025002900d00e01001e0020080b104a6948408480d12108004240c0b550413082005c00c0d2903075083c1809500c03514043d210b9440d4240b8000b010389043c80c00029881c0d103003d034024984000c4c05030f0708000584010000d01d0185842c0d5814100c165820092880c9101d6041c1c5984030b0309242d40303040d0f945000105424400520500d8041200b0307038004200d202c1192040c01d0131031107c040800000e0040201081c680d0344020003140c541c0e4051000140c0c141643c4060003110285e5440b43c07450680304c1c40003800803074000786107400038040140d44890690030810b542082501d41141404c500c1d11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 768835035 1250 768833785 768833801
    0xa060c060e120c06090109110f13060e060f040b09040618050d031e1407231c0c020721030507080d1401050d0c141f02010207061505030a11040b04 64
    0x2850408a00b80c4250358050201175000f800c4a402004131310026650711710441c05011005105000c000401c10302c9032514013051046502c011402c00051f034a500007104e100c81c0940d0464080e95404c520030b845800c1c20320900543c0f1000070003444180d56030341e84181c050200b24851071b405c902003040c41d10002d00100a00c00e9071445a840100300b04010388141040481710f0060322805500780001d10810f1841d1000c4142c2211240ca4080a4900400940104004400584c903401040001c038044401c4503151700410589281c0c1080c0407203040c4a00882c0d42d40b125001344034500308c900d00c00504140141800c00c141e40e22070b0030054100605030722000c400c1d4118040f0715170a0f0b40c541e91035003850b60601c0e00359405400202ca011003d04055107840d4002001801102c4040501e0386010000d55100e0011040311070711118038203180704206400902039001000111519400c08e071207000024034002d00034013502c0d0301400400116007251164100040d05100280d0041d41d0340300c000d0101d445501900d18 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 768836285 1250 768835035 768835063
    0xc0c0d0305040504050a09030c060c0905150301030605070f12150509041a06040203010b2205061c05090a021f0c150b01080112032c09151306050a060c060e 68
    0xd141c0d4a00070522017a54802480c2d002010f2a007503412000030f81001940d82e030150006000168003d03a00402d41d0018035540002e0f03401030b40010440f141009071402141602d110303038024003442d103d4080584500c0c0360000c9810218021030200c0c00a801d2617440300d0080d0110712401c000c25940e1304007141602d8020b50301503900103102080f4845640118110f035030480020b072811032440d89400d0605083c2c1c0580405100102c296042c0350022840c0d101c03001e80030300001400c82d80d0710751200f801e50061310802a001c803e5070303040c140081c0c0100ca0100702c40c955941c010307110145c4c45c15051413109040780d054400c28240000d101030940031540c1c804d4421403045444800180300305400d0005060248140d1100340128a001229400254880721404c031001441c21401040790080e01d03107042c8925200c1078541c00c0700380c2c501044403210ba8074002440e8000240c400302c0d40d07114181012010f85046002e000d4105086131000c101c101e00c603410031403440d4000d003000140d1107149140d131410710340600d030b400d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 768837535 1250 768836285 768836287
    0x70804152d0b010e1e030c060309060702150405150910050a0f061a1905220303030b120703110a0302030a06140f0115231306080106020d090504020c0c0d0305 69
    0x100a41d2100e101d41d108105013401c140310310341c480f140025403c0381c1d0340c1070401c80607218081e019480c1e1410403410b0810f80004040c02e4480ca040d42c44a039503a40c04403200030040c414615869038001152001c02e01960f0000c02034100d002184107004c500200240c03014041c1c0c814000300d2007110055205150144c4008071011803544c5900d0441001c0c0c0309241c103c018a802d0200603003071901c00103801c6403407801b800c0e03074075100b081800d000507102070081c501d190801d1003030802c5554071042e070f40c1003c03410340f0300c661030800181d902c030002d2144089030701c1d10040d00c0c0c0d0b1204500f4070200e441150700071207251004000115854680d800310f410700c86402d80072941c00c2d40300e01c4450192441a039440340c1c015402d5442c1c0a0351340c500311005000c20b46044541d800d00c40c035640d005a0320542c14810400ea000610720702543d4440c102114003103c40e0034800d0000252070900041401840420301c5e8520500b40c1d038481912038140b2007008000c0d4490302c0c120b0f240d0312444070800d10644601c0444030109010740c4582d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 768838785 1250 768837535 768837611
    0x6090a050414061509010c0f020a050a03110307060309050a150e0a0303022104020303070f060b090906042f01200105070210060f050108070804030e0a0f0603110307080415 75
    0x1c40155500b00800b013495190a206861a0380da02266411041d608880d20007603948050004c541d405820f5001a50059186000401880071011300c2000307905e4150119a02e0300d6681500318111000b0800007003464008030007200c0820b6105401c840c4520b15000000303071001c2c1c2d0624040c0741814008088012075004a00c1c078000c4544010604034842548080d0400351074503a0000e51280704508004003200201300c861020700007558030040d10488090510309960405107681980c848044400710780000721007114a0031040710f82490b249800c03004450401c440f00342c1005494615100b010100d01c445a1610800303201c42c04d000740c03402694150082c2a8502c1003488143c251480364120310481c810341c5000700b100f42d07404901d00f50b1002075407400c215175840f07902c0c048441c05615140c0f103a121040301000306401c541840031707030100c034081d4030108002070450303510803c0760100b100e5030030204003940001000308140700d0000c1140c1d910070f140020589110f0320081310308900c24003d043c50441e03203116 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 768840035 1250 768838785 768838789
    0x30118050105030a0b01030807030216120b0603012a02100906050103020108010602061003030327030e01180e07030e031b062e05120f0f1b090c03040206090a05041406 73
    0x1550301400058004d8492a4825110380403d040180700007401401e0020b040b209140c0301f845080314955414000080003644d07540c4001c0702040210003511b0803684c45e40412254030707051042c01c0300620200d419103044000d000d07800042c105680065800d50282c0d02c14a8200c04280c4a24444c00b846000001001d5040d400010504481604070741c080d0351020090065038201201c407601200e41c03500d400f1030a41c20a0700b6003000f290b469940c450110780114154410907030003102c4980031003000e076070300e00701c0880401c00d888aa11085c030403018031a19000120380c080b44243c0104040303a0301d5108807440d108166003180c0d00c09280e2408640960090b07018270090501100040703449403081204100780c460300495224030a0f50f03500c80c00c0e1040030300b28080c0000031014494550034803080c1f419200c0790780801e01e20985070094241070301032080404401d003040d841c105110600a00c0d4524006080d503451341c2c203002240d84004001c650000104000140964035405134000200c0990205d0b200d03400c1000c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 768841285 1250 768840035 768840041
    0x31e091a060307030b0402040c170f04060528050901060e090102030a290405090c060d0e0607091d04032015070806010e36090c032d0c06030118 63
    0x10680c0310f81c101180c00c1000c03640c6882c03456001038045400284051100400742e0303840c0e200410707080594601104201141e014000c01030301c22070044006100c41e0b0394503e01c0c0c400517025808240e8040c61250504c10380e46980c0d0b449242d0000519000050060701d4440111031680c08a03444c4d02c0726034002081004071100c3c0c2c040c9008581002d0020034405070442d16103201d0708844860680607a039680006200404100030001e540f000207041240d541c001000c407440508803511918001d8803d8002283c5181c1c4211091011101c01001c0e501d607106051605440351440500190100074a601e0f01d0841c040c40c28542c41e9814292400501780c0d15103688017008840001084034062054010420a241c1d802920818018404885400458072a521340f0070064189003c0310041c1240c025015103401d0764900550701401048080380c4906010700d0425036600c44c1085c0e400c0300038a06411401c14459030b140504403107000401034803101c0300305a0104455800076031101c1d903800d0b000800c01151040c144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 768842535 1250 768841285 768841291
    0xc070b0f040f09140105120c060d0b0a0b070b0708070203070c060908060703050103020a0b09030a060f1e0507210209121006080f03300f0103060c0e030c01031e091a 72
    0x40e0007404400f42018080a5550301403080311f01406410100804e00303501404004c206410041560f500c400b54060140010194680001d0041200324404100400f04206440080d0792240340032085954110003154004005001d01d030561006103c0880041c0410030160060310a5a45041c0c201b481c00382c040e8600700d4050003c40a00d0f00c3c000060025031034504040d010b82d91008201540da071041400b0a01d8003c0c0c41e42d010f0691407401d012000d01c1084c9800c42120301d05a03820503070313818402080507400c0b140160b842001050180c0703651205400c200e0103000840c00c862000505011005000c202e80444003001668941c000401e50082400d01c0d1044038040c28182004001d0706040c509513039035a04c214002c42c1070034948002032820a0500b954000320803200002c015410707052601c926401d5010a0001320f41c5542030009020240c0d10810841500c514001c000700700602600d40150000c217010700e13503450140d6001c0c4030301030904298064023822703a22807000b1107400c2d510000391005e549005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 768843785 1250 768842535 768842549
    0xe1504020c071401051e04030210050307020601030f080c0307050d0212090f0f0a03021507030816020d2f0a1101020a0305031f03020d0302060f09120d020c070b0f040f 73
    0x500103600c0c4500000341c48025603e544200a64000c0000c0068569000c0e180040312821070708200310507008103900142045a1082d00c5144004803120030980e501d0100311400c02c01684480010008200c60003100d2242c0c5008115031071500722150011810b43c1d200c000156400d90002c803d0060542d41003001d03d80c2c509030070f0b10715030914180034000382000c0d200c03001c204d00c5410b68403101316441e56110480720003980d00900c01b0b819041c0400300f03200b160300301d84815404a8228000140c0c40707030a41201045c2070809902600302810748900603180c2c0b00d10b50303080020000c1d050543c1c9014210708240288911034800080c80d603400c00f40391041500e0009050941190054201d0f4400241c0010a9a803c200001404450b2201e03040da036806000c100c1d81302030b60010b821030b08682070640200361b0f81d0003110354440e213054555490104030381d40d4402c030107210b6010300c0030400d400542c4200d60192103c0302042060305e8803240d88680c02c2225410882140f504518002800c002e43e19036003011800502c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 768845035 1250 768843785 768843787
    0x141909080f0a15020c0102070b1b0310050d1703090a0c1d0105091b0304031205100308091306090c02030c0d090609090222140f030307050a0f02190e150402 68
    0x940d84031582c80d512201d400800c0043c0103048900c45000f90303019942c0c0140a40c00071500c0e01c0f03040c00c1c060091407040d03d00000c11b40c2d00c0080584180c09110840348107259501c407a801070b0386000c003400110079581006462680d0b070103c07060300d1290703540c00442c001c0c2024002050800c500b42070100b001919540402001940808803040340f2040d081c0307090460f20100c0d94035015507a000005d40c0007645000000c0c0103a2b0000007000105034100c0050202c20519a4007040203580380507001c901d030031650101904002d814000f5800ba864050b101c0e80118112034004201e1954a1905400f82c8a164041c140940c0001c070344000000c40c07c01075214134806914002101c54502075000c0c0040301c0c54019004003980000c1c1c01501e46241d104c45ca0b8085540a41c0e241c06075503600c0318072030b003508820b52091046003e000007000f54134000069030b110310b400c6005400c145031a513613034145e4901440b504a03084648c12140101a0450340580d44c000c114000c032415152030300c0010210201032810000d03106030301c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 768846285 1250 768845035 768845053
    0x90c020102130302280902030708090c0a090c0e1306091503030e1c0b070f02120406080118090f03110105130302030715060b0a020f0c0a0506031614190908 68
    0x68020110301284d4055075000b0038100e0040a45030217004803062901c00c96280000080c45d000ea5034002d512404165440d0f140359142c07001c4a41d100c0b00101d04142d0b01440044042c44841b05a0380202281545810710586010407800416420303c1c0d1500540101540e03040b0230848401c280c000c1c206401042480300000c282596800340c803264980c06007d0141401550280440700c030795524ac81103981042c05d1003502d1529620007042402504420401400f44d071410350131400342c08007a2800e0b120151140d0b40300341e08140c06003805c220b20190300c55489842d040410080340d0f0342da044004150103684d5030880054001380e0035096550183c0303001e8400c504100544042035000c1f0564290b170350712000070b5542030b0010320071030b01402c1c41780c01144210200107401010355400240d5030710b41020b4802500e1220740c90b9400c0000d10000c81c4100340e0030507010000502e550b2540c0d031200100400b903041c01c0c10300410540f403141c600c0d0849419a003284c03062104801c51540c00c481c810008111100003003000403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 768847535 1250 768846285 768846307
    0x10e06031504030311030a0c112107020a091104030314040617040311061602060c16030f0c0807030e0f09450321060a2715090c020102 59
    0x80030781c0e124050441210020a081520a402007a400c54055240c55128240000d90b01c5c0100b00810303280c030205a20b403640c42100e64001c6146102500703030400c4080480d00d901c021200544c002402203a008417440300c00b04100c0310341e00c01d40a00a0b8403180b419140c2d0700314a005003c135940011a850358034030900c03041010750f41c0b1613410342607558450720481140d1510718007501c3c0f10020401c035000601900042041d441c1520403805840581e6030b0850b0490b0b1181c0e48514054824038012450510503410300801003402201344000600d0580340414a02c010381d2112006070b04030210840003c1c3c030010142480340342000c083c00311850125003506407400c06c41d100303801c1c1802e003d100c540d105140c181d00c1c0344110807003081414100080310b501d0b03407803c101d030841c580c072a40500c982d01e40a80b6080358201c2090780a01d2160300c50640986807810480c01c15400c1c0c03a01a2840080703103107c0f000c490160200901a0103840742c0301c44650306598100e8180611382040d204048005011a8414045604e01da = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 768848785 1250 768847535 768847543
    0x91b03030f200c060d1d1f020306030c0d0203071e150203090d060f02043c0e060103050c0c1905010501080c130507022805071a0a110f0a0507050306010e0603 69
    0x1500c219240c40da02e403028520540a000ca03200d00d205d4940d0b919481041540000c902150b9480031000884601f00d030820a1800301e010541d81d01d50585c1c01400000180e0030400b115004250000f801c0720f07110ba130346074a81800d100c00c241403032044007912282002280c0000000850f008500e00156040c0001c01000c00c12250303201c4406482e40d42c484030303480305c8201d02e5411078000c0e08a8140c900c1a035540c908101104860005080c409003519004800000e00b02c42c1030300c0107403090000681e03441d031922001180640000b40000c22081001c01540f62000c000700008070204480640c00100c280b05800c2484c00c440c816030103120540c03c0b442c1c6611080d5aa80c0b00480e0090002341b0020b40303501e51500803450216000c22200e6240c00c8110740384192081d140402c2c08043c4188101d4203810340b1400f613003154a09030100c00c48a00020700c02001098020300501502c028003d081381ca0010814141ea448d2420340082510345d50400138007441903040c2032001c0c601401400c0640700c420b0502c03001007561 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 768850035 1250 768848785 768848803
    0x30730031103070311210f100320030115030b0f011e030f050a020a0b180103020f0a081b0406030e1b03070e100302180f1f09091b03030f20 61
    0x4140c1c0d05e10b0400345038411802500c40e00101494403003a005c8900301041c4a29009503888000154130100048107000c0c03c036601b40c1500c0e48410152002c491401003403101484600f051903055484403500c4244411341e80e40d4000850140904500609007203030205101340f410382142107840103041c0c01c4070440c0419400001140d0748201401013014080c1002410860051402584481170080006e00b01002d80d0252100c2c044201e01d10405010f5440190204c0c41150b65564503c0130a02060030030744d01607820194404030381080704015a035501c03c1c0b21480c0d0302980158011030303990880c040c95030004100400f00b800e4822404006a0000c90000c2e691304114402d91318407400c96800590210304401500c0010344e80a000000102ca00403104030402404a0300800d41e090014000f800900f0b80d040d4454520f016031304007200322800c10440001800740d400301070b101c46042c0340d0500d0420001d600e8810085029a44400d00c3d00003540004107003035140c10402080300f40c500c54002003c440419a281 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 768851285 1250 768850035 768850037
    0x8041706062107080f0705130e0c040506030a02040c1107050a05060f071a15090708061503090307020312040501020106081c1b0807030f0806010306080c0409030203073003110307 78
    0x200741548162503c2d8150704480783c0340c0181e910285500743c0005060080e100c0850303102440c140c1564403403080325201c5481c1e030040d90103d0b0391150b5905040e400316403c810040e0981e00c407074105401003800d0b01c000452501c0054580d41c42240200004d000902c040c0c07000b1102400c00d6498440040c1032400754154041c20510b0000307020081160f0206090312541150400d0125464030410860300c042038450310724000c804210008185d81d11580c16603126000090103000c4035080034001e8121508020401c2400b48020031a40300940d90401641540725044000c0b80c0e642c5090900080c2910116801012198072403151b20b0860702c240741884104800610b094507080a100c60100780780b0710401000f41010000081c1d1406159000d0b0004191160720b490b102d81e01d468603401101200c070309101d60500e41d0000d280c07002084c41e00d0b400100c00c1314042d02c102d80c2032600c551601411000920030346411841401c800003208001a0103003060f0f90018101080309510703144101d15280701c0106080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 768852535 1250 768851285 768851329
    0x16031811060f1e0702040f0e1c0201020c011103010f05010809060c0a1403041209050f0102030a0315030b10030308130b0406150e071106010909050a12030f02070804170606 75
    0x2459005141050f111050198000c000381001c0c02400400d455025481c26030146081541050303032070342d0a00600b1140c0303080b4030003445090341044028401401d1a68114115502000b028008800c2406007042c183c0c4020381075660ba51408a64200801450b4001414000311b1810014110b5001c985c00340d01c100b400050f0703680c41c6c0c5100c0b07045650f14100140e070b4a11003004001d00c8144480312089108000d01501d400c2c2c040d680340e201300b11403282c0c111003e60041e48200101c10040b486500b1207000c032141c1031050030410b522541c0b580c0640c90219401c0c2040c41c0c0b0903070100145603015400350382259151210903032010140d1600f00c030010340200b0190800e03840700401100400907491100003000b043c000041c1508050300010b1030f02c80c440c00c60092600c1520b002040030140e1380706d040c20f61588440103142c100030315900e1810400ca6a0003100c203040d030b1000c4501010640340000d00003d03200d201140e90361401c01180300641e024494100141c0d9200a041001030b45820400900c43c030380c2c0b52122 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 768853785 1250 768852535 768852547
    0x114060310031e121713062009032107021c1a1e19050601050c030a12050c0c060f0a020705010e0105090d05120601051e031603181106 59
    0x1a10607494590000b0200d42c810540800440c11005542024a21901030340c0d280180c0f82504603854861580005411110040400c210303180100c0c0030903c844c407560700460110009020300354629000c1c001010124000150130f5014981840810140940c15002c01c000c0401114000214054043d000b07005030150141d0144030440e20340f0b010300a591200b0260b521050399914103072007010556030b42d8400c441000d0301120f111401c0500c00c1c032461041441e42114503504100001421014140e07074107000003000880f044150500007840d20150035198440c451540380303042d10480b00000d012515070407081c40001d0b5111000b00b84190451108400546240c40d007014500c0244910746000388298a40050509a003070190005840340d400d00cc00c0e98081140c05d8070598080c0f18440300c005101c140400001c07502d6001d070300582002c10714100c21300c580c50b011200381c1442d540242c0760840b00c8010281119000b55250003109035190b07005030304480d0b25480f5624440182c1c85a2000c500c502804114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 768855035 1250 768853785 768853801
    0x406150f091d010c030b0f010207060813060608100c0e060f0a0c02041107110406060e0109091e0603051b010e0f060d111201031a0f06010f02070f09020414030601140603 74
    0x2d0401c4480000030000590103100c0a00180882c030042070294a240c03403480b07002d42c000b103243c208a40c20303605c03545d1482da540e602611a00104100844080d135403503601060002c81040302a0640c40303d603d00055121505401900c21100200c0302d5100b150704200c0100c0240642d01a030f104140541401e416401d6140f00040141640300840503042e0804525141445130440180452800545041060945500307003228007c040e414076501091b529802001f10441590142c0070042c1810003808800c1c54501c20941a1002503000780c4566000a0078060500d1403c042281c0e070200900f0301010710003c45d0b020a480c1201c028000d13100380000700313100004504940150004000c0c80c41203d43d90100c44941c54031010302030109442c60b21400c40a201034004590580b4011184032004202d00d0f80c42c41c0045484500103410a01180601000002c00948019110000e40303410321026031550b00b0315090b0950384801138115032080c1e22038001040100c800c00b412010342c900a6540595030b0780c1d03101c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 768856285 1250 768855035 768855071
    0x61611010626010e0318011b030c0807080708030c0901020c090624041a0a0909060e04020f0f09010305071401050f09210609070f09050402031e010e0a05060406150f09 73
    0x300326260b8080025001b60012852111801d21003098a41944095000100400700c0210201c01004114104000c1002c100c016010340040c5c2e1103103e60900d4005191748a4415410507a1044c2d03030001c0c0032034840415038040c4100412070074180d030038000b40c4c6400b00002d0304501c0e520343c1d42d8200c1400ca10300400c80b05016001c0760090446c0e00b0070000820300307649101d50142d11280c110b20002d0442c000100d2640200d00440049031f05e031001100781502e4035020401f05c0c9207403841c07441d40700500e00b2210005446e48210113000b9809900549602c81c0303403c603002d20b18207140504a041080c2045002c005092201c1a40c401c0388050f210700e02a40006645c51029102420540e0800d21480b0100000700c040080d4620650318442000c194071551104840c0c19540d058800960542086829110710041e500d0035441e418607207000440c54510b4034500c1c6040c80c50b18030050b21190005410081805030382d01a041000c2003540c03007009058170308804d44901d1400c601521b1502501d4041c14114100a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 768857535 1250 768856285 768856301
    0x7120e0f0303040f0807050901080d050307051c0501082e182102211c15080321090601030f0f0b09011e05010501021906060806161101062601 62
    0x707800c99039101d0319118010700e0580e151007450014440d101380401c0d5401c090a426040b034013044000c060301400c0c141c040d550741c3c00c010444000c02c2001d008582c0b0ba520017440d03065155a100380005007550610740080d04013010340c84001400031071013405900d690000b59018455070021000000c0610a2405618900484e214040d003d01e481c4040d4011800c2d05001d00305220a07542c0844002d02e250390580a06056141101c1142c2d03101400b600048040a0034012112900710707400240c0c9546411556004035841d80000f0016032002c150303003144403421144180c0c0c508070291410150700e44442640c1d83ea0905010003084034124880480c10080c221030319168855000b140701031145048040c45000b8102107082c032015500010701080c950102e84529816281c0603400703489043c1d003011000c203d004903440121180e940e21100000c0d0b00328103001043c040e409603512603a078060541802403041a400d1080e1040d0791602004016101d00e40d08201540000b0340114401d40d4001013406005180d09 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 768858785 1250 768857535 768857539
    0x50402041b090608010f0e0403120603051209090105040e0d0c050c130c0f0809030f0a0215010329060609040905030d0e0f07080f06072114010e060607120e0f 69
    0xd54000c4003600003a890050f5a0b881d601c40a96070703640c000a0b076800da0700e8411401d04200882c08600400c4c854240e452408003035800114440fa40c0b56200ba140050900d074140c014000440d545915180002c481030042000302c80c103000504400b5800382d200c903a200c2c11038040c03002d6a00d074242080f03001c1c0500040010b000b0702c5021086c0c00040b60f04085d10003a58600d0004090b8045071030718500685000e4050304400c0025400d051042e03100030102c0e40480b0300503040d44152040781d200780e403e20304a24003840c498440d12000044030040110381c04c0381d482803e020f9100710300c104881030f1030304005c1c4c40440908550201d80300005003441d600390f00c1040802561036080810340c0016000004080f4192450030b01150fa01d07e940e40401c58482900f030340921019001800800c04851055a407a024000e40d0801601d039050160402d108503040c50b214000015002c00041210200c0300b034102c2c1e409901500d01c149440304a80c2c45100413a252118403051043c80009807050b82c071809008080c01c500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 768860035 1250 768858785 768858821
    0x141509010c1a011a2109070302030f010b150a0516080c010f06060e0105070314030406060e010e0103030f0302120703090516031110030b061b160b0d0c030204061205040204 75
    0x900c421801600c400f4000c103240c03a404d044030700894100d00d108484101c5801003104d040c6054200b402d540c40360740600519034512480d0b00110140e0790500000c00c6520004d030000078844016010310070901c505c3e00040d003540c42c050000128080c0c1090848811b0381050b28518000b80c0d5514100c0c2941c059084010415860071740c109110a0b684e51080c4180c506603101c118600c1d1465004403403601c21044001d001500d09610050380e000319502846d00540b041c6030120700035803104034400740f01c64240e00c04444450701c0c40c01002850b821010f4490360341054a8150701d0807c13144030030b81346200090419000c041d501c2d0b40c20401e110381070015201640038170b038401c2c1d5003d61b01c4c00d203e245484480104d52081d1240289003140c1806881401d85080b009420142800640a1408200c1d0852a0060613078020300350000c21110907290400d019001c0201e0064540c00004246001c543c003405c10720044c14410042446032032b4019150300301c030440c6010041056901e9101041c09082c2006c030950090203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 768861285 1250 768860035 768860063
    0xc070f0501051b0301120201050705010216211701060509030c0a08100e0c090c1602090403050d1b080c0a03020708031041010e1008010906141509010c 66
    0x2010b400a60040411403007660203003042c401201c01c140300030f00c15100399410400648006500982c0074200842c0901c00060500c200c030300c0040400703c0c0c5001d045641e10612030419800100c8031000d0814601c0601d41070a144e003074a82289400c40040c01640140200440d239903d660b03808002540d8000e5024119403080baaa90701129a0744207010780341c140c141d08000c08a9a1680009002c0300c0800c0024599030240e200d034210740b030b03050380040c4428036907031000014100035031a4440c202d805a4400e5541a68030100640b10790102e40740c04905820180040d08034001040d8413284250f004079004140c29138910400a09a0007807003944401041d40d08080100200100000c6420013120000c0d45178548102001c0340308940401e00762000081c1c0030341c404107814150000c414038000d44806041c0201d00081410008410341c02a121400c0003030310031001171040070580d02402c002400690845508034103c50000f4040c1103204411b06000d40e008034503404142c0c0f0464501c40c3e01500312101801c858 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 768862535 1250 768861285 768861293
    0x3040627063603020907170903030f0a1a15040305060a1d0f0312040f051e010c0e0303030609220c0501031103070e1002031b1c0e180c070f 61
    0x42e03500c503003071110310507200800c1e8102541c0c4040c01d141d503110300030740d4058156130810400f54005000d5500308101403580c100c0c80b102d8049903900602924009588030301e4000d8210110a0b0002c008c02c100900381021b100d04001d949070104000c8a0845020900e42c42021058901d030280d030340058520f20504007813004000703da82c050f1440d110400c14603088901c030038180e2640c5181e8601640c0450784204841d000302203511002a400600c40c040810040d00e16450302450300044100300d00c40101c0101c4032004402c02441001d000030b4880c24a02a10b07000ca1001984900000742201d004900b12000100658241c0340b0b03110100c00400da9094621010341042c08a80d8090b00805020915001000300807141d4030043da0311511459481d41c80d41d03c449014884201484007500c019844180603840d05036017442605606031841c00003c0800d1070b600440d12342074203000615100ad00194184d40085501c80060083c00159401007041d815107a66400d0185c1d07106000300645140c0309400110100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 768863785 1250 768862535 768862547
    0x420030313081504050303070f021009050c041d12130914090d0206010b07060906092a0b0405060901080403090329060a0b1b0111030a0603120c050304062706 69
    0x65454403080740c00200310341d9243c00043c40c0c02d85000e81a94030910001d0803180c410070313118840c040c2910603600304240c02d408110950f00461000ca07602d030000c404c002d40a0034584601c5003891201946c00c0014000d4240a540b181d00441400030040e81c0043c02c5486100300c03480d20001801d00c11004c01070404400c280103014007058403088100c0c0641040945414400500a03060b115001070311480d080f082c2c2da950004290320041124a141c880b201000441e000d034138041c100c50218074001d03680342d03035508144002040030380007110010005e200500c0706807290810307240c11030002e080c5a006601d8900f0700b9508248070782d0000701310100c01c40031a5906442d8002004a814582c0000c0501781c48020810840c203040740160024110248648403100000f45544c00c546d4620b6000082c11543c8522131036501d600c00c450749100240ca4180410070001c0c0c600d482403680c861032134030302d07480d001a556154982c4168410340c4208418201c2c040100c9810004005c001001a03014a101c503642d00c0c00034282d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 768865035 1250 768863785 768863789
    0x231207030311060c0a0905010e01021c0201060f0b1303080309102405090415020a051b030a0e0306011406070809061b0c0a03030c080d02070507171905060420030313 72
    0x243c01104007180d581d1030b0709000d40d40020607645500c0d8040c4c0c248401142c0780301061404038111b00ca090b4820700400b00701e10b2030f008000b0455002141407400c1085403e12611103510070040e61100300180c044c10f10900d0304140540b030b40004100d0303480e01e90010b02850031180c00c00c2c1861091810800e44900014840610b41e0511160b0080c00c01a80c6e400070030401da0b0b000ca40207040c1c5140c81c000d40d14689040d5005084410242c140035007051070b071401e0002201004034030340b901c0f070340300244100c10b0540009030414806022401400d04d0740c1030400754203405e14566901030190300081003810420814605468034403401900c125201e0001000c40400394a03162915421070040b1500103a050034070245503415650180c4480750002001e5441089a81c000d04440c0b186589c00e00030300b000603009000c0c00008003070034500c0a01c02035906401c20308080c0380403c0341e8030b40d00741035140c0c070700280d0046401541301c0d070050380c19032410440364680503803035100503c6c003641b500000071034000c03107081c030400141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 768866285 1250 768865035 768865067
    0x5100504110f0904030315272d090201020a02041a090601080c07020d020a03020a0617071803030e0114031008010e0d0512070e040c08011e2312070303 66
    0xa403071201401031048040d00b6040c2c96400c08805000140880d0107a0030202e9050319120f01d1590302503480c404219400312240840401d21003110b04c0d12105001409203074200000000020311001d00b0142c0c04081000307408080d100740ea120041f550079603000303100f0804890b801030000d01146030044900c01d1070340c0304100203901c5491104042921540f02d0710510344240346281c641c0c3e281c04000d800300b02c00100f5140301242e100d0444e28000c4010785429105000500054541d041d510804144801c00c1c11801005001005980750b9140c00c0c40c40e240a07418101e070b03018103120024045400040740d01c180102407030b81c0e0b8032038004107000a00c544501e0300302c200d41043c0000c102060344e61804a4440000361106d0380015410b11054110307849a540304c0342c04c0340090500421213500c042c0801c0c02d03124500070354004542e007000100807900c0b124000c0d08410183c40302050700b2070b04101a0b80007036082c40c9189078240d40c03090f101c1000d03500c405601e05526080c1804a644c680c0c1e81e454000d00b084034141c8112 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 768867535 1250 768866285 768866303
    0x1201060e1c0309091d030c010b210d0c05030d051005120a0b010506090a090507020607030b0d0b16030b0613031707050c01081e13120c110409060905100504 68
    0x80040c0745032440007450103505a43e0700400c54030300306040e0050004a07041015400395052a0403004400b000200001c014410022561a0b907100401804280c0349110702404030207060300508150f80801c0c501000030080c100b488142c905070920030b180d40207451704070049902d09004e02c40c8400c420507858080780c1c1d0072205c050144925a4140c0c0d1284401c01c3d00070002c40c06200140310500c1c2000c050702c0c0104019005a021f203076165150010746005464200240c0c0201c024030079000c0d4180610a6110300c1541c0142134080f0550740d4010800d8000e1506031440c19071181c1c0e0004601c6a0000c4040e144010f11613601c3d2014860052041c80340741c4421142c0d400c0d454040340010a241d03054502e0703660440d0144c2004840c040c019a0700ca44020502c200d01e03041c10811004111031084070b07901485042ea00c1c80740b094403070f1600c0300c8800c0407006007500380041001c507080000d40302a1944a65031003500e010424420b240f8040024003e0884000d156000b040304d041400c00d115400a8443e9010708000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 768868785 1250 768867535 768867559
    0x708040203011a060712020f0d2705100c0204180b0108010501080105040c12170f0d0507021f18061b1e090e100e15150405030d141201060e 61
    0x2d0403000501081c06812030307000d011340400b040742c050040c00c0700f28a6006030b482e20707192040d205060211000709c000c0480d100210903034000e01d541420010080000c002545582c2c10b250020710204210030481c030402c800d03070396001d04540303903500180001026010440d03540c94540c501100421424050349006628140000400f62414058607000300d030040c5040c400c481c08d00281c640307801c601c02820790312602d081004005203c00b640c0109000c50000e694640c13180d0310b51011406503400a0810004c66100b20808006940d0307940360f1102544420030000740c0452516510f403120b090690003c0c1c91240380a4103581c1340c030120048500780d540c0c3c568406010071303104969014045161901c000009196802c203000a6071440324040d0410410100d4444443c0d4400d0900700d110310448110000800c01240035182c3d0819100b40310f21000085441810142082d01103596001688c42c2c0038104503041030b078001e0882000e4122888180003500001081da140d01c0c014080b02c2d0f6201c65940984211010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 768870035 1250 768868785 768868811
    0x903011404120c0809030601150e030a021f09030b0c041d040506040b0601030914030c0c0103020304020607121206030f030806121b0102030f0d0f0e210d0e0105070804020301 76
    0x106442150b101030403151071010200115032000d914030048400050800c90719181c1e03138081002d1030007040340a0710000c40400803000248039038401c1110b107001c1d0340320b4084d1100680c0c0313010241e1f86c04000c801e010300b02c0d5405407000321003414403a40041c102070010010f100450107110014020f6848070301040d21400c1c02601602d030000400c0300c015041d40c000720301090004140703d02451704a0014500407035a580d594840700104031080c0c1d4028091380c40000c2c20205044240a80b9000400900302142145403a0f0007003074280c0300f411801450314214550341c4200307a020750810400d0101e484410070030141c50346803007440c89490000907804240351700000b036403901e09003617200d8a0310344480c060070200503c000c86c0200074146e8000760341903000c1400b100525003181c1c805050484510000480c80000c0800380c0011115001003c21103070300f041c0d80000c0c0080002504090114011303501c00d90358502505008003e00e0b400c86508255402c0c04140220268008526405503000328001c00c1001c0366050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 768871285 1250 768870035 768870071
    0x30109060e07110c091008100c020f071a25050f070515090906031c03020310080a05030a0503130602041503050a0c02150c07080412030e01090b030c030405070e0903090301 75
    0x30060a44d2060100c90f5107820100f19071078004d50500d0500e2444d40c0c40311402d905203e01c1103a1840313529503c6221b10180b550400030b811001404402501503981004040c0310321603031405190001c134000140d0058400141020000046002c050040f041140c03031501c2030301e40c101c50704e043d041c03803080d540c0100e120300c0c2206942c5140c4a07007580241c071349081072080c8203840f80700410850b41030059000700c4034034240c403a080c05080703032031981e0060b580d01c0e0000185401c03e6403a0800c12040e0301c00d80080c0d0020704000708403081c031001801c115459994982c01c2c00318804982070024022800402c0000c0c00c0321001c00f4502e410280d90301d01b4021340d034683c1c14941c00c40390013442c5080103034031a0800000440b0903100690700301c00100421840c200d45910f49a41c144c0c4158405007141a800c00001d060591003c0e00d10700254092a1607482585880100b2217180000391030307400326420000109007001800c1284200500c00c0d81060025880d001c007040d0349a80100a12038040d50034110312104241b02d0613 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 768872535 1250 768871285 768871307
    0x1905011a18030709020f04030b09121b0f120a0314160e040b21100c05181f0f090b03130f0212061003140607080402010311090402030109060e07 63
    0xc0c420038200381c00040407580109110481d5a010302a40401280080340381c001070841e030a080850968540c0355107400d816111004080d00d0f040c0c3c12540040780310001c08000c884c5d807072042c00b030105140c0a0b811107a40c20000034000e140880d100f40b0340c2c1d02c1101c10004000d0481040c80f51010010030340c1c09045c0080d00d440494031417058482c50813080300b40c2e074090400851140c0c00a000011f07503204260116001d0124500014a80100c0c802000f000381030030451a540b403240e000303060004402d94130007c0c045000e6410300410000c102c81050310b540d11010f003088840d142c40b280103100217019000c0a0018021041c80d0800074543d0000402c0215109017103a001310960050300c1640c0005d078541002d0b258510a040b41d0041c0c0c41400508444010400940a200314110f080c00c140e14600d40a140611860180d035816042802000010f1790403080c6140d202e40c081c03d0110f036500c40c1d040b03285100c2c854001e0f210390040c40400007145100031544010140c81c0340c0c1880e03103201d4842c03032026603c40300c0078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 768873785 1250 768872535 768872579
    0x9180501150c032015010b0408010506010f0509100e03061e01050103020903070302280e1609060f0807030f1409071a0703141309021801092d050306190501 68
    0x340c1e15000d618a0a900d603901400140e0a441741c1012090044030401c10030b9000c40600c2070b0201e400c0c003982c0b40c02c0c803506400500c2420440342d0b9548090003d00b2034090b20004501c1044141300e6144441d00032440740d181200000c0a0b203c203407814007030b4520324107031400202006c803500c80004a5154000d01c2100c10000d801401403001a1441d420484583c840d19805224110810304441c0c400d1044090000074144002c40112246446403d0801c2610403114003810002e000d0380400c14590411b10002e40c8040a281c0800580c0c0da204c0c1c1580034101d01c01e25950b07840c0c54048540055249800300074000c0c0625819070300c400b0b40c0c65003105280821007000e1041807004003c1c080000380525000c0c01900311810b241402c00096607134461120171168001c18142d6000524500600c11114a1540e11102400c00078102c1e400d11200e03c0d1141c151030b83c2c00c0590b15075582041c0110022a03450401407600804980700c0345008103488061854050039840840d0504001181310074000311400b12410300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 768875035 1250 768873785 768873797
    0x12040b0f0403020a030506040516050d020609031c020c130e120705070305030f180915100c0615050a060201020405010203030c0a03182105040515070309180501150c03 73
    0x4090025009038080900060148800c00002005031a1000300e14011400350000e00728038646030400f507041c0042010782880115500c1c406204550700e00720b590f002d05405071360306500d90541c0c502003446c00c00320b004a0004004a21100b001c0240c0c00121100240029503002590032207183c000010364a45210f03912540d0443c1c3c00000b0707001c940d4005008194010800c40c0c0348141e481d1980c83c00d5911806d044500075000090356248840300000d900c5490b202a100e908051800c1c620700c0400006444480380708503c1800c4d40d8201900c00d503150500a50411403c00104a4541c184481198644982402200340410008001d4018403d441c100d1f00c0c180c001d145107580342e03922601c07c0d41c48000900706066913101006020194004003e0910341310f0031000c40b1004001c0640d4034941000724940003040001c00c07003031005403240b401800140400f104040d440313404c503240603035411807150018040c42080d000ba540c4030600e160000e034100d506401c001030715042c1054045404000c6040041c0208103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 768876285 1250 768875035 768875039
    0x801050609040f1e0c140d02030c04020a03200304030809030a170612030307200d0c150e030a2a0b0402150c07030507030506010f06090e0405150a0f0e1204 68
    0x405401640e8840c411840030b00010131001e4000d215002620090300c0e21001004140032441d42c2e001c84d03200e8018100c40d480200c00c12640003036500c4038103942c4240960340206840382c8160181e0000128075900111031070310034017503010182c403981040b10182c0029882c14007040b2002170201c11200c0100d000e50701d006901155001e066044600030300300d903412a10341c1c81004501103040c4013941c0030f1031899840205a0b032070103a1030701030701c0030b01d0600c4842034006005002d000f0390040544828241c1c02a400c10240c40980d00310401030004c645440001d000000300078440320340c00b00c0090041403400b1005e01a082248074400111102e6031401841080d044011401500d4a02a0f00d14002400300041c1d1400f0030320600c0714100b203104d41c0b0071685940a02001d208109041c404240901211840079041c540f421100400342001841000e1440f03900d10080b6040c490140030304c1001d1400c2100001460030314090307200040490051a248803403601000d804c00c02d078045012600c0784141c5481c241468 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 768877535 1250 768876285 768876293
    0x60f120c16240f0905070602070f050114040906030b1f06140705070317040e150a0506070309080601060503090f060c03070f0c050d09060207060302070c0605030c072a080105060904 79
    0x4888490b40d20001900480d545a4811400764600c2c004200700003241d010114600b180c90401d00b504802c1c1550000340042c41084013190b200d8084074024603080400159080c1c1d840c8203485160407070652182003440220038030800142450160b00e210208080400e40080c0804c0c045c0010f0080c5400607441041c1d060300000c0c8800500011401203064452980d0349a41d03d8010521344440e0341171510010408000240b007400e10305a1019240c00b00c0c822000800b40000ca4002c168080c85224001c049038010515100e040460094498401254190b585550f4041c1040e00103ca080209106001288115000218045000c1c440c0140101c0c190384402600340c450300000c51103002002408100e100114030104032642c0c0d0b4045c0b94a5000d48203003020802420941c1a801100a140c010031202e00000d0280141070b0480341c1c1450a00d4482d102d091100c00c01d8482c54601410b29944e200840c1c42d1415825108607030305002804c05070866035150307482d44c02e80d58103c480301d60103031480000030045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 768878785 1250 768877535 768877553
    0x804030e060d06140310051006080405070b040602030d0b220f0906060905060f12060402010305040c05061305040f090b1f0e0f01060f0e060a1d060f120c16 68
    0x511001040035007000002810b44085a00b0b81d440064200a04c2d0285030b401e08060140c440c1c01400000d050160703103040030b0b000300d078840c00748140340c108400c0d1070010341801424095035015101407000550394030395494000790f99030080d5849001c607914007a0f45d0800ba00d880548100344030000c01041a07180c1c440028000101402c80c4140c17405071f01d854040c00041c0312881420003504035480006403504169081c40056405643c80718002c0055100c91001e284c4c0c0040c0c5564070070740c2403801081d20350783ca1920b40c0d10001d2550200da000540406c801c1c9040c50700520b10b0307082d41c105440400078800d85e8249001503c445550240544502c500442c24511020f040c04610343c4200c81401c401175075901c0243c0e50380130215003c991f91081000184241c4c0d5102d10003c490300460b190882e42c151928001460a1040e04a22018014101e40024141e82c201c680360f603000000170700d8140c4030300d64082d09110682c0600a0240f00c40360580008400d000c84605031205400709208154114039540c1d603c4844e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 768880035 1250 768878785 768878807
    0x405160c020f060f040915080a0b0402180103030c1a060112110405030d090e070503061c060608070801090c08070807061d090c18030d050a0c110d0b060a0b040303080403 74
    0x8059601c40b9414562901e0300108410307500e805045507582d1502c2c10040454004150340030801d500381744100b103540c00c00601051003030b030414a080690f0b1120310016070014a41c1c03540c11018240600000141070700700d044159041d00840180d4001c00d80d803007403580c220720101c03045400b08540c50400b003190f884d2540712805c0d404543c01400d19203600c4400083c6000c1d11680400e00003069010306100c410403d0240c903401600700d040032030179810700400040c1400580c42401e0036044130400d043c0103010340368204100400c0000300b074602d456180c2034480d006e00760705001520401c640c0d66000542c00400594082120b12200c041d2a1050030400d0403034040141d010403440c1c01d8003602080e0004e5132841d11440c080c00380c004106540b101107070700c000050150005103911a80082e00c0f07018117a6000340440d254003087d840c0031408014146060303602058003525494001e600540c0000c03c0000800f15507009071002ca403819161503480c1d4181e84d407482140001400501d000c404100064041e5a403c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 768881285 1250 768880035 768880039
    0xf0b011d03100608010506120109051002160f12020c0306090d03020705031315090b090d060b030a050307060221010f1e0312170a0605030a0b0403210b0f0405160c02 72
    0x550340b107200c02c811040e24101d03041200c06075940d2080c4861480c00d2000d80c4004840940240070010903034035410303294402c0044801d052a0006000c140b60307803451030091381a60b4026492280881749080c0071001e0008043c10b000540300e4069402c850785000a0403510900060005114280c008401100039410410084a0170310092045d00846010340c811080904038249035100c0040360b1800040c4150001c1c0e1156803860020468101c240e1501c0d510030f282150400750215801e1100000b00b4604240301a0260550002144040030481035400a0003040c4400c046002c0320a0b14044807c60302c0b00a100303280c1804400d180402c844840d001603840e4910042030320000859594507000031800c510880c08000039110030b202000903400c104441d800c8003221100704440d500b0100442e0f80d5130300080303025050180e200b0009003058800c1c1c2101010b1046c080040f40e000e00385003120780c046c000c50340380d0354801c1400917034408250800744105031150405192454500807031010540348521903140c240e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 768882535 1250 768881285 768881293
    0x414191503050f010c050a0e01030b01110a03030906050a0e0a150b150a090f0f091806020f1c27030c061a15040308070b0a1506120f0b011d03 62
    0x140c00c03204010510320007180210064580e14610600391800c44001e01c003110240075080c4070740c1c060581d02070034032940c02d4001e0900203500428003005031401c0c40b00801d0008280300b08000403082562640024a0f0940300e000280b12a80311680460241c0315800c001c01c40729404044404c002c80c03000c0303507084407103a00200c0000e090240d21020404040052481d070503400000500f100c41c8a6002c2d1070310340203182d8060605545410718280448642141c45081c03072054942030543c09070a03800c3c6070907412a40c0802d0455070303041003030340031031050300301c401e052000084035000500362034510b01849034074078190110340c4210441204010380c00703140c80005500300110720030711030f0000c1d07401c1c0b06a2800b4000443c04015910a80040082001c50442020304402d0180700400c0050741d40e000381d803c40e581c0140c50311401e50390050710a004020929031034103001c101c44c0d000544a41c01c41e00e0422040d03220f143c14030170715019654440664213212042800105201440b01940d034081d1901e06a00304014191 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 768883785 1250 768882535 768882551
    0x120c0c0b030a0207150915020c010209030a030905030706080c07080711031e1b06040e070c0f0606053f01020d050906060a080a031d01120e0c0f041419 66
    0x9040354100700c5400700d11950000b2102c05000d103e205032035000106000c14410348400d641d91403440010051803500507500441c40f480c6500f001c2d0180c032030382c1101404848101640f420001c200d10700e2031240900900440c1404643c1610840d0928481c440e1902c800b8a00110f690f110700c150f80c810601a2406842403410001d07607541484240281c80c0e4071100b00c028070106c03642e903e05040d40504219146030512221103050f07110071040c0c03000c0f5400781803d00019600c00c00155090900650010200c5000a43ea1001c000d0683c0c44072003a164240c6210041c211a0203001401c002c6100000b030004004003009428010903200704d2800c80f100c40005402c0c00c40c8001c001c02524016258091179401c00e07030400441e42032400f80c05005064540040ca2556602e485c040d000303010101244ca000c8001211a103c0399004200f42001000c1140e02004114550050a07490382c3c0c0cbd41b603045224007480d03510541c441c985070141034890340c2c0c41a114a055200c4003888288403070316182c091686901c030061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 768884892 1107 768883785 768883799
    0x6050901170a0b0a0608041209061d0f181515030f0c0f0a0509090117031204020a050a030c1707030b010611010905010507050403030e040603120c0c 65
    0x507105075912002c0c8001c014000600140d500f0114080d00090941d61200540b0300ca00c0c02180481441d07d40b0b5407048601c20308034400c0c0000940900c41800504588076404038030a60028000c00030306031200041010051000c24041002d207a10041004405401800035000c000440c1e00d808408280040d103074860001a000641d1030701b82c02c0000e90103948400844214808000d051074582d10380d500c0c020719541c48901e1040c0618445070001520600b445c0106100e00b000c0b4016500b0060400507143c200040104142d0b80302d500c1c3c1c440090641c0742d01c40084040c60080309403522281c10309404851041c84950000d100b948110f00c108082510310203058103441661602e80c0c2481c50217844a40942040d01014100e540380405200603950004c0040c411a40b003501e903a020340b881102008102d07001440007501a525071321000c0e140030b00c19001c80b6407142c4141c100344c2556440b105 = true := by decide +kernel

theorem cover : BRFrame.Cov 768705035 768884892 := by
  have h0 := BRFrame.cov_init 768705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 768705035 ≤ n) (h2 : n < 768884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
