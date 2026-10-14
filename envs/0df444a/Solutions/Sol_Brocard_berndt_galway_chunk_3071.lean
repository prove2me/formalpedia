-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:24.927387+00:00
-- url     : https://prove2.me/submissions/efb2bacc-617c-4501-8075-c3e63c018696

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 552158273 ≤ n < 552338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 552159523 1250 552158273 552158287
    0xf03040c060314010501021f021b07060207060507050a14014203083001080307020a080309010e040b13050c040812190c0602160f0c0911220317 63
    0x1050040180f100c04240014a807540740c00000b03903480840c1188148000d1602c008840301410540c1a40c600100d5804501c2c008039450311081d4854a09018080050145a401045060180301100d81301c030750140050201c10070329140c64980300308080140340c442d504d034820720200342c00042d40361401200072042c0280c44000c00950b60380000001003402082c40c41e50720304102107030008040d203a590848881250040344d4030100040d40700ca03d480060b019040c8500003042e000c0c4000060b1082c0b074400ea6900141d0f1762101c04540c0d40340111a807090001700152141900d0f0b08080d0003404d003030303040542696071080d1140c050400342c0b00d0459105041e86030103e010441c03004e08001e41201d002e000304a8514201015001044903110070030b4540900402c6040a410000326504840780b4550503000d00310a61500d26011343d0b1100c0c000020780b001d103035503a00803c1e010341d00d101c1e82d60440e2440c5d1009242c00c048007000050036488240428000110000000c04124078800c0481ca01603010101655009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 552160773 1250 552159523 552159527
    0x130506010801120f020d14060106051c0608030d0c05040801022d0309121c02121b0a0219150c0206040c0f14090910020a02151f17030f03040c06 63
    0x50307106540800212100401151100304004032180e0150f0392060b0308403d60800d4000c0140001887d44103102d10000042c00c2d9a01c440a80207031000724803c444c00140c00c45401043e6002401040000c3c7c0003004030174240701d8964440500200b02c0c0c20000d050541c0c510b92503003243c02c9007540c91154107200103541131004030648400400d034154440e00d0704605051081558481d161522401c8070030340043d01003111170b0440c601c0301040c0b1265100b550b40c1d40000c2d04019a100c01034035544040c0710081c1003415608200c90603111030041c942d00424051400c1041013001c0406140e0689001020001e030b180c2c41d0350b01d070003a08003149140c0c000f41b190341001d240c001700ca0b80840d400f000e2400d044010610401400341c07148404180100c0b41c680180e25003602e0035081108114043c44418800240700e141e0b5a00031608a0141d1a04500c80506603151407154641c4041c050040380304000348501808440c80e91028075808803005000c50b4140703940d07030b54007201581c0155000d94007420a4102001307019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 552162023 1250 552160773 552160787
    0x210031508120726160f050a030c11030706080a150905010303090302090109020c150703021303050d1215170a1a01031101030b1e0f0a0e0130020607030e13050601 71
    0x30365485044a04040c2030f4503440d030760b008000306480340e10700805d100010300c029060032401c081d4020043e240f45104070303d800b40c00c16003106001c48424040c05001445898045803072421141540c98104071603503541d00f80002001c88800c0c0d0042c08a5140c004603442d20b0500c1010b010750701c40d440e030032200c0c0c0c10340c0104400840705a10964580b401003060007032160700840c1928000781000510401611900f0080c1c0184c05040c0941011040300c40d000428000d0001c2c27a10a00001611280c40c0050b002181034166400a055606151a034440800201c514541c120000380401d0054034210085030781c0d044034000705a4400742c0e00515210052050011200302c084004109082c1003240c03070b0a44010034007420b1602c0000d41d0411507040500200c0d180c0c00502a20300e41c000b8040407000d41c88000c1c40e14124020b0003400d18040503810845190034402002e81d5095101d030002d6000070a140e030030042c0c507504c0031108808100340d541c031204076522080039084008a10b0140814070703151842c0010010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 552163273 1250 552162023 552162053
    0x30d060503060c07050d05030c0909100e060f18040503040b120a060b03070f03150807060c0501050601080601141e0c01020904151a0706110c030a08011202100315081207 74
    0x6500d007013007158001640061170400e11185810600e45a58400c0603e1440e4042e01c0c0c495504940c00104200500500450b140169801d213080c0c1d00c0030703403075120911500c00c4006d200107402044007400f98075143c20601d54245d10034418400c4a1130151500455070b065002140314007020f005817400e000d13008100c7c1c043e0744098540201080e080d4603261200401801e50500c1b48810b1594034000c100c8804046c0c825000904584070868040b180e81e840020307c05454014190b820794030706404640a58854036032680a80030594607410324000c00c00c0c0c3c0e040300d540070241484440c0e80e99100300030545001801b03802e00013032800c001a260203000d0f06010070307219071055010303401103401c03000d0005000078a500100000e06c01181a103400d40b1b0301c0d051000700102c003050b89461001003443c103848176001009240041d0103584504882e41d80b0305000000c0380c02c4040080d4019969414000000e2003540050145c0400c40300e15101a503803921860b04150f400d00480902d01c900040c0e510030320029a04807044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 552164523 1250 552163273 552163291
    0xd03021606020102072a0902030106120e030306060f1605011503060c2d020a0209280608062d0c0a030c0801180b030a06051009060806070c0204050711030d06050306 72
    0x90100165140c01c440510350255417000d8601706d100100c00c0c1900c0c2c0a00010b003041d44011556540c540704054032048841c50202c0d240741c01c03c401c42054020103c00da03030207144c02525140c10200364088901c0540c0001c1b52050202041107004804904240550021070762804464820641181490815610722981d450284070100189034050b01e01005440c0180145080000301801040b00803400d00810240195000c54031100340950b0928005101c54a2a0b42040244504041c002c080d010307140c4900c04c26005400403000140c0d03640c0140c03040c241d00f50064111042d814440010085004d030282c41c070008107800803070248441030b0140328507605e001d11410419200c0d0302d0b2900030468040f0540040c1e901035120090300ea1551001c11181440030f81c800414042842d01108660340c0410303a11405441c54145540000c0003803000c5681c5000c0e4515a844032251a000e030244000f0707201c0030744072000b0404040100501010240050842900050004140b00b1700d0700c020185400b0010f807415078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 552165773 1250 552164523 552164527
    0xb0a02030708010308030c070611040f0f0303020a0b190c031b020705091f15030213050411070b09030c011410080c0102061612020c03070204140c040302010e040b0d03021606020102 79
    0x40c0e41c1e608407009030304484e801440560740356079082039020580220500104a01d0408012100b1b2482d10310240040d40c021000b58040342d030b40d900006071010001d01c00030740540c00034003140e00803a99084501e9480051004d0844080ba81c400c4850201d8072040310010009650b031056440045010f0f500044000452006203149420100002c100d48400341894440e40c10210740c4c4120321001854000040040c00c00743d40b55500c4402000c0d000e036106a945002640300504041090325140c403c03001c4100754011883c0c10208540c0d1074040506014103524003170b00c41444034028140d400d000d1201c00300000049400941444224014040c143d43c006852503044a6109012a40d0001d005a40700c1d0102d8800444011240d20a0b50f0710034041a500307500ca800003441d03c0240c140003005082e41403099800300403448018482e0740303544c401907508081000b800c10040000d503101e0b21040680c503c004100180703120b00440015000c09980c07100b1009a0080010b003000001014000c1c0002d2075903000a40c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 552167023 1250 552165773 552165781
    0x30207180c09151205060a0509070203030711011418010605030303010b07060e0607021906090c060903200f06210a0c1e020c010f0e2d19050f18040308040b0a0203 71
    0x5801c1803410040215000e617102c00044050b9213000c814001010090100308c80341c10241402074032a802100d540020488406000303603682014032900e0101241c1c0c0d01c0ca1051510b0381089400c100d502205108480d64a41c40003140c10382c1e0500080d4004c00039148100c2e82c9518601d0305030b0030703142403100c200c8558010340c040040d4a500815040c8851054292122901c0c0329443c019000f0044140007412182100307201203080c94020404006490091038000c0d40c408090b40070561801f00d0b000710540040118414600605190000d0140c06e400c3d0612054840c3e0881080088079108899174401d0944500c0c001541e0303500048880520000c5140460040015550196031041840c0c252410441454005075141d4802e045e01100501b0003020011040c0c030561003e803140d81580300134881e200c02805644080d281640c1090ad510080054074900c0501e040100003a050302c02105503000750140c03500c0417503001410182c030f01ca6442034070703001d0060a190a049a40d584002c0c000f80c280b42c81003081c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 552168273 1250 552167023 552167027
    0x1081005040b06120a1401080a0f080d0f0912030b090708160e06160302071217030901090c0605030702010c03021228020408010506121612030207180c0915 68
    0x81000e440003070707034042254003980012411511a00c02140c03014840c031824840c9503940e85d000040c0f4070306504005c45841c0d803240c22890700c3d4080030100501100d00b503000c46000840c0b44002d4608410740d0b42c40014452a1076116034240ea42d04081101e1018185019840c955094031800d01109019a120542480c0408010706151005400e180660080d102c4403070341107218030044810751101411075a1140d40f0340d2100c400c070b05c603440da00700d0150155103004141c1805007030910046c0341c1c0020030a402200c0c05400c0401580c00035054407021f54880004c403001c80d001602400040560350b44041e40c07132924150080c2140e548200c031108060040240400d00501c3c4035903a42c0104200d01c0740c0c62140340448924480c0c15644203004141760011800080e05c041c11744c03100f44500c1c4251072804100701442001510340083c01c0042181200c0c00c601805a602c13100721a038882486401202e60380c0352194402c10f42010000e50b1001000d0b20348184201c4c1942c860300d050000d10444034a010528110080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 552169523 1250 552168273 552168301
    0x106080303010612110904090f020a08010b210a02030d0207060801051c060b01210906180506070c0c03080409050105040f0e031e0409090b1609120b0703090b010609090b0108 76
    0x2940c01031340e01e8288242000340004210f03205408018070402c40400c60345003541d21500b40c43c800342e11038400c1d1000040d040b0300600030307201c6a00b0000d00180c10140e8110441030390030945031088401e4419580303550016141004000c0014055030018000e851a2031b43c01030048405800c0507000304c075641490304100000c1c1e511f0950950f44080040340d103d00c2c201c012035011030f140030403035a881058020010100c0d2158070030000c1030f0003584144404003020103581a8901c94002c002c0c810781c080c4000801c01d610512401d150700d4841c01488868650325201d120b21904103170090070700150740302d00400103803a05110fa42d00701c0540c0001403102140d200f060310784030301415089104421301503940a08070f401c2541100c000e08142841000701400c18100300039a5001220110a980d655400040d01140140d8003070f0210f540901444020303080f1070351110b4940c48058081030034561920030341b40000b03001d107005d00e01030f0840340d1320004520b1a0070703400e10507102c070504450f06200110703082c40411303503440c48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 552170773 1250 552169523 552169547
    0x1407060906051b10020414180609060a180b011704021f050f041202090c0408030f0703030209101e1d0d1b091e0c0203071b0504150801060803030106 65
    0x40c101e0300c0b071504508020349902280307a070743c07824001e24181c521605150340c064029200b2601110440940c200240000c10031040d4903213000714440800a00a49040c840007540258090b200c12600740d82d0344458000a00640c0d0900c00c01e80d103540941040e541d00904100703210303400c900081040d007003a40202d20189004d03400324105010152207038800a00a4040750191030a42c0c14035031b0740c2c9640d540d8131140c01d0302001c07040744900c0606005c1003e000c01c00d015242914071040296107010300840310384265a1002e42c0841c2415000e0060941c95640d000085000e0308031900d6100503404146c1040340b003110405d15032400d1207010210860503880c61035102084550582d2075086601a60920305042138100084007100044400d01040c903440c81d810802c540407040b40001c1c41a04c0581000c42694083d010007401a4020710250021030880c03200850b8060f48039545000071900d0328082000d0b1100308250441080480740b0402042509101c0c4d0300081015001031400c55040400050000074440c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 552172023 1250 552170773 552170777
    0x609010c020102071503020408010b06030c0a0815040e0f060a05071b05070801020f0c01110f0322171c05060a051011190302151611030912010203041407060906 70
    0x140c00c241164002c01c980e20140c1103242c3d0a0081c03072032403070008029500c06d0180e4400340d4240b100074503903801d100042c9c9000300b001c5a007903401c0801c94001240c04800040524040b101118013840042d242d51082040700390a0f080581040b820115610f03140c180c001e48070380c0c0c070a460681040300c5954821000211240000305607403403840030707040240c507050791608040455480000e0040d103005500700180040c1001000071300c50442c0101c1c0415080c0984d501900e429130301000000c9000f454a480602d0340200c2030041030000b2082c3c3c644a03004030103440c02c0400804001002c9554a410b0b201003d0f813450f6200d401d110b1440c0030004980380c208140300d524020002c1055034041c650142410000c100c1d5100219000c0020710bc03007018100d015000c0907030141c0144900e4035000c403020380c60507103c0c4003040b05011f40301e840000d04444100c410458110300740401d100082c91b99644a98484c2c00c10301c094009626401d250402c0e5110704210b9400311700680c0070200c00c01440750420304480840300e0174 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 552173273 1250 552172023 552172037
    0xd05061e300106031b0305060106050c011b05090f0f060a0e030a060e0105100603020315010e01050d09050601030b0906090a020105090a0509041a10060c061107080703050c1b060901 79
    0x50030003252074100211000040c8104000e282885081540004100c0f4040c15880700c42000c40300000300180058000500140c01217801804054041c100400144605500004a0903078091007842c0b5646144107645c00628000344030031282c41c0c4003480007840282182c4c02296904410001034491088008030824010380b1201c8202d40d036010f02c00d1070300040c2c11401c280001210707c0c05060082100f2035064500650058000c5400c0f44a4429244103815503100c4002d60a410303401540d0150a50074200c0c1001020891440e0f4002c0a010341840244102c0003828194150301d080d441c2400c009186c1540e641c441c3c0704106000030002030b001c1c0032540a084c0540d45960610202c3d11140c01c07500b000c0d8008602d082404208007481e058901c00c9030a4900e21000ca8036612085644000248103480000d07980e0700c0341c000031a510f58401852400c030040b580789480e41d81d54400700fa64018030f50a502040703005c80c2090100034240510000800710106060003007040c000012824001c0c6d1090504005078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 552174523 1250 552173273 552173299
    0xb0f010504020c03250206040306020901030c0305040b0a0b131112010b0901080f07120507021c1e0806030f0d050c0705040623121c020f0c010c1401150b0d05061e 71
    0x3800c0c2132684c5d42e40c025008658544d12030820801035400580c07880e000034600504c42122500c0303031060074002c90b404a40d005454a42d10803400140201d025019030041e03034445802004c1c46140b2400e0100024240055180c824018188200d010164000040000c0801c03040500360b81c080705140d400346500031580d02d1929a444101c5007010803414902c480d501d404248845d003600080c280075201c502c0200031a00c1c00048908a80c00c1e8080e00d0022000700c20182d0a80f4514015000d455020038060304071000f018100c000c0c80d141455014508020510029403050019018007800c030140034280c4050000714a044009103c103640049a080c0385000c1006542039a61030407110003044446004035480200d255008001e44580c2030014000b600c912560036103d01404038030212004416140c0902a95803500d0788000100d00e0450825076550f40d5001984112500d100c0e140900106c2c0292921801c01035a0b800c201c0e1f0010700002d219404140041403607096801034590002401d981000d40c0c2d42c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 552175773 1250 552174523 552174577
    0x60302011d061c063c050306270114090709020c070e07050912010b0a0906150528080a140f0a020a09081e011404080306010c1e0b0f010504020c03 64
    0x100d401490504041d501e2804030b905043c049800c00728080700c01d4016822400c40ca4417494030040c8500764240d041000001c042c11020f01141003041c40300c400442c2c1c0000780c04821800c51f40b0f000320700b98140648a0500030150420841000613003c0210210714082415039025170b101c0e5144203800e404007214002030b02c124810429200070f180c2c00390190403480601004903018010350401c0c2402412050000295000c1d28000c0304111a6244180c889960341c0503002c550550198820110071000c1410100c018140025414500c4860350b50b1041c1d5400c03c17041a200b07a80382c9050030800704000c542072011081c40040c0c029040940c0041c016502e00c14504180d03400d03002c60307209402d540183c480c0406207500301140d00303204d0f07100c00c4004c00900340d1f2101081340602081d030707015010500c02e000161080d401021580d1810303004984048502020b801410f8143e90125400c403000803044c000c1c01501c601c20f05c8801c1c09841c00f164154102026454007540e81e025640c540c0c5a8a0903083d0861983d013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 552177023 1250 552175773 552175781
    0x317040b0a0b1f0f18030312020d02090d0f02090c0a200f011418030712080c040f0303020a0209070318031805031c020f06040201080112061e060302011d061c 69
    0xe10061400702000410f0728018040c1025000d81601040a004641311541c0c1558444020360341d140e154902e0309151105120000d400010a18480c56400c00940d4500c0d5690004128a9442205224840c0c3c0e403900c1849003000d00500309225603c01841260101a00510305003076062a138001c10035009488009180f03400d2045010701d00701d519283c0c0620944104c1740005115801c4442090300c00480c00502da6a07070f00c246040505080241405c0101d10b610070015207030040b501c810500d0030b094480c9842d900c002070a034401c41c0968400d407004411410702c4500c01e6845009400e0400c0004400d05604154028002e002805c1080a00102c0307084890b68000001908029045445903000015828600d440012114001d842030312078051a11000203452803242d40e06969136212640380a000c080d02c801c0c0c1400c11954079880cbc04001e02a05d8030b2104e20b1032600350181c00414420b01c2d50001500c00320f10940d2003024081c03030030b102109544400c0b0486501042d0303904034113820311710146403034010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 552178273 1250 552177023 552177049
    0x6030203041e060b1f090b0c0c06030c0705070902071104061404020903100c0801030b0928140a2003030c060609070c0804120309060201200d020909040b040317040b0a0b 74
    0x100980c1818022414100c80d82e45424450b00d0320f03961b04e020380b41c0240d0505070103502c0301c42c4e100d5444580d00080302d0400030055600403180054030360800b2442e6494a085c41011f4001041c2c4e0390303000c01c0310750500c001c019080080e080c0a80e820002c070360400425101c0405905440c80c06240c000449030243d48082020040ba240c041808100072104940000c001003000c1c40309a80b45a0585c004c202010787c042441c0746400e5031900d04044c40210b1001801c00d10120b2a000c3e030b611824088080e41e120030601216180c00c0c4640150190a160030012100100162098501960052001c52420305002940d40d800070310407603402416943d6080f046030012203c041c0208840400301d400100b49186081c00203006203c0c0d1a01100603495001c201d00b201c1046070207010510200c0301d981c80c0c00708400000d14003000811009490084038502041401e5400d44080343c1c01d8054800708410300d03070b000f00051030500c0c0d0198034150904041d190002c0c8004094040c42c0700301e9030340682108987d0340038440d0f848 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 552179523 1250 552178273 552178279
    0xa020a080a11041e0e0c0a0c02100306181b020a03020a021e03030a0806100c0506040609080408010924020301032a1208033909040e0f0601090606030203041e060b 71
    0x10484070720007506503503d845c41822040381c0c0c018045000c0707520603001e49040c1c0b02c03595561400e41000350200311008650f84502c009150751a2800f080d107644040d00d052003036a81580c0440c3c0b204001d00c5925191506e099020119000070380003100091303011035a903501a07011244506c87c1100311244072200c501a2008035414031001900b001c0c1590481c01207803041b201210700506451a024098560040050300180540c210000280000300c850b4401005a03014000b618107203074846548900b1540340c0c0d0025100558040742e811211042c03ca085050032020040039401d40d45940d4400091031840100c43c40c00c03400306a10b5038503c80039041d0800090400c01c810308840b0200d401c010260b07038402d85410705a03c455209a032030303600d02c6e525604010244200c3e02c1c0c100d040c510b803054401d0382000381d6440d80a81c9508540c0c070404d004101410300d00da41c0c08040e004035450102070004032501a07101f07409040c014800c00c0089090100c1c000d500d1540759032185035107500791030308000606100400c954 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 552180773 1250 552179523 552179549
    0x1d0a020f040f0e06310608060709050406150f230304110405060a05010210230106030c1d010e040509030d0f050a0c0314130218040b0601080a020a080a1104 68
    0x20b4521400c4021400c9840f441040c0714603440d610140641c4035881003a0340c14620781c0c0141c404800302c140c5103005880415000002d0f00a80b01d0005a0034403906895880000b200301c1e40034489407409100e444000d003c145850301c1c1581600d100604022000300c006c00522005101d402d407809100d00d9036610f449a030f0243c3c1c0d0b9a82c40c162030074040401d00242c0c864007542c58000011100c0c1420135059050301c2c4160000d013110021b21144070054494118407441040745070b03142c4c45400b581c4041250185c420b40d2000304145400c010004c0400850b00702c051070710a80d04c1c81e00609660440a9803021650944010400da5511070080b13255104200741160a249000e0402ea01d0440a80c41640a062845030605c94910104821030554030849101403800c1c1c00000426401c9001044040f552440038000d0f2140520400c89021064402c440607111001c105081150542e80000301590000300a4003c40c2000d40e8964000c106200061160211590303840c04a0040d2178210192001891510203d070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 552182023 1250 552180773 552180779
    0x2190603021306050901081f0801060e04030e030a1502030c120a06140a03020913050c19210803042d0501091208060607031b060e010b011205011d0a020f04 68
    0x18000e6011110700076035640c074501c010803d588118101d40044070165100916078888201c1e01e0200500090151504110600006846102801200010214600906091b05e82810007030030004400d200d5038440d42204a1480000f400d5403c500103400345064010b8030390303448081869141c4030b0042014501200c802c1045000e1215400100642c5d104404c1910800e0045091040140c0c4500000754400442c000003031040c14444041c6c101c141c040c03421500460800c0011803102280301071038241d2000703907100610011032161568000b61a461203142c2118109444036981c07404054401022102103d400050b41c0c0d08030700203032110701c28142c624030801d034243c90424028030240b00b0071110040c0381d0050001c0c02d8003640b00e0511505015140c04e103005203542c0c003100c20045507200403048607440424040428a01c0c07007041120080540000380c0101240c00241c00980b145900014450400d001808080004450045080710405000d0b400f501c07803484250207070003191250a10b991000c00c2c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 552183273 1250 552182023 552182027
    0x5070e041b17071b021912050601080304060c06050601140a03140912071209120b0a0b12030904110409230c070803190e100b100306030b0c0304021906 66
    0x400700d4103141d1141c0110311501c50a2004036002101c2600100d074180c0a040c03645070103007030f181c58107a20082540d8240b81d12620f0f490550a655008101003002c1250f8400c100003042108a0141042c10021070515241c424002d041045620f4000c1c00700b40c442c0d022130321590144070320320b16042c0e00310200c41d182c0750010b000900501000c004140400e540801241100501207030011001500c0819035107041036a44030b01e980c20359109070403810025070b01030000d41021940c0c0340d01002d5100c2d083c8000c1c0ca082075001081622081d074402c80c842c003000500928030035800000c65100307441c00d4a02259002d0b282d482c9a07280d02881d03100000407801c1c001c400d0340e0750b803008104003880c070503916405502d44c403090b00240240c021440c0041440030b0070404110085840b55030031310000344444022a60006846903d81003940481c420540151500380400551804401d03c900050003840c0402c00507107180c40e038105006001e4443e044440000011400350340768003c0c00680280020501e05501c1e5841c640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 552184523 1250 552183273 552183311
    0xb030d11010c0801180e070b160605070509130f060b03100f08070f03030e040e030c010b0103060b090d080a0201091a010602070b0304030f11160803030414011e05070e04 74
    0x4035109518011500e03202ca0300951100707041c0c0d840742440003e00e40e0384164103002000c40b001c550865104041d400205006148001d0100d2459200310301c00d00c40c03480c50032074155800a003100e010300809006c0385c8181e4481c0720340072201c0000754030701080b0660503000150080c0040c6d003203c41111000410405404400c0b90004202e40c0c0030900525403655919003940c4844080c000c40041c109102d001300b02103441039a494005030401800055036003440c412982c619400381042c0000c0341d455900c0a000c56800d03100f040000c01c04040480d281014040028040c01c40810004101c2031012882d600524401d610032150668005061410f034ac8200d158400e000030f0900c0b512005118444000c0b900d07102c52000c1e64001d80e41500c07012604e25032254251109070132035203401a944148040400c5226401c08a074005000140245a4a00300b80c28919425415005800540da04080c4c002900e850100119014034110801c0091180c030b9a0000701c411210000d402507000e0b040c11b20025901004a01c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 552185773 1250 552184523 552184547
    0x1509050405100204053d0c060b030309100c05011d0a060c030c0e040e121c06050a080d050d110307120b01020106080d111c0e0109090509030307120b030d 67
    0x1101e44010810b6845810703403003075010321500b03d00031000080001c2c00c8070b0505400f04910b030000301c107070000d0004014640428111040005500d003001401440001e110303000030100141c01441c07802072003501060300841c0d4001ca050402c400d0364140410f002080d0320000b4071601c05141d4503108402c1c0004281c0d522924142501d0240c60808041c0405020b0310403581449034503181d0b803100400070810003005041460f050541c078058601c070421000720380401460106085807045a0080203e14240c089403e0740d0000d500840d01a00b05006100002a100e000c032b81c4140380c0030750744981848c8400301a290319a000c1011100210a00100ca40c0105070602c200c52049410010f0301c019400490030ba64045c425503100c0e03001001d090101c01e21130112001c0c00710594080700d000303a0740e80c000440710381810243d410005004a003414160743c0d002d000c03080244048102030016080c4181880d440f4400030f00f000050200901c86506081c0e4207402030a002240102506d032041c4074201c0140903074001407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 552187023 1250 552185773 552185783
    0xe1c0b1603020f0424091a07022e030e0a0209010b221215090b040209060103090b0405010e0601080d0503150a1d0114040c09120c050d03210209060315010315090504 72
    0x110b8041a140c854134500c1b044400c0586844522400c02d1141022503103e2602a80c02c10300c000390b001d00b03041c0506540004000c81485800305849203080080840d043e21405541542055002c0e4000d40e079064501c50640d010310b41103030341e11444000d8290304060128900041c42c18200000201c8070760b0821710407001c0c1c0c05444101e100e040f00000b0501103590b4900024442000385000c9400341c01c0c034103000c560007881070400044400fa40d03101c1030700c0520122401c0b43e05d82c1d112110000e982000b031085030300400c00c03040101418081c1d404060a180402000c51116203015143c4188a9032a644220024007240074131107001001c50b4031100c0c1c0e05000740202071007003c10250540c05400d2501c2070349200701c41aa45c08030f01504203119444190910035099621081c41d04d008a079a0350384200c443c4801e442a11034441e0740685100c2180d841c40b25a9118906c50301c1444885095151501180d60200e100700b406141c2d02040801640240801f0150382c3d8a43c410031404100b0070300d540c2c0900c6c0500d0041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 552188273 1250 552187023 552187079
    0x903080604050118050402041d07080c15030a05070507020a1707080d020307020d0c030b131a0601140a030e01050108031b060106021207210e1c0b1603020f04 69
    0x2000c1c4800e44000384101c0443e60f85010403820b44100940c44a80c00c40d200500103d070855800e00820b0664001814640d280d800890080002d10001c1180d10300f425000d0720081107a4021951404860000801c643e070210344860010781c032248a04115511580d00402201c2e2a5071a03034084a801c0d40f00e042c1114652081d250086021403000428224110443c0d00552600207640e0034030030829081c407400c4800ca00520004400a00d032112824421600c0c02c0d0101c1d500000741c10b0001d005d07508101e089040c1a20242804400d0740c0c8450540450305502c0d942c1a550b861001040380101101d100f03800c01546414004501101d0100080c000150b00701c1c941c0c414030303440d69009612032200384128030240c2e10000f0380f01110b800c64005010344a000301070f0301400c003441c0d007034880ca0200c1c85400500012a5200e28018510700120540c1d07000541c0e85c502038403000c041d42c540d0b80ca10006030101c44807030f082d681d040610740c0c46501220044000e40746041c0d103070b80d030f00d168032203ea081801c41e40c142c03007080e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 552189523 1250 552188273 552188281
    0x3070906230a110c04020c01050601082d0c1308010c020c03060c16030c05070e24012007031e0b09030a0f050703090302060307090f12050c040f140a090308 68
    0x4540d0100c0030400507051880c1c9070580258069a0101c007000d048843c1d0300030300200f00310654030b030b1000c1c242070030004001255518101d070004041103401031495200c8a041c10303001e03182d401410043c0d80031200c0c0119210458a03a014074090900a0480d810640b03201050b021842c80030641150000a141d0b03000c440645003040e0805849030000c880300402c83d01c040c405000d00598450445094078064144104680320a03118a401e1141c143c00400a0042c82c0b01400011010595801c0c203814071030ba5018031401040f00000c0001c0c026100003c0030040984024180c0c1c8003d001c00f01c025075101c10080d08052080c205040241074006c425218600c0b01300020b09075003004001c542e6805d01c03c1d5144128181c41e044140c0d0310382c01c00310b819000c010240700007000580707e01000354084d03c1c2c55103504201915210045400c0101c98210340c15180184032400700090f4001101102680d0072103002c10390110a681030301c0200b030840700c0000d000300360000b8048480782c0d641c001c115041c0039554220607aa1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 552190773 1250 552189523 552189557
    0x3010b0402091c08040803180f01050a020a110f1e3f0102070c080604060e0106080c010e1f0503100905071e0207050301061419030f0b090109050303070906 68
    0x1d0002e038581c2180e0000f21024509280710311402031940f00344070840c146501c40040034510703080100300800d00c41d41c1002c1c840f081c1c60144e0a50020070801d2070518a4a041448001d480c0e94080398000c052801100451389a0781e0780c0c074031a00311582d01074a0041074201d4000000301c0640e5504010340074055202c4046c0340b001d0010320350782c0e009500a03220a050315a4216071703520440580d42c800c4240d5824006031002031342c210307011f0000f01144401004981050b042a004644580025820507031500c42e040140940218803185090400d00388604182c211070f001c5070692190a059242c646802c3c41a081105c0d0000041e5004868020500020300e44030044202213501c180c0e030b881e0100302510404100c0315046c0f80b68440d024040c1c03040d12002a07070350010030309640c650341004c0320181c504518800c4078100038140c0301412440c11100c000152a5880c1c460301800c0da034002401500038000016400c4100350419200154490b00700c95032880c0a41c0000c010500340e00031640011012000c9040e04c1c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 552192023 1250 552190773 552190777
    0x100c03050c03060d0b1b0307090302030c1813060b03061018020313080a03180b061003110304021513030c090b04051603270b0a14010320060f0d0b03010b0402 69
    0x101d0141c203c2400b580d04d5203612492050050003c1104214030704400d015070701010103940100e645480d0740010500350310415040540403800c1600034240841e24202010483c4002ca0b0400d4008220000d5811107007001030140a2402e0b4040d05403051906201d00580c1c900c880e401200c8125250b90054503100300e1602c00d03407000f540e801c11040d840c030040c5004940204010302100c103260400043ca62043c3d000c0492035510700038180c5114058008100c0d80e402d0480348503511315407900c2d080184038a00070003040c150002400c06401044070748103550b0307004101c000f1241c44010071940044a2940e030b141c01480c401203401221001c0c6d05000c4500040c0c00c0500270079020340081c1025140c50f04425000301e00400c1e0000d2a54144001500d0355190b007910700d58262042400340400000a00c0c115107000c05480c4040c0c0b001004d000d10100400c0400c0d04c1010000d0740c002c02116640701240c5105c00102c5034081c0800a010302c0800240d040807402495200c000c400009400030b0140c1d40312038041004074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 552193273 1250 552192023 552192031
    0x200d0b15100507151b030c120e1c200d03060501030509060609041110110106150f0503040804050604060c020901080304060c0b0a0f180308090a02061b0f100c03050c03 73
    0x1050b01031094100180e8030020141507281035101c009000c11900313588803200e514845140c40441e585603d00d281c1c0684c040b00000241c40c80d060113001c0c0c840341c03298044e500e4500e00e882c1c50282019400310140c00c1e21481803000c44045221541070811144081182c030340c0c0c0c1000c94400449e1401c403000030a54007070f0141d6449101000c0191145940c1c10050004068006000b19070100c0040800d4420390f40da0040f60f50428840e0303440c0300e103944a04030300c2070031181c40d1b030041c0d00081c40303044240f80619400092141155900d2400c80d849484a16128655004070740200d58414000b25000c0b400c29800f040c00d462690007214401c4080c1d80c8e030b88219440303100b80d004090000720002c0c04075001c18a4030b9034090700007000c40e000149a00e8060705003c100c8046400c142030b0040d46028030703024180d001d00b0709034101000c4806051700352a117600043c403038820001d06084c1240e03518406900541c2c24416204da0481c20170035a0703004000711300d0400040080c984c03400301103481c2c0000303c0c0462408009032441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 552194523 1250 552193273 552193277
    0x1015020a120507020f040606120e0c0607021e031e0d09080304090207050a0c091d070b09040504020f090907081009050304060e06070c0306061401031404200d0b1510 72
    0x10341001c00c1400c0750164402c03941603030854540540401e5a844603c02c11000f04925512228065509000c841c06c2d640404031006040e030084003006084c0c6e854604480c0401e9040b520b10b1140c81d50024540704488410006039854083c242628141c025140f0100c8002d011120907140d003884100030030745044840d40141c00d01c603030041c0418030500565500078101030707001c0c00454010211a955000f0000707440d4020101444d01d5095000c0241003115030040c500007154060701e24981001c00018081c041c0c121018829a116000f0800355141c6242c2e02c440c0410187c00101280b5014080303030740e140d44030700ca018501d100b00c10b080401958036220340f2203441c4e8004050340c03a09140450484034003400d03e011941c0b151007084a640024214403140c0b006503c6080c000c0340c65480c05c030b091000340c515a10014140b5041c60f000308035400489091582c4241d108045020f40104400f212581103001240540c10100700d010703840902c01600c0c9440d100e9494446070449590b0308509202d00181e4030358080c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 552195773 1250 552194523 552194543
    0x906040c1b0c2408071803151b080106082703070b04020a06090e13030908070801060f06030b010c0f05030c0d1106070e010504060e0d1203020d06050a150507020f06031015020a 77
    0x40111b20034044850b11003545c07449201000e84940720341e030300030103d032203284c2015a560103044000c0360310b001444222805030500910741d600d0100040c0024a0080c070950010700020070b2140e441001e0b02a00d0300c10b801000440b600c91205260180481600765003d82c0311b02c10983e000240c051180411f28141c03a02c189180c0e01c1034403000294000003141030000c80c2400300000005c42d840c0020083d2034000c25081e000422800e01d00080100c0c00192504010b0030181040e10340c0702d140c2d030001540344900c0d9020040e4420000c950900c4e0f0f065015500541e14a4081c10702c0e080f03010790380141c2004403030406409403041520b40f81c2050707441c042c440c4090780c0418400c0c0810041a8021070300401410006452402c5021031030f03a80e0800c03803e20058800100c2c2e400704000800c0c0c0d45a20400c03000d007005271032901085042c010f080141143c0d901056040141c0011031100310344500b9080040510098000b1307469042c5240401c441c0d1800d0702402b0082d107a4006103180304c40c400074000c1c80391500801004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 552197023 1250 552195773 552195781
    0x30f15030d0e0f040510300210020a06110c010509010207030c080a0c020603190c08090319050706020d09120804021008070c02030d02100606050403020906040c1b0c2408 74
    0x14a0a840c0301202c81c0d400b030b2840e200c8181c180c0311401200d04c1000a00202c00c0e03001e042460050410340d01c5c03c510788941c2001000c10480400441d210314110b84c040307508491006c9541800c070718002090701d008001034105a0566851001c5070050000030705040700901440d40e42c014214200d00410038040c0000751400c0680e400301e114400200100c0001786040e00000b0019000f050040c2e00c240c0b50a070601c40050188292100076101c0c080b40c599003480e0442071401c0400184d43c0d28010302643c080140b0341401240da00a0003002280c02c40780d8480015915034004034034100c0204030a00054400b1540e407a0308403142c51180209511450f0b0003040c030300d0f4080c580c400460384c9a200070a008140038040000c24007698080040c017030f101e00320340e004014040e0b1050702032041d104654441001d03c4420b04c41031005a8881041c55031050007618000340c001d05c00c00b005c80710704950703480c1c142c00011210030f0b240074042c1c800411020742e980383c1c03481c0c0d20b031008104d8032800794400055035000142e04071000c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 552198273 1250 552197023 552197027
    0x1409070e04021309080d0513170d0e0a06020a0305090303010b0d050402010504090e01060611030a0203040e10051009091d0d080a1508010506130c080703050a02130b030f15030d 77
    0x55801c40d0018090324040c5201c403440c2401c8400c5141d00b41d611807030224505602d0f205174002c0c294416078804c0d4001703541c02c040e61500c10940303002d5050360b2580400314225030941c11580c85901404001c0c0211108102103040040003503004040c1140040c0c145000602000c000004580c12140031144c01d61904040141c00d800400026204030b04100d801c100000c0e44120b0390280703510205000740000368041c030f0210003825625001003101880d41007806500c40081e0080701340e40031101c140c40710050f9940c8400f0380e010800329941000b503001d40450307504030f0380b0b03580031450905031103121004000a4403111000c502451414040c108590312403200601031a1041071800e4125904001c0400c500201d024840e0036081c0b0b90300720040ca07a55a508020325481d01206100011845810800c101c0d0300d8080000d240000c0280004145901e85000c00c1034400154100c3d0300f05100170f40c9950340191291701000065005441c5640003001340808103215940070b0b21381013925180100102781c505070803241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 552199523 1250 552198273 552198299
    0x4110f0d0207170721030c120e070302032508010b0d0201300b010e120a0f0507030606140906041104060f0e100f0f030213030305030a0e1b04140907 65
    0x41281e40400304a43c4404001a00c0c0c040c0c40c940344a605512900ca801c20340031858980210003002c00c1500f4480c0b1604290b800c19200000324901c0d450210b480b042d0f080c3c4062518201e5400203401d0302c141040001c2242900c0700740030a1122450310100c52564802e40c05090712a4014940e03803105011001400540c01601c0905c0d010100070070901510320b8024506071084010050000025214610465039690206100c1d01e0014110303008111030781c100001c156903500c3c0307a00090070440300c103d0302c40038000300b04484070045034444030a02c01507032950001203440c0702c0c1c10415405142c40801261844c6072034043c0b0000b988855110a0520345000e0301155122254004003040c05544810030b44c40761250303211482042c206403601f100680e42c2041c0203205075482a040c078100351040c06100b0b552049141281c08480d050714142d07803680c98100b42c903801003032034500704412071052410159008101c40030000070800100c80801c0201a00c01c0410480c141c101c2c1ca01e1525000b440b0305010f000e5002c02c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 552200773 1250 552199523 552199537
    0x21912120f0c050c10050f0f0402030709050c0d05280b04240602160803040311010e033f0904020f040b040b0403060b1002060f0a0e011a04110f0d02 65
    0xc0450701d81428248141240c100003622000038000044030828203104000744070819400701c400b0446442e0820b200183c54002400d2401076005450100c0d0655070100140400b608503064100a030741004607540601d0b0b80540340ca800903070b00700f0000031510040c403505008074042daa04800b2902c92041704000090043c0c41107241c0c00f07940e4a5500160044884001c407002c0300c0301d5003034120b0a08048019140c5005e5410780780400000d0003050200b071001109480440e94800340d810300e804071803001a1284000e52901503014840e104509070510301b11264040e14103003060f10071a11300d0f1200c2407020007000700c000249840408100480d0241402d038001c0041005240380c1d80c1c14161103441103c12036210303034091710300b1120204062041c41103e201e00c03e4a407108a42064401410b40c0020b5210507000300103114880c68180010040415a0803040100840c00c2c000c0224500c860107248610100c140b078940941d242181802102d5801401c90782070031001251581420600c00501c000b0790310400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 552202023 1250 552200773 552200807
    0xb09070305070306180212090307080d091e0b07080f0618060607020409050d110309090411120304080a060b060304030e12030408070e0702010f06050f0d02030c06030106050901021912 80
    0x44c0000583e60404140c802a80440072409680d80c40747e1075030f00041500151000394650001c1000c400000c516404591142000d600003007074280035400c040c048607030405c681040210000b50103504200840c03000c00c0c41380210352240c030050386a005007402a0f400c1241d0035a000740c0800d160300c09160001d80020b034030480040c4036515000340c940c007290075500d411408541c1c50b030042c0e48a400d099040b011040c8020007800003907040c4801034001039071100c00a0405407803e60070f403c0301020354583e01c24089004507108212682c0c2c40e6144985a920301803a00d00340c44540c513100c104802490520220780c0101d40582e40c0b42230214024040180c1741140000300c0034203100400002400345810300c0044014204d40d40e00046ca407030103150207404d5527406d2284681c4989041c2c41480166207100c810b080141e020f483c00c000c11080da01c04a403406800e074220355401040030000082e0540c1c0a0000c0006140070303130960303150a100c503052616917100150000c110548000102050520a601900c1402c0c2c0c80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 552203273 1250 552202023 552202031
    0x9091109061809070503061003110705071e0e0603060412020a05010c0f0905030d0207090b030f0102120105150310120213150806160207180b030714040b040b090703050703 75
    0x300001a0301c41d805a0710718003803090300100520706403400c0402c455006525040440c031b5803421900150707510072080080014180d481c04440c05585000055480503070703005c2c5c210b5140c141c0b81c8251041c030b814004111845900d100d03401103203121000b0311960040308098010201380d11147c3d00c01d0382ca002e6900c1c0d00000c604c0b81204081c0452001d0144140d00c5940c0c0d100c01c003035508902802811000c40390001d07806a844680c0324141c00d80d0000b00300040742d851403000101074485030002400c040802c1e40481c0715600110342c160500701d1400d0386504840c0d00304d414000d07800c1c400b00820081e01044524481ea1400004100801001a05403280ca80e10003030960f64084165502c0100f01c07050700702c150180c80c0102c40d043c441d003c010040d980c0c1105250301c3d40d8400c4c00058030009c2d0f4942250052240505181c40045441c40064102c50a4540000d0940b100e10f030300e80382c8500301c0c0201e00d101184114140441c00010b418148100408030b01c01628030000d80e5600c0800b540a00b0000c3c0c181c108150366 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 552204523 1250 552203273 552203287
    0xf062b0809060f04030b0c0a0f140c01091110030c080a0207080d020403030309050115150c02031002030c22060c1e060c0203070201020c041116030908070311011b0201090911 76
    0xd02e030003003031400b80c5511503948650450420010102c0020b00c440d41c1180704001c0c640b06c881c1c01410342c4400b140b00d0b161241104050b8045000e650182c0d0310842c038158280703c40381d01000000005c4201d2460117131401000e0064000d021800d8440351400d1030b0101c1c80200104203100720326002080581d0060000610b00440b286582c8201d920991054000941d20b240c1641001028000c0340c8480440c0050074422a080c00c0500d0800e8084815440501481a09406c02c648060080c0306a1502e40c0508644a182c20b0b4452201d56122210a400c2030316a00c0d6070700c071200041501d11041d03c4840e0380f09030100495239108802d08044910007108a21b0b0500640f0005255024005100c00507601440d1111458030029241001c00105248a01c0c108254a08210700c0343c01a61502054076072042007070551401c09a84424154020002c00c0c040c007080803050001d034424800041c4400c1e43d48613080e5204a80b00255502c2c10b580007800682d10201c1005003c145801075034401d60301000651400c15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 552205773 1250 552204523 552204529
    0x3020906040f05011d090a0218040f0605010906020318121c030b01030612050c27040c050a08012a030b03031804050708090a0219030f05060f062b0809 66
    0x40d500c12080c2154048043c081d65034010107003101040b60b062803061820f08040082e42c0b40074002e1816040990114044e50f24000c411240b111440014200304501e030020705c001e0018080e10b016090101d0641200003400e50301c0041204c1000d07482d130350a000715801c410300f001001c0f44078480c626035a104810700d0065003403031480940003601840d20f000862900e64400134080d200240c0c0241c0080402a10840200341c010807614800342044503881c90403500ea0b0304800144101d170505600310913000c0100000c0000b000060070507643e00b19004030b1455034038681242a12440b11940400e1a80305211302c1c4040011003209802e0702c0c0c1400c01041001840b40482d165820400c43c000000d140218280f06505052050580050315031030030407450704d49071488a03561105001c000b030090100d14422208101042181c80140d80c1c40760303c40c0e420f54214104181d60300c000b80c1b2a502d40c4148900820a87d24241284090051130444581c00718615410b00040e10700103560107072202c242c104a8620a0781e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 552207023 1250 552205773 552205777
    0x30601120b0109090c0b0a0f0e0a0302030622080c03092e0e01030609020c010609060909030507080f07080316030501090605030705011412090a05010e12090402130e070f0201320703020906 82
    0x11f030940d8501d100544c1c2500010a0310803881c102901407021a1028405030b240440c410b42d0044a280b00c58400b013096000b198030000d52850301400450b000320f407907241040040000c0c010894115494180701c0c4c1880c0d46848109000c10b103040702d1044481008174084d000f00c0c403036205088141000510241e440000c0350903a071000e0340c54941c903591004e05101151007440390038003a18003000d003009141c1155a0140003481101c1d0068510b00012070b100400086010880c0d4400b0707030050b15183c582c18204010b640d012002120540400d0515001045a194500c00c02d0110740c001402401c140d072420005441441c403d21103460344010810240c049240040c641c14050010300008291980c01030a05030f08503403424a46103240d40180103500e00207240030f4180c6000c010100c0d40140e8030084a810001c070101d03154498406842040104540c0b2500240e03050403000694000780014442411640b003000c0c204107550707800324400314000d40203107000d81c18a5031065480c02c0052802d20b213900042e040b6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 552208273 1250 552207023 552207037
    0x901120b06011808070302011205070e090406090f03121a030705010e040e19020a0602011406041e1104080d050c1005100b03010b030a060e100e070207180b030601120b0109090c0b 78
    0x2503020705c008008550740080c44145a2917001402c20150814090080260307542038603191240d401c1c10046024040c0c5640890381d41540a042c070206008030345809030403104144440350601e4944800031103200400c18103020311110040c040c199940c1814015180c00d42013503041900300f039880f504010038427820420f031814908512500d5610b16001e104000160040c2d030059821a418404250fa61000c2c0d403901c0790f004513048030045403103070201c0d41205030114242c4118aa0380e00313150382c0c840d00c0a2004014410f0300c20403002d0300d500f803001e203000355018842c0c500e184000758024002881c0e41d020a6201321380124160140341040399680805403202c0c1c1080e00314242012000089c000d0300e1860344030701001894101c50b80710b11807401d00000300746850284100c62406540000083c1a035100b03000d40b030003810300c505800e982031003809680c1006086201d20b0600a1284200100720a140103065890b441c4d4001d5402c0000c2e800c151218029052a00040301c1005250101107a01c4003032001502c29 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 552209523 1250 552208273 552208289
    0x806040807060e0312010e060d050d0e010e0f091b072108070806030a0219090609020c16030f0f230c0108010b0307051b12120103110901120b060118 65
    0x32600d49082803002c5920710280320f1401d80c020404541c42511030b80b1080e04407148031400c00c1d050b6544502085500c880c8040050581c058501c000c6c101a40140c1962629002aa625400151541d062100c64860031134003550200c04207000a825240c00001d4240028000084034144095035541d04404c1019803402d010701d10411010642c501d81c090b2180303901c0741c0c40d403800c0101307410b128000c03d4541c080440082d001d40481025045210400030880300113001080082026586e2038001c0002034005159001290040c4e0882034035a80c0c0c140d8514098940007219100380704112b0b901e0200c0d031400c1c03200c00c5404104000f180c00300e021105044500314415540505540b0310240300050000c03005812141c48280c091013403002d010f92160507200b040507003180d500300029451100d1458920501120b214048000513040c1c42600407281940c101c0e803051418402d0300c05002e080101488003401006480609446148003040702e064096411210605120804221417910100766102e56004805 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 552210773 1250 552209523 552209527
    0x50f0c0f0616120902060301030609060b0a320108061009030803011814010303050d0c0c1b03030807030c050d0b0409150219140a03050c12070206010e0702010b030c130608060408 78
    0x2085400000d0724140481c03002d0f00f00200e00300c65001804a000600016001c0f990f1070169038200404c0303512504136440c0051a007214240d0700c000700071420010b0b607101d400340c58401003e07046011600030a0114140705845031038181d60b803207060101445904e0b4260701049414400000490050030045018044040c055a0402e00c1e1050f60710075510042c02210303040c0ca04a00400120764031006803005100c5401c0c02140312449024205c0d100d0206501c090403042c41d10211041050702100300c1002ca901c03030307200c0407000d82d1504015012507841c0310541c0c5c04540c04015aa9403407210f98020214518010b100094815598448c219100e50b90101c604006030300048102c20a03942040b180c2e8100d81e280307810180d6415655040c1c409024040048081c161544089030443c40a0016200c4054407042565090303d0581c3c070080d520213003032290202c201d4246010414061060052085407040500100221b03024501407250746001c042202d169141c0c2d4440c04150300300d090215900450082603095 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 552212023 1250 552210773 552210811
    0x1a1f0e07110d0207060e0f03100b100206010e040609060f0c090317042d211a01060203071b0f091406010c02030604080a0c0f0b1b0406050f0c0f06 64
    0x10702010703640314440700d1030b5000350090107035154001059000d8a00c189402c2c5c0c0c401010300c000c500b0f1003099030303a0254503018027040c0c01402441d0f54800440d4040840310280c450355070140580c2c6520f000c0c01101e29401d00000014042001038021840716449444000b070105280140c107000c903003081c10a94002683c80004000b40600900902ca02e0310008500354a09498030b00400042c1c402100079101da03000403610308503400003c048107001800e1000440c1384492021968030f00414502008481e042e850300b180e56000c100c0440f0741810385040e07070019442e15555803600d015198403070302c000020f0040c2180200303c01c4043d03180340d8020310250380c010504d10700300c2610b5584400000d00e028100312040c4068405a03600042d01030708584c0003207000d940c401035260116030b0409201005088091049442c3d000c1240800c00244528140300c426903c02107084801000741c8100d104003400550280a0036050709286401040e0284101c1d00704d4143e034002500c52410030a080f01d0200c4c09074a844014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 552213273 1250 552212023 552212027
    0x100206060109080105060a12051c120507020c0603040605060a260c030105040f02090702030d0218100804030e210105040602120106020718110c160501020c0406031a1f0e07 75
    0x20800380c844100280446c0c90300c10b0114140e911a403084043c11301c5200818824840144494800000032404200400b0700c642c2011b404102e4120301c106059140c000095074462000c0342545802c1401040309141d92a5600d82c48040d103000b400c0f42c3c2c0c0c021603200001510707045044020803541040d0302c00001c40d5240c02d040500307180c0506034030350203030b41032104000004410345050040030740d04a507030b0035180c4c0701d440c012441c40c000c3d900e4248805200017120140c107900c84507401e40c40c030030864404040d00b042c964100c55118084e50010042580d03140030400d54a440162080070518018400041c0c400740b43c061802d4800a0750b040d03a90f540e000801820355118851007130f024105a000400500e45031255504d04021004080e12903595030342d02070111240080101c4100b40d54003001c9607031f44049105d020071482e460340310341070152140d4803042029007003500400c0200c0340c00007403080c2c8190380030b03004480e180307001840041d0074a00c42e00011156009a0017040103044600304030300703092800d040c1c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 552214523 1250 552213273 552213287
    0x211e0607030e0120031021020924040f0207051203090f0304080616050405031c081e04060f021303051c0306080309130608030a180f06020d0c08091002060601 69
    0x2c840d10350341050b011300c102800e0860740800c1c0c40f4001440590700d03901c0700140341c1c15106c035401c50a10001c138040e0105510911544105035a4000c07201030341c80e919103824050241007011031881e1038082c1550810071614080d40105500840c0d00c10240c0742c035a20f0740d0303030b9418088100c1c40c1101080022080c00a840d070b04012500c07407480d0080007545881c1c00e10105503074515000701108840d030182d011070b0600a00c42c1090320010100682102c0346d032084d6888811514501d1901000040e00c0800061190303650a2a03c16920103c000c0400307803500c41d0b13125880a0084101008040c6800300716120012441c0820400118006d80140807543e04090505a000403800c3c054000c05003881d0007440740032004000c541101c5421181050749800c0c1030404400307004c09500132100350002250300c1d007015800c159100002450401e8a6060315117079840c2c0402d110641c011840160700c10048850300310b000b0180310021900401c051420030f02c00034000f40401c41064281c60041c0c11103420f2000c00d5801100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 552215773 1250 552214523 552214541
    0x1c091403010b0d08030601030617010c0f14070f0206041205060a0c0804080d0e0a08040602011e020a020703021011061005030c030106081c2304030c0f05211e060703 72
    0x2884600c180000080c100d10f200c98018250440000105402c3d03802907100000410728030410b00080b404101040f802880d15884034004034109040d8000d23000d1061500d1078459180081c081d081220744d4076120350052030001e089800c10300402010603450003c0c10070400c0385101c1c000401c5140b80003040c440035500024008403d00c44110148000104840c081c1c5400100613140000c1c0a203001041c2440c0074414200505102000100800c07a030768107400940052501c0340030000460385a40f00030040344926000b0300010b80000c0e4080c00186070800000b60a0000342c901409541c08000d80c1c903090200075101c03441c030b031013211000704510f0805001141c803d010840080110500e0008440d88130364050b8540104c034019100300c4c80e07069000c1c90b84600d810f0284900c00e854604115031310b810641c0680819201d8101c1e46c08001008480080010b00b662070241c1420307412400405500c1c141c13001d50300a030b04240070350b20f511881507403000d1509540c0c28076100207001900300030b0720180440d02d41c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 552217023 1250 552215773 552215779
    0x20718020703141303020f01020a0b0f161b060c05040b0c10050705210903070f0b090705030d0203040b0f0705100614120a02090601030204150801030516140f031c0914 73
    0x3c400000c0e08814802a030017160b4042d65540b001c00c0c0c1500041f81020040a00101000c00320020722141907500c0c0c030380318482c10b9503d070002204c0000356015240004060071100d0502682e42c2c44a0014000380c1000100820b0386c00c0c920300b03203030b1240500b030303141d411002e2040071a50220202c04042101c07805080e8000f025400d11504c1c00300503920451840942c0001d04410743c0404000c02c40308101001150112600500c40141d618101d00c1c00008007441524441030704d2140b00700c0490245004542c1d07482161841c0c008500e400d250220301085030b008207003903000f402404e100003004100240020181104d2401d4000b45441c00c000d0f1000640315026909030041000300e56500c404800011502d09560b0105c0f450081c96031100012000b03072042c2c1c0c10003c0f081e25947c495500e403a82200c1118103907031240090340c000c9a21404480041901440354060032049401c00304001d0410f9080e0016901d00a800e84130362100312511502c0416055250400298880d0820448020301614003445140c0403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 552218273 1250 552217023 552217027
    0x326040201020a02011805060c072409121a04061d030a05070b0c04030615060f17010b03090f0102041e050301020c210d0f020a0809060603100c02071802070314 70
    0x2940000350355040008009041c0302810911802c0b8042020f143c80c01810b004003c1c1d0756034490400c2d40c07520b85480b8891b09211803070441c0d1250404000d480740c820846080d40d07588100528180048880d200702d6501502c0c110344081c1c02c140c80b00e05024103103124a0140e41c0c045695036261019150020707000282201d80d07002881000d070550741c018111006a03030041c0b002c0d10680c03124101c0c803005200d07652004041900e000c07940c00c081003074611040111025a20f03040c409104106050300e48400003010000b0000800340140540181207003d150410144400c949014400c0c122090899000e608104002d071403800c1100e0f201301c0c03940c0e50300d0301804080c0c0007503040044c0714080307554808a034a800c2c5408980b010802c442c01ca40c4030280c17501d421038100c082c0403055041c1c01c1c41009510400d2580b00041c040000500043d00000c0e2075030240780c028000701760b202c0310400302d030000b400081c02d10070460249081c0064209060300b6109184a10f1100c01aa20301081c50003800140f59800454009682 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 552219523 1250 552218273 552218281
    0x1204030b0f0f0a0c120c0c02190e060402031801060303020f0f1b101205010306200a08010608090c040608151605042c041b0524070303090f0326 63
    0x96002000d4010714041c00c0420b114113005415a0380c00c40c6105058a2549445013196a03150b000c9100100d15009540c01196618055640011400e09002c1d590781c1220400104041e818150b0055a000003241100060300a01c1c0c20802d0030758031030390300540c010380c051189040703a00800d00c00c2c4c04039002260002e0a1950380281c440d11002e081000381489042c800045108450182d108000b09104004c800c109075078503031130070100600890404980346004600800b0031104550120780f0042225103e90000385e1a201d011102f02e88010840319580c040c600c19194203480e54003c910180c05850058050f5007649612098260002080ca0a0301c4003d80e100544a682000031241030b00d0b040d40d00182955801c1280034000e00352103081075403880c071a004110501c60444c10300c00d403558182d131b8204412381d82e07042080030b41c080c1300f00b0031039914401d002d0f440f8103c0315001c01482640d04c207090201c4c0400d169244c0b2954120800c2050700402c00742c00d2080c0d11a182c03040c082d6031450340000703041d605042c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 552220773 1250 552219523 552219541
    0x2402070b15130902130e0c0a090614010c0506151201140a0c021c050901050720040b04020a2a320d050a08040312050109020a140f0f0304030306081204030b0f 69
    0x83c0e0804030381800c40e5986c0c0e20a80c00e05050005138100396010744410480c83c0c0e5107003500010300240c401c50900b040d00b558082007a612840700c080b1015001802889680c40c0c1c40308440c0e040c2441051594814100c001d040f0f00708001780110b401c00c0c8107494260344145840c180c100b00f40c0f501c00848000f10b402c480100a641e590160344101203101500d00161145061401601c00344190311026244080f20b09600c035000c41c60514100759107200380d80c2031101d0034401d030502c026805040c801801091403405942d01d4000010a85000d401a450510494020701d848003a600190130b1590303e0b03002100030182c0500824a00d0002c10100040010440c10f909504000d000f80510080c070410403000c400814280752242c41c918135003101e034140401031940d451845000a40c4042200d0003ca80c1e1550020307000c81815040e1034110035940c003000c3c5842e03403210071942c541e0300041c011400e1550345c07980807490150410245450f02c0c48030410f0340d40c40b03003103090002e841c00c401016030050302302060401040507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 552222023 1250 552220773 552220789
    0x30c0d0c0b0304030203131413110d02071106030a05070810050108040b04060f06080f0d08100510050c071e05041b03020a0215091606020a2402070b15130902 69
    0xc00307251081d0b031261503030f00c4c0490542c410220f180303441044101c4046030604400340002c1d05c0e4101110515000255071200000b0395200380b2041c0c9036440103101008a450480e0000d0a00391300c150149055406010009078941e04141c80125003076070748070104200c150700700c007203603800555111b40c50003064508800284407520040c40240160a0207000c202040b445801820640000b50303424050706840b074080300e95075094030032015014882c02170400700840c01210000d01654164070030718800703400e00042c00010300500c0142030411004116543c51100e09000400c081d000000c4a5a04070281055071242e160b2640c02c43c0b84aa4542102c0303800914086c0201d10220301c40b42405611640240016403c0000717414240e03507220320718010010140d20102d10350b01520b9008500914168480000b240c2e51100400014074410740d0110102c4c0c81040c1d0304003e084410440d00146c0f5054260341c0d01c10700d03410160303001c1c0c00344400040020310f0746c0b41400c954042c242d5080e1003085000c0c83c0b030300003034462 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 552223273 1250 552222023 552222029
    0x2103010510021b060a0504080f06060f0609012f0601090203250c200a030302010b0301050a200f0d0c050705060c310e040302031b0316030e0307080f0a02030c0d0c 71
    0x244e90001e401c648890044007500c0013495914140c803030001d040424584c440b1001c41c0d445206840444042400d4a020380c19200b03510410303502c456100c0994200d009201c07071200c4502c081c8010783c800c401140c00d02004030354040d01441c03001586030b0410002c0c0814454a00f814401c01211815881000035070080c1d102c0800d94014100d64810f5040002d05c0d10a0118031401076040400c40f003001c010f2607015004000d5030388090f00204900d5440d1040300381211207084106003441d490b0106880714243e1035016088044007109030501d09694a055102125448005076000c500041842018804c06106040d44951a140c0d00b5217403920f20303c8004070b170502e8403409800300a081010000000074141c005030190101d51109901070605007000ba41d40e401c0914044036000040c1c422080c0d4000c040282e9025a480f0900703005462001d039010340d040010808582d406114014000a04010400002c10a047c0ca40c02a11095000d030040c503050640c00b80390a402800c0700c0c4036880000e00c0000c0d242c411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 552224523 1250 552223273 552223279
    0x109060f0c060e070807031704031101050f0409062706062705030d1701060e03060a09020315041b09050c070605100e0f0f1303020705010807022103010510021b 70
    0xd4400034a440342c0100503003141c3d40d0140c07050403004150540001035510503680191108450300741c2580540000d03203d5070100612001da100c400c040e00754002e1001c1c0440010b841e54003401d05448544410881c0c080750302c00504880941c0e01c0e500851319449000020003d01c0405006242c00d160014000300901510224100c0802d00c541e002a01e81442c503002500c00141613580c04500400001c0c2803584401d69070303000f80125800012100d0241d0120000800054050308441c0e40b007000303440040083c0c00081c0d805010300201303940d003031040107910380c4214844c282c510f50b00d02c14200c41040400c3c1c540c0200b8100e920b8603051102c19402e13030090b2015250b0001011602e6940c3c01c0c44510ac0c050594450069454118140182000c00342c0000303100d07009100e03903254555281e40d00300703651003c402c402801580204d1014401c6510079030b1001c0d4040e080380105d516408900703060f079054200e032035099251144040010300ca01d190815407450064158401000c0c10307110380521500c180480780113184 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 552225773 1250 552224523 552224537
    0x504120c0f030e060d140405150708061e03190605180c0d050c0307060f2a0b09070510180503070341100b01140f0d09060207030906020c0109060f 64
    0xd00341e40388021902610b214001c140b01b0b01459000300d06100500340c07000c540501403014107503504081902802e11940d5a951011402e4840740309100d40b40c001c10b03203840311075690094000040d8600700107500c12000c5111864402d002a400d02c071084030005016141c0000da0300c08010008240010720700701d0324008403800b100f1121146005403070102e522503465014003817010001200c64014411000308081500c90794040ca10310f9400a1464102d0400080360296020100d400320b48031880040e4404801e0003100c00940d22007001524201c0021301600004401c4006044400d2503003c2486c01000c00381c00903d8500d0a41c1d0781c9950200018a41c00c090307400c01c005801001481d007400320440c0c007100e03100001000350180b010b605c81281010300390b006c5050001d0820194803907801000c0745c14034061740c24140441c8045158050380040e082032425038075821460082142c40c401800090701c00d88640b8501440d0800103410030711340903242030501028440800105400990110b00e08440e443c00d81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 552227023 1250 552225773 552225797
    0x801050f1008150d030504030308070503010b0d1a0310020d0b060a0804080d143115090305040f0e09100c020a120c05010608062e0b0f040e0a0504120c0f03 68
    0x1c0c0204180343c5080d8403043d008904402c1c141c00c50300610507070f402aa51340c810b607502c43e00d00b900c0b00c0c0b100784030310721001030708020740c81c1180c03681c0e4001803048030078032012071004a400c2d0001c0e04e026000d00601950907400242e11444034210311940000d81d405842c071b2030a2030354009019201d0f00c00184040c15550340020726070700045a99002ca48403044055404200e814014803030321030744031500311211105000c0b0f00403041200c0c4c02591510502c0d40000c03036600520b411362030038000c2c000c00c00c4101d0900800f80008100d004051903400041c0940040380740c06490441c6419107000d050303c20348003502c0e1518035a0328040b84d0200d451602290000c40388125948103c0c01216a40e101d000c000d441946421400714070058041003690160407641541110030b0000740707820700494200300d6060728884074003008001075003980000c0e0001811100000782400e40d152000001344100b298400c0d9140d0f03860302044200100744900a50300b04180ca04450505031a40d24802e40c552221405406e021000c4408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 552228273 1250 552227023 552227041
    0x30409050c0706050f060f09040f0210020f07080307030e1503011514030906010303030c020c0102150901091202070501090909051905010f06060c05060f090303360d0801050f1008 78
    0x5500d02d42e07000b481007025140801c01500f200400f0b03102c1c1481180903000403080ca1811744080c0d400b450300840c181c3d6038000c155080224010880015400350b000d90801c2d01444441840301d0002040324170040c503a2207040307140c01410404c081c00c00d01d00c02c4280311044000310744000103403810b41d1402c03104002079901000702610012000c0e0041004003c00100f0031040d040c0c0819a14103da06c25201800fa06949210a0341c65511200701580140c0c00004c54200700345480c41c0c0b61390414007403800020548202d894400e1010b007c3c40704800568040030f001c01165a00c0289400100300101080008984541d079658445406498a490241d100968102400801c0d480003601d001036040c2000a1a61040003605200701c28606480764020280010000344082e1300451040340ca44018502d540e944d801c103500e40c0071803040c80320340c0340d403101c1c4942d0720004008100304003448042d4024010100c070642c00800a84050b0441c60140d80700c0701c4c00d140540ca560302c80031013814071801e01190340c1e40d680c190 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 552229523 1250 552228273 552228277
    0x10082806150c0b07020309030307061d0328020a24140a09060f022805120a0f1a091618030609021203120408030601030f06080618060603030409050c 65
    0x1d41040000701d41c262205036004062241c030306100e6071441e0443d5031045010f030f071a40100d281e800c2d0950020003069001445a60000b8040c4240c4100c18644c0314a04000919642005010511084410710005070341085911a1038608002380f00034200d078200c995412100010001024240c2c03c0384001d140441007590b04610042240910f122605242c490701e014040c0c2403190090391020310f0521050329090f80740c02242c060200c00002d080104000010050f21018103a0411080100a0201c03c01c251a035aa4250258000c01408240b140c2c042c00300808481c40c51142e010348002c030f003030846601c2e01c0e030050317090344001d03840c10166030f401c2040800e851605014428244920b80e1381408401c00c141c07030b03000514803802030b81c0c00780114201001f00c5c1c0c0d0340e1044805046610300280c0001340001c0030400110340c040750614001c11504807440542054a626801c20069a04090100031500354000203031a00e06d43e44d64014030803800c1c503e01007510ae00c6203001c0d46007800e44460024000450003c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 552230773 1250 552229523 552229529
    0x70803180a060c030612080304140f06040305040f060c050714150408330109020304020103142712040905090316060504210f0804110a0e040210082806 66
    0x203440c50480186001c200a00c1d620403d039010034900800400d8070030050300c4204c43c0c1a80410300c146580c0315030311981b6141349aa114240a4422a02840540f031024007106000ba4401c1d00e6090316a4200340301c0400c0b01c1450342102c010060081e280b1004030303600181200886520441400c0c00c1480000801c10340500886034001c0d100c0b001800003460704001801040039240c15070b0700c903551203502c4141d5003102d01705089582454540001402200c003682d0086402904c1410002840100790312040b01c821030485280da0200d040b075180502c00840c10a21008400308140607101d605070701021b15000c0e0160b402456000d942d034a00003821500d0800454403404914842030404410034038206001e05421517088039051001031220b50104e1401c001d460110b605a10f50540c140c0b21130300c080300c210400a0040e0b07450f108012004030310307032140840b03000a070800340a007482c1c9192a0040c0720840741d940c080001001621800c02400b5818401c1c000444100d0062141e0015409448440a061960 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 552232023 1250 552230773 552230821
    0x13060f0305100c1107061110090f020301060806070c1115190f05040e040204240602071412060610050d020a030501090e0a050607030209060f040b09031e03070803 71
    0x800310901100041400000041c03520a00c031003d2118402c40b510801d0300300e0003841d64810b00d4107011190013400001c03080b40140040382c1d40a0200501794082c3c450800c41910600240c80070002581420b000e000007400e0340c800142003e0800880051202401c4000501020340b01e1000c00c0e46980d0b64204c01c0215004607140589a010b0301d400d00340580803c41c6d460700801c00f1915210392040c015000e075000c40f540e845040c600d0395142d03000d00c405040340091070078140218503800d403001e440301070302c0d0005040d03980d000300556420301440945103516500c41074440d0341900c0c60280905000034000e41d20000c10380700303644420340604089d41ca030b00404842514941c004542600429415030002d4101c0d600140d050180b80540c02d203158a030042010003134416040b907400100c2e501d0081e0001c014400016004900c1e1185540c8071111036000340e00141c034491400501c1c651507181c10003da0b00d01c002d000c101d103066051845a256a6403007460001044028044001401441c1041f51900503032410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 552233273 1250 552232023 552232049
    0x1101090c0618050d1e020a0e1005010e090106050f0706020c160e0f0c030606040509040803060a0515180f030f0f0d0e060403020f1504032409020d021306 67
    0x340380a4040c400325009a40020b000800c011001d103540c0800001240c5001d0101440041d4607180d2001c9450180241d01446407000c41040041e1100c0c040c04000300340a0704590035034203001d244040c00c182c403917101d941005a0038030703404140e9841d00d05250441e1301900304156102c0005240120b180141180900b04a1010504044a50307000c29213503c00c440c518228400c5541301c420140c3c034001b044d140403000000000c002008030103010011500a04010002e500705517407040003440b4054104d800b1a501d0314003109009a42c00c00c01d105002901044440359113000d032000482001c1d00542511003004000590414250303150110a06d0b1a03403c060141c0301e0034412440e64940e00d00d0221070107504d51140714261110907120340d0752081c3c0d2480041185161510b9a001c10031685010291a540001e1150824401312055002071004601c40c0188080c1101c10a05004250a2031620b800c5924107200403900140d4444402030366590381120201c0d800e410b00244140105641c2d00700c4201075902d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 552234523 1250 552233273 552233291
    0x4090615140a06030513121b061b110d1413031a061e1504150206070e010e01080c070f0b090f0c0307031e060b04060902070b09060c0301090c1101 64
    0x40314001120300307001628070032201070703032032004800716082201da4896074075030300200754000340201643c0311001c1003510300462a056041c80148101c100b0080448000e5510001c503e01083d000007220b00381041c0382003695900b02d05100d11501c1d9144030310806c082003082d9140b010381c0e10300c242c03c1d111040c000312101462140c9900d02030b09503030780c82c1c0b20280d4040c882000080c2c1c0c034500501e5144070782030f12410740451030000c181070041c1c2202c01500c10301c482c441880080b50b281011a0000c40c2c04180341e00812144c1090003003c0c000c0502c90030340604010250345c0c070006a0741c1001e115604003440b0032406070756080030705000c0b000c4030048400a00100545040c003500704800038810100c00d5241c000e551141401e04105682d40340300e84001820030040054440314003440785080c100c501d0194101041d039081042c005000c950f100e030848151181c0c040303011014408100d4005500108240040c541d80c1400f03c0c010003280414800d03081c080c1e89840e0244120b40c0f00360303100c0e40c2e100200c41c024421208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 552235773 1250 552234523 552234539
    0xa08040e091207120215010f15140a021f1a060309010e161802120406090203030c0708061b09011d060f0d020d050912030403030b151c05010b071104090615 68
    0x14010358030100503c1070000850b15902d100395054101c505061100b40391912740b0400d4056245404061018440040340603094407000310300400321951039038003400c060801c1040e5040340000c1c3d84540000146030260700e1100e0345180c24450030314801159074039100c1c0c0c1c6800c0da45001d4910311070110500e009001c00070720201e141c0205102561350b020032019a040140e1043d00490213001e40036104c1100c80700215002c20010f0b4020660140058107aa140501e0032000500c1c10300a644900303c650b000104200b01c20398502d5507002550b11b91000704d45807040a400082c040b00c40500605031800303080a0031016a654401110150980641d0349520307035200c15211b20080d003100c0c2c9161009030810002231401c0c100401c10b0007900c10720b500d0443c11a192506c00f107005043e0741c8105500008824100100410000c002c0c10039041e00c24441580720305420803000503030f18180d0124030484000c0c01403500081104540d0301090000391350000d0b440440d424064003034071100035035185602c0400d2010500c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 552237023 1250 552235773 552235793
    0x1617250806090702120904051806010b0901030b01111e031323060705150604020f0d021c0c0c0b0a0b0d1a10060e0f030109050d020d020106080a08040e091207 69
    0x7401c403403001e1255284901643c40e0038041c00c280c050760f9400c010845d42c500c0c1c6a44207507000054400c003082c130210a5403220b0300d054401e8014400c0b072000843e524205d07603418010000c03c000300780380c0b4000c02c40b0b100c80d1007a500e05016204800c015011640b40020031340030425070b5545507107202241c62040d512400300c605c2850a03514140013101030b480906541c1081812541e02690089c000d201c0c1c000e0725031403041c2c1c00f40003500a41c3e00540801841e1400074140000d010741c19148040180d50700d02d00170140e15214151030140b90030074240481c0c4088c040c1c201480e00440c541244100790f8544c0d50340701400042060618255211007420065014003034112480c000015050402d000c0580343da079450b11143c8802d101d4140044c0000d030b2526200c0c00c180102d12049240500007091250003039071038500302404140e0071001a4071542070115159424001d40c001818004042c1260525584a0702c846125074003848441c4610040032070880c0310100600c5603240c410100040d1156150300d00217002c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 552238273 1250 552237023 552237031
    0x140f0411041a1c11060c010605060711090a060e13052b2d0e04090f061505040209030c010c1e0305130602191509021903060516172508 59
    0x54418849000c04040e000f0440450783c0d4001d202402044800000c01409910101d0808059521814000b44c00d45803c40903105261154030110400401303801400b203500d0004205080703480c10184100904090881295089005148107000400072800c0c00d91620035418400c0c032240c0723442c82003000c0c514000c00d600a070568460b920801c10029500600240303404050b800030850364000c0440135110300030034940580000c00780c004210082540c03102d10b2060300b0b0900031f8400300e480300c0c500030701302241d85031000180c50b00315011070503e0f203d080820741d10702034201d200307040c04015050031040c055100c41c2d98240c1c2e841e040c0c00f915460703000d250081480d009000c0c6180145016100420040e00106000515029040034000340c20150b888071140c000103e20840d140c1543c640c800030141c0c88441840412580901d01044401d2540c54580105d52004208542007c1c0e001c101c038103110b0740404040132840c056a01c2c800076032030f0020f210203082c050b8014049903c202c084070860054001c5205441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 552239523 1250 552238273 552238279
    0x9170303090105130506060d020a0b0a0e01020c10080a02030c040308040b0c070e0105010f0c08040902070309240c11010525030905120a0303020f090402040e0405010b04140f0411041a 80
    0x20f40e0721000c101c3c580051307851100034025045030703002400c1c41c101207004010b0140010301400707800707940301c20503040d0ba4081c1003201700084420342d03c00c116503010400c16080d00f405917602c2c02404000c5000404101d130280c0741c41c0203070741c00001290442d0100d006079000766401ca0001a95190342d0180312180358031040c60305030640200d2000007215034005020303504075503061315034580c800d18a040803115004103080c01c4a02c10b105102c00b0843e5442c9201800502d480394a8884100b4245032a907003000d502c1a410029204181807080c1c29154070220500159034001d100b14420040d280060340d05008144030031742d000c140a101040744d0f50240c0c0003890b0090090f200d8001081e1500c05200d64058500f070305444560000c1031a034000b0307100380e0082006801189000d420a100200000d003a030340181e001181c829185800d0000b480300a1207501030082040310b08028070b00f60040442d1008800902c102c075050040000182031009142e40c15480510040040060903001d2003041c40ca81c0070540041c4c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 552240773 1250 552239523 552239531
    0xa080703050f071b02010c06110d05010f0f0b0c10050f16030606051b1f0507021e0c010e03190c170c060417071509150f120507091703030901 62
    0x1c44000402280d00506183d03a40040d0940049001c4e104c1c00000c440072410011502c81c1c0b000402c0013881b139484011504c1c0e4015503510301d0b20311804191041030b0010112004140001c0001007640000c540c12500404034042e03c59008200e15424007039072010b00454541031004100400003050683e0707114a440c0f00c1210790003065898110f08039120b038007034a80810810081d891030120030302424180070f6244004c8a0004041c0c11050301caa038401c44030705900640300c0c010321000a4060000d480d40281010980030b0019060f8111030351112002907090500c20750348202400c64400f8000310480c0f40598910340003424541c5031042400080740b2a88000e5640c03000d032200c141c14081020304034000c00a0000d03040c41d090890b82c1c44401d60280e10003070544202d000c0003035030a100000c1a2200034090f01c171005c3c814501484080602110a41001004411400c001c0c1064000d401c4562418680d5400500d5a607948010341303640c07807960402030f4000c6211900d03480c0300c03600000447c031400841d0002c1c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 552242023 1250 552240773 552240781
    0x709020d1509020705071707031e02091e01060f0504120f0314040b07150b030a0303090201080c031e06130207060b0a060309020319030203090a2c090d110a0203030a08070305 76
    0x94200d0040c400f00503d240c006d44010407602070f01c104401c0140c2e000b1003d80d80003039582e6403104004e0b004140180740c81c802c3e071021001540703080140b85610210301200f20304440c0c002847d589030003030140100001e2008103e030108555114170155006404443c070f121401282d24100307442042604801240000c00180c40c451900301894241d800316065a5030039420b0041559603d2001703030040300f4446190f5507466103034520342e40800003903440714001d0703c0000e1783c0015030000501502009002c4200000100140b040281100d03000107070001250924141d2038460100050070440d40400000e0514004035010003409140c0e800580107942c00c50b03c44080640c3c1c0c41d4241c0c15640540d4020354035400204140d003160460385401d10b4032034807034819079290041c100c0014010560765000f82d18108080291143e01190100150580b43d8010303100c1d441624200040c40c0d0b898004401070340401028404031601441e04020001d202540102582e40300ca03800070000306444000c40d00d0000080c00c28004c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 552243273 1250 552242023 552242039
    0xb04140d110a0206072a150503070f05031f0b1804060b19052106011211090d03050d11030f010918080a11070801050601030e01050114010f020709020d15 67
    0x25040007801c80190400ca22142c08200300f58028030002e481d1791004903900301c02c221381241d021a105030172803100c50405007000b094041c825030110240e1b003400310070418480e40a40208014002c4a40c0303140c015625170704c2c1d046940c10000180b580d107807252890070000c207054a03140050070380ca401c800300700041c61680d0030030001a03610344d01c100400704004010f500c80d0740d240d6413250f1031481e900d403c10030b103850442042e80c50355800003c0164010306035802400011b60340481c5091403211500703010301010207003c2041011b4031440780c019119a0100c2980c50030140113000344c440c1c8240142081140c0c00605000c40603a50040b621a588a00c03030300004540d88000348076114490b0704007910010369040c60381c0c5655180d8441c203a20001d0010101c01d0224540c010000c90300500b45080002c612410403130f0014042e9102c034411030449904200042c48000310658401c00c540c00e0034a011040001980d00903400c0030002e81010062900014450290802c1c0707030065802d0b08003500342d20540d19034600c69 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 552244523 1250 552243273 552243287
    0x2a05090f0108221a040c1d060a09020a09031b0501030c080c07030e0a05030f071517040206030604020f040303031a0402180108180307061a180c03090a0b04140d 70
    0x180440ba001c0340f843c41c10454815440200300c082c42092440503c160001034500c11007002c403070032200400e007180c0070b02c10a2682c0d0000031481c040c1c0a40400075040110014612030040d001c0c0f8420039174089081e2181f40d108000100080d904201c1c0722000140c030410b40240030501d4040c00c1d0100b400d00184540c45441151024400c06031000d200341011042e07034007100c00784500300c0e40f42c2d88250324030703804a6030b40e034117025400384000800028262149040c03007085100700c441d1039400a00103051110503070207049111071b40d4050750403141c940e6203985003000a4024025000e0f28110070501040101c1010f40607406000004075045003101e401429604000a070b00c1005403a00640b60300303801c00b00c065401444203e4200c0c41128190f1850f8a1914065185400c540025074840e6240d0282078a11201c0081e01a00f40317600f5105010f40c1c0c6c0900310305a00304c0002528998441c1400400590088030074800d90f80802c5d4407400e0811030b820305041c81c020000140000c0042ca000e0200200c58050046071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 552245773 1250 552244523 552244531
    0x60904021e0d0b0f041103010203070903030c050a1704060206010918020405090a05030f0a140a05030403080a0e19060f0b0907110f01020a0302071b05030c042a05090f0108 75
    0x1216560410807500080c88a003105003a8100e2501d0700074030000703a07948001074800c584007200400c007482e081c100040800004120907010740d2040051000c040d0303100d15142d0940c0d4060800480e0170201d8503206180a00c210380280c88040381d01c00c900a02c0003200d0082c8111406542107403c1070341c9441c1103000310b5613158088010b41d021209000018101500a1030707000341c90405403941d0304956141d150465202c82e0800d00304550010700b103080c580d0480380944280c07600c5034595040500482014050784006400030b024000400d00007481000190003164240400720203440c1007c400721607040e21044c20a608440e118200307091400051032a06c2106000e01000f0500781d00f640340c0c04015580100244000c802d503004d91455150115824001004c005090f9940166a403070681401480300c4191a080341150a105c40c04000e15580065402f42003442180c0000e10300d081180e000c00407040300070000403031803c1c2c0d0b051a45170b0307138201019005845056904200781c40e44d0800446c0c000c50215 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 552247023 1250 552245773 552245779
    0x30a2019060903020a050a080c0d09030206031f0b0c15010905060904031d0303072303070804090f09060e0604200105030f1e151302040602031b0705151206090402 71
    0x24500001203182500528030b0302d400790040c1c3d0300c8001580c8406040000c1084140d41100c00041c21410840040105807c40303080e5281c208941d504540c000b50440c403010300f100001d40a030100115084441840d844002c0c0000e02403a6070b500590880180c42c1c01ea900303640c00d0440030b101e000040284039401103511507036000384040e1443e0360b03035501540c4410418a600d600801e04c1c03401161280c5040008015160150041e0845031401400d418500c080c90140000c2075013090248400050212007601c1c1035919403000841c1501c604200f64009141006024007040d05042d9894003000d008290103020341c1c0a006000d01480c6400301c0024502a030758059030003d0401c00003c2d03650a49902001d0300410b4501951224170300303e0091403245001601c3c22040031249a060a101f454048000840c0b100c41d500c0960400e0720b002000b0b91a8000c086440e90a031582400031400c0711014000c040141a000b13151110038108903100e101c2c42d400071080b20340400400400b00f840c0b4608050707143c0c4243d41c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 552248273 1250 552247023 552247063
    0x1050604054006080c2b0302100c0815060a05040519030c030803093715050a020403170c06060114040b0406210b0f04020c0f030a20 58
    0x80140c0c0a0102040355501c1c0744003080345112007a211101c1030070300105094080218495080c0400f0034240005d89490a10844c2801c0c0002850f0200001c00303d500241d40310004001c41060900340e0070600d0445070b010603149821031004500f5041082d0034001c0c0c160101e054a162400000d1004a124490110b0f01007a418481002581380c02c69559502c2001c2c07183c0202101e540e0b540d80822010107800c102d82080c008401c20810301020450320f42020015007a0f06404121104c01500485d0300038010820040082e0528060041000303a040301c08801d42802c020914012910700c0003500076002c100d6400d01503030346401da060901c2c8150345020358004043c0416460303c07001580c050003401c40031001003405100004501a4450180c4000c2416454500d542400701e4141c0c4106248000d84142d0903203001c00c0460651035140e81010000c806540c01691400c219107018a004070403844000303e40310005034013082d00d42c02085028401400c00001c42241801200562108038050754054104c1780 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 552249523 1250 552248273 552248299
    0xf090c010206190e030c12120a02070f0f08090a081605030303040b060405091c03090201090806040f020918190303060807080307030e01030209060a080919050a080310050a0603060e0105060405 84
    0x90380e01c0440e07107404c24011a4139100050514a05100c070721540390314120703004181c620345600f052402c00c0e03010302850310440c50f1070201c0da44d18021b8407505102900e240508440070b8200302440b800c40c0c044110091911701c87e02e9503003040c642e9503003040c0307003141f052400342c40d00042030304001003940d0043e94000d5103c105641d4506c2070100600380105101000d00c6112a84110380c030b0540034401c100409590003041d85080b03800050b140c1c004507440710050703a201108200120342002c8014074550f90448100441ea00c0d90100404a603003d000c0880e030900034401c00710703030103007011244202581c420345061151a990b516a035845075680e00c240991600100306000010b480362007040119281414010b007400c14400214030550056601003010803448070900c4051401041081e01d03843d98030050203c0e501c0d060395580c2c0c4030708669000520881c3c002c00465074141c09040304902400c9c01604075040c00d41d1722074005000c0c00d5103100300800c81c58801c002040701e0414600315000c0c1c0c0c1000d0032082c100303a0b13 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 552250773 1250 552249523 552249571
    0xa090209100302040621110607080a050a08180307120509191a0307090e04020414010e1e010506090d0606050301020c0307210504120c08010f0902030c0d0b0105061308060f090c010206 80
    0xc0f1f803045240e07009108000c10000a07001e8006864411002da507072903140c2400c2000680700c04805089050366402c11281124a440c002080b9006c6960014a81202003008401610715008000c4001c1d030105090b00090a40109051503504481c0c6480350400c0140c510b105900203484250394440003d01c0b090018010258503002c400c1d0003910103007001130712150041041001c114280c210364540014034050040d521800e5800b140708507621700400c41c02d54035000004026120b18020300d03010340000c0d2102e03024040190b000b50f00401c4094025942e40c0b0740c0b822001e03265844210121400c803a40030803001201ea00510580781140940c450601c1e0070f0500f940644ac010440c0300890707404015200204840e0f0080c044c5107403c3d081002c02040f82c1945104160400c1148140c243c02441160071035000f04954003005411100140c5c0c10036130711074110b4141034412000d0b400c0110a4031441060000c00010b00c0001881000f401c4140c03040d0061840049071600000d544141c0390740c00c00f4640b419041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 552252023 1250 552250773 552250793
    0x9060616050a050106030f051c021903030b0405271b0402090319050304090f05060904030302070203030c030703080406050f070804062705060f07050a0c03080a090209100302040621 79
    0x20300840440315a00070707950381c0609440403900102c481f071100d0350040040110130001c400d0f401e00c5080030001e000540e114025980c5002450324543d003080424840d080c0343c040c1c0c0c0305610b050806070052003242f0b80000402c8aa0400c107240c0060301d401004103090058002c50084d20110369500c00c00500c40c503113000c000103500700194499160150011000d01070101071800541944a440a9900c0340d00c2c00000100f00d8a0b4076011f480094282030400a499607100e04140c0d0103580350a0058885449001092450103510f1190001f8071001840c1418150000319441c842ca20480b4240001c3da5645000d01b10304405842083c042050800480c001840e80d800c0020400d901d100a240d54200c00e80320000148801c26054540d13402a005002d462808280d02540c0545a0b0602d245080e003c03c03401000c04582c10380250030000c0c83c2d8042603940394180c03c580c1600d50000c06c01c0e1964101032001c038922200c1d9110403441240782c0032000031b00034408058680b00500400010729210010740300e002c0b1070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 552253273 1250 552252023 552252067
    0x60d02180102120a2109030c060f0b090c030417040f23060d090204021c0e01140f040303230408090906030105010b07080c0f191209270e030a031a090606 67
    0x4045005c1c40c8400440c0300e4440c0b008828080d695140020140d401c20400311824075000c2001103080040c95480c2d51900040a81c2212200d102d5070740c1c03985d50b814131074007008013805443c0d0440c0c400600050b0040007803c4c15016103c4408c03048001180881040c0d405c1c442030302110341c01c00b400380840340042c103448d40850a00c40c00a8005494442081c4480b0360801c00f09800302902036643d42080b410f11400d2040184120f003000115802d41803651400c0006400108010101038039512044040c00b03121205c2000710681c501441d605003010326240d844c580104000c01d0084554030000f0782c0601d014060707141290110071200f4139040040c1c50351230941e400140c94020340d1040600c5003841c1c000402c6448845c100803a906400000c1a01e005054003d070250050100402000c05008101603110040000301e560369a01c7d01107070504a03454045c0900c501d10b00130714040415000071454258103c2c244d450b41034001c016019100c4010482803100666040e030b0411410b100500040e00000d52480c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 552254523 1250 552253273 552253307
    0x20a1505190b2e0305060f010e10121104051f120e0106081e07090e060c030915040803090d0201090c060503040f0b0a0903110a03020c0f0f060d02180102120a 69
    0x701c00d0508810040e44022051400000443c0b480d1902da550780351040700e410030307001c0316650b201101a8000812162214841c1841100e181031120000c5000b2050321468003102034080c040302d44030881ca007802d6049480380e10300036400700c140070301542401810700031f1410558072540c540c4101d5401d050004c00030807480c05801d6585107400301d9909420400110302446407082c22021001c0d52100e60300741002c980c40025501d06018612407d00c01c0402c50342d601841308030000f40ca07982c1e040051b501e010310308040380d031413490414184801e104040004500c41c00c19001113900c0a00744080403030894103002000390190050400c00d0001c070b44240029a00280540800e1080004684592202c844159010f4480d1581c0d10107442c1016001900d48000e03c01c01c4000d0f2107030502c55140a92500120b490151148220180c1341000d945c0d1a42800d20600025003203030303180e0f0980100d0324025070040d505d40181e40d050f401550203647c40051307000401100c00c2d09140c2014840041030b9000d40580c014400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 552255773 1250 552254523 552254539
    0x8040b0604230108011409030d1a04021612090612020304050f030307020c1f080f07030e030a03020909010b07020d060b010e1804110405011d1f06020a1505190b 70
    0x260311000300c0403900c800e041005041802c0e514002ca80c50846941060702000f800d103000802c02c030004003005542c451204841c010031100120f40b0001c400405070101300b540720340b020410341a02c4201141d0400054800d01c6007140b4882d1110301950012014032031f1000240c0b5000302e07a803003130b5055005103400c40d22501c101c0e0601082ca4000c01d04680084964100503880b5404965842c0382042002c0e51110107803451041c00251100000c110079001464800c59600c0800814500351082d800340c0100302110058075110180c6000c01070180d80b140f41c019100b01c0d641400429100c0180044944c4640e00074a40780000d403241d40c1d4100035000d02509503051058040040e1059102c1400d12002c5002e50201c010360343c41c107413130000484011001400d020b1481e2000502c000c5450040144103e0320f4ce6105a4040c1d5a54805604100d0044804040c8601d00d1a0015225800299042178a0b100340c4081ca02085084c0d240000c0700d0b001c80380c500d044012000d006150040ad9884402c0c2c511020382020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 552257023 1250 552255773 552255791
    0x32100b091e0306090d0212040b0d1a04020a05040504051e070c05010b06040b190206010b041806030c09021201090b030a120e1207090e01021201150c06060305010f0b01020d08040b0604 80
    0xe0400c00304541c000300da41c01150001c521141d051200f240900c41f90b0801c0c2d414a400c208075032006000340420303040c1e019035406070100008207010304c102d034041d0018011365882c2941030000708550032034403909000703600348000307e40480041102903607110086141c40c5800c2c1d80b1042c08a035204429042030350345550b00c034640340b12500c4c0e520080c030140540700640d50750382645030449580500840411001c54000f1001441a80c00700801c0700c04403410740c5c1d80d06102c0c03c1e000b40d412004001c1ea600c001d2511682030b800242170715054018009543d00c0300d038070051316070b6030355620001e94261048480d819007100e030081e000a90190101d41c505132185c60042e130072141842c00b09409030300040640815600501040111982601444800300a000300a5046c40155034070b02141d80c0e0180a40d0502c401e0101c40301421070722074001d010896070021014070010b5a0f03030400e14002c28500b030bc81d900032824042c1c1d42c8030550000800701c09448250780c40211503519503c07400c103010400781c6482c1d8800e407a00f2201c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 552258273 1250 552257023 552257029
    0x230c0c01080f040f29160c0215030a0b09040c031712061003090b04050105040c050d030c1101050f07030806090f0f0a1d25090e19030332100b091e 64
    0x18070505c11a0010071410b003070503d03080c080200c0d120f03410002c0100c690640801600d030040942c0c011318880d0a842d4403034460100100241c1803c07500360b07400054039020042400a2154407500700d074018004651070b030410306480b40d05442000c00c4841c0070010040891100d042c48500944246d0b918500040c0403602e6545803588a10152001d4403540e45440c180700c1404515034017003000340400c0b1000d019031703065541c0240142004a0b80130303080c00e8450180c031155074025801c841a030302d0100150f40d6100503600d806000400140c80c041c5c0a0a07004000551120000c842c450060004003002c50269860314403440c098420800b5148001c0c0c3c07451003200340d014081010038041c0c1855400d1ba6252000d6010825104a166010810381c9061040e90003101402207101c003400b03d0300046011041c2c8070382c28141c01400b072400691100440c2d021001044015101e210954412a112321207055203440113007100d040e11034012164544030403c20020903261441001c0d00740c00303154520960504102c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 552259523 1250 552258273 552258323
    0x9030b070e0307050f1e0a0314150a09020a0e1003020a14010201050606070f02150f0409060501020c0f10051c0908040302120703030c080703230c0c01080f040f 70
    0x4100041070111401c44141d2606000030b030080c1000780c40d5072002483c200c0020701506144071403619081d04040b820301c01500c401501c80d015607004258860104040242e50759181007a560101001400d80041034008406014ae80540d0780c00500704441182000002185441c0141c420340741400307481800170060303c0f246030000007070164018a50301d070b01000001a080d210000e14451140700c04200c078200207408030444442c000e4040d00c5408405c840307144044103d1003040001e0303071301c81c03000b10300010803400036044807040da0342c2a03080c0e4503500e00008c28458140c0c0300003030940e40280381500000302588100c01416190340c10011600100c0e011030480000c44503000390541c0c29a50005003032056007880c0a4442d50101c46034020281a49161401008107904220082c1501c900040d164140f41c031841d608400c03400b00790a0783d440c03500c08500c0c0c0c80a50b03010b5082550540540c41c4094515805000307003510620f45e076071030044c083c0d44aa541c101c482c1900f130390841d16110781150244401201c181 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 552260773 1250 552259523 552259531
    0x5030426010e0c01020f06131b0b0315012717010603080f03041e11040b0f03060906010e07020304061b020307030c08010603031404240201020d14180c03070308070309030b 75
    0x1000d0103003031844800090030103c6c825800d58070340c0d1014050003845066243c4400760300e90007210b032008030210400d022001d0207081d804855468004010b01480c1084c0080090b012032003600c506682c605075060703102e210306c4011400c9200c1c3c5104507041241040498001c0b0b5040300403000042c8954503955901101d0300200b03a03041ca2050044200f004021460440340601510711084501c010045e5a030282c400213400565401207490b1400341c080740e1101c4600590741ca80040c29228185001f0103102e0340c0721703401d2190b40c0612071a0004500c400740007004031003c2e16031a40d604400d40001079a040e40342a1401e50498061151580000c0450756000302000507180c030b100007103a890328506000380407020f0748620180122003003004000c01d04080c03072101180d0101d000300d500341e44c1100c0c0c0c0990081c0149814065018241082143d40e40d4004001e548104400c1c401041250268202c0799900c111042c001c1e41c241d0710012040c404180600040e024003403092500c015120389139601d2890346e01c0c01362 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 552262023 1250 552260773 552260801
    0x180507031101140a030c121103040204110306010c0201111c110f010c0909050a0e0f010c1b0203060402130f0c0903060c030c0503010b070620120901090503042601 71
    0x10034410098031040e0705210407024609404550380d404441c018034851390f03140c002810340c0c0b607030080083c0e4051100c0f00044030505508001400240c00070f019a58000c5070203c1c82185085010100140130b00d00b80c900650040c0e58100d941a41980103403008070741c503108450785101e1041d4a20740056009220300b00d601300d0f65520b044501d19648141e1808071817541a0700030384d0600196100c070b95070084485084a01a00d80480d068554440380c20050007248080b00e0f6501074074859003001070701500300003210046559606540c0c2c2d440c100401100082c440000d5040d0080f601103009031400c42085210036400841c0010680700581410003101c5403000c940021603103845040040c080b06110b03500754942c141c202400520782c0894000c2c8540702c140a20000c1d200c01060b03040c20b002c00342e4040306c24007100e500c0c0c0079a450343d014402629a00180f0900301c031140c1d400001900d54030180102c0e00c2c000da02000031410141406110307980c40d04a41045a03501c0444031a183c1246c900340a210322148510b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 552263273 1250 552262023 552262033
    0x3060e19091b0e010f0506120606070c060201021e030f07030207080c0d03091202010e0607030c020c0d08120603070b070609021224010618050f12060408040f090b010503060d02041805 80
    0xc0f14003007040c4164000915911078881c2017045440e94011240580e9501044088c1130380c039200021034070700030060050043c43c0ca85901040750f5030154010b0220050104803079075840c22401c9022034610003220890031090040000c01d10860090300a40b4080e48135860160620200313807015440d22501e03001580c0000d4543c8041c078140401b2000702c45007003819200034403404200c0c207910b0343e46d0034000d040041010350f10941d0100c8144240310740030740401c0052450440c040e250420041a0b000000001800b05099010651515000900340b007110881034200d424200c0d00d84411004000303036141a1f0b04210142d03007e640b918000c0c0300445560b1760b03190150309803000d015044160b00d80145c1100d020b121448039041c0303031110380f403010200b1201d0803242422040c40302d0011540a0342ca1820070400e500c9008248020401520040d005035501d040105095542d0741c074609080d180c080b92110301240c41000420810308017503284179051400030b840401d524950303c101840c00c103001b40c0d0507901c079000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 552264523 1250 552263273 552263279
    0x40908040b130e011a070b06013f0204050a0b030a18051c020304061b050a050102040b04080f030f03132310060807060801050613050603160e0103060e19091b 69
    0x894142400740c01c0c48088020b5004910075059042d200e044170152400000ca4001fa490340e110381c4ac441c03107d906100030420f248034441c190f0020200342d041c0d1110020060092800740d402c0314400d4800304c80d402444141c07050300d000001055540083c00c48014940c680380110a4142d2000f0b0852403d48600d00901a505920004e10b000601c003404450854100300320412080d503100c090442c1c1c840100120101480fa180b400500d804417440005100394008140026500b000c5d0002c1c0c022a1810016900032034500f0040c0c540301d00c200f0248401405d030a1000c42c206205503104071003020302c00c074269803110b00710300d20b01c0d808911200e10350801a0b1000d10844c0c1d40c212940500710041c91960000c04542b17052a00c05000000b0501035180103000200e85610369141c00c0a480d03004050290041d60340f8102500110f03182c0d906d9440020100303203404504291544240300d030b00100d40a4114501c150740302c11f16459122010490010100d9440c1c00594012407540903807000750080348280d10741080d00d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 552265773 1250 552264523 552264539
    0x5030a020c0a0b0403030b0d11010f030b120105040308090d121d060c0d0e0601030c0303081e0f010f0b09090105120f10020910020609060a0b04091b030519030e040908040b13 76
    0x4411fa000380940380341800c050000d05e420100740740600302428044080b41d002d40d412001401c4104107503500c5032030b1400c1d0030416041035110a000718066660000c0c25614011900e40e1120704422050024155031001002d901c5180d0100034508203d402c0484c1d0010b04520544c40c01e00190754941c01d58100180458080140348280402c6c1c1880030040e000c00e602d1510703035000001ea144009824400c5080014280c145c000000c5078041c07a82c03040b030140c2030414200c15140c4000900602c101004c403281701041c2000c110007601d040e90002040d5071960ba00748018425040c41032060000740d803180d245401078844d8184100524160918070068542e500d000070003611441c001090000e540041060041a500200f0f041c0e80c04548064003086a12070080860020061440050040c1c2e00e2080d0411904c4680c551f914226400b5804507075007c03506000d660b41503441088004c0c0821907a20000115040c1900640101c0340981340036400c050b0741e1424003003030b50b211980703070240c1e012500414880740d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 552267023 1250 552265773 552265781
    0x2040e10060807180b010504080d08010801110301210201051b010b2b0f0203190b070f1103042c011d01060203040f0512100f060305010608030909010605030a020c0a0b040303 76
    0x1c49075000622915140c80d41d40050961400c101344016900c5502c1504c6a9028008139001000781d403084078488004801700600e0b211081c02910403950a00744600d81c91400001074031305a44c003c030300705041d0500e4455204007070703c20705004a05204017880792210104102001c0c14103105030b27100105e165003181c1300b00403840e40c200050a030440d0300d002e2542c80045400b552200c140394403080304c080e0001180006407401e482d0842003245841884c510204204104191b10300803c0703580c1300e02410700300020064500e0072318403a125019600030700c000c20442d07080c9692002d40303100c14400b01ca1094031006083d0070807203091b044801a007081100041c20b0001ca050114010009440910b0410b400c0c1442000740030014072a60340700b805040c060380d03008a020304c0740d1103e040840004210400030001e04c47d001d06250710094465500c0c00f000042c4402c4044129828200300604205a5030708296040d113503504080c5c030212000d5401d11440c1610760341004000da40030700030301211502c0d10b05450010269 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 552268273 1250 552267023 552267029
    0xb040f090b06040606020c1e03010f0f050a09020114090109050a03050a170c060402060f09030a110a0503242e09050c1c0b060f040b0901030b120309100c02040e1006 72
    0x840c44d100301002800da001c503203030642070821215411096031106412100748041580e082d07043d407038101002c520801a9006a819101c1a0310034042660341400107800c5038078004c0003030b000c41c0c41800c0310f040c03403403510340180841041410550402034031600492901a5540c2089520b44e000495038000d10503d0b807861903230142c2000320b141c40c02c3c02c4900744a48607480580300034080d010108002003400200e0041c0d40b61101e01030219100301c401811700a105480030301801e40035182013080850642000300e000c03002011191812080740b81c0c20114400a080c0c000d2100640c1d07000401c26000c5c007030300725011b4003201c85000d040041090a01d4000d01c1146d40141444981c110204186644100d086c440314030507200f4100300180b1260214007107190380c03058504211200300d002602240c0c01c5008406000500402e0380c0800c0440700c6e100c00e1100745008100400c009510034806505685084518401058900c1c504800c0c4809a81d002c0f40641d000409002481d4201e102800c5240b0302da03106107002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 552269523 1250 552268273 552268279
    0x1212020d060b0918070c1e0b07020d03230411040213031a1e13210c060c02010212150d230c030d200304030c081507030917030a0b040f090b06 62
    0x309040c010000f4000890607031008001058501880c503d00e202010b41c001f81d160881002400303890310716402900d034181c483d04003002c0303807405589072030944200c0c04207a100c18204542a04907213458540c0c10041c1d104003400d5038415020403d250b482c1550140d01401944079849003283c0780000200f441031442c005142d8648c0300c243d81c0c0c4640b074002005044642061074605601c800303d0312402c1940380b2180c0e840401d00c41030340380c0d1514051a40e010035030899050181004200b106a42c1c4000c034241d120b1032076038920920f00071001c20103d40a40100111040004040743c04042c6070303595070001c50601c0c1a94003001c0941c3d00c802441240c05000f028003850045015210b00800d6200280c10142d058000790810f05103840b60b0300001404102301e070041e503000050140f00503035070020280d444200e02c0c00c4c1c405400c03011000c21400b40c003a00820000541c8640e004201d4410608200c03860b030001401c003501ea94890800c804940ca481c4903801c026203009001051110326814448010b05001e49881c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 552270773 1250 552269523 552269569
    0x6012d0e031908040e060301091e110907020f06090c01020c010f260103060c0c02100516020303070c0315021c050c090d0c0f1e060c020d05060c0a0305131212020d060b09 74
    0xd003c0c2c0ac4003203801011820702d104214501d0a100741e6002c1c5202c24182c104410b0000d01c10100d0300020315607002815001103d0307203503032000c0a1030388503030100d014240941e008034004040ca60141c01310202c01880c1d440c000310211403140c0c0c40e25860341c106440c450040300300c00040c02030152602a8104500c44c5040a110b040d5055001c9001d00d1a00c541c040700700304c404102714586603424044440c4407600181180e48984d46400c044581140610048801402465051041c16400d00a54480945949101420850946204014000050428100140404c03000340c49903600350020740c0726801030010071b14079811b001c01440c50a0450704465401c07031105414060f0001d440075440c00b07507500c5240140b4004014030118414130301010740142240100c07001c20248248032006044600c3d0710356014811502c800c103400e080f02204400140141d001d801c594580035010711003540b002c00b06807070018608000400880c04441f01508000900c0c440010380b00001d14108000c80010260420131074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 552272023 1250 552270773 552270791
    0x25031a040b0d03030513060509011b0c0510021305030604050115060e06031f05030d02100b1008041112010207030c0c061412040501020d060e06012d0e031908040e060301 74
    0x210742d002400e074000c08142d01c0f00300042d01c0d04500c4812407005540440e0a0205013803044029010700560340064440010103010003400b02e20818507810115003240c060010002d650201a0107540302d141640b40c0d41c101d4440000d0b094404104c0140b266001d4000040c219a15403403407284030740b040d40414100445194540483d944100c203c0707800011410242041d00b01500317840540c803070709900150b454041c5c1300c2c10004070754020a260350303480d075000030800105403903008100416542d00d802c800003410a90009000840c2d041a035915004010403800b40040192026400da910000c000c030001012000020100075040c84041c01820341c0c0e081c44803e00c00e00d482740c00c00b58015095103511805130000030400b480000e50440700421075075a01408029100e0042d050724400685d0f2150004144070102480302e004c1454941000b0804281e0a50f45a408541103841140c0991030f035505001c2d95400382100c9125992040350300b4425854152124030300803000c14be50500500550080c1d042000314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 552273273 1250 552272023 552272029
    0x3060905101412010642081e07050a0e0402072409170301060f020109050c0f0f132703020703030804080702130506100e0a0302010825031a040b 63
    0x280c825240c41009803800140403000003122006443e500e500b02d94a440d00204a034140440c6100001c444e0a803400021078829480d5020602d400c10340401c103040d114002c1c44424801c04a0a42244078607079081209000c03044050303000c50f030644807140880c10000381c0c080f0450b000050342080d00e004603804c500f0190725494107800800043d40f8600350100d2460300100c0d09000c1d41c40018201c0c1c000d020366609440c203524140c0280c1c020b00a0402081a840c90240028414000c0c003d002da48403000c0c1107150800300502415144030040a80e201c2801c07414959240c03240e80000300d0b40c940c000004222a1643d800d02581c0c1b45824070780c0e40704500e17074001030350210b500050601c080b69810b03e804d4495942e10b043c1856540a8000000e500c058544031408115103075402c4030380598404c4455102c00715000100b900c5070144100c1061b00309140c0482003016600070421158000d51448051907840556480e4407002652404402c0201e070352018043c40c103210200440f44101c10640b0100071000c040c00c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 552274523 1250 552273273 552273301
    0xf120c0c10050f0622110409060e06010c330f0501120c0e15060d14102102010519024207050903031809060603070c171e090103060905 59
    0x10b034007900c0d40040c0603506000c5c1d00744040c030b03c00fa01d1108100507844180c207201a40e0143c469a900241400404114160f02148042c050203050310b400d051240c540d540c1141220a4140c0d4101500f036140d685580320720f1440140e09043d030101c81c0010f5a95002c0c0300301d421220103810494120f840120389030b0000308d0118400041d182a17101c1c25101d036031550000c80d1840a0500f03d15040708011408010504040e0030490f03096215507080d1169a8901c40807401150042c420205101e041d40d02c000b2008040c0c034107009150340189006464505c4112006186881c85a0910010b83c00740075903ea03c21242c0545000101c010f480c40c075220a40e00440c0d0000303106403c5400c3d401040000030801090141c011241035000140580b07858600c0029090341d4240f00c4e080c050300440100c00090f181c2c2ca084411207118680c940c840203400c900c0c0d9100e10b10700550600541c5240c82c0d0130807070000700d4485481c03e00c8050480201540d80d42818800041c283c4082d9801440d00c40c1c2001c052040021075201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 552275773 1250 552274523 552274531
    0xd090609171e2808070f110c01050c071a1c090309140d0b0117060a0c020a1209030501020403210f021f2304020117040b0c0f120c0c10050f 61
    0x1600d01d480c0c14441c010801c60700101400c2d440100d90f191500107200d908134010360b11072503040c0c45901904070080e90070313140c800b910307040d0191940000b00e5805256000c0c00160100f0b00750141140c0311140c07a500005d00c00100d000d0000e92854011407104041c0c1040c46850128004901c6e0902081040d1340d00076216584900400740d00100310304101c88541c0301c400401c1812a003141d48103445503950f20030f21442207c008124400f85c0262000248105881c0c000c80e02c0380145580106000c030030700d40302e10380142d00000d055001c020003164004045842400900040d5016100c03407a54515070111990020170f01415100038000c502c01c0040074540c020882c1c481c03074040440e40007488400804071100902c0c07020001d03030603d215414001e0400341190801d51280e0b100f0307250680840c1a07103010a0f01b41004641c02451402c4000c00500306c0d00c0420060941d074400e1021a909000c1c07104a1511b0b00601100c002260000100340881c03090020400c0e012080104c400c100101d0401e50150040040010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 552277023 1250 552275773 552275827
    0xa180b0a0c0b0a1404030f0e010507050d050901230301091d1e12160201230921030d0b130c0203040506130f0e01091d0606040906020d09060917 63
    0x40001003c80105800003401c051410340000c0c028602460043c1c5581c4100200301c2c0021482c46441030654041d00880b14465040b800a0003030f00c0c1d900d0740484195101c0c4603040c0c10810000e0307074461104220104001d007158200c000d01d443e07604000c804811a640500e82161320340c11001341030420360011807a110801d240e00c0750407422603440100d107442c02c41602315120344d001c000103801090b4203c0c04000a08a4801d030f0b100121855000b500007828045031070f09600c903c0b810040401c951170090b01000010100c0d100f08074960b070a242c1018110b800800300c0300c04460302c1d031515904e145403c88000c074829540010030000d11400100080d5039000d01d000300d034003582e000940807201c104070502d02401403004800c2580c1301d503140c4144149200080c0f01c5c9802d4241400101c0201e04183c618080c640c00109008083c20340c0c0340e50130030019000c0c5050680b02d8030750805c1803100442d018090030700264050b010228681c40c080c9400441441d540c4440b1000032400e0012100d06201750400d000007041503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 552278273 1250 552277023 552277043
    0xc01050a1a100f0905120a0b070201050f0a0c0c020915040617030426010c020a050d1b0f0c0b0d020702120303060d02010c110a1d090106080613170a180b0a0c 69
    0x10744021303248204c1c65008294080ea40d200c0840200c0c41c00500561020302c60700821040c1d842c1c01c68260700f65801580c04402c0061900e0000d4a075040951203140f00d1102c0345004c4a8403407180e00843d02141c030544041d40309084603408204181054040c0b14002c15403d0b601d5056141d0507940103403280154002d540c4040410001441d200b60642c00c48000c032004000200030340403403107001030750b500c03803000c001c40b0f1600646080c01c0e8a81d020b03202091058500e1203641142889640d200038000030107032400c85180303081c0300380401e20740000006003e55103844500140e41e040d903070040001d0240540c401c2d51490b4810020015281c17108403000c01c000364282402c10040c0d50500c2d0843d000000380e0b03003003a0401003911001070103c04281e00e01c003076412038030104040780e00c40345901030a071480c2c0d0103802111341c441c401003481300c2c080b0080d10711880c1c02984980c4503040f0212070b0b009140d2009040350001003204445e910003484c00310806000f0080708401c42e107880340c1c0c07820290810007102c00180480002d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 552279523 1250 552278273 552278297
    0x51816170a0212030406090605120a0b01020a0b0103030206070905090c04120c0308070b01090b0607051f0204030204090b0109421d1909150b010e03030c01050a1a10 72
    0x104010040007558003c1000e040340c1032405249950b41c209216020024541100004071103005104550750a015600d00181300e40c4d5a21085001d000729450b21070443c403501c141100403c81c3c480070356020354425400f030300b240e0500800c020a0940c0c990402c3d4828100e800034880034a0018003254119010665246258145401c0c85d2007480560b500c007038000140010a1410000c1c1410200e050703030914041000101145024014580107a010003002e17030340000c00181141503c90000b062103140c15401614141d00c6c0c0c0d02050076580da0803412201c0b4004000184400c44990141b0315100440041d40e462416078032414680c002c984800a9140e1103007024201110f40c0003004100151642410f1413544420910194000c2101105c00080100070504070700e00b0031279240940211180c00c074a0380000d42c0c81c80c0405c8001000b10761a0303141032004007144140c0d07035282440549800c00506c0c000280c103140c4000520300f0340303007600d10724004488a4100071505a0782d500301c1810000c810700d0700906502c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 552280773 1250 552279523 552279569
    0x8070b070e0d0609152901181e1205060402090402061e070204110324010519110d02160902030a0f050f070219030504090f0b030f100b0306040c15020a15051816 70
    0x34048440c03808c1c0001d504c04116044210311048482d502c03035003051902c9072b86922900e62183d007903a000340640c0107200402c0141c6000c8007141d400c1400107040340c0c980103000014014a1000348c0c01d50003414408500b880070b502c0d083c41510380c140d100d0191075140d0320f402d401d41030500e40590601010090f5481c21401c540c1d204074255000036a031901d0800304804101c4002c0c0201e41303040c640140341d1003024584511070b4404901016640d41c44443c00e11058100424080650801000d0003907c90746c41c032a401060009001d0603010312100b030111002400d1a640c024205485654000c2c021205081100e000948c400212012200b18030b6000403039000d690140d02c003400e89010415454410b07000610b0307100c3e0001c220304504801c076001c02c00c140400350702459243da108840141041c07181c40740401150b9003022050301d410b1b5441c8140c400544844c2d0ba0341060302036000303801540507510001c1221030303010101121401041e0400030300d601075403581106007107410f9009150040000c00400c6003480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 552282023 1250 552280773 552280787
    0xa0e0304181424030a050d051605010516090902030601081305010b03010e070f1a0a031808030c040e07052712340308070b070e0d0609152901 62
    0x2100902e441081c40c01e0041003100e010b86600c0d46035500410f20480781d240c2d4640084d0021605030300c01c0140025082d120002c0e155604080b44046681044400c03c43c0050030038414140b00c0c038504101c004444000b500020031844190f08404100d5104006000c8561b0301714106a500403407244010301420342c1440c0c15805401844212038040d82005c0c200089040701081d28016103104c00c4403881c0555803202c1a8001202c00100c00c0c0c4988010031030004418401e800140c440d028002801000b5022503640d0101c0340d10458010b854a000032030107020a5149802054010505292441c01c000c1030f10020003180c1c148154415802603820824581900c84c1910380f040c400d050000d030f88652105043c1c89d40510100c100103902a40c00c000081c0643c000e01c508281500e4000c0c0d2840d090070125921018041c0e0003620307000c00c3c04802e80c00400c455032400b403040e4030b85114801c0450b41121926194803c81d01c102d540c45a1281006001580e040e214140c11030f038903071030101111900d444140169015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 552283273 1250 552282023 552282041
    0x2130e1311010906080c032a090114210613060603050609010f0f0e090309060403060213090b0d060914030708041a030705030115030b04021605060a0e030418 69
    0x504460020000c0400008048203942401121580740307a10680c8011110b204050041d01c012800c40f03000701c1d0ba0130f80c0c0c80c4080c1d640904540d101900340908690003055007000010143d480680000d0660301d40d580c8404890550070b03003402c1c0710781408621140849009510321054040030b401070001840c9650b403411940e080c0662020400215885001c0200079200445100c0d001d0340300007000050740349100003140100c1c0d2521038600d0903142007c11341c0070408005464903203d44424040c84400b0350300c0c0c0006000944c440d40300182e0758980d03103220300e64400084e80400005460040b14060075100c1704c3c200c6118644c004c0c00041c402c002403a01300c503444290080c9400900c00419080d0800c4000d03c002c009036048a04001c448040700d0f059801507201c02c0350b0b1200083c00a01c010400c40c02c4454520340000c01070304012480d109220085000c036003068014802c20f00d140b8002c0810701000b40310640e080000b444050022001905007141e403031040d80b04e00c2c507824040b4001a081d00704c16502c1078844c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 552284523 1250 552283273 552283289
    0x10e030703080a02070501032703350105130b030d0302130306020703170c090f040902031c0341090307080705010204050a0b0316300614120a02040213 66
    0x203c80b080f0b40000d5032210740380034a034040b82c07074000200e9200000080281d05001a20740010720341100b517404442290041c0f0312250040d500d4a110300024045251046200604040d8020345600d4030040002400301d004101c0c40701e41c5403910b00540360b180801c005070f908085080142e0303130b82018000001d80c402154006800948049030308010140e0102c1404500340046030b6070032854960030351050340d0340715407841598069108592a074650401c1e821044400340010300f612242038121070548031108140c41d0714000030742c1e00c44800c900300007146d100306a101c10103955917503518801540300302c080b408000b0041c1002e181d0b10000d03050310000c004981d4040c2e485400962680b1a074900180030390441c0c040ca501c21540c840c00444e956869405a0380300d520020390302c3c81d8500b0851001c0d543c98a01101d030065119603a910107030071085038600f031010b28042500010344e0f5031801d8102c0c1540700c18140345511584541603198103030074002a01c541900d40403100142c1e41d61201040039148842a404256 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 552285773 1250 552284523 552284527
    0x10207081f0b01140909060f0301020a111b030c130227030606100e130f092012060109022206110106091b0e0411030f07020d0201050411010e03070308 66
    0x508811030480141070140342006004115004005486401450300c85286074041030000d40e081d403402a540542100028101c40102600000424203aa0060721000081012800e00200c81c420800201c3c00821020b8011980d070980d41700000c2e1101e050700c207070318840c014040d0031098424055040324080b888000c07000c3d00b8040704902c10300307441d070440d10410722a00500300001e071142040c9000101c0c000aa94a00140415403c10055031010529034071b000f5075070381c070403a4214040a205204000f4040c086001102018003100084030a11214041c05818142c803e800b0320440022420f054540002025854499142428420030103a5100700144240f0400001c1c2c103540008140781a4a454030080c0141c079202e8240805444c294040100040c010128400c1046c4c4a400740034107030300c40100041016003240118101641090b50241d0811041c42c0c00e000b8402d40410409602301207600080c07140b441d15072030317001b01020700c2c8040e1030500620400005080d5001c2c0306290266a004900603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 552287023 1250 552285773 552285793
    0x1b14150c0109120206070503010e16020a1506081006060203070b15060d06081c05040501030b0418141c090e07110109030203040f0605160809120307081218150601020708 74
    0x254444111200fa00240c05403101091501380702d102100c0c1030b2402c01c0302190781d9445d400c56603108020400c01fa04118050070b20140001a5240d00038610001c1000c8081406400c110985040007010040c105000340340010402c0754a0300402645d10641d04002c409406584409601a5100450410300ea0110307000442c0183c05c1181e911003010380d07040b141100e4110705949000e030001d1241600300804501d040c00200019880b075006001d414a002d0400b01c3e004c0030011402042c0d020343c0a0840d94003071030b01c03c5030b007040c0410031283c0750001c1408903040b0f03940c00010300545030300254081c41e289100d4120024940502410844a007410b04c40e008102403155030400035120f82041c0120200c0001c002c000240b42481031055404a9040d04403010548001d60f548521580c02045101d8200c0700841c80300600c0481800a41041801080e809589506100c024294548000c09600352003c1d502100c3c01401c40c00540099843c10701c21456030181c4813030f00140d140588540c07061003148241040c074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 552288273 1250 552287023 552287033
    0x1504140d0c0606050f030715020309090108010903020d051c02070303090b040f0309152f03071506060801080a020f150c07140901060f03092d1b14150c0109 68
    0x8150081d42c04011541d1960200003c2910342d1050a030f1590010005102c504c3c1d40a01200852109004403843e1141c00004590030784826400680c04e030350b46403041c00c00e1640502c044842050b080c50401d107003260108107030303000c00e50048460680350790120300d500c1054040d52110901c180c02100300d09043c9043d240c8554500c082c28401c03070000744144400140003848106400d4180200d44641c4a6400e40d0b4071010b6011003c200208072000d10304036149024003051008190413401b80080a1403200501d00700c10a4400f00c0d406101046408401080010004201484101e604031503480340c1d11074680000b02c20f00340d0070b000c4100308000010005c90350790002800a081303440d00385007450140321200400c9031000092140c040864000003042e020540309603c510300c01441618003490410066690500143e5440500f0105040c5070b035210080c0410300d84c400744040c008a941c02516400c0c107002c14401090540d25038001d204a01c1c2040410384080280c420040d034803c001c1000e42c2d070500301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 552289523 1250 552288273 552288287
    0xb1503010e06100336080412060b09130b0717090a1a04081905041511010506030f0c060d0e2b02010b0108060607061b230403051504140d 60
    0x706038030903070803c01d00e0342c29140a805103ca25801c030038411425404d142d0f001c2408940040501d2a0304850500c10700009078403400548080c0000151151152000307140020417a0b0030369420900c250050010031540910451802c078041c0e90004402003075484180301a07501441068904001d2086141000598040055540d00082c010242c42d07003452004052041e0001080c1e0f40685220402c2012085015800c0c28403801120107280030b44c60550b4403949040d540080e4007c1d0702c0060000801403100140901605e42c00040440c041c01c0c1110a8080082d62081c80100c50b84c0181c00110b100045d082980d0f00c5a02580c00503000d42d5056400741c00b5a18000d280e103058850030f018036100c642540c504c14450490704080c1a142c030082a1202d10810100d50822103040351180d494000741030500c00e503800405a0140f1540b203160352951904070070b8101e010700500303001881806120030130110b900000c034584100040c202d60007030f945030703810a20039040101b0307504180e0344158607080000c1039014907 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 552290773 1250 552289523 552289531
    0x6021207230405061209030d02070f110316060e06090a030f0b0c03090a080724060302010f0c0b0121050303150108060f010e01110f0f0303091c080a0b1503010e 70
    0x219100c000181034a4a40d100c0c000c2d405003940040e03050085441000e000509030b80c000c1c2d80b0f8802c41781400803902d2184103a03880303002d049034951840d01401b400c01003180c0800a48034401c4001d0002c00003101002201d220042c8100d034208219580c0e030b5601621064201c500710078000d84108503680e02e030304214000c3d0a0181c4211540409007000803410305000c4181da0185243c2c10260a40d1845e42c1c4400420340c012031000d4804903200ca171740e43d60070141c584040c180c014241c0d0002c034032135207180005801c000d0f00b04101004e0080b01501072000aa4022240d03064a01c1d0038451001d40844c032002600e035141c4000001c000f480004140208540c01c156075807140303007090340c0c1c10803150b55a205203c3d40c10242c2d440b55000c1041800805d002e5070140140004c0c064401c0b04450910342c20040f42d81c6080c0702c800300c841081c1c100009201c52108203021000340c0681500b4401c0c591040d084000301a4000102180e141d02e40d100d03141c0c040d136524210714214940008160b5034407541c40d003122510201c802d1f6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 552292023 1250 552290773 552290807
    0x50d0f030e15090c030703050a120306090f05090106140604210501060816060207050a0b0a030b090a0608100b180a0908031518010506160507053604020d080706021207 73
    0x100403901d18031700054000d065a40c4003010b0074600c1500c4d03859a103030034111601d28081c540c6a4a011501401f40c1c8180c41846d507030f4400200d1300e4100358090328211001900328a01494000d00c1c080307076a4665a048804441405030008484070100b00714084c0310341820f00087c155420f200c00002c4020000601021841c0101c00d12101d440e502c92050342d550b03001d8401d4541040c80b2001c10002c20100401800221130f1078103002c40e20f84e8007800004c220300c408940c1c2d4900c3c19601d0034284000e0004204881c4d070080051000c002c0e880d4240b000031043e2000c4a080c620380d0405800080b00503070301c1c1c2c2121070400d9004032510f0710390424041c1ea000c2043d2012403070340158048980c030031206100706022412034401030b04803031034440013400c80202940000c405580c03a101e89035001615071a00c80765008403c403a800c411201c01d805070051180140c01c41c61417100d20080c1000d010140c2c0c1c60600041c000380c1e202003610b5907041c00d840c0807400f034002e201460884818040401651075008200e9885600e40c035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 552293273 1250 552292023 552292033
    0x2090c16050f030c0601360f0603060507090902070812070c0b0f063d2d1b0302100203040c12050601051207230406330903050d0f030e1509 61
    0x161800318003040c0701f8814102a548030558001c5501c0d00000d41841162410f5000300e85c4000702c020880603074480d50b000b2103100d680c541c1080840ea0748100003001420207880f080d490440b551300c441d0041e000c0d140009c0000d030400408558543e00510400c1c094a510400101701440c2c0301c1d202f401c0aa900319940c0b40903460031880c60340104418040f42800c04d400e10b0351803041840b61002e140d00f806a00000f41e00340b16010416040762500c40c400010410940d00d44c80340c103060311020003400070352000e00b14502e140079115040c00080e0080340840ca110560b1000580303e95580c207107403904140f203600c89141905103072001c44c14483c0c0810704ac0e0680b030040d101d5000c00100000141d5a50040b8842e4860302d840301400e510784c2d4845509403624400000744007003120303038481c50a03841280106040c1007814006a04190340040440618400001c0c0d41c20b00b070203514595100c4986500c00310038000b080184440014441c240a81d10040c16400700c4004c540c00404021592510481c0941d01c41c00c007403145d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 552294523 1250 552293273 552293279
    0x20d1d22021810120b031905010b0a05060901080a0213030c0806040204240b0f040f0b0a0e0103020715150f12050105060a050a030210050f0d020a080a0902090c16050f030c0601 77
    0x4070b43c10040c001c0c01d5954002c2c20110305914500140069440b030f0b030b403502484646140303080340042c02d030010034015000001c115410500700003450a0a6000310301074003003440034a1007a0703044000310754801100d4034050faa59111982a82d01010f4541009268450144c0d0100f201300002401130300c501e00c2607900b04900c3c0c2610710141680343e0000702c829000c3c1e02c039000a100a6101c840517102107903c00469508040d00c49004d0503c0c203080c1d4100e5012100081001110280e1200c80702800007000e0030114600f0020340c58002d020007411905580c0745072288024036034110030368040310042003c40c101d039034096280c2c00e4242c044007000700305850350b40c2020003040323451a129100c6011500c0040500e40801e2441e070034400600c80b840e8180c4144101480510f4a100d041e50060241c25030707940c00113035a1400300c0070151540002400e08070b180c80c540a804401610380c0c4083d01c0d0040201c640c440d855410081050041c00600c58004256014000d41515414400009030048030041003e0b1006681c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 552295773 1250 552294523 552294529
    0x306020d1a0a06050705030f040e19020f030f04140a05101d0c0108070203130609031403030709172e06060804050c100306050d030804060606020d1d220218 68
    0x1e600c0d504180e1001010b98100103590142004202c400d102c0c801380d0381072840100c10f20500e500103900c50100381060404000303d8004112110240d401040e400314181565200098814000140f1401c10840d107000420240001104060222101503003254a00101444d100303884602c1d0020461206044c04130a03a4182569a07114080048600042c514910403000450b21054080d20903030070b60200b003000b060491410808c00c030150070a512286815480c6251001c0303c60f26403406c2040d650018020b00c5440c691040d180384c11240c040002c14100c0215018841c1000d407512194610883c0880c808a0021950310b4003034890920301d031007044000e5a990013a034000c401207400400c039801600f060480c503c0e041c0e00c6040034058500d0009116a103400100d04a109810003e801190026040104000c01402001d0141c0000d1010f803e00360514600941040341c01d00c0c14402c014101c145000071501c880e10082c62606000c000c2400f41506010614005d601c40d04224054482035000f02040b41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 552297023 1250 552295773 552295811
    0x2210d05060112051611010c0c0b0408040509070206040215090d020d02012c1c020607080c0703150207231906020f0a0c05010c0f050d0e15270f06040803090106050a0306020d 76
    0x1c12902d8801c1203100c141cae600100c03404010b00460b20910103020200c0c990b11546812803260416400900e03082c00c041c010065816840103203e51582c404000b144020303194001101e1256505a8030844048101d100503184800c8010075010000300407a1041110f40c9401581e44040805681c0304080560490300d480e400d042100300603401c0401040500000381c22040100605030448040d40d4401d070720b0f40c1c3c0e0940c01d01c40b00710103208001e07008264041480100c40744000512041585000c0b03900d081c0700d05a0300e400c050118401c0a40480e10960b05000303040d0121902450070000081c5c0e990442100585001e26180c01a1030540c40e000082c10164000c02c000410100c09031901401c1c108150603000180c1441403070703451280210600200400306580c20b49000f1590704841a403020403032603200341d69006841c031148459002c40a80e9441c034070701240e12500030703400114407580d036510980c2180c0900401e40c00b054020103608800001c0c021254003600c4d44407509201071040312141206140c3d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 552298273 1250 552297023 552297041
    0x3060302011b080a050f09030307080d05090a0312020a0c0209010807030309140112090303020705101a0301020304080a080717070207030b090a0201120b1507050102070302210d0506011205161101 85
    0x6660100034004c501805400549000e03002007000034581468000883d081d600100d8080301c5055000c40c02501d19a0360b4043e40390300252400003004541c805032401804107107914044500e4650010303410010754410f02c41c520a043d0058000c3e50556560075003d82d54110b00d120a800040182c03034007040c2c001c141c0d5000080140141d560854400174003158a0060207511411002d06a00300403640005505210401da80e5030038500000e00502c051a648606100341042544640d2040040000240078501541e840800500d00402d01d0344e5130321802c0d48d0f4082c03881d01c85038031088141e042106240e4000349600580c2d01c51400002c25844d60b20300c4640d0343d070100d00c000f4045030b1469a03050400c0b08551100c07940c0c0c10f00400c050005200ca0090520550140f20140c4260b50006a00003d00d6010880320032943c90340011204586032041c840c0195005502843c00507584070804191668800d422141c40c20021200821070340c14070a001040e495820458480403c14000e84400c0131170b8184145100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 552299523 1250 552298273 552298283
    0xa020c011d1c0519030e0a06021b0307030b090a0519080319060b0c070504060602060136020a030c020c0910030618080412030201140c090609030c090703060302011b 72
    0x910900d010440d000041d1a2031000d4850501c40040100e041084042145511060000a0f4504c0303814001e001c4410904168052034014808024065001805041e01e010314a41e00e01702c190321b100001c0c10100950720160441e06460706210158002254071a91144600d0848514049880710031b040e192200c400501000c40a0000035410240f003404615014078842c00042d0190700c402600603983c0107107543c002c1941c082c001c20b0107103003018481e18002d0865400100119031400340758100c0400b2038103800c081c00411642ea07040c559482076038105a4158204199211415150020b0042081c1207207080103114004000c007890904001c0346020303030b03150b091000c60030f81540c4a5002504031010107045040c640140705c0086074214010700301510081001d03840e0b8a03043c1c140282501c141c445644100c031484024003a5000525044441100301950000d4070313080c90100090808054094180e08404120100001194113070b2210b0180ca02c00d803a00f041d504001e035102541c0c00d80070300b0f0040c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 552300773 1250 552299523 552299567
    0x604030311010e07080703030909050108060c1602040203070503250f1d0603071106070813030e040f060e1b0708090904020d08070302161202030601091a0d05030a020c01 74
    0x3180c4140520700001000c60000306110310340b620400d180019a5101002c01c1e008408103004041d440a01d420091500d0f010500095040154054544c41c4c003030100c3c6c90120b0f0010302064040b240c0300403400b039960003c0c011034591038011400703451584200e405c010b0070b0303000560040050511100301e241c2d100144c0e550f0140003401d4542070302c0105510510000b89a004140f014140d80c502e002144a120150f0b5032000310401d00784400c1c075024002d01004141b180140c104650840d841c100b80038202e402d40f03030280c10b400705078021500401c41c00e2000c0d418503051580106004a103001c50074001c1c000c0e0380800c80c9402d14400040c070907001d0340f10002c1c88054100886006440c100403c19009030004156904c2c550895681c8910f5070700201c4200c005da002400d040e850840e42d005800b0041542d1804046420150781c00039840701014015244516a10f0050503900a400d181040c69000050301903201d4901c3c505103544d80350080007140c80188540c007050b5503554412041611100202c01e0052 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 552302023 1250 552300773 552300779
    0xa0c0b03060607050102070809011b170a0909092607020108060603070512181c080a11130305030c0d03020f070f030c02040c0f080f0c0d09060908120a060807050604 72
    0x1105980041c0107240e00c400d040c044500419420303c010700c2c00c1c81c41149010354407081c14001400c0d0860721052515111039010350a0b01090841c000c405a144034040700c035907140c8240b00c0551395650705410060545241c00140c0c03042008079404103000051900760903c0380c41c0c0d0452444002c0c072031031800900140250000c92998103244002d103810443c6400c03d54140500000400d498100c11101024100d4000551507170308030052184140000182e041803050340755840c0c2c0500b0b1507001901c036510640c1c0d01c08002c00710f50024815503a1004502ca019000d40356241011940d94018681248007406880c105400481c041c3c42110103814080101c9810084580c850158081c95035100781c0070b000081d40001b00681c0d80f4030a5040d002000d4641e41c03907c5180003802030800b44000c0940d00b500c80075000340301442c00e0350015101c5e90884c05601180c1c0031098900900907080110006016050120b06440070034141003019109680040c0108516591050035075510490380c032070301da00310f08200000c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 552303273 1250 552302023 552302039
    0xb0c0705010f0e10151203170c040b03270319032a0f03090602160b09060f150a0b0309070e1b04060c1a1005040f0e1b01140c010b040606020a0c 63
    0x7034955405d060b400c0c4660203a5601d0500d032900b24183c011000900e843d541c00c2011301428200c2c0f904581429012400d0605028a40e8441c0c4030180c80c0c481d0414110b0300007450301045400340b0300ca5190202c2545d0308ea41e540401d200c00300e01c051100d000883d0805003541c3c0304449003020228030380c20700c074522074850314854420745a80c4e11510040d402c044e10cd199071408207506000500c0c00d144007000d05240c074119804c280b20030f644007030010941b94200d041130002c581c05102c1c01d50b40084060004d12060100d050002d0044500b1b81e0141c00d1840000c070401299030b002003002c2c000c4469542c0342c0d1655540e4041e45100c40e4900482d14807010728280014007545106804084a942c4030b000540c0e07590085d6480105c0c04030044a803940ca06081103400c0c0400d00305402140e008100e0000c080c0300507400c0d0811607858943e0081d03810354106c0032100840c40d03a0f1166400d03c5a2092207030042d03980d401d02440550103004c0d80000f550040b4100000091060300c0000c0d034524294107d0070f50305035a404c104d46 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 552304523 1250 552303273 552303281
    0x6090601081b0c0309040c0f0816020709180b090604030906180305010f06031101030b180402010e0a0609080d080106020c0111010f060603051e01050109031104090b0c0705010f0e10 79
    0xb10314581070764003200078000e0040c00c020b2450300c04031002103441e113407080708000580e4100f510210070451616500e0400300e410841540e00101e01125005100b12080c90492814425074809407442d800c28600100192000d0300e201c581502410907004030340d940160041d82c640041e10010005000b031042041040e10900d60003000c810f070b0802d11400f4640d00d46440b4291806507803005601a0380750810404c01c180c01c010454104da00303080c2030101000c2200090741c031a502c0010b1800e1900079400007011603200316082440d6840080c107444c10300c1d0b19000024510001d5020b8007000e40b040c0d0303038142c03002c0380202c490700e040700c01c10741c010410740ca0382d2801115100402507a904c1e6540d2180d82820b01c3c4210ba0140381c014242e59070b40011213103450803242c80e040c0020f04110305007051071070040c800b50368010241c40c1607a0f080300d010324a00c41d1003c0880e00a042c00c043c00b030210740c106014003444241c00802481164000c4000380301041d0494052800c0b207490f812144402d03401910041e00710051504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 552305773 1250 552304523 552304531
    0x10f0305060f120d020f0d050901080a0207021507030e030309102601090c08310311060a0b011115060112020c0f01020c120304050a0201050304080705011b02010b03060609060108 78
    0x1c01e411444140840d00c20011520008600d030095407040c404d0590410110191980f6040140f009600010b00980184121001d6904100c14200001c050340304503011540007a130b020386102c108022401c003003101e54100c560224005402d1008c551300526001003502d584000040c9650070241d0001d50580d24110700c0503801c81c403810903c0c1c004003d818811705140c000c0060000114280b803440c50001d0003540010705007000916030848806120411103400e072140306a85400205410140c10207440c860a00d038140c000c2d43c403400080144039107050b0005a034445081c0c0729110780440d0b151145072074280d01d007100440c0c0d010410010b901907124410441d000029100014900b00700404001d05100391401c141c429a90001000c00000ca07040042c241c07408442c4040d6800d60516650301600c60580400103410803801202103018030126800700c0e18410b6000c0000c120b50300003c90940114001c00f00c07914095480d0541d5440b0310b00300800c40e148114002004001c0655640d00151001007010b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 552307023 1250 552305773 552305779
    0x5070905062a060114030601080d0833040f020306130b06091c021c0b0604020708041509090e01021c15051504030b10080a02040f0b030703080c060601020c010f030506 73
    0x2400014015102d11001100388400318040c0545606046410039203600b01c1084034042c0e4003050040080980c04911801803041603d480d1440752540950305101100a5502c0c0aa13150944124905010550f0703244005c147c0c10740381482020f1030b174410780080740030884026401c010100074010986a050384406c00580004003c142001c00c0f00d0041055950b0062280d0385040303080310308c001507191030640202c1c201107029500201e407a00742da401e211500007030002401260003082e07400410000d541681c010b08081808480c20704560b50b0020b004140b14417840d07042030f10340605480402d1040c02126000e440001080780c4040d1052091002003209841c40340e40c1d1480f040020a40e0360303416401d1000b062002c0c034035a0311345045042c80364407040c001d00046081030b043c6608005c015004a03083d40542c1d01144c0019502400c0c0d0f042c0c03c054082d4456680c0c0c503008440000c400c018403403000d00922581c0c2422603500351703500300059a540b1010020940807828800000c0055882500800d03405400a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 552308273 1250 552307023 552307057
    0xc03090d15060902030f090d020304090e0703060203041a090706050403081e0406080106170f040b07210608070509060d020904050f100509010c0c03050a180803070f0203100507090506 80
    0x101c50807080b160340750401c51409070008180030344881e10402158002d4000c501500100c20310740c0001c1d42d40d10941c851110f845459450901540310144412401540c003e24250b581c0c0ca0541b426042c0344134a0600c90711003074011000310300e08990005810041d11015150245814110b07191031b000b6420011810071a800e211318900c0d101c1d05a42d0203000145050780719030344c0e035504100c0041c1c08810688250300280006004003c2c607080d0002d4040c0e082a001010703241e0580314414102d0301c0e085801018002d00d22016941844807050394818030890b2410026510040d0700d90b82001580340e0180c40c8590700c5481034041c8005450010903031070b00700d88104201c40079400c80307a002c1401c00c0300360b0341c5842c1469924004c00806450a000e80500f40b6003d1a0a0150380d8480c0c0c3c02405034002c08a4100411a00540c490b01e018106800c10b00030f41400c404507a00c0d060985882c44034030b41c090070200d0207801034071441e40580041703026440c041ea840d5140ca04000313003004144110703908018a000d0f005542 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 552309523 1250 552308273 552308303
    0x5090a2427151514030603060109111207090501090e0c030f18061603060503030304051203090f0613021008010e040206071113060e060315040206031b0a030f05010b0c03090d 76
    0xb0401d5107030001d0207905881c001c030025080c000760a200403400c28541840c41001040100d50f0086070345419503070b0f0158002090460219810190700800c00d180304404111810300c4005600314100c8412a403003640c903100b541d40c441025040c407040070b1300e80014900c42400811001000e244405c5e81c040705080c1481c080100c0990303030b18039001094409030180380043e10810443d603030500a45028020a40003180780d42000d40d2096502c030001500c0844c403540c007001042d8140002c3c040c00300400c10003c2214140d003840c500984203480d0201d0300301d104005200b0400c0c0c0080c01807062604a410a502542013a640c980a000642d40591800c61340d5641c00b0420395a15640e01c840075030316501500002440030b05100c2c1c1c4451801001c0d080901c25480a118424514165484103174402e40c1a1500d80d1a0384800c0901115451015880401c15801140303010785240d055000104440e04c28406000d9a41e0718000000207100340c4406203420782007040051118101041440c090b40d00c10340c852210980 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 552310773 1250 552309523 552309551
    0x1b0b090a02060d0c09051c0b04031107080705030f0a05120a020106170307020a080102190c06020f03091c0f050a0c03140d0c08010503030f2205090a2427 67
    0x3100c880f4810443d903461120758203081c1d00080041c003a24090700c80340c000034004c0b42c42c08460300300710030024000e02030840000d0406205081c0040c2c8405004101d940301902ca01006407a4003103800ba10303010307110762280850280350002e0744100f5182c1000244c804903803801c030302d066613501210007042550f40754003001030001c0383c13410000c6a00d6031800c05580c80e2030491040040b00b00c40307503100000a82c01484821b80c041910304140d40d5035005802e092503056201e140140290052a0b680712001c0f101004103c80c240010a5018200c650415103030400187c45505a903001f588801c1840001d009124080c600c90180e80759810560090816000c0c00e050401c5c2031800d54041c0585200090321303002ca0044081c0c004094502504040300650b05002c2c080c0c2000203d401050031140c9000405003c000d1440d6040364a000038090103812140705282400a080207400e00c83ea4142000306005800c001020b42c1362008000d035017130005031010b07101c409610803030310314100c1c07111071001340d40c40c001c004880e2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 552312023 1250 552310773 552310777
    0x509030307060501140a03230a0c030b0103031107030f02010503132a0f0b1923070227040206090301060e1812030c0d09080405040f1b1b0b090a0206 65
    0x5842901d000c510f41d8140400b0708100004a6031580c000d04410300280006403a100b02c00014607082c4603042d4101845030021481c10075492800340c080c400040000c0284401103600364140e81c001e407a04c21900414801c0103980d0314043c40f002d002107031100d54010056125000854004010500b0740c002040c01d80c841500c001641d60703058481c0404c1440420740300c0c0c0798181c0a002820302001c81035896107407055545a80c4958561030629480c441483e0070b905003e80005a03024880c070700540140c0c0741200400030b0715840002c05070303c00c5001c404000e025141d06140c44608654060100300300b51915820f120490300800c80c03455042d503c030354001c900d43c180d10040d60301c52030f0103c01c46480c82d0003062600c0d0406042020008480808204024585074014102c0d0740440840a0000b03030807040d4241400a4004c9400c4941c0c054107042c86d407558440305030452456580744c80c2c01c000860909103400e45485070300003444102001d000d00140046181403a446900035818002c0e85d44040302980012003503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 552313273 1250 552312023 552312037
    0x1c11060720040c02012702061306050406120507021504170703020c040f05040803010e0c09060d290f240a0206040b1006080103150b120a05160b09090705090303 70
    0x35880c01c01416000d071a00c3e005540000c03419000800c00c5a41072102e0b040c18029545401c5100b40040d0f03002d00031911898201ca0741c8224040d01035581c1d5895080c004c0080e8814032491000410519158540e6281403144902444040d0003c1094010624000b601540000d20a0f01c0b0119001c20841d48540403800502e081442a80904458140001007000302c1d800c040f40100e00c0c615100030800001c0c1c2c4142140d05581201c020307070b50b160740d8521050134644242c0c0021908000082000b00e0840a550041e034011000205601e014120284180c50b000c21a0041c80f54042c3d00801c1c144070700e00b0094043d0b07141c1c60241640c4070501100c01861013081d4000e20305040164000303010030051103100107103940c102c02da014100c600e0328035200d8000d0406a06010140c28140d03282c030481c0c90b00645a1041010a4014211528508200c43d034951682400c103c242c0d018010711071403800e04015036100006840c0f400ca41c2c242070810b20818809a401c0041107441406010000c40304603070740400180c070745 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 552314523 1250 552313273 552313313
    0x807020f060c0d0e06070f27030b1815150103060503010606050304140106030305120925090f0e1510030c2705062404030c0e151c110607 60
    0x140720341426150007104d6203d40d0718083c580084041c0108141d00c0500c107015640b1a207050b10a9400d9000d0705010701c0041c210f42c1c050b500d88850004200801111918030441442c04044e107031501e490f00c015110031041aa140d05e0700340180004081447d5030105404440040c5000510b00307849002003401c64503250800c20204c0c1001c4104410441c60f40c00c6001c11043e050001e000b018590f5070060614012040c003219010580c1000075041b040400c800001c4007402d8007903041421500180441880040c05030342c50311800c020243c05030070f100f03006001814880d14005c003c5d286500002801c640b01c042c00316606800031500020106066250340006024480c11501450026901c0044084810000748030305900f05801c0200c1d070b590f880c8401403e0080d1103007481c0e0590079000003008a00c21904001e00710303080c8800114049419060451150700c907002100701aa03000410801e070054800842400500e90301040c60000750a00d4040c200640040c0019090000035a00c074040104c4072402c1c006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 552315773 1250 552314523 552314527
    0x40816050f011a190506030411300f031215030a12170403051813141b1611010201181a150a03030e0f0a0f0f09050c03070807020f060c 59
    0x440c4400c10b1200c102c002100f00d03884901c0344c11180100501c4212849802d101c0d074404000181445198090924141c40003800300d51404110500040c05107001807005803005080c003608040114002545d0310840150001036007062000d980d03901825500504c401542807070419015003640b000c205a114107489141c466802c6408450004c0008100349480004000e0f420203000210b6080390460340d8882c55412510760780314140d80031940d8000f8020550a03031501d061070041c4440c0e10300d20310300e0295000750300070450150340c603110984500829084e031481015000480c0001040b80b01e00300c0b407181c018000401c04008150b15000c0441144d06c05942040b45003410700b400c007100c48203199009889000300c02a608072030010074603100f0213000007030901c500c2c0d00c000106a0344104071000e910100400c42d08006444051003424040381e80701e40f2514517109030011440043c0c80c06440d10070282c2000c000d00316983c50000315040c00b00a0700729000d50091980f400e50a400c14860305200b42c0e00d62030865 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 552317023 1250 552315773 552315791
    0x120609080c0f0a26030a0c090503120903070e010b0f0d060302100906030b240c070b0403061d0d050a08070c0209010e150301061409071404060201062c040816050f01 72
    0xc0c079034203440141101130982c0c0c0e03e01a8400c018609030398119901c20400a00c441455031b0669900c1c07001e070040f0764507104001c0b400008001c0b110040916000c141c00755420160b40b01e0059032038641c01e02030021080c800348404c3c101140944081d1800b1019641c02284841d660b03008102a0080c03416010001182d1f070509000d0140c050242c050b001e00d040d191080550003502c00d03e910004010b030303201c040410000e0b40700c8132110308100c03900282101072a80d0f90350b966240b50032002009a500001500e00b401e0350300441c5d64502044c0e900c0c0b1245036460300352411240306001c4607200c10052240050080443c40e220150720344881e0140079141c054080d04103070401d00340e021a41d44004c04510302c00d0b8142242403001242c060581c065869056843d007071b0a482d0355406442028600d490042110320104000640f182d0541081c0100d50340e07400c2c2c0880e2064401c8a40703101015240b00d0060964455010400052040780201040813881c0c040301c14441070356039403609121100084c3c881c140e454079459 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 552318273 1250 552317023 552317033
    0x702130207150b0906090105130212100603060b13050f01030e010e0604021e03030d050a02071203200711130e010c09080d052d040302130c18120609080c0f0a 69
    0x12000c0110121403441300341c90700e200021400c0350f05002e030b00d00440032810b104041841907016191000459101c404003460700034990303d903612441c1701b81c40c002420720500081c8900c00742d00300d480c07d085442c4a806014200307400e0226031030307008004604142d520142144281e43c00c0c8902448100c0c900f010b8010780c1860f0040200300c100c1140d4000071000010091000350760008215000b00c1212100407a09035140d0300004000d004507400a4a001c0c5a4544007002d00c0d490341c0400d15442c0329210701d0760090200704e09680240903019000b084081a0f07a8880c40b507203003d01004010300402030f4040741c685103402285080d04c0410604c40080f034031101051100c90380500003140da080080c0f40550401000a031444841d01c00810f80030841030703c09114144d143c513603900b01c5002c0c0da0054030300b0461302d68102c244001440385401400010720745000c0d80c445140801c107503c040380c40342075580b09090b0301c030b4aa0100610080c08121050342c0c0400c5414107217007013448282e0780b007101c12028050342403441c104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 552319523 1250 552318273 552318281
    0x70303020c1606122a0e04090b070f0216031e050111041409010b030f0f0c16030509090a14011802070b0403031413050703080f1201080706110c030d05070213020715 72
    0x42026090b403905043c45401034403d5101c00210100c0c03600d91b0f050020480480e00070422150040c1c42e4040b40410031071455084035101d0012204d59003104c0300c03441d03500301e0909012014040107040300105006540507903025060000308038020380001a14455036004030b480ca9000d9845207488081c0113810462a20344910f440340107100040055203507103000c400d440b081c0700008040c50586030303a42010441103900b00c4240c401310312206001c3c07410f06600f0b042c043d103140c20004d213551041085200050310701c4424020100c81500030300311880070743d00b001304404d00c848035424140c24040d824840000071809403d42103000e14020340780021820b000842d50000104000c010000750351070f1442132070010700002100401c0701d8001d2081e903181c0c42040304a60151150b412000650400503001140719103020030b42c03200321501030312804a007203008500e0507200c0800c0c0b900154503810000c0500441c600450060451920041010001d1294505c041040360060341d0155052445204007400300502841 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 552320773 1250 552319523 552319541
    0x307171315271205030706020c060f220b06010e04110d060605120103030503070c08030711061b0d0c090308040905071704020904020d15060e040b010b090303070303020c160612 77
    0x1200303229078029001d041c1010518403804080d03492016800e004c1c414140240e900d2130307a205100359500d83d00038400075500d01055900d54005d10340c4101060809004051041811a0b418a070222042135034481405801c401401c503030621103403000040003640c641c07081e4041c0702516889a62202500301350f46040b01c0c081d401450902008021f80714140b6031180759035044030b51528055540c1d58414000303c903509151100144000404414042c1035900300740384843c034003201d0084079070350368403111481d0010307052010303100c142501042000100125500000020306c070724101040b1040e980e9550b02880e130300035844201d0b003a5480d130500080310317404010080040e904003007220320b07800c0940002c1d40c1c1e800050320003803203528100060800c00030080101d0700c0081080700304000d000d070764014280380b1a208070340172074014202d00004034560182d1405d80314001b00140c02503042400e90b81e1306400035403202c4c0d107402051088245901018100d808840040c0c000740d55186280310003c42184241c42c6105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 552322023 1250 552320773 552320807
    0x418061d06040812040606050a0e090d03151e0e01030302030a1b0b190603060f02091513030b13060c120b03070302012a050304080c09090f0307171315 66
    0x141c1404089080074007030300d00a040e4940c00280300d0b02c1c2d82c58004000d001c203034041c90b0051200e5800160f0405c110034418400c41007081503c00a120b0118101c0460303c0e00b039848202c0700d01c00501403040c1c038918455103001240c81200303003610f235441d20191408820240e004500503800010b0803101680e2002c0c1000641981c1c00c1403000c80012585d0740351010750006c162002c546030307c060a6100034800e402100c0110b800c0141084180e03038011040d4065408100042d018801c21340da0312089075080030445903d0003e01140e01c06c07440c1540c1d1040d40305038000e0500c007501d90307003082220b010500e82d11400a1555460b169064148081820b10013a942e100b1015031003508000c50030070150744c02504042441560b0751004119220721041d0b043d0200c02440064a01d200118002c0380351440015201c9019004070f8400c4010360b5980402540c0f42048101041e842d0001c0c0254000210000841c24101604100c081d0618010b4200b112001c4d0250344102c005944402da090711300713a0001900c0442100d41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 552323273 1250 552322023 552322033
    0xd050301050102150613061814060f100c05030c06060f0907090e0601020a060f0510050303030108100207140a0b010e0a02130b0705210306040f09020108150418061d 72
    0x20100207501d56815610f85079601d05a1343c00a5a9503a40820059101d18038000c10440c2d1502d0354010300d0b8030100c0300070f180c0225240070800413600d0b50302c1c44802e100d00b40091100404014050901000707030500a4600148024106040e0000d0710500c09401100d107990300030602c03442e01b0410008076a02d0031803564000c500100a1080d801d6106034a0310079104054024843c503155000101e103000045900039000ca884e0100b500b074414181d070040c40c081c0003910054503100340c1316030030103840b88028405c1c0d182c03d0348500100307003000303025402070f01c0124041c403c3c84460500d00c0c00420300700002c44000b19440c24a0300d0045c00319410300c1c00095001513004404504080059070803141e45019400b640c94900b80c04942c26080040410824423680124403e07605220008203030843c0075081994064400c17400e040d5114243c15481c811548142d40594400309640c6840c0111000d43c070b030b010052600907031140c0111100c2818280f0340030305142b042070300103003c1141c0c0610700741050340c02034269259001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 552324523 1250 552323273 552323279
    0x608040201080a0b0102030d1401090c0531030204020d05090d0e0a0e0907031209140102060c0327030415030e0705100f0e1903030e490c03050d050301 66
    0x100025040c2d11072500c050000f461324100c40140d180d0701075941840303030580c10140494095040240c0803812516840824050401c81e200152200d000c0c205811058000c4007004942d2224504080300c0c07820140c4113a1400243c0f2500464283d81c0a420b10001d5107466900b4400e05120801c00b20300d510740b2234a0682e140c52138420005060910314072409401e14a080c0c04a81c005400380400d8005683c00782c0340e110044c2c0007840142002c00c2e148a40d24508140107100d403030381d50001c1005403003440115011460340c1c0c0c80d004814205c240d14a207858201d4100b5020480c403d000308000c5c0090041e2a1540e1600b07030720300400405441180c0300f4640181c1040b00100205e480d4655048418525401c1201040742140302c101c2c3d484000401c095446903800d40940103980c0170442c610240c82c0a0303075450904060480502c074040007807090940c0d98821396102d4100c8282000901101e10141c0f0b65038000042040100c4050048540016200881c4407401001040001c102c41c0c070b65801d60342405411585 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 552325773 1250 552324523 552324527
    0x618021801140922060909151a04051e0705180f09040206070503160804153b04051e0106020601060e0607060b100c030311090f060d270501060608040201 67
    0x2075982e200d4014981000d9018910145401035680d1541342e1204014090b901d003c4070026055481003070f1022220a8041c001c0021a80502c540300c0d003071000300054900c80103050000501009250807800980300d049054003200c08400309000c0c2120340e56094541c2503c40c075074410380010304003052050540e0a282581502d810424543c02030701110740c1d54a820490030440d0640c4034002907050044020000c0f10704218518001e0419a196100013001407500040161504e600001c4211003502107034a80c0c20f103034410b40707007840c075540d081200400d00c1c41301200c0440c0a840c01034503403c2c01b000074400060120030001313002d41d00420b510310081c1242d516184010b0b00544001c030070140511000150541446000d400c0140d84130343c0544039520115440000a102506945003107000a05080d0104154415842a24018600100410401d2521608100042d030040c4201e2080d00d031100c1ca01100004220341111154501088800e640106486c0c142d003100c3d40c603040603080c000350300c0a110141c3d0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 552327023 1250 552325773 552325777
    0x6060609150702060f0a08011406091f020102130609033806060f03070201090309050f0a091a1011060901021204350c0f030307050319061802180114 65
    0x40604a2016030368400c9001003413140c460810f40300c2c070070040010a680502d0b0301405640c1224058038031494904840002c100041c072a08000780d07480f112121080a400b80b4075540720010160fa0b0000600e052211080c0d6010400c85600240100e18001c40403c18007004055800e10041d40c010b0f52100302d010184801303011528008082a80b864050001d0141e071500c804407081d9140d04019552649003400d0000e002e03001c84581107000501020000440f420200780034000c0104c0100f801c1402800e150960000b0050306424107454180a08041c415444103000402803038040ea560b40c1c01940102d0a4034540746018007a0080caa10402170040c0d600d0100b00b40c990000e43c000801da0340945004819038401d01000c402001d8a00e102209110500302c0000800c02c00144905030b42d8801001049203803a400111800303400308400b040003d160f1903204c1d12404207052041000904c03151107249072098030036141d151803e066030006502e0031500505d0a0000706032000d20b0141400c40c0030400800080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 552328273 1250 552327023 552327049
    0x90c0e0409050616020a0b2706090c040b040603020a030c15020d08010303050d141f0803040b03130c0b0a020615060c070b16060504050a0309051f08131a01050306060609 74
    0x40c2048074200c3c1c100c10b20a0007444111b0b034200703151103120b00340f408a081c548846d200303465141c003400400c40084040c0100d1001e03c0362084001034030100024038280000b4003031240745594015510413000c0016030303680c400c5401540c0294582400740c2d003800840000c1c05c0d1201c0703055055500c140c800c1c204155011111360b041d40da041c900580c58100444105014000c101d003804040142541046480c884040003841205a40c040403005a5510014240c5900c220702036038118040c100009480000b85880150a59210300d01c1d5962840c0d44500880c05074010b0344c002d40068121200b8003000040900704103c1c40342080b40c0c0c030741c542188509500d07900e241b14844c4074002100820300e03640441314400741c01e04c0c40c0e410100512240ca401d1070480c0d00c503085a402140030607038025011a203801e05a00c0c50092a0050034440c1c1c0c2d45030a0201500d000400428090941d0591a015030000b221303c0c00c20701000410403041c1d04c0c194108000c041c2480c1c0010310f4207010f06030074014084641e40d242400050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 552329523 1250 552328273 552328291
    0x30310060c0845030303040605220501140f07081614131a0702130207170a080901061a0a050309010605060c0619050f04150b0a090c0e04090506 63
    0x11592092600b0b40240c01020226540b1540e080010403450300303c002503050043c90607480d2400140d40030190b0b0781c04105011025019030081c4006800282c82c2d0b8002d42e00300009440404c105d011305d04103040a12036021040751582d441e070181400d04c4012652960700110850101c245924108100070042c24000b000802280e00d40e256180480b40101c0801482c01000000d80d070340d4a6200029520380340700e0340f0808034200b011400d1094644c00c124155843d4550003440035240b00003014582000e5042104180d03900c00b802840c0500542c0c2e8900102075030b03244e94580039090b160290f80b582c21107440ea17014401d200320aa1201c0340001440003207c0da20400741c10100d03120f0301c511942600411017904890b800943c0010a64507140c000121288108401081c804039416503141080c1590b00035211001000c80d00340c00f1030700281611900070a01d00021400091b50400d0340001920300480743d02c0041c039503944020007500242d012030403072041d1a040e242842000d07000e0780c510742d40e00001054500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 552330773 1250 552329523 552329537
    0x90b03010203071407020a081c09080105060904230312010305060610021c1b0302031213110402030c090a03060203010612090209060103050c07080c010b010e0d0308060415030501050405010e0d0203031006 89
    0x31540c2e00b0700030001820b0840111041801100302700000d0f0710301142d1180228131540d20001d91840140105072055002078031090503921242e0344c210384419100488000c91b08800506500030070b040010b03142c58180040c4c07805003540b55040c1941031260180100f40100900410114541d0700000d04048408040c2052003800c80c0d030340b6040700c00c415130801c111400400b444d41d41090550000142c800403040c1940a41145c0310968020760a400ea00ba00a00382040c0403550745041c5403d5010b554001181c070101c9242030381c10700014071080c0580d002150007503030100043c85007590003000100c508818240c10810000707123800045141c90000c1855041544502c0003d0070b422103038098511080e404000c454580e85400110b0740600034040e17002d03002a0103c031812a103403500c07403410703000d070768142d22400f80603242c0c0414070001e4000809103002d2000302c40c0c00000016400d2049034032840c050400064034040384140b03241400d101440b21800c41d4414018401c82d07040701c601d600101ca1503820500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 552332023 1250 552330773 552330787
    0x40f110a0807090b040e06090c04021804020307110105090a020607060f06030203030c1b090c030703150503300702180615070f02010e061809040f05070b04090b030102030714 76
    0x50100c42080d00000101e000300c1e10005a50300143d0084a501c00c801c44040c0f18441074088500c1da1100203c42203080c50344444161041810701d68001c04e060143c940c4441e546050304c802040aa92080d0755500024186041503503c8030030078403d90b900410b20340c0143c01d46803203a40002e242400342d6000501155520320440c00c0807501580000020b65024058a89803200e04115544503000f0030705d10036032111050b41002691a1407500240700e4040002c0c000e0464451080840082031441e540905600c0142c2c0e001c50140d0702007203180c4c3d84142e0010035078800075401d8103540d01520000d9042c42043d405218440c0141c0ea13074102c602811034040204405955100000791813400c00395804100910001502018045290120030320706000b82c07610b2500e1aa88420320515200301042c0140709240603441204078035002c100541c000d4060301c1c20007a19032094441c80e013000955403021000d410005400c00c51700109006444130090308500031420b41c98000d030041e0184404075001408104006811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 552333273 1250 552332023 552332029
    0x9020408030a110f0601030c090c020304050d0f02180a090311120f0c070b03100e090a0b010915080d0201050919050309010503060103090c06020d020f0613030807090e0c030618040f11 80
    0x540c1c8210035131801c0343c0d00740d6900d04140400800074012240c110741401a404580c0e13000000310780c00c0350b10180c03604880003181e403142014900181d2049901030401008501d030240740714107c50080e002d05070001810314403403038068840c80c20800c86403100c0e0000c403814101d00242e20259180d22030000b06d0580c0c0c800c00d5000c0c0303601f003040c0c50b0011189080084240541e510508024400383ca0010b030710100940c4070030100668030f46450000034828000b240041c07189c1740c03142c3c000348031541d046001006c00b261112060342c2814501d200e0340740147c0d9600100001280100941207000004082d0380c50303120f480e07407030b0329460307211f103035216814400c000004c41d41310392181e803043c0c00d500e030000c2c0c0709641c41d500d0302d10082d00c03100d02c0c12007140107201711807000611110119206e800f035114840789541ca030074103941c01c1d82c04d00d000505020a000c1c6614000802203c9102d100b0701c174141281510b560381c5440300c20001d605030740240705504000b415003000001b0345002c015001c007942002c03d004c2071002c02800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 552334523 1250 552333273 552333283
    0x6030c010908060c220b3001090b0102010b09190507080415110d0f050f15030c090403050903032d0c100905010f060e0a061202060f07020d02100f0909020408030a11 72
    0x2d00d024440707035000006d0400c03038071025251021110060401444000047c07030070072820305402d035104a81c880c0c0100709210140d030080c480400c0600001c80d82501c69000501c3d41c090440300e080d60b80710180e0150500c081280b00b80c0354002c8040c02c6c9010181400d85030403510b0150507044811259942c009a07400541180540e40200c514090031301401d011010703214040d050513a1000c0d2040701020120321014041c0b01420101c5d800600180303c2003d608013001071304a405001981404002c00501c012610203100404e922038600e8104221400510080c0001000800140c44c24200500c071518003d040864400c80c10700e110440455004a10f04115005000c01c220400c1032901c1c00d0300000ba24185442064882c501440003041a17641d100c84c1210014031700030000750f01c95802c018841c0ca6003001c00161560307a0015110803080d100d6903001c103142c0702c5181d44150102e22003000000380c031079000c00d2500c081e200c03e03003065062500cbc08203226a00d0040460200601c00703291b07400e050213030040007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 552335773 1250 552334523 552334567
    0xe06010b0a0f031404050f0f030315040b13060834120510020a02070e13030c1b082e06030308060d0609051e070b03060a050904020303120a0506030c010908060c 70
    0x3100c13450400717281507039680340d003055214400d0203880001054210080140c074421044100c41c0c0b1320b8440301d101080010300c11081980d9019048038034101d041c0c2e500748034400c007a2005030000c0041340300d4510f002c503988103004080d2440343e0000380100d440401189408040b5006600b243e00c5500c0030785040341c184102c900500854903c0070030045191a400680b120844103002e14256054030f4003d580011520003e01c050302040501801400240d2400e84028681c070161b0030980e402ca40700c40c081401e2601d80782500151901a12003d0000342d03035580e0b03a040003c0c3e801410800b031859907a02404054005104903c141c1c1c03c0030300241440100d8010100071544041a906265014004103840b03039000ca0700c0160f5403280200202d2110760817811a409013400410382d02e80c0c2da14088c100f02c207907240140101e80500050242c4240d480c20200910f001d8045c04101155520301030042c185081c0494202c5810407062910070001a580031901700c0e0480002220182d850b0542d40d034240307252076005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 552337023 1250 552335773 552335801
    0x5220b04140109060503210c03041809030806010315030b060315100305070f0305030f0901030f050a240b030429010605040905070e03030d0c030609140a0e06010b0a0f03 74
    0x4041620740900703503005241610070941c002c000c4140c40d0030905a880f800f2890201d0b905112510049104421038042c4c062540a4021240b0306070b101e8140c100c02c1507944015010b80364075241030004240c1c108803455400b030000e20381081018181c3c09134100e080c0d21031001805100615010a171140c50600c2860b0309106032003801c44460030890040310a44802d84800d40b03803405442e40104a00b0004900390040320740040c01541003002488410a80d544460b203107034181551002d15100f91012801218032411440500241c122a040c1d4075070000054810005000c0c4003c4d84140a48103052007581c2e042030f00028101407141c01f40c1c0c05035546401c0a041c0340303014813104000090050340700005200362010140180059281c03c00c041d24401d40200d011503044c4c0042c0440780e801c40ca15840845100100d00d00401d015681e001400110348201080c1c41c04240e04104000310844503004c1ca641c0d400180c4010825589030005802150107000b003911708000001c461146014466007040f0210b01c4c0704 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 552338129 1106 552337023 552337031
    0x30f01020f180a090903050d0c03021c0504020a0806040f03121a0904030909050c0a030b03210309030c06010b031609291905120a050105220b04 63
    0x2003241c1a000100d0500014510140d07000e945c000fa4000e444107640c0d400c2c1069400c060740c00b641840005d050042200e45d8036189a80301c04501c0203038004001429032210320005400b001180e10440c600d114200a00040c0301c202101100d849110352a69018650058107100542e40006040a50348240c9101c1d11101d0601400056000d40300c0d2909d81c8072291190340701d404446040c2c07a56050034402240001445805120f00f4542c601d00300e000b8003c41c03c15180d00c54414269240300f00c041080400846c40c013141c01c00c00e40c2e0a0040c140150342c644c0da10b07410b5019907608203e0340c0c801c80c030f000c004c0f40300700150080135000255031405d066066166a00c2000c1c801480b001e0780c5102c501c400820440350300c8656202906400441b035940d880e5200c484050100b549003024086c005803619180c010051503540e40884d0340a015520100c0b48046518a1424000c05003140101e40241c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 552158273 552338129 := by
  have h0 := BRFrame.cov_init 552158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 552158273 ≤ n) (h2 : n < 552338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
