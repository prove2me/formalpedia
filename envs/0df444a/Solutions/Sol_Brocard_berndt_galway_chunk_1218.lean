-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1218
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:49:32.877873+00:00
-- url     : https://prove2.me/submissions/79d5f0dc-ac9b-4a21-b1e6-d8a874fade79

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 218884892 ≤ n < 219064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 218886142 1250 218884892 218884901
    0x1106070c0f080c09160c02060f190314090c040f020c010908070501061706071b0f0609290a15080601030f120e060913200301080708150a09050307081c 66
    0x350f0603194030605050414020701a00c041d5078400c801c1115200b400400c41d1a40401c0c2c40c0030104042c0c030707992589154107042d210349c8040000100060314120098017485540c0680c140918903c0018100c10b1b404882401f014040c01d08170383c49165002c0242c0381050f41c1c03d22840041e1405074000b940c072600c0302d241460070f44401d0760240d10b240d10104014441168007045864005c01c2c1c0b818038148002031502c441e403038001c1c1e00d100a4103450442040100707000460b080803000a00c58071100714203201122a2007408507440d0a50012450b008000030315004032603029402c616200d6009400320755568100300e1030410260002c0f00d0408001e264401006a460705503900b250240c2031103400d000c540f43c04280c05000301d00425105d0001c01d90103022151007503101122040a4020414911400b078400e2070055000f885580014030503c034000810040c0810a9809200d00d0b41301c0755404d8580560040c0030305103141094500e40410052000001c102d500101071341c0403a440515840b03030070f4807003800858 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 218887392 1250 218886142 218886163
    0x50a0801140612071205160e1b030c0418090f0807030215040314030712060b1c150b0a030b0d0b0106080f271002130f090204030507031106070c0f08 65
    0x8200751040c110f8036020100c0c811041d110003000d40502d6590711700345035140055031031040c01408145000811858407081b8064803444000341c51264800c10404011141d104c2158080c1b05407009000c04d0200b0301c0e501c4210940707401072400103e0b410360240c481c240d4219020742d0072511418002040010190140603010110540e2456900baa1400740c5000d48040d0702805201d6920303100000107119140501200400415819010040c103a1075822007404d617030000c681e0b940c0002d00410308940700500340c0140f04c464046000e451040c140b0f04910070348241c00c40710348101495224406c02e00a81c44415440c5021400343d070499910794507240014120740d50190041c1c3c0c190100008211502c030561121a00d2902081003494118155080e0142007040c07011210341140d000041000403001d20140c00c605654662404c5495a503580140900303c1c4210b100041c2150420501080443c4960912400002d00600690f00c0c141080c0d9441c0442c1025800c44041d485016000f8010120100718441d844c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 218888642 1250 218887392 218887399
    0x2030903010c030903081008060a050403031407020c041401050a030f150c08040c05040e0d0e01200a110907090b070807020909070e0109090312050c0c030c010605030d1e03050a06050a08011406 84
    0x4641488e0700d094079081c00803d0050b2183e240c801140401d40b20350303c801d42040070900228081d00304104000e494502520078244150b05000c0c1c030000781c40d05120322078101c81000701b011070407903e55583c4a50030b01c11a43c0555080748a20410a180907160069410028655070b030071846240901c0c140c48001380b2504041d000e03a24001002d407610800091540d1420100d0600e65149081c1c200102c80322141480429406010078200032a08040050000002c0b4800c0c1640c14240714070100707101e4804822a006400540c015400300822100080100016070003800c403240340c8001a0082a50090141c1d0305002c0350b406003000b080b81000c0d00d41480e014002c0000b05000c2004640c5004000b10703941d00900815a65501c081003041078a04204ca200074100360a890715100e960540c54000d020901c101b034001d010790340b04010b80c01d1207807040303803045000076a03071804a02c0c02d00700c2100149401844000403e81d90200496035940d42000000100442d0001040c0c0b0b4050b28070700e1048050142030b0500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 218889892 1250 218888642 218888671
    0xc1203041e031a0c07110a05060d0f06080604020102060403030504080904020304201e040b0307031707050616080c03181023090c01050c010219030b030c030a0309050d0302030903010c03090308 84
    0x415045100445d81144d802c05000180501482c00043c284c024aa100c1a0b014000007125a0f001070303250441941c03080796070720030401c082d83d440440342c86002c120780003401a00440d0025000a011340d0189400500446074241000383c01c1011404980c0152401d8849403600c00310b90403041842d1254102c0b2104c180c441b242402401c1503800521004001d11a1250b038460011900e40d4404001103c02075401c50342c40312613160300b1701c500300c20b41d84454016509401201c000480c85042014101c010701c5096503100c4090b620001d50f4600c0740c0010b411b08484001e00c0c045880701c081d0030044140f1303590180e200000e040f081042034415210b00c05941268880d064010840e8003003002c1a032030701803076080c00c00c0703a44da1000c1800d0720b00a11031000000700490340903403130105555140c0d100d001c1d4008154101c4411f81071003420940d030317009030781b000500050783c00500340998205081e01c944201d00c680100c0b41030500c1c00b00000d007920000d04c0c2403000a6076683d640c0b8140740c0d0003600c194020880e1048442e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 218891142 1250 218889892 218889901
    0x7030b06031c0923030105040c0806010605120c07050f0d05030a3602150403060507030501060203090d1e0f060b031c022d0102070c090e01020901020c1203041e031a 72
    0x60a0321041c0c411030024680c070741107013940080c80d110004000c4000400811141c070b040d00d00107031014140d000d050f50038880c003c00807603c2e5000c0c0d4100c404403590050303502c49954600034000c17816072007400c0484050207880002e10301c017003082200170408032480e2980341d181c0c0342203011402203843c00e8041c0440c0360219844e10350501400c0d00c039040703c0340d1241d8505084030a140003046101100980809402d08001400005c1c8222a40a103000e880700c1d0707030248901d9036541c80c104da89000701941240e2010000c0c86140c0010b07120842241681ca0500d001c6140307496a4950306030700100041c066070800d461361441a4545801e20000300003600d811108081c060451100a6607072140c203100420b10140050701c0401c0310032203080300c10000c00e40d03030003550741d080603141c282418481c0d80b10b0000200d0a20308001c2036841d040c000d40343e4840040c1c0c01000d103d40c1c101d081150702c01e07600f01a030170b1500042001040b04a042500c4083c088040c0220b480d02610b907140c00600f510b44070b99050400d460000601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 218892392 1250 218891142 218891147
    0x9030303180f120d090501110a0c05010c0e01080f0601030b0402120406140c040e06010203160501140615120c090a0f060f03091a09071509030605060f0f090c0c07030b06031c 76
    0x880c01a240c2c03000c00900000c5d5072074150b0040c651160408900034000c6014440e00354400e0142e008584980020b0000080302c1e6015a0790480d000b40581c0403407000000a588452100d91a541c803403c14500420b0b00161407002c60100d9200800c0c00103801702c55000c00c401d015040c051030300700c0440000c4078400742c6800381e07003030071742d0300507401140013a050300350110b007030343c2e208006950000b074520040c14400005481c02c94002c1125401c8681e07042c8003030001504030320346100d484002c1102c4400c410310740413a10780300110a900082000c0b0841005010380c1c3c920f501e8400c1800c01511031204080c8240d410700d0f80c0900f2074145948243c04041c00d21100d0000100f00303181c0c0f59840310341c41c0840403140e1294000c5c04d050206607080303509425034903c451200b8940c07080c110411030b80a0903003001192112018045208003000e002500000456031060017403c21814280d07000040c09602420018045022810214668020396030119107609008552405114411042c94035000642e0b80d410301c140003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 218893642 1250 218892392 218892397
    0x3092319030201171005060d1b0c0c060509010306031406040506091225050604080301170307050d080c0c0607120c0203190e060c070f0306180c05090c09030303180f12 73
    0x441c07061180707800801e16008035588039401804004010230b13181c1340980341c04401088008400c820703200e0314544000242d40207014810001c2d4200c0407921103541001415a00c5900202c1d040e4100b644d107140c00004142c4601c0401d4540c0c03002c1016100c00d050a0401c1c600d881d102908009254100105040d0088034600c110f641441a4642c48041c0d288107110101d50034036400405811401004104420059010001c0d1705941c40c000d60b001801c2d4081d45140e27070b02d005408008150707601640c5a030141c1030049640c036a000f00d00c40c0d0014901201031012070305001069034002d0220b48680720b040d0075041706000d01c400c180d909100550070001d1000507002c44c0000c030003000b02402240f0405040c1521140b00f103d070714189841c01c803090700d55941e4240b2107041580c8010340d211490070100110000025560b1020a504503e4041803141032078200450300750050004c06078000100b0104050b81c41c01e102941c03040d40000e88001510000240c01030500808040c5103036150401c84101d98865959801d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 218894892 1250 218893642 218893667
    0x10906080a05190212010e090a05030711030309120102090a0605090d03030504080d0c1e0305011d0613050a05060a05061c0902040b0d0c0812090105031303092319030201 74
    0x80400c907a10750504441603002c001e0312103c0198000502000007a9003189110304841c00d00e14501020b07954281c040c0d440d007040210040c8184c000300401c070f012850709050301102030002400c0c0e03803500000c680051284140d581c41c00c50283d40224094005162400c1680d00a00144c01c20302c1c075001d00207000070240d90800f900241496600d401040620050b2020341d9280c0141110800075a070120f03001402807114020071f0045064140b48c0210740278840d00034941200c48030b0194110012510b682d02c06181c00c020151074008842604a13508030819000d6a40a442940ca00054a00384007082c4440404181c1203e0b00401c0100300140e8040244406001110281e5034001142c0407680300003009012200803055111102c039000e07505001c4031001002c04ca501030801c0f14510914400d6401d07580c05820441804030b1002c1c000618600404011000d80d98480e01e880e0082603120000036901c4020b02c1c00410002c0c9585042c0c000d01c2c1801c489803200003102c03600c980d0a4602d1540001d040f444180c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 218896142 1250 218894892 218894911
    0x30c03091110090306020315090105040c0f0807050904090c081905070b090114030106030c08100e01030f050a1a07030c02060c0301030618140109020f010f0f081e090102070c0501090608 81
    0x5004071074003841403d0b0300c005194410301c15903484c141034049441002c3c090400520a21100000060b24039143c400c84806d28441c2d00e0b907104056a80101b0b8a0f440c0005200a003404000c0007548016682c41c419114890b1180760325241480c14207116601c0d02000361140c1c5500b01007511400080307840011860100c03403074902c0315980d4200d4280100c0355810680d202e145a08004000442c025415800c01d00e46141c15564049182d903d200280307001c0002c0b80320b00d6007030401640061011490002c00c029031503004408440070b1540d02d60350928589001301c03890b08404444001e10000c15414000d0381c80b9a10b09100411050915a101540034403043c84005d101e90313501c00d40035888141000d811b990f40c5421282c052203403042c80030107038060075030150201c1c842d8079225070125080d8041e0a6400310f056082d901d095440c42510002d5400d00310150041560000e00d220644032084944215032050000340300140c0c41d00c0309864034003044400707900710606100c1100c806000265008000c06d07031028925 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 218897392 1250 218896142 218896159
    0xd110702030624120a02011b0803130618050c10030c08010b1e0f070b0a050403051206040b040e03040905010602150c0f040b03041113110a050c01060f0e07030c030911 73
    0x241e0a0003000c401404580c0013481000040f42c010b0000c200c840c0200d000f82c0790300c0482c6c2040b0310301e04205000070070020108130b801d0000c0740340d1141110700364080d9403044c800052800500041c2000010220b2401c4a103a80b009003030103464140001000c0c0002280d050901840900c1c90000c0c0007442e0500608100c0c090104503018400c6900006003801115121a2030780e403042409a40700643c410712007660801d0300c400100d0f0b4100343d03034403545200e0340e096580e03607080008401c1101e0400c00e025000303a03841903e819840c5925503c9105103900751210000655686140100c40c1c0d041c0c40d8142d0103441590040810036110209041b0780c16881700030742c7c031450f940380b141d1101c0640703601403a00407c0310a0700c0402080104003031003030180b420000071240144007591400414050700e0381d00d0884901040c081c420b054410b8040c0c006403052100c034100100d95030740c0b00c41410b030000761a0380c800001026100103001e10f00782c041c8281071881030280f038203002d01001500d90406903080b5584660161140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 218898642 1250 218897392 218897431
    0x90c0904080d090803070306060507020109290a05041e060c0807031101050f0108210a120612080a09360e0601090b010909021303061e090501020d1107020306 69
    0x750480381801070892080090011900704101d0315001182e907000072901d80341003c103071180940c040d2411158140e50704201c2d24205258003a800321301d044126606400340c900340c0c070f640320050301915409142b075503100d48071443e1003131400c01803001c4c0607085c00c4256182c4080c0007841e40b0006c1c80b04010341214280d40d40d882e0520f02100c0201140307a400c0d490f54646014007882c11040040e4504940745001220340018070342c0841078a00c1d03414690100e503030303100b0020f4a1886000301151500300744c1c0c900000807038507030b50761040e091450b804008880380140040c08070103036900018200701400d103166008243c80c00c249640400000d040b81c8001c0d10240d2611020800140d940142e0741c1c2c08151015a00d5650352100540040c0c40da00e60054041141d68001242180891007a500000c0c40e0412520b82c661551b100c41c2d00810403130107009000c41e07003400008042075a0b80640d0044c60303c500300042c4e845c00048040001c9800701c61404004c0750041110801580d03001858a410110315200880407450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 218899892 1250 218898642 218898653
    0x3011202010c1a060f06130513020403020402070b01090509030703020706050306040b0d12020129040f0e0601060e130612030827031c02040605120c0423040b0603090c0904 75
    0x4440014021440fa06503210340c2100107290500a24055401d03500144403181000b44900481e901c1d0481c04d404100708000c50f141804075103c01d508003410040c0740ca034030b07600410f042c1c1e8041401580d0314650400100b06014141c0708545e032100040c03000c0d6040001c90358000b500c4000ba481035404002303000c40400d000703544507449282d45900c002e005a0b00740009217404089211420440c1003d54600946808081d948800090094010130100d1100300d4150b001c0000800402e12800c0300542e40d5828070f80300b0039041107294042c1a440d10b0711454110040d00300001040307404900c0b0400da04200702080003c02902c0f10041c00d980c103080c031080e16654600308455a08510180150b0360003c580c10b00e0210b0700200080418440c0428581c1a2001e0342c1d00b41c00a92145103d04400a40200001d0b0a98007441b04d0050300050100c001c01e1a203a616010242c001080e410900b414041c614800c1c1104c3c5024802c20810140a4690360f08502d80408081c3d21003a610031600d0003080403030006000c004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 218901142 1250 218899892 218899907
    0x60102030f0d0b0a3309060f050f120108030711010e010819090b010b0706140408030c0706140c0a121505040c140d02090109170a1203200c0c060f0301120201 69
    0x540b940e40c0500000903405d6a02c8400e02c102d0240c0d0404d10086100031244591a0f40c41070711555216041029900e601c00c840c03d0340194694402c0000600c0642c284a40c8032145600a18a0100442d141c28070b1782000301c40200e2645607913062010801d0340d051281d030054011540041c81c0201c001540d41300106400260406440c010300c403d85400000c5846100c0a020307040703c1d40120000c001c0310f080721050310410030060381e02a01d040340c1400040c420188402c0200000c5215510214402103180b20905852f8800c5e14041da640d00702040040840354000c109000a251404081c4a20005404803458a41c0c41d4083c19000341c0d00d0b88000c0b04918050119640b00701000d000c856a5038a103084250001d4100c428500d0024062600001d400036094400e0b001810080e006404250b00542c0e8840c0f92460802201090644500d00141d081c040400d8003032901d024400c001d40e442d12400c1800e8280b14804000c0c078442c101c240f064806106007001581d05440d4400c2c00f5911107070705400140c40d0603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 218902392 1250 218901142 218901149
    0x3110d03050d0903031d0a08030a0b13091a0903090a0303200318030607231305180910111204030509130b03010501060c0201080619080f010e06060102030f0d0b0a 71
    0x55081c03240c0c043c03c0541c164081c4804408540da08010aa9a00212030302d503441c07000301502e904010300c04135150500560260b48440c034010180c0e4551780a060300e00c4203441402e05c081e10b0207503004202c0d01840c1c2c20419a1a480400b00003e03614201c4010000f803203075420390001508202103032818413100000303035200400401a000841c4d4549480a03440b61403d400e00f00700c28040c0c0210004220040d000e940e10306103003804140c9018010707803081980100b542000240101c559092080021a40c984640103900c02061008441c07451a00182c4945002c0d0944004440b0034079101840204500100940e914080031220140c2e40da1911b0408858901441c4d55155100260294403074201d8100d5015501d5000141d00a2040340e9803404181c40c1e07a8080c40700680460b044100150261401d13041788000c20540c51105400503031a43c400b249007201241d154541c0340c3d5256030740082c1440402c40a907002c60309200039403600c100c2c0034041c00940606402228540e445002a40d0385966850080018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 218903642 1250 218902392 218902417
    0xf01080a03080a15080a050c060a0203040e09071d180c060a0311040e18010b030d0e0405181c03150f0e090a080f04090f1521050304090b0a060201020403110d0305 71
    0x809031604041c50321900180c40c21101481545d23142505030400d0b0084e00d600031100e802560606181801c03255a03044024001141c40c080d00342c0c04606104041401d0701240072401103000903161002032003803594241040c54031070b5401210002c4050fa1008202c0d0760803c40c920b80458140382e280c420003510300a54100c8600c44203180100459941c1001c00240c0841c03490001340091541501456203c00b55070200c1c45c0055403942403048241010f8019039086287c0c03071980110410340030340d82c0b41009010903a000e000207000d1400b10440da4035000e010444c220396454514a680750a08400600009100300d044101090001401c03038081401030191081c0c20021495881428210741140c680c01400b901000500e02400007201c4420340c0320b00000d01c80e080c520307038200c2030030501404088000004d01109504260541d400010300034805400149030100300410b40703400f0380040004104068100d0383c00c583c4140300400c0450b101614a400300001540c2c20382d604040c0741003c903114031580401000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 218904892 1250 218903642 218903681
    0x12061505091003050702100b0105160309140621100b0301031a07021b01080603100f0b09090d0507120504030b07090f06092403090209040b040204050f01080a03080a 72
    0x145140c006004100300102150824640040e07900709600b00c40056504d5801680105840184030310203501411110f241414a1070030300c500d08030740042d2a080074804500141c03000004100e0240b0006600c08811000c442490500030b070351b85c60915011080070503d40040508010801d8800195900009000200c0784075580b0f43e141e04110710100c0d201c040c03501c88a402c0c00002000e40707101080caa45d80145005170001c10b0b0449000448070320002918480c4d05010b01d40d552202d9511620803003000d90324044000c40c86e0800c1350100441180014541d030202e8120465220045501404071001581d1100080b0040d2245020880d030034062608000c051040b014280105250890a41c400301c80800900506190b211041100ea80c2c070103124214082c020810055503612454003400480000c0c0d2600052581c80e540026072345560a6600b40c400d65a032400f03100550070b040c005c0e2039000900740e07594961545030841c2d90341d441d80444400f0f42084109004210044503640080240011b066400720 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 218906142 1250 218904892 218904929
    0x1090327030206070501020c070509090606011805121b03210d0603060f05040204110c0a031b06090807050c01140a0503090a29010504110a05030a0618021b0f0c011206 73
    0x38008c0d80802c10030701c1688074450740016a4034018281500c02c0b00084003801c03140e00e401c40107641d00310752818150041740d81e002c00803406480b02e20604c0d10484940004111888168035000100e07014094082d0080c0c2103040c404066079070900300700210f070f5003440d4420390706c02e0514803000c0101855000241003e013070000030503101640e500558090b600885080040c0802e060b50103859119811100b05c450f0051500d02c008280a84c4030300e10401e41c4c3d030030024034440007596101c01321095031408488002000c146281404401c1028000d081402e0030103400300c007004900784000d4069400b00030f081020000000b41c003402c2c280b12040040381d01a050f81e0008c1c0c0041c0348130303107041c60310220300040080340000001d152900d8002d2030382c5070516186940c41e012450700100c0d510b41c401001c8041454a60400141c0711000400c0050015040d040040c1c80d018014100c8181c00011000f05070194045000119281c0c40403440280c1c8031400d092411901c8c5400040101424480c1c0c010350645030500100b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 218907392 1250 218906142 218906153
    0x10f0204170f120903010b0a0b07050d031808030603010b12060a0b01030b06090d051603080a030f020a1403060f0d0503040501020c0604060e09042d140109032703020607 74
    0x62041d224541020208540103640d40e95031502e0040d07404030700b98004036500e070200b1800030050140020107400842c00d004400085018140d19a0020b01d15500c00558041402024040380b010b41006140030b01130344122840c0c0c10001c0c91740400140c40064000080f4031103980c254050a4440c1014040410a500305061946c5900701143d06000c1d07a800c08000c1d04456200e40f2a00c1c40d0108020300280c01d102c0f00308140410002c8005085030140b0402c00c0d050030802201c08140d009502c1001c40c19541d080c0c1e0340000342980c0c3d860341900c001da070062007086802604110758035502010005d03500d4403039645500082c0040111909940c01025090403001403000200003401528401c0e0201c43d85112550140f002c144510700c951800580301c408c968840d4a461650590480e004400341e012210002d0300c0b0200c01c001c10022811903d03840c2d20501c1c10042c100c4001d50090780381e0b0300200102c01540c1c8003d01070003403001e13907142170240c0c0910241d01010651220303009540c01500c410f84990b00752508 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 218908642 1250 218907392 218907397
    0x30a0c06082a07030e06180103060b03010302060d0f0b04061202240d05040812090a02030607031a06030a0f15031406010303090303030b03071e0303030f0203220f0203010f02 76
    0x262000615554000381d5100d10b194607000104040503900381004540d04012080d64100c10403c4040041110b000c0c0c40070b9a071203004d4580c00a407407060030b8034124580005400c0703441c1e0354003005c01d00b801440104007580d034401c10350348203211284011400c0364880d070808000304841c00036030754450328000340810b00700c004040282d603061023035900000da242c2d8401d10400d4000300b40f101001400f030030021035800310b1894205a40040c4240c004608041080d4443c0001d010107c0341000360303601c81c042030010352800f00a11904280241020000040d4400310700302461074406550340604000804240c010041c1d9205044c48200d04604000714010113480e82088c5049101c2600c8000c1641a23800e80b2850200350b940c1203a41c140ca5000505103165415406480c01d980c20942c5030055072400160060145101c0da91000b4000c0c040e0026800c61a02038219500c480002c00580d2041c0100038890200380c128410844203038031000e109440518140300b0002c030000000750036509041c070540340c40b68517030003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 218909892 1250 218908642 218908649
    0xf0f010c0809031815070c151b030207090c02070504091212020a022802090f180106030b0105011803080c0604020f040902010c0318080105041a06010c030801050915030a0c 75
    0x115400c0e5900ca6001055403801482c03040080c1d4204031040c0591882c04000c0002c541480c0742000b82425161f80b1000b080d28407a511400c0e280740724006e20340e8402d0b40001c2c1102a1000c5543e130b188501030301e8034002d41d0f4800b24001c0c100e03529940e00000d6101c40c004c01c000300040c800100b007400040d580d858440355549800000002007000700c0e1071081700c840a8000d881900ca216802032a071900004c01c9926800d00d00310442030800d0001c00380b1009a103038410054445c0760031542c1c641403820301e03100b160318034100d00b802a40141d140410502c009089200380904480c400d203058050008840c00c00700300e42415074801030281800158020f1407480204c0c0091089008403411051003c8000c01e00050790b10081000740001d00711024000060f0240c018000e100c00f581d80340c4000d081d19a80081c1c21902c080c0d500f500d0b142410046000760340c4404284590144080ca0f24290601140e58060b00421060040e140b0551100c80001c0e1071410303411180200354401002c446c24150142071180240e4407500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 218911142 1250 218909892 218909897
    0x10513031806080f06010908010e0a0c0f1202061e070c0302130507021e120406020c15120a050613060e040218130305180621101212020f0f010c 63
    0x29001040050142003034400c807905520f0b00001640e0348191000303040401400b00d41030012640012075000401d200d500301c5100ca070070040c0308800c1c0d5030820340b00001c841e50046412401222003480302d144020000c1c031400d64190740391038a40400074041c040d80c4c07884100c2c5c41500d41021070b601d4144400004003404481c000c0d529658030300300718144501555811035240d009070340102080e02c0500d59000400b02c00900100541e01c0c04112040101300329030041d403143c1d0050784540003c07603551800c81e0030381d46210180c0e00781074034140d0701041c0001803000c0100f04601c042c0c0e40701c00080340d6854203a03482840c400458410001140c46800d030405221003603070164094440c0000680700c01c00c1900e8150b006d03005003442103001e04469a0111220343c810043c2c040031560f00203407080e01d074803644003425654440381c8010416400f032000c0e000d10124000d10786a45071403000e0080081d140048034003c842d41c2c001d004885881d080000c02c2c3d00d451001c10355141c070b511480d040c1d00e200c11019407020740018401e0b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 218912392 1250 218911142 218911157
    0x6010f0902030f040b040f080d0b0301060909020d1e06020a030e010f060614070201030f0c020a1e020a050105030a09021206071803080306040507090e131205071502180301051303 78
    0x218044022400103d0f14205507980322408103010402c51400160322610517210250070440c5540c43d038000d500520070700c802070f0351516042c02c400d1800380070302e20150181d02d038204413107001e940000300180c5841001038120241d540b01113506901c005071000400c0d0f04aa02995071314000c881c010020b10444c0644080340d480d280b41e5150111103070051004480c2d0503039400e25400b0854403070030619800b0007000c13418141d40300b049803423034801d030700440e2a801d0321600500100c00c103604106400d9880c1030a80d42120640864000043e942d03401c0f060b0a1324001e213040d540340c2e951212100300420048201960000600140100c80000050740b1440b0316055607415014060000d072214100f201030000030004901480065050b05040d0302c01a072049161410108165a40366901d04201040e82c00443d000840120743c0280700c08200055080070315450001c0c03520740c4a445244c0480d210358408031000381c0000321410030740b0194491015600c8014001c105078103000c001c2078228150058100c01041c2030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 218913642 1250 218912392 218912399
    0xb061608190e03100c0201150801050612030a050f03040303020913051b0a08040b1e0f060907080108030304020d051c09050a120302063903070e03070503030702040f021b06010f 77
    0x1002c44608081001d40144019442c0409182c05411000880000c6644e5503511000b83c40869031944c0080c41c5c594000103940c10b10500303012002c8942102c2d0200c56001304034070312165510008441d0750240c4070401d5502d9407541d150880107071061074a41c65000c541c440c0801c501ea4210fa2000d8014502a40e40e102c400070312503134010386801a040d400c1c004c82c07a01d10004020583c5000356940c445d521529042018000c5000c005d40e0321010344e000109010600100442401c20100c5590806291308003140d05614110f18265a44401440240541c106007811410060100010100752001000c1c0801540043c1d0f40140a070b642391003010700c038003da520f0003c0c0420a25038085503254050b4090207803aa10051107000303003801e5045160811000084514948201981e1801101d000c1d0021aa580c01d19403030003031540039400c0c2d602d4400d800c0364500300200c0d5000001c072400154195000708805400101d400d0003802002d1140110b2030b00f10403001c07030528010500d64181c0351b140d030400050585 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 218914892 1250 218913642 218913647
    0x1302030c09040b2530062303013b030d1505040509070e1b0a0e101e0c03090b03040f050f010209090a0207020609150307030b0f0a090b06160819 63
    0x34021301030004036401038104000c1c000785424008030805201c44a04e11424103541903000c85000350320a0b5000420502c000c2130030b0080620300e6000d064102c00a0040c1815064000318801500c02c843d025001c594040010054584d0306000401000f401903d4039569010a00c0c0c0141440c442c62031507001c500040881d003450076108060094080b180103280ca81e0034160724009144024040700254170740100d0074600c40070b400008090b203d02d07903603030142c00310200030034440901e5502203640188802201303181011402000d503240180028a4804030b0355041e41004d5498401a402081d45058004100b10074064414066502070303206a08407a440c0c44a444203a00300d024804032a43c4c40b060f500049002800250041e09842e400201050700e030039000c200090940c580c0076001103144801101b00518a900352052204c0103005480b140e5092070723404000751505185d030040c150559070700c1114154070b4a45400b41c4031a0107803614281034120b141d080c040d440d500101f45c40f003a00c2c032002e001e02c030074a403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 218916142 1250 218914892 218914951
    0x20c0108010e0a050c0f04120b01091a01050d0b090408040f0e01270b040504030c0506090c03031617030a0207061109010e0103050903090a0b03160e091302030c09040b 73
    0x154140c501400c07548030401c20350042e20300a000441d061038280151b44000d2400401800100628550621003c41501c2c00e200300d02070503804410a6031030809041d401c00100900c07030002c00c409107006552807849030001c0f80205a0914400d800c04540c40403c003c100d10400244240c62400c088000707141d030b0324000c01c400302c3c400f4064079082c030002410031007401d0b607210300c80903440c0692040803c0b030100354030101d41154001c0700c0a0300040c1d85030000c0c6042c8142132000c242c02600404c0030741407035140074002c259640314604269140d001040c0361001441204190400d0b014805c000d10743d03603400c00b80150400381d002454145c40300b528103900c84400d07084400c204c642c608010b8440c1082c0b1004100103500401c0b000344040a1808100300400c0da03030350b4842480000e45102c50300c4d00c0d140d00341020711401c4007058080700000d000c805660200743d651086001d41d03020942d1600b40d040385070140b0109082c50005640242c0041804040c80308001c02900c03080d200382000d1284d1404513410400062600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 218917392 1250 218916142 218916149
    0x302040e2109040f0c0503151e0121020a0f080108070e01090207110303040605040e0109060609030b13051009120206060108180a021003060302011d060a081312030c020c010801 77
    0xa084010072880408548406440c04038001032000456060034000042500c1d020650400090800410840e06038081c40c4c40070710034042600c00e0000c1c000b0080c50320070300040d03100403d8103014180e919040c603071244901d42000c1c610081025925040c0ea035001074032140707141d00303030802144a00d0004031f210100000c00c141198900541c041403031340307485d58681c001c0d40300500c160f4424a40a021b03c9003900c1c100002d02c02445030703913070b210341c2c41c1e16200040e01c0281044e08441030305030914400b04035403075000444800f641c1d0000032080843e240c400d82c009404001c018001c1c203038000c007000c206c80000c03241d00c0600d169004503030000101c129a90708a0b10b8034030031204a80480c422002182080c0b001a00600b4040ba0000880f04000c2182e000500e103049580f5841000070746401c420700855900c92a40761032038503444410317081840b41000040b03c81c010725610000300300380d00002a03600c107940c2c1c0c600b08400b60003003d042c0d4507501c240300040c05000c03502c0207040503100c0d98039070f034410354450040c2c18100d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 218918642 1250 218917392 218917423
    0xd060306181a06010816120e0601170f07090e0f010f06230922020607061a030a0c0504020a03020412050a0b07020f030301030b1312020c031e0d030518010f060302040e 73
    0x440d81d441c0700184112071040c400344100701f80030070000b14008492165a0f2804400301c000c00340c940c98243e110401e60741c03601001380103401c4220046c5ca10000014a2819640035100104401e011241554a001c0041c0020f50840d800c010700741a540310b0720750001c0183e903090392081c0071602040c1160f00c05442284411070b04902d6450014541c9691501c0805020b40d01c030218003008000ca40000d24907411a00050710800d64a01c0d098054260120000c0c81c149002c0c0c0c05860408099140c0140020740c81c482ca9016030f400054100e005c2e44290b0445014000d403030300ea1046241d2600384280d80d05050728084580104000214500e01e00005408031459218401140385a0071550303903805440015007000010700c803004080b00002d1800c20352408900d020b07402003c0707844515013050b207040b45812141c1001c4120700d00c2001481d0b0701240d5441d0036a000d040124a030f0320384901c00368881c0e030b001401408075480d0402d00750348206544c10481c02c490003200c06104070303a4250075441c0c5414028541c41c130f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 218919892 1250 218918642 218918657
    0x302011506230f070605150a12060507020106090903110d050405060403020d050a0f081207090e0c090121020a0e1504150e09100302011701030302070504020d060306181a0601 76
    0xd07540042d03414025581c2d60400010308110001110f035009030080035045454580f90420000c034900100006800c00001b290085012031815010a007160500740c006400e6030380303c800044c0424000d4100d44001c0c44515010044442c4c10304005004441e0041d140c0024010180641d9480b4820015182680c50040c10700345058903580c20032504a02c501c10440d0a4040d440a1001040361a40300003541c2d070180d00003540d10781254480350944a8010b04140c1401070301c02c000d009164204130340c607038402e000c42401503403801c1c1c080050310658090b0030743d0915171210001c0d10800001c00d0300603251440386921103031f0780d0010000401075503030b400c3c4503051b8000b9803e1004018110302503001010300c010b103040203810080c0c5007000c50040e4a00b2145d204101414080401c1103507800120035a12200b00c840b020025415558002d40310f1005100d594032940d000316190300d40264a80c045d4004550105041129504003000350b0000b5003a020309890780f6032a0a00354050400c01540e036441403030142d46244 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 218921142 1250 218919892 218919917
    0xf0b01080601030207050c090703021902030406020a08090f130222031a04020d173004060c0212070c06020610030b010e0423060108100b01020604080c0115060504030302011506 77
    0x5001790401c14080c1d41c20f11508101c54144d8886542c070a0185205a0b80940c0e0780c1c4000003906000081c81d5003032030855000f00b00400030280d002c9030241c144ca0340110200c1d5900c0e01d04000900f41046100c1466206240420004d080396580c1e0052002c0441610850300c5002c0045030800320382c4907071002500103c03040e95050703103000d0740c1d00290b54010700c01004018800c07819107403241c3c8800310402140c4421000540d844125855400f80016112203103e140d840000401d50000403610280009040c980c50b0000c4405c164000d011941c400300ca0000e000e6202c0c0c855042031f014030704e0703107116407000740c05a407000c204001c006e000802e081d00d400012012080c0d10f001d255600c10f85c4000c0058544010322040c41c1c50900410900b4079061186000804687d41081812402e040064400e07103203240c0383c4070304400c160740c0202d4420341c4560042e907003503103070710044207400d0151003c0d050450111419280101e0002e803c03801130015280298020041d5103002804900403903503500403440842c100d0790088 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 218922392 1250 218921142 218921147
    0xe010902012f0d1206050a061d060c030d0209090115020a081e0f030403080a0203100923100303020f01050c03160903050115051203090109120c0e01030f02040f0b01080601 75
    0x31001280300d250b4603800c481c14401c00702d00380300a1803000070000c1d4507001c4041c2c00d001c4034010140504012141c4502e082d00c0c004001e0600c84240006c0e03400d0108100c031140403687c50b001660100d000f66020b0301c1d5910707460140320000350701c1014040d2099100764008501058507469685840c1301c140c004100c905501d444d240c0464100041404c802c1b021941c00b51a440041c8001d09200040d8403c00364a03400e0516015011040040501d654030348140100400b42c1205201041101ea0000c40002e814414a03400d40e076109140a140d20848080810310081c600e01c0c00c04e640031a8066400c2c2d6094500c00700c203181c02d070f07441034445401d0000103001264514000c14041c000b001800d050019a03a940d0b6596a0b094079441d0180080041e1a00001c0280342020f543d14030380101140003451801b00d49000103003610380c043c051041d121010382001c4081000398403140c8081d04031145032a00350341e503a16002c072b10108024803c0b4050785c03c01388842d1924091703015480030a107058691052030741d10354004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218923642 1250 218922392 218922437
    0x60f01050c070f120302010c030e100b0402070c0e0420060711030c0a060e1302040b030106030c090b0f09130b0d0b07020109140d2c0405190e010c030e01090201 70
    0x12000a03000d040c00000e2a070500121410084c89a20312491641e603103030502a00b1144144101d0f0241400c103641c0742092007001c03650104c150341d068000244c858804000c10300a0040600061020f20700a0000c60080c600081141c0700314030851280400d45070750404403d2030718038110959004803003400040c0016a0b000750b02001204054101e41080c0303403040c0045c42c0c2c113840c1e0b8008004076542d4202c50295040030425062170303004181d0190300d4070749060190b002c940300503c03600082607034920b07501a600341f06051034401040f000b540319446880c0d40321110200e50103001058410540c0d651580302c0044036018104070a04003e012006590154a406450710f00003001003007195070b40c46280d80040c40881c4408804195600100000341d1507a002901c000d88dc0200d80c05200954800c0300a044600c60186607065070989011459131140442c1c0caa03040c0342000c60420035424008092450101540011520a03055074280110540c46040034200d44042801a00140c2541c21419003007100240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 218924892 1250 218923642 218923657
    0x80904021207030905010b012c0402070215030f0105090105030a0303051b12060306070203030912160611030703150501050d0504111f0201050c03010b04170a060510050301050a05060f0105 82
    0x40585000009001c00007241c2049450304007095440c031541c414003400b4426040c00403801c1c03c00d2124041e44080c03001144501c4000141c81810b0482c050005071116015203004503130240c400800c0d0440144541441d0700700b26164ac11404101c0000220751502d440303058100c442c05006400c00e242a510102c018200007450b0540c0c100c841d8400c0c2d40c4200c0084003c01400541001c9080c46040c0b00040600305800506042e085610500c180403d907000420103100e01410908425901c61610040d003030b100c04c210078080c20306031604401c2030307003130280200940c070a980d156000c00405130b13100b0b0080a10344007070082900040b02031007281c004207441d5011580190003039000c5011800800c0001392100392910f810310501032006c0300000141e409004441d08003407021b04081c29581040041c0e0498000c42c0b040b81d1045101301e002c500810014460402c0150300700c5018803140c074010010310311011172803007058000d6281c10001740c9c000c80300e0b129660050400409007844464042c00447ea15041901d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 218926142 1250 218924892 218924899
    0x3032b0b15031e0109091104110405010f1202120108010b030a031b0c03020301091a070c03021209060d150f17060106080c0c1b010305070309260f0403050c0f1503040809 74
    0x500000341c3c11410140c0a00908402c0f4011404551619008546114050b072050040d4107010f13030307200c8503041c1506903402d0303420038078185002403003400c01200d07065807010348006090f20000c1c0740700c1c401d068a411030381641e078003000a11083c200c0c0010705558a0a4150140000f0700000449400082180400741f0960142044888a9071640c0000b42102c40e0350100b168216800002ca181d00d41c40625200d600c1103041c2000001c01710192800b07525030380c628410010007100050404001d40d2024103450007070140500c01c1062104164010104103c03501418409004071000083c18201c000400d1600500c281c016040c5a40b030303c1c4c01a204600043d1800811080500c0700100724002000301d401c14900318104480d03074115044c0007500b207840c0904160101801d18840c5408503803002c0b181a80c1501e11070218070300a040201103126030089002e80c80265000007800402e000c00000d540142c2402250004040310304001085640c4142c4035485030120810300c00600892070010280c4003440d00039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 218927392 1250 218926142 218926171
    0x709030203070e0406050c030f1302040906050a0501060905030d1d010c08030a2304030203030f0405030c0d090510030e1b010201090f0813091a0f03070503032b0b1503 73
    0x25030000e4200700c0140c02901c054222001004103010072402003d401c08062081c00c1c5c99801c10028140c005d110003040c64802d407051810381d50440d101c41e03005040f40b81c3c100c84104880c0c1810111080078110030712030480015400c220100742d40c580895140030340180f42d102d060006490000001c0c60104081846040c00804801000441e02c40001544a07912000c00018014145102c52922041200d82400018030702c6041100080c1c00004176a00849400425840c0b0340d6103140007881e601c100e0078420024001d007050030180c0d40d000019403040c2c803c1101c1c1d5820260b011541142101c610019100e01340e804994800d05405956070414800340043c030010440c0300c1142c4581c5c4016515540499070050700107940000d8941081010000e00841d080900000b071950030040e6890400d4240540b2850103c1c40d070007911703942041960000d240207000c2e203403950b5602c100d01044c0c180349000c0043c3c0c4000a00503c0081c1c00500c01c58104080040c1030011181c0c2c1540b200300b039034000800700305840812 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 218928642 1250 218927392 218927399
    0x70608090a1202030a030c030b0d08070c030503040807030506061e0d4206030203030901050f04180b011806090e0403200115080109080f13150c020f03030c0a08030709 73
    0x2500340c40b6040240ca400540d0b1710844881d0042c11160080c41c0042003518141002c0001e07510920301c0c0c4281a00882d1480c2c903100141012501c4074481e5000800701d02c4000740000c0c1e00f9502141613400c807030040c0d00741c8000c0d40d2078030300744200072034410540c11210162891031003c901c2c240c110343c907940703000c0c041c0001c6040241040301101c07405d00c45003462850307540c449107030401110000b4490390041244280411865a4041383c1c0c4c0c3d00a00719158140540401c14051200100c015039004003540c000402015508211802c0188005d41126000813100c0064081c006940302c1c17031008460180d40d42800040c41c02032410341c0303518007400850820000d62041c2903844824070405540d42c20325400010100800b60701c0e191a01200e9000142590401e006580441d0039403007550400c80c055080c0d40c0d60342c106540c842d4804403083d044807948a812540100c170559000001c405661304c06d603550311900c94803004245e0f80c0e0051041c5414154071a89940c00001c600802442d04011141880c203411601d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 218929892 1250 218928642 218928653
    0x6120809061e0301030f230601050402030c160f03030e0d0203030705030a0e0f100c031a0618090c12010504090b1329040b0c0903070905090a08190906080603070608090a 74
    0x1707a001742c0e144040c02070b084d805e021000039848561070101d00105081e0880d4500d0986a5030148626071141c1e40c04000101064000c030b0480e825104c041020550042281c60306444000e042a001d0700081e282c800300c1c40210400080441c0f4034000344e00190702b16078079644219810f900c000d00741c051310b944903940295001b00030400e84c1c05802c2c840e00503100111030813a0700c1d011582600c61050070581045100140340d051012100099481510a0b543d0ba9060a0300e5510000284644035005281c010401c482c0c13003e40c0c4d020b01800b0030b4218581d417450741d9070410401500c60314000500114444c2000c0b5112080d04088079a1061241c0408140111142e890580c10a00000f801c40170050a004000400c9002d81c841c50307004c5416842541002d081d43d02003541da806d180222032480d581c0d140030404080c0104100a07102c2d074000010350f03484024a00202c0f0180380700303803801c000c42e800c0c50f000f04da040e014500c00d07442201d0150041c0025403500c50b08555280020745803910b01e00452000401040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 218931142 1250 218929892 218929897
    0x51302060a0c110301020a140702030a170c0d08070509040203061f0f02010501052709010204090204030c0e0a09020f0f01140f0403020a140102030a030506120106060905010306120809061e 82
    0x795915140e00c0e14025040116000210b242c01c14407a92041103045050340d04038404680c40340b070280c100d42d140c0c000d42c8086442c0919030003001d42070307040b250303103070300003030081200030050841803000f90f0721a01d03c445c034160350b0300c203050f1100c10200b00c0610030410300b070401d0b9000d1365012400400c0d003010515451800c00d00888821740750000249404500743c000b40e02400303070318010501611500e4200c10220750300d00403840000d541240d00103908010502400d025015140504009141150303682d41e00e203803260100c42d0350304c10004c1c032484035070000700762000c40c0c0308114010340c000e4484800e1044c01c6c0e04008844004c501b420b81070068049001410300c955401500310304685110740c564860031401040010300075548004140b402840d843d0000e642c0c0407096030001c0685050101d032a40f07800c40098814000501201c82c02c2d03280210008069074480c1c107210840d542a01c0411035984c5030752404402404d03c800103049200c040013010742c5410004010400948109210000d501c0b200401d0019035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 218932392 1250 218931142 218931157
    0x1060f0f0c02090f060411040311060a0207090c05070605011401140c1f0f050c181e0d0605040b010506071a090313030b06040c11060403140c01290d0206040905130206 73
    0x643c0d001c010017101e800d10348100c1078a2044c5c82410350a107481d541d540e40c1006200c0308541e00900f00440c1d007005a5000708013040150000d81c01c24030003600075200c003c103a900b00341030a4406509180000a0207600c402d907054407034030180c0d12243c884034116104502c40c0d00c0f80c15618503a1043d240c071a038524102d6200d000c0082c0744c1c8900484e0004000510300c0581c0d80c041c1898420800422451003500da1040e9210560036051329018041e07e011110310051804040d10b164029501c1440202008242c0d400144190f01c10805410242d807910240042809401c500400d00c940201c1040c0810142055255201e2180b1084900d0442d4408442000c104654000ca80001d05402400718501d850700403005804440d18080c0da0754800c00404a030b40d44400b52015040c4000b03440d0309600e81005408803807038100307807500900202c042410540d9020214008100002c0c280100c040e083e442d000d2030704604941c002785003905243c2454030000c01848007401381c4070020000c004807001a02e4200141c01c0f10b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 218933642 1250 218932392 218932411
    0x315061c170a0305060a0801060f030308100905010806040213060819060608070303050a0905090c030a0e070305030c030a080906010b120a090c0f1d06060d09030e041404150501060f0f0c0209 83
    0xa44c10b05c6001c5c000c4958031364020700e01c40e904203501405640007034003903041240c0e05458580300e107445010480c01c2600080c1c000040c0c0908020000c181004000344881c0503600c240c3c0d2041e00040c1c251b000c42c0840b085405500741070340044100c3d08084d80c400161003101801204005a1240e6a4030b10703910700003595100300c010500c0410000b0b02c158101d18140001d160645030b114080c03800c256450039500c8000c06000001d43d5851901d40b46840c20000f041c0078507030007021a079803100038840707045e0780340c10145c03008000510040c00255440f00100c2d49604aa01b5108403d080030b403040a41554800010719502c081680d4030706000201c0d401d001070070b000308002051400c68908001440c08070881d4040180745529606c4103122550302d030082210f8402d501564000340c003110914048603240020b00009a010b030800e80132504c84281c40110f607000300c3c403a0151500f000030b01c44984058a030300740f28034408a40c619040700840c500031841c46500702c00e40d15000300f204004d5400121000f0040e103141c040b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 218934892 1250 218933642 218933651
    0x83c0c0f041404050c090a050c09150d0c050301090f110702060c16030308010e09060907060e063610050301030b060a180507110a050c0409020105090604060305060315061c170a03 78
    0xa19061400c1b00a0b0055914402801945402c074413560303040c420740c900180107105019240a006d2000400d582003610620014818a07441060003066074100f8040c1291862400444142103005481140040210100d2590400581d03030200042038011020300e54840c0100315600c500300e00700440310000f0707500c65102c0405550504850010400c0000c003d40d02039480707407044c0189420002100000c4488c24900040480c0d8403501050b200d01990301d05410f44203011500c0c01c800301d004140403100c51842480850045070b44810807403d01450900e034404100c4c20401400403d0741d032100e691b4444000381c031881c02e040d030b0b0f400640580f02102c0a100c1607190340704e09015416602004140001782080014100301e0f03210348503540c540f001d0044452280399605c9003402164000c0041c7d680c0c0c542c0040c101d41d210f5950f554003401608089580038802e0090148282c258500c0385d09503401030320058429101064070b0110900001900c04041d02e103101c140e00d6840b08064100000c15120f203842c2d60115 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 218936142 1250 218934892 218934913
    0x1308071a15010306060206040209070905040e0708100203010b03041704052101061415250f03020d030207110609040b030d09030506060306160c0804083c0c0f04140405 73
    0xd0300801088030780e04050500301c1c20440541c2c00a100380c0c200f0f4041f50840310540380d00509031000101ca500858000b800c02c01d240303211040205100d0112a0098140c508400300c13011807504a2000740a9800b107004144086404581007424408005041d444101d2400391600006071009121402042d02d50b40040581c030070909081c000c010050180148a400008401c000903149241a6807100080034020172441c4d1440348100781e05003141003d0403004074250081c10b042070000750b545025005031041555203030000d4030920032100600d4000c0702425440c0c0b041030400c10141d100800b119406511502030030790541d814024000b45007003030f4030740b010f41c0b42c69881d1a0f4180032005015501c00c0c0c01c400100b080c6400e15486003a070b5000c003498640b90007a01071425403014091500284418070842c90904810300e502584141d031170980ca1001e0016442211600703100c503004080c0c90960790050002450070f404c020b003840d05c100308000d0001c0f4500c0303403039200c0b0380c41e004044030242c805070721000120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 218937392 1250 218936142 218936161
    0x311030d050a0e011505010503222102120403120e181f0803030c092403040501060f12050706031107020405040b06120a1106031308030906070e01171308071a 69
    0x28845589400010700309034071b03040001c3c0103408010f0611403070b00300c584a0444021414024030110760382c404d8019070b031442c4084041c404480c0326039021015110b2100491240200303181594100e82e409800c0c00390341e0440d07031411038018011007840c0d0b4202c14090284c000844107050707481e10820f0030070791b01d00e40c0500814a402102460b82c0c4400c0d925002041881244070b985411501c80600903a44002c10502d20404200c6c14441c2d960042018000070060000300300c0c064000e04112000c2a001031603641c2c4800304c80e180340340c00100040c00380e0b00c041c508004850281d001031b11898a0072070303001e0514440b80c001c1410b44000700c40803a0244180000c1185520380200807001e402010402400d00300078aa4904024100000b202d904c2000c0c0480041c903035805070300c1d000100541c00401c1c5070f12406d10840d1180e40341c0b4191707000030102d07102c10704a141310351207a0722100800034158408901926448030440141d000410259098032041080b40c01280790703668101c80098070079201c4655490010080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 218938642 1250 218937392 218937401
    0x319080105010c0b0a020a02030f0d0203010603050c0a0f120e0706030501030203070f08150402031e01050910020c0d05070606120305070c050d030507020907170c04240c0311030d050a0e01 82
    0x40360500101c0583c200210390103c1c01079610225600300140c3e82e258420050340b40d8081c03d032010001e690700081d444080102600950704940c01500c0901440e155900c4c0800140075000c254000251009641009548241000741d00402810800070f00d02c0907840c0075a040c540260010008252603800400c21414100b251100030080401c5c03007285e45007031160355600d0300618840c42d828007071040c011400307641e801d0004105003500342c1d0010b98408004803d55005e00012600c18030580542d400e182540280c900031070310500c200034050304800c1d64240050795190014017080d20540da5070480410039111f11172011680c40d003e5114280c80f480c031498819584891600800d01611444100200003500501600d502036412075140146540d5078804541e055107145000c0101c01a05c824424a142040300074000e4811900e091200f0200365601042c1d98841400380b440042d40c000c1b03403000403030300c241410102142e00740141c078039105800e88068141c030815604403400e540e5942803501424030074800d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 218939892 1250 218938642 218938649
    0x7030e03060702070308210109091e02030d1103040504050f0619140f12060103060e010e0c030a08090102070b2205040509060c0318010513050118120c1403190801 71
    0x20701062030070b80c2c802501c0c0c0200e848024801840440c48a1071055509040c2481c44452107001c0c100b0340c0e40f40b0841c000341c0301d0b104046d25040804407043c103841d1260500d07130003d84c0d00a8010144030820241c1111021128903600c429400180008202a611801003501a00300c05106d03104130f040500c100883d401d0084540501203446401c100030742c9250783c03000126280101c40105802c5030310300100d020240010341d40c03900ca014007000401003243d154804250540417600801100d0851b49400c0e80c0e0300450281d05906903c25090100002c152500500b03d041043c4140c54903180e40301c401c480c541d000010b2012001d80018076140d031a440644021004140441e4203010038101785114944610b405459200320b40400000a9a00340050301001600031305000200103500e002d05e060341040510117800c039007030350900b88c03d0540c402042040c507401c00d800c030391181e00c80c1c0400003080e960900c10700c100f100c3e0000058480324125400b4000790104a280d2401e82d503201076400e07030013002c0710016003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 218941142 1250 218939892 218939899
    0x51609050910030b0c04031208090706110a02040902030109020901082104031a0403020c060a0503060901152a120c030f03050c0409021b0d0504030c060e0108060906180a0207030e 78
    0x1000b4010503440c4040c003c6a0f00280800c1543c0c64100240a00f48695000500514030216400004590054010b40319849500540c2c2c180c0f615003200f1108101d08100c000002da01c0200342102500d040d81c0b2030607000d0300c02000060303a00308990100c6d103030607002da001002e141c01400c061118400984025040aa02000c400749003d0441d41ca0002c500515120390801b07015032030000d01014020011100c4400c00188040d0706e5017039595000f07180b070303204a60703090043c00d00c0c200000b120048028007051201c4a6240d00c01000785121442d800c04c1c4190769a0590350514201d4040851100396441e0402c1113513070741d6049580b00c242030103002030314201080c00800d442d1071b0401003048041410364056524244002d695440c804a480300c4c49129268030921600901906007030182d004001001200d209200c8145925504c2e00203685950080f0503103808150f00400040c0390b490201c41503a4002001441c4940c12240f120003035002c03640c1181c02c000d10a900042010a15420074052050305174101d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 218942392 1250 218941142 218941159
    0x60f182112031311011107090e16030b04030516060203040b090c0d0c0614040f0e1806130602031f0e0601020f010605060909091f020702011b17090d050105160905 71
    0x155420410f0081c0100080d1018682c980e2020b0390368414121841081c0080d0200d480c240c0d290b4041ca80289a01900010700c1e1203280d04851224440040d09070881b0740080009846507200d8409031a43c0e40080e28140781c00e2000e03001d079400240184040e43c000d50044100090701d03e405081c0c1860301d04d11f1008684250301440c0301d83c00090640c0480420750700c26107010034808016013407140d801c0c040c0360803e16202c80d003048007140701c882e06002c10384540d540386050507504004418454130380d60b0a0343c928107500100044400825403c0e0000c542254158a0184649411100c07005100040d60460107440151205002c2c3c19a410441d26200403481c0000304039152610000550744e100c2e40303400601039100c2c400082d00c408030a02802c000b140702c00c1181148424048030b2007000b035111420880c0429407006080000b009030207006000158806250120420590200781068001203103c55001280104880c0001d5080c059940902c1403120082c0451045280c041c24400407500664040c2482 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 218943642 1250 218942392 218942401
    0x3190c050c040b010c0507090504020f0d05030f070305070b0a0c030518030909060f0d03020d090e090606040f110a05090f04020c0a030804050a0b041208010e06060f18211203 76
    0x455000716020007100d00141c0468801c0045e02c82102184c00500240151000000c055001d83c201522881c400c4031122500001101044507401003140e002d0082d1780148802c0040480400003072980d00d009080c4242000500e59400380302e404110307960b61b511501d806804000607010300486400210846d1035007207503d410f201950785c0313018049415102d5500c21001c42d00d980c07201b0360107080502c4060b01d01140b07041c0c2811b01942d6030035071090610010f11012400aa580213801219003d08034074405081a603c0d03900802018046404001d15911b94400c00c0a200d825604010014a10715890303a6845130300590800200d110003c041d03500803401007105c2040a5004506a44400d40c58104604a9221410180e207001c4c91640003c100a0103002030200f400286c500038034140605030386001490fa05c859000031240c038191642504500240400c52a6403c510042c1074880c81310b00a90005260420000701d60030f40144400802c00c2c001c00751340c207a0a01c2482800050054502d036240345040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 218944892 1250 218943642 218943653
    0x6060c031c020f190e0103060509400218010602030702150915190216171204060315060207030803061c1403031602071a0307090b07030203190c 63
    0x40c1d0380d001d01ca840c038a80e044007070410140c0c196030541a14050b0543c0300d0341042d6030510b010140044c03410110380f405900100d1584240141d60690707074003074150003450711070216040d940d00321001036507075001403a21078500c10340c0450303695122450620100d500050785401070000a45541e00c9007003010303c00c00e0041c4205900002140c00349541611211351411b01e20808070040c0c02205881540700139038082e8440c4170a01c44020380300c581d04070f202c9080c02600c1340078240d0756410b0044081e00c20844081041250305c0d81d02030402105a83d88099a4244440e03803e0780c55035030b00940041c00426031382c60001302e1000070303004894040e154600040c032186095803102c00150000804203441400c02008215401c0640c3d10030030145075020304a00101d0519030011a00ca410840b01e0390380b0000b4036240045414400200072048400d00b80400d4074000c806c00301045540d2006005900303220320b22100041d00280280201754135070282c0c0c040c40e00c401ea51000c040480403480100010400041d992002007a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 218946142 1250 218944892 218944897
    0x160510051b0316140408060106091a03100506090402040512030a030e210f071b081c0503130203120c030d06091a040b03071701020904050c1903090507150302090906060c03 75
    0xf000380c113003c0c03008030b0881d410ba400d520481c1c000f42454001c0a00004d9a0703a045a45032058541d00101e042c6101d04400c00b240e034170300040b10072034203208050714100194203050008105840c804bc202525042c0c5820108854404044202c2c60981c80041c60023011503240c0b0a9298401161010780305154901d50007040006d00031052508940000a116000c81a0942110403450b4080e1741d01e214001c46440c00300041c40c10f0310855034503004150201a00c8888803007100c1d40f403840740c1c07546d0341192142d903068140d07924854402c9815100e100d81e0102045408006000050b00203401103554488003d18076081d18102d51129076203904040d01180c02e80d241019882900006480c0000c441c5950750005e80741c550786030f020349071003103d030b41148100c1c1c50190010188190142c0b0103010588940003a080144141054001c800d00a5a004c07115240700e90481c24809000d54104c03102c0701e44840e40300e50001513000703a41001c20350000d40e181c40b83c2403000c00c0766400802262300c2070030b000c0c5070b841164692 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 218947392 1250 218946142 218946181
    0x303070807081e0705070c05010905060f09060c1c030b091012150f0207061503081902010906110a02060615031b0408070306240812160510051b03 64
    0x12445800103a040443c02d000050b0000c420002c9078894140410003030a6a400300700d099502c400384d00c0780840c89501908403e0b01b00c0e41b01a00c070b40e02d894101c81101030242c100c1b041c060360041d0100180000401c0030011010086102041d45c40c802c1d0b00880040e081301d10b8040c566004a8140741006052158030400500f21002002c000212598628010b40b0f42551588002c020920741510300c404218654041c11110b44500810041d00c00a212010001e00e12440028018042000344c002007010203150b81c902c00ca154000441d1402c05580c4810903034a60302e0000f610700d84007240c2e0f480b480c0c1d41000b10f0354125005846007048a5550740310058144402442145a4240d40581d054082c841504403001800c00300191481c1d982c0760310341130700030300040380c0480e04007603000c041780100030803206004c0116a400700003413818a40c0000610025000190b203242c0f179540351144140400ca0500280501c1080042e0000301e81c503000f8004e00510f8a941c001c62007000c01030040003556a884007031514078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 218948642 1250 218947392 218947397
    0x90c06040314010f1109040f0b03030703031107080301030b040b06010e1509210a05010507090b0706050a020405130b03060a15050d170403150501050f0303120703020405040c080402040e0303070807 86
    0x2e85204aa07800740140c4200d902d00780e443c0050310400075034240064a50404200d40a03c10071403500d1655096411000169034150010070030640043d010f80e00503a01c0e83c1d0750042e00e60408005494001c11074209900c00d541500c548402c00c001c0080e18410300368084000d080c81e140e01810440440c0c60428040203202d50404005034414541c2c3e5100403d8105050925148500c03055121146490b1b00f20544200e0300396080c48045184540500811400c0c0c80700309071001e05001c25500c03042d0141c08060416100c481e401c0201050340e480300303d14a190301000c038901003070302c01c19401807501c1d00d0801080700b0392091800b92508800c500e490803600444004855030b428140c901d08201124a200310000004c0400016000040021604038031074075001900e01040700d0b07a6100240408050090384443d80f5401c2008586120780c0031140031b5401001900d001401c00e61260082822100c81480400220301d400040004528190040f00c035040c9004000d90705605040c1c1000e008000d02600320f0f400e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 218949892 1250 218948642 218948663
    0x180b01090b1920070303020a0501050a050403080f0c040f09020c15010513020f0d0e0a11010203070314030a0b0a12021311041a0f040905010303111c03180b0405030909090c060403 78
    0x3c0c041c1d0005140c400507440003040d90309aa9072440c000c0c0da07800382520304903025400c11001400d0703109584605031086405480f000440e55404980c4a4000d0006040051b045003d05c408260f01504501c00c10140c0b03110440140e031400300e44c000d02e00d40682c420308039480242020050060340c80701d01040851001e030f00009070b195442c0088802850089160100145c0e14145541d0111080080c1e0800d00c1c5001d010b00241c40b0580c08012078a9110b94074000c1e010941d0309203824800310256004651054203290001803802607000020f00100090384652030610b60307e00c02c2400d515248149119440c181c0300c0400c0006181140c1d05e42c14007980c81440e1082404005051072044144200ea80403030034411026a80d586546140c8000c0900703000a50004100100d03001c01c8081c00a64100e45107a100780015427a00c00c0d003001c402814040c800c0e95410388607000c581001840443d050b80c00750f4414005151502001000d00801280080941405912030036030442035445000440c1d0650340c01500d50701 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 218951142 1250 218949892 218949917
    0x70318061e05070f0303020403020a06080c1b0a050d09080c09061003050c040f0803070b07170103060c050d060b032d0609070c0503070b0106020c030304210507180b01090b19 76
    0x41d543d029841d4003403c0344698034800810582d1580c0188140c0340b007252510f00041c0c65400403510200222040e21541a0401406c0b0780c0d1400d0903803523820140f846003110481c10f26541e5503420045131034901c4006c5141c0d4401400022028070543c40b1001d1f00750342403611480c20100040322500c80310200d90078981e644020445181c006412180601000004070211590301c904456990340092400e40b00c9009801c04121618868013420700d00d40c04102100020f6420364440c0f0008040303501c3c002060040411401950f04014020300008004071400192680746c40c64110038010016144c0c0e40e4600400003c00030b00f840c1c13070010203420071029074200c020341ea51554240c0d6405101d84000c0c6c01484041500401c0064403c4420705840284d82520745000c41e81c0d040c0b42d9240514045d0055016005904080c81000c4110000107140218100c0d41c1507a583c030030f450700e240700044962100a4480c03440507030a58000003250000c0011104c143d1a080d10028035101c17224612100d4010000464000c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 218952392 1250 218951142 218951147
    0x30c0308011d130515090703030201140c092e11071421070b0c06161d010c060b12060f0f070504090b040b04020a02010f0e01020a0c14011b05070318061e 67
    0x968481072005c1400d0a1402d008901d203030b0710400751004400540c01c0402502c4440242e078852401186114189030078600000c04200045040417010040410b10a0b50400b109a0310304841c02c8003d91038031611600e0200d12921800c21240360802c880e0080c540802e90713060b868500e40d5104200c07070140001d442c005102358942c00c22540d40c0c0b0655800002041c408007032100450369034040c241c0c018040004c144000c1c41035841031601c0407144001ea08a480300c02007540541c0c80c5010a41c842ca50000300041040001420f91041450b200d140d42d101700200049032490320702a0f40c2022011040d800c07c0d20340140024030b07038480e6004500d4407603114080003c198485410003030000100074404c0d034581100c9440280241030031406941d415061007210300c0001410700c210b030644800382c1d944028000898031280740502042401400307941d40c1e800314400d1008148011250440607541d80ea40d1040c09040c02030040001c1041340c901445544820001544c000c61615441429901da85503c040b260209 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 218953642 1250 218952392 218952403
    0x6060603070e03030a030c021b0102030a030e0c090f01030201020709020f1801051207030b010306060302091008071214160e01020a11030a08030c0903070e04030507030305060418030c0308011d1305 86
    0x700b039050321000c00c1ea0b071070144c3c040d00304030440c141c40d60840703042051140d800752100302604e1105025800c01c20240b0822f0f0701c070b500302031008002c400449452182c04c0d00450058107049030111102aa4800107204540c1c0c1400190000c240070a002e40c100000794505c1d524500c2a1101c0e514040c51105200380c160340030b08280c0b000c1e00f41409588915181001018018141c83d00380580001e16110012407854000e20070384140e0407010304042108130341840140d460002c080c02d55400d020000f003003440818040e01802da109000c8107203900341c504016407603101c01c078038002100d0309120350f0124031003050340d00040d0408416080585c040400c2031440c0401d0030480c0d040405001e4100010070488035200d40002005060019004c0728602035030b984001d84269403da600500043d03041060328003192180e0801c1e80c101c480140000340080b6100c900160220018104901050380c03004034105054100c4449030040c02500c4a105c00040b401554405081c001030a2002103404a2460001d03c00104003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 218954892 1250 218953642 218953667
    0x1206100b03040f080a0f0806060a09180207050d02030406030c05120a1116051c0305041a0705090402070b0415020903070b070c0e070c140316020d02030c03011e1109030606060307 78
    0x16005e40d100c03514030000781600d02045100000c02c48800110f00300342040400c036001d01295a4030000e0207030030501103034280d010f00c24100f42c01ca5020300164010030790620020507404004d030000c0d0350341e41c41c0c800041c1c1940c400080e0a0b040c000b05002541e1540100421690700c814012030001e0003c0c6a001101c800e4060702100210740c040800104c2c0402800107010110351900d201051044000c0398001c8055031000c0303c0c014520a009091240ca602500030302c1c2d0780000190402c68203100000000c64104d800401c1c0540d44000e2000910003486400c1040c2d861946891400f54030700301001c408243e80c0c560600c18460300030070009405041c0000c0003035040141141100c02d50326030905c400000c0032b40c02d07900002d40b446120081c581c8021280081125003411010003100041c407026000c1066020082000b40d030580680c602110b4665401c0c45005090103682c0c082c4030452984603108801c8450361109603690304010004d1580310307500040d0b075641c0094111a030540e01d540d42c2c00d0858850b8072051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 218956142 1250 218954892 218954903
    0xa0306020a0311160b0f070c0f081c021810091404020904021209060901020403020a031101022d0c0307080c0603040804090e2a13050a18050c1206100b03040f 69
    0x90000700c0000c1400038441d9141c0250342140342500c80050503410b0b1181a91047c010410560324800091812800e401c021070140050f641003451807008e00001801d482c4c1420001940010038072036807407013008010b1200109880200c9000345c0550054062803250296406c001a8801a41c04d507030b9480e0105c40c0009405041503403160300d910b6846158078001c0d104a0840d019440001d820010144280c40403283c00601c0b00d400c9500d1a15400241040c0b13070300041c11801240000013040011140e1500140c0010000d105031a200044490403c041d1030360203403080e000074070b0801400b41c002400343d191000c21a1710b85c0c1d99482e5854000c045220b00e41c8070411260601d141c00c3c0b034001e070114140c072501e01212008000c0815080d060428403034080c1846610116a00c103203d040b449540c0301c90351260300a04009a081d01d2848080244050f0100440741603001340500d0b0300a08000003983c10040d074444c001c00c00c0d41014858000d02c03407034034051810302070000300010302400032008a0300d00040c1c000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 218957392 1250 218956142 218956147
    0x120c03030e240a020d0507081213020d201005040e0720010603150203131704091d0d210c12020d020306090105010509010f030e0f0304120b0a09020a0306020a0311 71
    0x2010030720030390032100f00940980240748104c03514078042c0d0116800d06501056541c5400c2a61401c000d90400203041d004000c000301008800688a41c404d03201c501d400342e1480c2c00210310450b6401030001410481d14021041c120401c4442c50b00001030320162840d000d5195446d544001c02103440000081500003242d040c0c50380040c03d44010f501c401c09882c058030000c810b800004150800341d20064842500e41e0800c06400d03000700d04001c034001c2d800000749071854601691440c2d44001d4504040c5d0900041a03a880035003800b40d03041098841e06041c0d41881202103010b5404c0d100c403601140d400e118103d480f002d6807234019103e4440c01110681c04482107441d100700410443c025001111111b009818071340000c10b941d8020010344114603416507034a186107101680480150007600d4103d48603100303003500035007200b0051020f04041c1601f5002d0040d840752900304040d0002d80642400303640344c40d004100b00503840e04d0041c07070141c0b41c00241c00740c3d40390b020400450007071144038070120107078501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 218958642 1250 218957392 218957449
    0x3041a07080406180803040b0f0715020f0a020c0910050d0606081f0c03050405032d030411011205040308040602070503090301110a09060e0d0237060306120c03030e 72
    0x18006001c03446a4184c0200c096480360702081d0381c0e00c40c5002c2c1612015051110607601603400c4020080300303200780001243c0c04007042e080d0050b0380250200d200d0091000c11184000740d03040180b0344140d40200c41740d221904010401101c0d1040c1030240c00e002d4044000c00b0b0741800110b0b0007a40c003e000314801c84001d00703482020b0809203540b9036181d00409051041180c545840780c0a840e008030b070860041e5103803141111540442000e1503800f200b590b2800201c03d07480d003610034043c5108a0217650007516400304403000400c8144080b5541560030714040c24040400e9001e4a441d0340958084001a80d07142e0500300700b8598003031a0300250341582046545190032012201400d87c501c0c0c66151845c242d0b0b1a41d48c1910745402c02a01c00b42c00c0903480f0316200142c5042c0c11031140c4001c03003034060300200d9241c440450311003202c444c6007e04000c0d40320b0100b180369418441e5400070603840710404c907840e0441c2d443ca2030145407440068100724a95104000540e6000071400c0e0f00c641400004503203e90 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 218959892 1250 218958642 218958647
    0x2d090e0d090e1b13080a0c0902070c140109030503041806080601060f0302090105090d0317070e06031b1306050301140109050d0210030e100515220903090e0a050a0506040e03041a07080406 82
    0x6c48904c101c41203003a84000240500050090f108841e0740308014200982c140101400103060394182c02e410030070f003118000003003081840100054040418021041c2e00d9500440c4140d8200f40e100f04460383c014001009401c0d8083c042c4440310030309240260380c40401c8001290140160768032154403d05811410041581008440350a0381080d40301d07540d55a40d0781d9095995080405174079810100800c00261040c842c240c62810910020701d072030b4240402c210303198001384140d41000020038400801401301c500c0d51000c00b600560b09291204503507081c00e0214150f02c2c801351000f40100140203030b866100d8020b41008a420882030300311800903401c034091002415007515010200d039048030344040c107800e00c0c3c281d07144119076010f80c00010742d60705d6070904005c0c960300e5402d504100c00380101040c101128003820b4001c480303902c0041032a0030701c1140b11048400103480f9038880c1d071400c0082c80e08150b0100033f803412640040703040783c164054020640382c58400e00c20000d160a07400180810101e8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 218961142 1250 218959892 218959903
    0xf030b0612090604030201050916060e060403060e0706090503070f05041e020307270b1215091003020f030604020108130c1d040c060801030206042d090e0d090e1b1308 73
    0x14000c6e0f00074800e54803048a020780b142a10350403525608030740d203418404103025030441075540e03101400711807400703a480d250101110101031090b503498000324420004594018020005800210094101686000003164800000b4030403580210388502c90204000311000e1402d2820410350425952403510729002007040244c0b54810020300f409106060080700704001d610f0694860f100050700c0c00008980c00f69a211005104146c9076040d02680c0b11191242d00286004030b0540002c40f01c060b0440c41001606011012000e02aa00c130340104030250b07134464011904200503012440419805042140490780c01c0d4014a0041d0406071715070081c5044080c045100d5401074040d0b041080d12200304a410324400c0c4000f075400103080c44240100c0049420851522400c044020300d004002d80051300c1502d410341c030485400b41d540c035800b14403540070320192007080b0b0503203040307070740c20f41044a02c1440d11809012240c60381c042c0041f071074240c040075081342c0252814040d40035000e641c0e8030040d0b5640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 218962392 1250 218961142 218961151
    0x9051002040521150405340b030f0c1b240603060405060c0a170702011a010201200d181104060617040b070e1302040512030a0f030b06120906 62
    0xe07007008070300010715090f1400d014400802c6601a18002d42400446140c540003c2d0099481d80503501d0300080d65040340c41009020102e128104010303c10b0240c14035111103040d8040d541010b801c0040048807400b0000c82903024041ca18201d88038040711b11982074240c000941052a44601400c5080000d030b10441d101900d00e05603050000c0d0780c0c1d000249500c032001032324010442d03800580842d8588030048040d0502c4811071426004520409400301c8010708145c9100000d40d6580910302c152080c00710801c0c100c0b100a0000307101c0e040804015081420000c209115050340c08501c00f20010300541282d00c000c100d41140c143c3c551607504251f1010a00080700a02c200d140000c001007281c001e89003100340c092882110005a5120745511038400c1000b0b01a008104d85a00d600f8071540e900c807902d07049110031204c0182c43e01c0c245014050040d1140c0d40300c000d540d00921403682c1d820b0384010507003216042c91030041004004040410000d0241c0701d4220071004001c020003415000001e40c07540705 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 218963642 1250 218962392 218962399
    0x2190c0b040905101410030203060301020708030f040203010b1f080c0c0f0304090b010801030f060902010e090702070501020c0a15050c0c0414042a09110d0213081507021f090510020405 81
    0x220303511100e649040c1c100d1001680c001d0003030f1b03510081190285d8051070b804680a4000342c0f405182d0b950b0414950700450301440440801014003095045c24400e007903c908095554145d401100307103a800710310701503042c00800c0201c1c110000345405042825038000307014490458824050f42241705460390041c2c0075007100c00303240c0100450190310900f01c21781240d03040b4580a8610803243c0320000030b0500c0ca4416410702081034030358800c0e42c88036404244111040c0d40a802c0c51402c010009041441020400f071040250f90f00c188802d0f0740340d02c40f820b082c244506015541e101c141141a00385410f40c03809961083c038004003591111070288006204a2182c40342d00350600d101d04c08464001c52414041e445c00c40010000c0c800284d003907202002d413050742e840320350800255410140681e400f2117806074141c08000001c204c0e415003085902c0120703c0c580c0750303020185000c0b8002980c6800c0320802d0760389214210248002c0c0e9409500c0080115044810b1310587c3c0c0da0401001c010350f00c0340c800c5030700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 218964892 1250 218963642 218963671
    0x1a070302101131050409080702090a150503060121140f0a110409050d14070209130507052b020d14010501080c010e0306060907090b0a0c03031b02190c0b040905 70
    0x8040c2c00000340c4465001581d0a16a01c0c3c80c2407070140001401c0800c0102d45e1518200000300c0980d4410b01640d204041c1540080340e180c0003110750070f84158195000902035800f141c018440705071140380032600881030480301c020303038031507070400c1a82e441d071400700100d990041c100c10a10849005c504a0989809043d00e8030304175090a0a21003110400e240143c045e81140d60840e105602c07801074840d101c2c443d14041030600b4801e80000b007280b9010780e1071044d000744618401007085400c0c042d0710000d01c004ca8051845402204100340121029900c6030101c12980142c4e20440d070b2420041c4101c81d0b00106024100190195050b0080c80c00f0b0284076050b00c40c4001444042d84903071b416204100010b4090000e540703c84c41032201c1140003900000a0005480005c40d4407d04c00e00a4000703c0101d56880390903000340c1c10054115030b000850300ca94084900804405250001140210160486240503062696080c00d400c19000c50300485c500d00d4001038005000e9000da00724034019042c0618041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 218966142 1250 218964892 218964937
    0x6050702100801030b18030c01061202040506151606020f07030806010201060b0903030708130305120d060905060a030b061203031602100c090501050a1b0803070e03071a0703021011 79
    0x100d000500f440010034a007810300000d524181c10704d004140382d54205080388d04100b01042c0309800c0d505150407010409021100080c02d40c6001e02580d90040402d45003000c004e442d01e4070700c0090380b29007030a401103542d010795141c040061581c100d5500c20980302225403100c0903481d00810000040d6043e600540c2450f4012401e0400c01c0101e0b848070100400a40c507100f600d40e078203040754008072a90352949401e101c00001080091010303074071f030303814000c8855a07038940100403600b166801e4016003e05481c0c0000c2200c03a0321029400026a604054491050740d18580003442d482c031403410000b42d42c040402800180d5115030841910b081e06c03070702a00c0c80440307505030000403140c501108200050780c1600c1000f06500402c014003504101e0b16195120112078140000120700003181218400b1001081010302c82d4481e1141002d104200c026004e02031800030f408200c9400347c9c207000703820340b800a45070003054000c100e2040742401d1801d051100281003205503d1542040c506c900d60842000300c1d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 218967392 1250 218966142 218966147
    0x60906030c011d0f0a0608010f08060415020f07020a0b0a02010b1509101e09050f0409050d140d0e1b0901031a1306150501030b03010608061801060e010605070210 71
    0x245010040e51240c41c0708080206020b40c0c1000c076580c0f640c0140c5400200f84180d00c0340e282c40c10140845445845055240902034a11040c0d16800000590400020301c000242244c4800c40e16215154000d80c0310306032421841d0041c4504071000390300466512000440001c000050208506284c000b003111028000c01d010020310581401400e200080103403000e00d2a0503c54010b40301110300e0040084c0c1c003000d0341840300d05141c600b60004140d041c1c40421580c40c0c60590b589a9610a0b101801005d0140e911030351303605820700100090205d90005688005030790002e4500c1586410410b00042060700e8840d5190b040700c9002104001c130485c1c0141c164108800301504032580322181407014010140d83e1407503032034081c02c268038103100301400308c01040342400307042002c2000100000f4030a1600001400321107000c060107011303904005081240b000e011881a6008568240c28840850301111050040206800940c9000c1c1c0c280e001007160b55000c0003800c8614801d450480340d08186407400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 218968642 1250 218967392 218967403
    0x1030204050d0204050406021c06090506010908030712021f02030108070e06060a0c0303020d0518060105030106260c0910090b0303040f03031101090b070e03120901020a02060a0c020d0b06090603 85
    0x115500440b407154030100505140c3e2100e507115018443c01801c150301068030000210285182c41c00c0d490310b6140c01d07c004580ca00c14103810080034244440000e01d0301038a25228002c0c18006840c480e003a035a480850f07802800b08117544180100a012541104000c19009402c00c2c05101c2c4d0901c200c40b00850440032001505001d5030303000b00482e0805c2820102282c9407003214008400701502030180c91040e8201d03000703460040c04060b089048001500040520b0b1000503400355200ea03050550400c00d8049101550b0484280c0014015500240e4490b43d460075205000c07464020b07800504005c2d40d00103104082c03059801c265814807101114108041d83ca00447c05803803100ca000c10000c000090203003550741c8000041900201d0900032079101e002d8908001c8034004041002000003020501e0244030804100700080a17507402c140200000030355622003614001e020724800039102c84440d010f016181c8025600402e94060300020386482250040b05403403050143d000305000c10340b10300c3c4c0802c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 218969892 1250 218968642 218968649
    0xe180702100f410c0703020c031501090b06090a0e01050307060903031d01030b03070305010204150309051507020f060124031e02030a060f0b03070906090806190e01091109010501030204 81
    0x301143c21503143c079807054410b80440540c0c07140441d0341d00540004540c25001d9031040322003c4009407162400d0901030306244d24400c04622070b4002004118249050b040031905403998604009900e00401c004959a0301c10301d0941a48240440700011b108016a000941a5030041e400d4985140d0340b060260344200c01c0b804020046805006038407403800704002c1401c1c0f840300514010035000d07826804030b410b04055030000e41d240c0e500040e0503c5050040414901000d5861408208050540c2c944984030704402840c210442075002c0400c80c464801c0254104040203482a900c95503034903032460000c00032801201840000c00b0f90503c900c0ca00030300c40c202c0c140780303142d00440002c0301c625138000080d4001060928819554640819041411b0344144082d01d00022520380d2810103072400783c242e030700c0c0390701c91410030a0700c00f0b0922601b200820182d03002501c4d210a80010b00d00261801c000d0038040940c044030f580380061034400d2040c11111410b29807002c1c1c440d9111642c80b200118168411800b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 218971142 1250 218969892 218969921
    0x31202030c07031506182c1f0e0d0306060f08040b07080c0d0204030305030402090c2805041a0901090b0a020d0c020307080105040f0b060a05100e180702100f 69
    0x701c00f080854004600b0786182c803020040020340341e445034018040034003080c000c018195521f013101320480319035949111034131514415050b00c000080d040f00740d894100b100c150941c1c00b1242419400041d00d6003214048a03121001d4403040d0144d084000d00030701e4a44a1017002600b001074594202d409074076a2030085803c08441040d81d030300c64205490604020340540511001005121030020f171a10240000c3e41c07090703840c90b40d01c1c1014010442e00c45805814500d122008116103041c81405540d0aa002104080c45207140c4030640426505409603510107007115144410701c10301404984000c1c16045401d8940c40030040e00d0744071000c0c40d4028444d174035004d40c0c8241b032043c20b030600070707c0140c01491006044840e00c907100e4842d5070a590099a003140e170365a25106aa0070400c10400d401d51121042e0345032020b00d4900000201e8015810700340c0014012108001e54541d181c0d40180041840700306030344405420701800003552030950024459a03585400034100340b103040d50080c54110035000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 218972392 1250 218971142 218971153
    0x20f0d0c030b131d030f090f06091813050118021009270207080408070303090e040b13020d120513170703081b01050a0f0506010203031015030b0d0c031202030c 70
    0x703c0f020001000c2e4004e1800c116001001003458100e810002000c4860002d200d0540b540112428031800c80e41c82000743d03209010900c00e662642e25050350149000c010080c03031070703034035101c5000c0c05041030240600681194242600300d09402440d1007810f803240d200fa2201c90160780c01c40b10845d841c09480c000c10074115010301082c0c02644001c030703c2c080b03510340c2d08500502d000d10035590090994007a078040c4400e5003010b90104203042c0c12071788a80084c0305800c00c2c2100b0b40740c941d440b400d581000402003c00d42e8500d003551403d5455001035030744066480f41100614580055002e03003a0f41040102407041c2041d9070010803103032142d161203405021004001d001c103d0540d503d8108640086c0c214940034500451740700d070a85824050107004203824070700000c007140301d81080d80a480c2c0040c01e85055600030010303c2084c0201800201c1285c903545103a807211800030104601412184248030350001d480079160b42400350140200c022070f8819941074030300303180c42c000a9880e13000d04a003030b015a8009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 218973642 1250 218972392 218972419
    0xc1d0d02041a0d060504140f06011503020705010f050613110d020304060216030e10080c18010212131805070f05030402030c1c0303150506070f08070204020f0d0c030b 73
    0x50300002c0d108074400d82c81440b1075240360301003070714405050815036410b038682c3e007803206102c200c180c070107000e60581000d0a00c0032841c54403555224418032038100302c1c4d03110b8070840502c03030310aa0658200a50040080c400c0c0c41c07154130f4400c05031105407807171841740c2442221300c2c940309176504c01c041054a0840080e8108000c41a40340000e410040050b40c800e5020060601100021040305425274400e403141100002da05080c00942480b90141b0014096050140600c9054401c00c0e10740f0380742c807115101042d9045c2c01c0100d04214400c40b500801103030100d54880003486140d411010b0b82c0311841100c02d851111032511003526401d07a5070310003007154484c07511942d51050006540c028006022200b07031041000c0481c0d803030380c031140e85940c40d04141210f080425070f25016140c04044c5203210000903900344000201a0f2050318002840044046051010880905d050b50702040d0010011521030b02110011001588000c3c0d4500a29240000d80000a402031080320120000030f003401d146c103443c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 218974892 1250 218973642 218973649
    0x10c0807020a0b030405061e04020a0302121018050c1509060705070b04030303050718150302181c020a081f02090d21020c15030a020f0d0c030c1d0d02 66
    0x8100800c0e41c1102d03a0b5031012038508140401580514801c400500f00f5117000400d1441900a039500519440f02c441d0600c000340c0d07581803000c030503240c0446002c14100145c8010902d028114041c010342c9a080076100c1001c50b841c05204850786000d40e0594503950500c00030001d090311882d400c0002d2100034030541c18181808000f414116201c1c20031034800c0e60b1250305006060300298412000603070bc400400942c01d5021100b010309400d100000b200f19410b0840400d070340401d02c00b201c420540e0204007501c2c5808542c680100c00403016000303042c4079140001641d40d8061420099015205102c00080c01003030004803004a034240c07000c995582555080807401a5000754074055004802e081d11101003820701c940d0064044004c01040e5220400340006401c6c042c4c1100072a20401d411181d1006681045044a030301c0640c801c4016a601a601c00b42016401010801c034411813600328091440360305030b80500000c05043c0c8030042144802103406041e000100700300358001110700aa00010305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 218976142 1250 218974892 218974897
    0x1b0b1f210206040308040f050117060f040c0302070f23031204030e01090305011509050a0b01050d020d09050706020a150c0203120910020c1501080c1804080906040b0c0d0905010c08 79
    0x41c40100810310786640d03604e0b0440d40c0d030069080118195101c890401aa6070400030195080111582104a03860005c0014514a02c650311180c025602c4441d0961280d1280d8125407129501800022250301c880c142424004004015901c0e001000c41000d90390001c00400d66507100d0b0f400c40340c2141070381c483d5001c0766841c92403042c0c41c0c18015a08004070008000f80201300c1c4038511012034258591910403104159007000c2c201c90605031405020510a0364410b00311101903803110005699a0202c000c104010500c40340050010b004100001ca0050b90100350075415501558642c4030001803100c8032003c0b502c0d10031030b240150348108000514a546014030360b40c4440d40ba015104440d00303040d05402683e10032542d92a10f0382002c5403c03d4403054150b1020302624400d0003c2050300380c0c0c03002140e00300c0e812034101d9030355041c80c80000e001c00002600301c8982d20300280181d9180c55544d0180b868a4105005100e058082e05500002c2644140d824900b1228140d54600d44500a5100d11800760f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 218977392 1250 218976142 218976209
    0x301050f0f0c220b03071d030d0503060f0913030305060f01080604150e01090903110a0c051c0203100605030c0108040b161211030105150c0606101b0b1f 67
    0x5040072514003c1103100801d0300c01c014400c210800f5a03078508840c0042c8003082c0c081800c41d4090007903c14942680300002c029184a940782040360b82c0e6110b1400040308814085881940055004200a090f41580d828841114441c0d00d080c401c5885543c20403080041680c507590004140c0c2000800c58a4207810075183c04000c055418461134990003100d2041c0000d800099141d0f886401c00780426a01140d50194540342074050460840d180c0e462582200c40d03072103038a1140e488000050814644401000301c202d074000c0440b10340180495940f005002a445660300c2405803403060b44095000356100c0b0b01c00c5902c81c03508080ea0b40d58100f40327078103410045600e90030003440c0e143d88120148144154169000f400200b0340d00d07985404c0400a4491032604002d64002c02404a481c4006000503050780001d0100d542100d00c60f0540800c0740c149c0429440320fa140c07160131202c0c0d0309012170f0403401030040402d200c802c080c0c00c3c80754800243c0c89610f40b0071010342d61003401000e000014007003e0309144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 218978642 1250 218977392 218977417
    0x90d02090601120606051317030f0c070b04031b121101110c0d2003030c032b2c0f07030210020c06030a0f0501140f220c0503060301050f0f0c 62
    0x60a2008414045130002c1e00943c010070310001c3c3e0324100c002c00b0b034000e4008105003c0a481240420f1802d142c480c0250740700b10f085204007140807101841c061122002404520301c110713803601c2e075078200a0044401c141d103140720ba10086001080305548012007031105a040380560014410040044480418004403070701d10b4000c040b5510b1256a50102095050b4001d00200743d503250846541c42006442008407031182c3d00410030641122804801d44160492203042042ca580c40304440c9810005040c10003110039180001c841d806a401054441c0064051080905000d206c041100d644100c1c001c0c004c01d0a6119580410052400f01c5010300604003502c1650b4290030440c0100d510307508140c0d071303c0d8041522100070520400c40c0388100c500501d041104c0c081003500300000f0880c4543d45d0740c4018015000c601c0c0644900c00302090314060305045210401c00c2c440003900080598205607281403081d400c000204000c51a640e0300d842c09032440120128298440c030b40407030029845040309019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 218979892 1250 218978642 218978657
    0x8070b09160b0d0c0216030f0305040f090f06060305060f09130605090708060c070308070503060411040801022d03010b07030c060f0914060f16020a0609050109031202090d02090601 79
    0x415241c070620100c02050503003031407a01e42c146006100292a2980f40038000c40d070010b1500740c600c284542101d402c40c4d812003000200512107040843e0144150340014500c0044003100082c030341902c0d8051241310301c210504000190b03c480781101a40d41c15610168045501400403201c0d103050a403ca070481098406035914140c00c0e5959003d480d001c039644015500469000c0100c0c0c001070145a6008010301061468000c040d81d010705100c50140c1014100720020000400300c2c1c88070b5000042650350300c0182911240e503040504d001c1c0d0300050307414a829150380b91803628038180214802d0190300c1c4180840c1160300b4491004090b401410043d8100040d882031078010603914440c4004441c01c640d004a14012039051502c8ad1019080100d039440d0320002c1004050240c800035103400c094112004070b14a040c044080b8500b10380302c0c0019108500d0040c000301007210560000c4a428420303100c4043e0308284408100803409212803164115240400c00d00062614a001540c004c4050600310f0307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 218981142 1250 218979892 218979913
    0xe063f03090a1d0907120f03020c030a0c15020105040203070b09031002040801150b0903060f1306050109060e010501091503020d11070620070c0e10181b080408070b09 73
    0xc014a0040e4400000b4103500b000f001510b0020ba0102e503406044030f0002c000c10b038134041a6a0301d42141d408082d00d09001d40d6510000c00d0310900c100341d400413006040f5111000c25081000715025540b0900c0c01c1c40601c00c003042003603801030061a02c43c03500180601052441c2080a007080c0e440982d0b400c2d0b0500134038940d240c8215003840a4000b03400340100000301113429040d0203802c1e10380c540104400ba2030511014203240d90004d542c5502c0440c2941c02440c68403558501c2c41c250b0321104000300118100400458140c035154401000c561b47d0516203210340e43e8503401928040702e60702412200c564042d2414001e54040c0d0020806500418000113400b80c0e00c0421442ca508410012240c023520f40501182004c204e104a02c00d00483c1140146001c0b080d42c0d80304400003040c440e90000341840d43c0056281d81881031040b00501048089000e811800c102c003400070f086050244151003001d444000700035114450035480b5030383c0301c90143d140120640b524070800d90000e02160b9a4800c0c00c1803132 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 218982392 1250 218981142 218981149
    0xd12050c0a1101020705040506130c03180f0218060d11060724050a1a040b040216030c031209030e0402031005042316080402010f020a0c0e063f0309 65
    0x4040041c00b41d044800c2c0082048002814000d043e400548154241700a010056650300c0100403803020681380001d043c1000502600134040c08140e2141a000c113800303100510004012242110380700320340c01d0300f40403820f141c0300e5200f0360b0503684035410000c0d64150a001510038800507003266070041ca41400e200c2e06540e045d0b2030402081c1161500d01c8085004018461580601a04011030a905001d07031080e410f11915015126100203104940301c4200c00c1d03030354035140d0445410529030400003001100d2414050040b00a456084001994141c1d403803031480e0403841890002071303165503140030b64607076501040043e400c060b01032002420100d90009032036490f0b2160700d21038000c540b200b442031603840c90108251000145544c050740080c003180d0302444e603c0162158000e0703090030406030000c20503400320700d410700030440180b00e02002a00481c13600ca58210341441200100e40000907105d4260740d0706600d00b6281c020001c0c1e22103a02605004072401c1c0c0613035628880c1e240c1164281560344000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 218983642 1250 218982392 218982403
    0x91404020d0521041509080d0e010c0b0a1b031104030204110c060708090c03150c03071403090309040b03010b030604020f040f020f04030c0b18011404030803090d030b01020109020d12050c 82
    0x40d48a043c00160811000f65040452050700e01c4509100f00c84038500305115448240d149818010440c07620761102e07182c2c2c004c0c1090b1001c00c0d00440804540e1800404e01c9000700355040c4080365a11402280c801c55074031034000c00514400003c110390900e495a424013020b088031040d4814055402e01860300398207001c00c031192080e000c51703807002c5003400c040e001c00341014466540e0074007a4120140000741300341d41e000305681201e0319003290307070b41ca54442c1000c5656299005101700000c0c000002d01443c15000809403000c80c100722001c101c2c0021207410182201e00e4081086d0b09600400b0028000d8500b004090480349005000840c0442c68410124202c0e40700c070b081501606000b05061040c03044075040400030b40103646c0b4042c034254503000b00044540303000d0b0802c3e041159481009400540d0b13a015540119401188283c40c0e060180700d45455100d100d00c41c400181c54100d82c2503080d8814000c1c1c034289600680014191162a1a00741c00c40b40d40150305400c5c82820440941d940780104503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 218984892 1250 218983642 218983693
    0x60f020309070e061903170403080a020705010806063a0e150601170117031204150b040b0d03030203100f0807060f030c050d0b0f090106030b0a091404020d05 69
    0x2030035145040c280c4101d80d411001e07103900d0048420240d20848492045410811ba9420883e0000d00e602c4001c02d2048a110302d800050043d0030200c1c01984c003030780008958007642c0b0240c0f036103290f6075a1003060100b5401400a0490380c4050007014101d54100c0103c0c0b0010713440e2080d01c40b48407008503000034098170030721100da0905034050400000048000d00146401841c2441c040001c2c0c6d20054942883c4079041c05080071004981121406441c070400c100c0d1000d00c101281c8640d2440c180c2012074100c00e5582c10480710743e0401d0651403076403405104210b640c550003003451001d074410780c80031002900002c2c44610103032902c01021544a101e140c1c55070041818030018000c080c2000001070050900c484072400781401e240000000c19082410b554204182c07040004e54020345100244039a94a4074440e50001d5241001081c500c4d0700d40c00c4581d24170f80070b917683d0070001d6131078010000300d070a40b01c80542c44050800104005243c0407002e201c0d45400386084a00700034085429001c5a0715129 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 218986142 1250 218984892 218984911
    0x3051c02030c1e07030f0f020309100504061112030106051317030a0f020102030f0106050702011808100e0a0804060309080c01110901030b01021f1e1806140709030f060f0203 76
    0x307190703464503030010f505441c00541801c545040c0101e964002d00300094110381c0c0c4051040764117020003003500c200103841503a100105480c1d00003112040140c07040c0d0080c0140400144180340b14502088002a2281c1c1d800c076050a0328130f140c1c6060300c07c4030709800c462103961024440741400251070301c04401507035440540c0c0b00a15920300b0000c0c806070481c11031611142c156401401008120855038144038110340490800c9075640c0f070140300488076820032074440244c0e500070b4200820707000d10002c3c0740307451103245440820a0403030b9540f01da0b03614507400380e005090740d100300030070300ca010312a8220104030761013481c00034180603650f43c00e02d0a45001a5840100400220b6a0015581d06004424440000307002500803440c1c4c0e102c44030030b60b281c43d1442d04019521008404145015805205140c5070030082c00c0081d200e1200b81c2c00400e194250041e1452418050000c40c581003048a0f18007482170341d08c92002480c0b0395a50b074001c0342541d074403d0f10101d980d40644030b80e9160f5800114894a40306 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 218987392 1250 218986142 218986147
    0xf07082401050603180f2104030b130303150602010b01120204210309080a0f0c0f18090302100203010b07062702040e010605030a1a010806100303051c02030c 69
    0x2012003450040c034000c24000320500e400140042001000155064881c1a1491039481c2e9a8941c0750640d256181c4018500344601000309043c0c00d804114102c030700360411022072551054440201c00c40c01503010242000c030f1001e000c140c8040b0403400c50008680320381030214040c0c8510b81140c080c0344031540150003513515003a01e00c0c17056a102c8104451803c17080411401d142c101020a0b20b140c0d5120481e07a29910880e100c6424540541a170a00a1080e0403c54142c1811450984044d04000b0001c0350301d408401c20110302c001201c0b400c04265004503148a02c200412807504025011049054040d8001d00102c2c8082c0c1411f40000c50181c4040070803d41c0d81c44061401004440040d210b1000e5400c020300d0f0050384c0c02c0c40c6641300c0101c54040b5404609000f00e82141401090710360300196241c0f1458007120b040002c4038101200c13403a12040142d40070380e0384064182c0c0f5442c003120106044054207500f840081c1c01503021746030110182d100401c4030b4000003a403a040303030300c2a6103110090101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 218988642 1250 218987392 218987399
    0x7051215030102031602010507021501050f0f040615030b06030103120c080f131418340206040b092409030d0606031e02070f0b18010524101d0109080f07 67
    0x90023001d030464004d100500310440c0741c07280600010b0040c0261440b03440c200301c40990594400003840041d0070b008108011007555540e8205c118150164482d010900b0000304207003d29103441944d048a0300001944281e21124108589083c4080c90032510b408013480342107210708112018000103400d8004590704103041442c40c0c03034a1603032854868482e2002070780c0741d50302100e0000c2082e08022030f800d1052404007a00f1041b07a0451040031010440c1d4411110617101641c00501c5a02403400740707a01001640707540c0c40482d11103800803628a0707140019919102807454060a80354003c01140540b130030070818030070840c1519500d902c00d600103603d5503010310018410003440012101c40010440c6440e8003595014020308100314042c1c40a11110b0004e29608081e00ba4014140c0a00d4001c10031880e0070100480240410000884e00410b6151840d9007420404186c949504086c0c039442e00205030a55087c00365040414240d040107100d20700029080400c100300901140d140014009041c01d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 218989892 1250 218988642 218988647
    0x207083001090c120b120316060509030a020c1306030519051218040f0e0613110f0315150d030309120c03121a150316030203070512150301020316 64
    0x40e00b045450b43e161800d0103c10035007010780d005080000b40b001107007030400580060941c80305101c046280303020009001c0e03515507850060501040c03007040204403589130140c40c2680ca000344200340c400742c0d00201c601030280c505034441e11504202c0407404601107459a807401e040c420151a0b07040c00007204034192007040381c240302820540c0e07240c811180c100700314540c0c0490020003082c40240a50f0b40c420104001c14451b0b004500c003d83d085044a0040c1004018246605c2d80759000799007070f0140880c01c01a51074002550070400700c00030300428004d210b0316003103081e410b4082c00d203000e2012aa40020f0300b58071200c83c00d010443c081e48002405d112a03041403000450f08125010800050010060000e90000040c9400340350142001170780c505030041400c141c0c04103681241c0d01c540043d524451a12812005521900035808881012110403409a0036400103490a001090003480001c22940300301408a50206070007401c0034118000b0804682264401d0f80c40d159041000d0350801c0d00d094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 218991142 1250 218989892 218989987
    0x304110306070215090a050d09080c10090b18090a240536041101020d03060b0409090807060207050d021605150f0c150108010b0405010509040303020708 67
    0x16000c0e8080c000d00e24020000a464080d400390f1307036820314240c2c00820120700d010414820001d40c8842110304415001c400681807064a208001e15031080d004640c0441c101681d5504610700251681c0417514204805909150414403c4d0740780d606e00303004800010b170303140218030380a40070000e800108040003240780000b0344214241d41401c0880c9110030001c80d2104c04502040c0e40c000c0c0c01d0002d107138170405038038611000139202d0303441000e09403000d02c4141310300c10380001a1264245c0840300c24015014040e4107483d081c0c41400c003034010920080040d800550000e0709030911985056250148940e00c04d0b0490b0440c9400351082d41c08103d090340d0003601001088045c46541c100810341503d004006507030014100204103640c04c01160b841d06400015055440e49182d00c0203840050403624600c0c96059801d01c141c20b40d81d070800070000704900380f034801c2c0c034140c0700050107407109903850f600d06401170742c0007400864000da42003040342c46d20801d030220510310882454484883d10113400c6040300d400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 218992392 1250 218991142 218991173
    0x50315040e07060503100f140405011d151201060b041d1306270605040516031e0f0c09090b06060f0a08091002070b06091501141615020304 61
    0x80e4a0825900900400061100101e0354036142065a95558003254000c481c1e03554044888007080b0080442c3c045240c02e0110000300c01500c0030407440c0c3e62003440860341985072409003400400b08010a04100c000001202200d102070405001c11940c03450113030846115501015100001050501400c01c0c5980041e946444224624040c2d041c01800031102202e00040100101e6a4a203040395900d060407140040ca1401c80002d84108a60b003400d10207003204680480782c0e8010b0200c1e84041d80000c00401c8142e030f0300600d805114040400100c950f0700d00080d01911900d40f08000740c07001820049885001c5c01020ba40415110060315200098003000740800d40b04036410b024242580c01d000c000c0d9010242180382051440c0c6980c40301c40e06012002c2c1c1c0f00c5001500000f882c20511184058480c081c55040da40e441c42640c2c2e00300e5010010409481303080c001141c0708442404807a60001074500540101424400d024040e500c039000749540f080710300070540d008410002401741020305240c50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 218993642 1250 218992392 218992399
    0xe031206040c020f1b043201080105010f05040207050c2e05071104051005030d050a0219082a0d030e0d03050105150c1515030613080301060e041b050315 67
    0xc01d03103a105115114112104180220b041c42e205c8910181c1c3e0750f07042403141c0c20000f85182c403041d6540f107080c0503120b440140c20203103102440c0009000c1c0414400d42c0e040714600e240102a060400342004003a61201000340d40d039104549007080a0b60b6500358581c0c03012200b04592900140082201040c10f12901406090140c140030107008903000451070642c60904503400103007a83ca401c01030034102190380015400d0720a80c00c42c80c42c000c7d00403005002001c0607400b1680c2000c86810505a003440d11034001f495030304240702241c50524483c2d01d00840c80d00c035908004140060047d078134034050300004404002030710703001000c1d05200d0a0007080c4000c0c4052034248595070400c1e001c81c191400d0b160b41035000110004000c00d0081c0c0a00c40d003c849040c0d03511818081c2080f004240490040f50342c0b1718800d000b4203011814040929911448955001d64680e0440e03290810940b140c442544540390400d03104c082c400d55400c07088101d961100c0035611140d80301c0c140140c1f82c48020060100f02c600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 218994892 1250 218993642 218993653
    0xa080a0c0b0f0306100c0f0b1005040504050c0d030207031403030f0604020304020a140409080c030409052d040c050904120f110303010e0c070c0f140609010e1002010e031206040c02 79
    0x300095141183d03801041174a400980d050522802c88100c001c6a4002d020800e0480c08642000384c1d8255503070084070744c2450305900f80d488008000441c1e8040e0303002403840c0e203ca001a0100d00b800180a080140240152400e0599070348400f0400c60010500000e590400004c10585046c480c0c80603410090940e02107095140583c0811004202801181500b81800d0f030400c480d0b544a0304110041580400040c1d21003113030780d032110b5030b0707070824003072068080c0c1802d0001c1e945214080600b1b29040502c0056a8005c0e841c40000442035000b800030f80d1490000500880d80303880303c04ca010700842c420b02840d01c0d00d40d40100000c0142c0c05050050b01009008a00845c04d1f22000054a06650145e06008600c0c0c071803c44905040c031400c44014074009549500050b080d0804481804851103400c11030080400d05041003114419000310310301054151000307005c0c50504c01000610350800b800001000101e10350301a156800c0300e46030200404050341080312a00f064010a445180f0b00d000400c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 218996142 1250 218994892 218994907
    0x20901170a140709110408010b010309080d020a1403040f0204060605041d0a02071a0f06040209060f03190e0d11010615140418090614240a050a080a0c0b 67
    0x40d12010740d40700152511050000000d1601070520840300100090903080090075aa400d01021903000703885a5405035207400c0e042c4446500a001d1030b405658000401843c0c0440c0ca00280001c0d000500f1042c03c0002c29081d031028101810300560203030380075003e10b4000038524810001690415003000d020048240410048807464180008502244100c3c402a6582e80500c540081c01400c030b01401e520300070444e141101d02110381c8180030b11500c150740f12550380d40b1410701c416803050008407074100c0c10802288014001050145070003c180c1d00c040040d80503090000c030156820b400481100350041008030310480d4004980c001001d109130024800300b458000c0080c10f0100404c2c00c1014094540702505001c0076038400c84026100100701c44511083c4131405500915070840203c0b02903203454041101c03030b41c09450b035510590040401428000b0080900c5010000d80034417250000d0503c000401c1d1075884840000103458840000c004e100d425041c402e201e0291750313002491002c2e0802045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 218997392 1250 218996142 218996189
    0xa3c0306080129061803060f0709080706020309010c050313030b070306050d0809010e0604090203160e0607240608030304050102070302150412200105090c0a170601031704030203030301030f020901 86
    0xb04468400300c1351591110700c07031a40c890040c40492495076240c0520000c1020002811003581c0c0501025038078a10416200c1c1c0203c1e0392008940200070140c1d0050043c6a455803042c0001c540d00c0d13108005880c24000e03000d65601200601340c004603030340140001001210366152082e400200001c580c031421600e12512840054410f00480c00c2c10031021034000000d940b104c0c4111001414101e50441d07407440c040d003e0086541c500e01500c40010242c920403030319441c01d0800d441349135400c00c0c03140b096030307188090203180c0c180e8100c4101607541c0c446c3c0000400c0325041c0003840c03003035010340c002599420030b07890001c0c1803e420440c02207100c0c0101061001241c41d03a0100c030700107444d5080c4081006401e07034544000e140d501903504007660900c0e0410484d0400450103c00c9064240e461600460301e50329284084a03e04180c4a11a400700d0010004140300c1004d8008039020129868603050b10703500440d041d54000d80054400f1040c9203200e4085041034512640184100440b800002e45072900c1e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 218998642 1250 218997392 218997461
    0x10507081608132103120e010f0c090503101b030b0105090904060e0c0a060f0c0c0305010c021e0303040b160e0907230a3c03060801 58
    0x190825034042508898032000152034144a0b030000103064a40c0c0055540c0d401c524864010135011103103000510340002004500709002e40e50545a01442c0429a01c0031360040a002c0c20041540d0340310365203040810810710407006128044d0396007296450500c0285458454000200641c90303103400c00c09807000c01c0d10f1b031501e0040070351843d000c90706110510048030a0300410500c607a200c804c000900040009503400600344402001c20b84611300d070750808110002c2c80510030305005c80c02251034030380402e202d4480c84841a10450f18a09842e84946549084442c17038140c010259105104100001c14003205070355400086000541c03031131a1a944851200d42c01170b10102070301e90071503040b402e8140580248070b503201014000c1600d500d011100144129170312158107058018103a248450211b10104646110905844001c00354000d5050079010704150040c5005000641c2403511905440268122041149a40119065040a00403800c443c808001e0100b1b540e000300000c4010b01c4060780 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 218999892 1250 218998642 218998657
    0x6170f1207031419080a140726070302040f12020f06090105160c0501110a05060f040305120703020d2a0e030708070905040c060801060507060c0e03010f0917090105 72
    0x2030a5803104014030302614041c01e81000403030350303110200e60304113440030f0380036201419902c0e60381d0b615260b155001c0960072941d030203640c06000d018a00014000c035010721064016502c04150510100c003c81407224040c000a440180004c4d40000e400c00c1403410070321120002c0e0000c01c6401c0241d8106034005000185580c80c1a40036040200307182e68980e0265050365880848455101ca44103034500d0305020521050080c50f01041141010303225030075000034820003a50744100100016118204d491114180050044040241c01c10120900c03403110b514850207213246880260712200705203050016140c0c50341c3d0744810313605880c000d203a0700020b210f50340c00340b081c603403d00728110510342d404a410003006030001d481074483d0540018154925610442c03190340110300d0704285a4031440204e4602100f0300c40c07040010424003040e03002c1512030b404a2070200080c20210788200b10f880209003550900894000700590703a82e050401e2200101034100d1000d8400c1314a4980020840040c00c030b03006451 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 219001142 1250 218999892 218999923
    0x705010b0910080303190209030f1011071a04060213030506010509010e04080a1409030106031a09010216140a020a121b06091e050d0b01090b061204020108060d0803010906170f 77
    0x40381d11b062204954110b40c15000094256080113008800c0d83c0c0ea1400d260a030314090343d02c0e10005034000003520040d81d400d10303803100b020114090803140c1c5591001014000b924029800c01c04c03c40b071410746e00701550085210718040c204541c0b5100c100854a14140e01000360440898100400501508100c540041103418040340d580744107540e010150252600b185c3d0035603e0400c01206012009000d0042d0200000084a07103a44c0c0c00750b56400e17402039601200c4645041c44080c0e00042c58500c00810b012084422100391034544e80024404550396030158000f1034200f24407209000800105810094000042d0750306907182000c014180100761080c41d000e4208040c40f4580c40d40701d86e0204000f803000400c0000509030505040c00c400c0001e1082040c030b9071400000c5030780c60904406071050031517071300303d1084107660716001034a16140c0205202c0d40048038403401d40c00142180003440c0600522000020741c28242210401880700c0300c0c072811415031051b428900f8140d0005144030b51604484d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 219002392 1250 219001142 219001171
    0x30908160c0312020330040f0813090204081c091a0d060602070501021e0304090f0b0d050105220809060a210c0f0c020d080a0c05030705010b0910080303 67
    0x14100564200d020350030081000c907a11105803e1144c0c00800781c11070102d15a107450301c400103010030500341ca02c010b60001c010300c012400940820b80780d021a4045602414115141020044078001c0740301c2d00b07810a1036119800300b014000c1d42c00030440202d140380d080722a01d01341101001d02070b01c0c4803030901c9841c6001d0004040c501848076140d0548401c240c020000780260703a1a8030380a0340700c03c05805658010700c1142d01d000c922211469108428002c580003651402e8209000302d070140058140c0c800c0c102e03440300c0d0f030304206407030b0000c07c810800d0049000144138201171031290b0500e50b10244015245080803441c0c004030b40c00404490003c401221203903078a19a0701c405907012070300300303500c90680d0f01c0244107040411010b40200361a100d0701d03a0b81f82d04103c203040056a044100280c041d4106184d00084000140c90740000c0002c15040e050400303000000350346045c6542d00c46da604542994550450202c03905018000d0390300600481d0382044e1403420044c4440d0f032400010181c45d80c0003040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 219003642 1250 219002392 219002437
    0xf0818040213050f010f050d0b120307060b01030b0d0201050301120309030203070f060906050309031b0309040f02070204140f0f040f0b0403020a0312020301050f150d060806090706030908 82
    0x1290001000400140c825520341c031180d03107a40d80007a62442824025060b03100100788640c07140702d440d6098a000d840741ca05141c09040024014520300c40749e680c100e03000b81c803d250060382c01c10140009600c1050301141500c5007a00041c02e4035106110140a01c00301c4484100607a000000d0724150394000011608402c0d180c1000c4401e60295070010b901401054070100340d03803840d8170010040d9201c0e03841c1c00100c9642d81a0031039840c4403c817002d0300c3c0d0ba04117101c41003000703100e030802c0c500703910802c02100e05044026001070300303c4145e9004d00a42d20750002e40030707045061a010707100241c010b01c01804511b1a18501040d20b5503c01000d000d40030880d007001900f040f65440d404440550894940a1645003525010f5615054110b050300805c3c0006003182c0d03100207a008072810383d9000b83c841c00510001c4070074040081100c110126814a050116180c0c1c11a46c1c0b00703030701c002c1c0482d0000b0641c0d8100131048500300920394104100305402c0425810100c1c1d2210111000c0c04000c130300c4082d86221 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 219004892 1250 219003642 219003667
    0x209061c0308070e030a02090606091305010f05030708060129070c12033e120f0a0f08010e04080d2d0e06160315090207030f03050606070f08 62
    0x40d80e84110040448102480d4149544030840301c1c4a0700e6581c0701c00001e10311341c0b01010350750608290001d5102c01e00400150075804c0600c0035103100317003024100c419040101110101550000d030070000f000b5008100422251408002100090009401400c00c0f075040804682401c08403070321705040d00c2c40d10800500c400100c5012128180e401550390100b4a0711140e094450890381103094000468401800003401d09441d05a04544001c104000f20b0f080c0340c1d41c852808070041300c0c03045142d0040f020847d1070300040d04010000031024082042d6108880a000380c014180644c8003000c10118070010700601140d68100343c0c10603041658181c40f40300700b5002102034800340202c950b025007800c00d00c1d40e04800c150040465000b000710117000001c3c0080440359201300840702000c0410b407818400b0881c034000c1c6d01404480c07803d110300007005c43c0c68210000070780c0c3c0072450440020341400c6412904070340c50721445401c020101c5007140b4007002c9480301c2c400c242d040c0c0d5000d043ca00780064100e46a94 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 219006142 1250 219004892 219004909
    0x1609020403170f22030218090a03030b0f1206040303110a080619090f0504110f0f04020915120f0114010c060c09050a0801060e010603020a1205040807060608010209101803020906 78
    0x4124504c2c2c420000603140c0c030b4100001461004038020907102550308401c41e10340003014888c1d59554000e240014071620101d024180100340541c1245040a040710540c5038285006a1521444020002400c051030001d08a83c1c0c0001c40d42072a02c01800242d8105600007242a00845d0442d03680740201d900f18408a0500d949500c043c0ca80c034030304103141001c8402600107500c03e9000c2c2e019400c00e4140071090249441071000400e5202110f600740d00c0c11882e26501502800380302030601b200d80342c446c00c800c2c0ca881d48200852100109540c04001c2c1c03451040c04a54003509010350b12802c0820241c0010f407407540d05200050000d0740b100d290400085c40780c5010001000000c228001003940c6139003190091102c1d01405509800341300022a0300c900a000701c40240d001503452a1000201814000c0217007006172048a000b1010880c0c68041780c010f00600340508007d170001070703840c1d5003541004100d5050903401c2c000e0140e1a0a00322a039040401100122601900c1e40c1d00c4030355500d0300052020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 219007392 1250 219006142 219006157
    0x207050d0905030a03080c0423040e0102030903040302060d09080c3409020304061416030b0f0108060d0c0b030a05061f0906201b03120c100903201609020403170f 71
    0x4510a01940b10748041e00000d09c1061101035808002c80d901d058055400e0b0704c81200c91910702d80c0108010001070411070700038201072550000000d05164140d440d0280c0341c1c05403070480066401801080c2405607200d1031500300602d240d202618458400c82a56240709071031003407a14080c0d000c0002000e004282c3c1000f812103120030703242600c2e03103820f00e41d1415402402d140f0100091508403003404074180000ca003800c041c416154034039941c3d0780030100301820032444011030b041050750f403000071014403000c0694011451445c0104440c0392050501c041a44500b2201c1010200ca55202c200320b50417600e404140c81480c50301100401d40013030240c1100090340301b142c01350b00c640504906001900b003420101860218251480c00c007d4500c18040e034082c008000409130400005091000306540c0003a0b889442804c184080408849020645c00300313801104642d40c0250030b0300034003461001300703c501030001a8001c504042c1182c640014103042c0b201506024000040c0310b182e10184541900e40c40c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 219008642 1250 219007392 219007409
    0x2150a02130303230f041401020a0f0b0402040c0806090c210103081909030809190914010905091506040e150a060513020721050408100207050d0905030a03080c04 71
    0x72160b4900d0000c10071000c01210701d041c0540b48800365800c4000e03a08a940d00544d20101c00c0c10581085405120320381c1e040c014074150320441f4078550004112600c00d4030000e000b80010030840c6001d00510080c1c43c03201d100c03603003040a15410461150b030350114460700559100c3e0303020f4030307802d081031664400c010b0703c51001c20b604ca50500000400c06040c004210010380501c8007620044204420b40c3d1102a9000c000d006010a004050860802012020840e403002400c5003506a580a044080f1180e4110141180e80b00000601c1800c000b0301503290072010701c8006149000c2403a0700c001500401401c0c0a100d907031618100340c07020100304160381305542c4840064a42d0b00f030002403030b402000b2910500c3d010b520a00542a081e20f81c0c0d00c00e480380e8540003102000c0305100e1080c40a06550300c1640181444024400441d1620041016807100c90318541e0041e6501c00c5414018606280b22002d00d0400201d0b030300510054801181045049526081c0f0f0007040d01c460034207040c0d86c06160402c44c070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 219009892 1250 219008642 219008677
    0x3200a0803040501060e0c0a050703021903030e06011e05060f0702100c031d060a180f120b060607050304061101020d0903170603011401050d03050906030708010f12020102150a02 78
    0x34000034000450207284148000c01019907540388511081c1c40458410440460a018010080d0301480080420911a00c1540e40c20300d0303601410488400355840a40c0003d9a03800d00d047d030351008020160161200400172607070b5100b1140d01003101456400341500034000420b68000b030103861425955000e0f40280703004040402003e00030081c558400050f400600102010204020641c2c9000700c2d05901400552500c030354003506403240042103803520038000302e100f0002160106c0d600c0e00d0018101b10030309851500b0150030f12820821700500384500c101c40400405001417000030456080369041c0c180710319690f085101d900c0c028000e03681d40590b21428262044105580326001502e4084d0780b01c2085110b460302c1007458201c0fa040c02ca0201d0791001100180706510340001d1084034503110b440c0041c0b90004410114006803c01d848401c045019580180143d200f10041c0a0182580c444002d90341102500000d680d0800c03d5221580d104455003c00c0c40822950121110030b06031130741104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 219011142 1250 219009892 219009913
    0xa0512070b01060801060c1e051203150901050d06090c090f060510050a1734021c08040f030c02041b02060a0606021c02070e130507050607030c0320 65
    0x86038410801162802000c0001042c11401003c9880c10383d4601c0d503c0964403501c80e591100881081c580900303a070280403403041c00043c41000f6401d9400381f0701850503142e080050488800011310390032544500c081d400103000030380307440d1b52800782c583d0880780c00301364007400b0b0810304075010031900902c400501744818400380415540101e402c40d802541d40100c003d0f020f1000b01e9080c092151004002a0f001e01401415403003181003d40090030000c0030540403030300081d4841d81c244031121a1515059001c1d040041c25010f00483d070804504081d58201081c181d880140003283c01000200003c110324008030074035220b1140d080d44c0d10b60282041090003c2c42a48118007103660900b000144919000190810218000c040480d803003600140420460403c1826205d803105105104501c180b40340081d94403511030b0850f0013004c6035401820310402d682405421b109260300050b0041108000501c00668807208a4241640501c2c24445020901004000c1c9010000c0c0302d0580740320710b40e240e2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 219012392 1250 219011142 219011173
    0x1a0405010222050904061104050607031218050d11010b130b04050106030608100b060d0219120501060e190306060b040e0906130209090f06010f1502120a03020702030a05 74
    0x600d40a10210001129001c5a0284061603403441c01020307008001003000ca400030301b642d0880c40008007490807050405031203401141c00c0750810082070340003480d41214000c040f60648a2a241c00d4600508504214810745945607035502d030120460801040404c034804045081d400300075140c400403c00c44480e00001e810801415080c540ca900c10b07071524000040d0240240300380740850700002c01074070564102c3c03150800140134802c0d01d142c0020042001c40800070103031004080c0c4e10a05055400f540300c001100826140241c070b0059041460b080051051a40084014854102c03c4400b210b15401c01071420100302003ea000400c52410080c002c500098068040c100783d41c021031783e0102c80da40d00301c20560385280c19100d402d40c103a10211120050b003070240302c15601c036810100312044020300410291424400f41e1003003680e1040c0120500c184050074444071118200f51000b0090b1091490b0101c590340f00d422111030031f040d07002808204649061040b800200d4014065441506812461 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 219013642 1250 219012392 219012397
    0x1803060207050c1906050922020a080915040b0603031314040c02010218010813050d020c0111060f19140108030a020c010519050f040321081e060d1a04050102 69
    0x101c2d11402100408141800c1c100220f0082c1407a100182ca202443d00c1c00c2900d4691007002916000382ca501170300020b003204151035203480c800b100d50040c6d81d18400e1400030205d00c0003408250134ad4001e48600c40708040d054543c0e64129404c00c104242e1030725001f000030720394400c9402c075151280309100b0000b01c1c0320346601c00480100040d501400201041b03075040b0b08078818003840080c812500911000301c1c8d481519510b5000c4070544d042901c0712800d448140c5411031090140340141d0000c83d4800c203e5a0011440c042504042d00801450825400307881c1100d80c0201140c070301e40704607924035071813031566041128202c002051056031075845003031580c2c03039500010030440544101103091005504c40e10071100c091003003c03480e04000c52a00d40c116010b511040e00303801d42190900c400700118001d841c9840c00705c0c00e1a0070200480580385d401424903040189030408102d0a00d09070003028504418155020703904a9034034030f2400c1c2a1419115401c040d8404040b03c860083c00c000410005500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 219014892 1250 219013642 219013657
    0x10030b0909060106030b060a020a061a1503040309060507110409021c051b010207030b011703090a060f090905060a1e2c0903090a170c19050909030903190318030602 72
    0x40c10b1103030040407001c0c0300c07991123010302440c0180d00503c0040701107400d83d03200108100c8a000003424407a500d000042001c0f101d802c003400030060010610080503000500000100024240142089045d403584020494003c49003402503031180040e508554903c0142041c440c810f03008049c1088250070210f03500c012447c146501258998064000c540c00010194200d070360110b6246a50381c00d2030381501c02a0b0100d07950f10b810748014007a9140b88e94501a090b40501034950f86c141a040142c48010442c0056920586c1c103d0301d00b05c140b00d00c9850b0550800281c40e480c1c1c10314500000142d40291800c041a40030650600b8004c902c1c9040000f441d48070b00b15290404d03140380040e2100d45a01ea124403902c0301c52503001520300300c20002c8042440c07600b4002c040aa0948908010050204142103003608a10a02450316102444689496584181c21540c0d01e0001d41c00c213000780c8088aea039a103c160205410b04d21054180003010701c03c00b0030592000080c216040f04946d1fa14007240030b50420803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 219016142 1250 219014892 219014897
    0xa12060320030f01090b0402010f050403050d030e0105180303070c1104020d0c08090d0c02010809100f0e1002040305030d0b060f040e0612011a190f0b040f08120910030b0909060106 79
    0x840f049000101400b5101c0001d8100c1c92400c0f1548545e40155002c0c8051b108038406d01809000010214905005030380100600e920007003080d42c00f203405075084640003041c480302c001e00c0d8007050640a030000103590b4003440e80d00b00889c21000a060003c02100c41000d01e0743d0050000494544200e00d5400c041052400354440c5056503d17854030068403101d40100e62000501d10181100240d84501c1840341c11017484400d075043d00880c04121415186244401741c40e050303c0f13170724140800004108030000302e03a500d030b0214101030940c0d5450ba200c0c03007290000724003191103200006c05655443e0031503c2c0e413024a5030803540c0d260f44003000c480e5070200300e82d07082c03094082060f680b040d0030040c01107015544d00746071840c030303a84100410000030711806452084403608001000c9607a03a20404c0a0000e084042580e68031285098840441003c0301d400c221101e0708504240711091641105407150320008644114035140600000c50080c104880780c182d1218403d41407101c4034401254040c140c800c05c4c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 219017392 1250 219016142 219016153
    0xf03030612050a0f060b060d05040221061302011b0b041118040f05010e160e0a150b1c111803030315092703250201050a1206032003 58
    0x120306541c00380521410207000d0341c00c00b0400c0d0b00011028940344080c2d61060b0030000d410400a03003c60040d42012a030310480c00c0d44c9600740029031824540001c1c68802c0c0f02d218218542d010b010b05502c031000034041480c46a10303410210110ba006040c00214044161080161f02c3d055041c02071003280e080d41c00f0b603080c030b25a501d4032459003868a6600c1100c20704004613921501c0d1036449102c5001319207000d032080d558548113807022a200744403040003030000505052455003041d0071402c000300301428421326186054615048000d05404200c01c40e0350760186641c40f03071907100150b480482518040c40c8114a40091011701200b000040d107030625805055100056040e81499540e120594400a076190020380484140c130344800e009600200e4218080030701c0414003c4001c21942244203c40079400c00308055686040e0100c18090801503540c01c190002010780000e4030512548010a0030013a02c40c1c044503420206030000c80086620411100941c0e20642c0202d44d01d0f02d04028562190085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 219018642 1250 219017392 219017399
    0x203180103270201030603081c050a05040c031410060b030a1503150b0607050d030e0f0c100c1b060e03070801021c020901090e040b06010f0810030813050301090f030306 74
    0x348152100610b142440115144a02d9070b45503100c0c4030007104a04042d01c485000c0002080c139006003e0f070b004000f586204450018007064152030b4001d010001c09481d0000b04000310f10f520f442e03a01202e80000c1442c09000d0111450380c1007110b2406440065410400000b80000b95240251722071040d219041001ca4203d24040045040314480076024001c0d00a007101c6900076070380480d003084001010503103000e840740d680e103007820207030310a0340007180d502d0b50029040c050a1100c43c01c07404c0a60080c000c0c00282400041d03030a5088420481000b501000c5202003107403820748a050b034000001006401992a14028914490b0314803a50081c019041c0002e13081405000340c80888010030b5810600501044200e0000d400c145100c134108038164000141c1d00100f113040314042d50044120121078136049002420b00170507051802c0c10460700004004d1070611006c80c0c81c090340d85c0500a999a078210035651301010050303800043e8107510300504001040740807603800c0c0c21940310fa1400d0058564 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 219019892 1250 219018642 219018647
    0x4021503131509050d080a09150207020108330406051903150b03071e052e0e1c02030c03070e150102060403050d09030c0b040b04060b06090a09230702031801 69
    0x41c0c5800040c02540001741c90200d2501400c4400e60115a40000140592147c1c5592103c00310f10998a8101030340050b84100359640b02d580e03a94484c1800506e103040420041c80032084040c60501f05801c0030301000600e01641e07e9800c260b0051a0042051102c80303414402e10b1a18030b031038441221400c51401481c000c08649002e1110040c0e80200908551392401c2c1c0030191110510b40600301c2450140c2000c5400d5640c000301c81c1c1405c4c2100c2e8607400032119201d2420040000d0341c1e040082c0207400e90030071003030ba8410241604a8003140010154400e1500c0805c0c50704500113056540b40c028a6401710300010240d171024403030500300795201e4044004100580e12420192009000540d04000c0d007918205c4139000510302c103100b440d08034245107454880d4a007a40c82920112120182c4009001c24080b4602801c040001c080398418646440500000c2c001d07405440350071b02994903460061080c40e2500ca5070700c81804201004ae030b15140a8100a46a900401c0050f00c903803040c0c1c82250300c1d5407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 219021142 1250 219019892 219019901
    0x70c080c12161205010212070c0c050102120405010e0a080105070c02010207050f030d110f030d06050306100605030117030c01020d02040f08070605030a02032802090114031e040215031315 82
    0xc50551000d02d15040000c110300343d00b040c2800741c40070342d020441c052010031410f070364500c9036a19030346030700c80c2d100d003483c0145644080764429411136101090b42031204d0f680c1c804503011a602400c00508500184000c03c6d2004100d5102003025460841000391117a040403032509406e20076400d99107810340f6907040282c0348001081154041d441000b03134482c101c0c003c4014190200c018070444451020f00803805240d0340c0301780044500c00f511054104180d007800c0204c59004100c9201c044007039410080c008046000511030386910401c000704800000c0814003c0350100601e80d0000e6607a15040c28403140a036001340310300c10b001100c40d00000342403c00440c00301c05a030310590342c02d490740d200c500c100000b940000d880081304100c1522001c0c80c01e810351802980340c400008001d42c403021444000b4012844480349603184941c04c10400001070407003040c500c2c0c1001074681440950b140d0740049071003510200c402c030b41c00d401c00200380058004242d115100e0b15219509a06500c036045c0c0c8105c0c1502c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 219022392 1250 219021142 219021163
    0x90c050f030a0b0a0908070c0b09090a0b0d0303150b03010b031e13030c0c0e0f0907050a03020109090e030f07050109170903030a031a0d060b0907020d0503010e0c070c080c12 76
    0x78410f0701051240c2440e400c50b038034840c020081c040c14a8526140d5003004459603001c04016400001c4030344c1039042081c3d40660014240000f0845540703004082003802c10103200c001c040540d9441070000b03074904052480050000242c54a840303686540d4100001d40c029515020300d50721840d03000c645400030b444c0d010310407540d011485416601ca82c0e8140d5034107010780d4003200e040030b5290012403041d41900b6424070031a48403040801074140911610700309001a0880d03030144141110030320140c0d800040340001c441c0c02d010006132120f0103104042c107501500a9428100800069200900005420100fa40341c00749880c121041010b80044807c1d01c076000070b1036010307041881100c1b0700900a600055101c0e080c20550100f459030100010b0341000700d604115140340e80c510309241103040c900c001a500c8003090004205c0d0054000001d05180414400c001c1003070141c1001441103c0d1107401d445a01d68000031130525181c0750303d40305031510400d0380c4460165043d2140400c250383c0004102242 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 219023642 1250 219022392 219022403
    0x200406050703210e060406050702070b04050118090e0a1505011a0904140901060905060d0c0b0f090d0305190827010b031903020d140904020d0f090c050f030a 69
    0xc144050350152400c03403800110f4881c2581c240c0445041a080b030181550500385003018152a103010b14202e801ca44001c0c08070802c540c401e42c024040701008404a500f903813406d090812540603000f140c3d0b68401100d41107269001c0c03d00c5640605040c0002d64003282c1c82c4201c40d40c0708140c429030491000c4540902c035100c0c1c8070018940124076150040e000303010450b8054808242c248804a441c40c0e00c020640e241c4a541c0c1d954402002100101e10580341c218400300c4001358201d1254646000701c40d018011703202c92035400915580740400c04012030300c0701c1c40e016000d14030300c401c41c2c28041c00ca1f420108668030004002b000074110103124401032807081c0c40e21b10805c20043d021002c10145100c41040f82140e666886070407003035664082104680d610820581d01c4036114191800a08185402514400b442540740712044002120400d8503184042501c00503120400402e001015110700100c0590f018a0103002c071080c807401d443c401d001c0d14002d507000704142555000341581e0300c1d02203401410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 219024892 1250 219023642 219023647
    0x60108010902250b0603070b070f03050903070f0f06122306010e191a07151109090a0609051b030105090a091704050316030f0b060604170120040605 65
    0x5060056400b0740005401c40c90303400c1062022081815800f00c05074010390b20000080104809031500b0884080a8240c20590500f0001e0310340d505668550440b100a0900102048040c0325031020005000100400d1204000c42c0303a4440703120030004440e000f201e0005000e0003107007050110328001c5150b0f003003000207500b240180c80d140c940341181c409000b0321b0400144141c885e8299030b501d841031080e131405040000c0003628110001002c001d107160b01d902c03505028890200495032700c0c03000c3c3c0e00740f451082c030201d01080d070402e0110a07413040c95444c541c8141214188590034100354032070025220030080410a41d1290220000003204201402e50140c070700f040180500e050402d807081e0840309580340811800b442d0b80d01c0d201d03100030300e40c0d0f0721104440c0407070f08000301d01d000c004012100d40340e070301140070380c0e4150b850315089003c6005d005400b44040d10042005511000c0499000b0216140780c40c4000c0550f4403003e0280281c0b00f020700201d168080510000e4903c6000c03a421070b02d080d00e4692 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 219026142 1250 219024892 219024899
    0x1080604141b09100905040e01051e04030c0215070b091c1d0607210c120507140d090602120c030a080a0f05040b06120111031302030703060c0c030206070806010801 72
    0x10305918458025107030048203103c1002a41c89455500a00213a0303070b140c8181041c20101030000b02d4050b824283c140c2e83c1403900780080058501030765041090000d00420140c0c0d0f0b00e00341a12404003042000b500214a13410085102d000440a442c0c1c242c850007012589484046070590344400640034003500110180b8110711242c000c00351030a0011203507880d4181d11904000140450304501015140740080040078000285080b010300450342150a01240d0a6001d4a1306001e207528803003585c06100c00001d43c1c6050082d000104845100540d040300c078029400000148412018810f200244c4111403001d0b00d44d0050100761344000541c1001541082105041107402820181c800651907540e6000703c0c1c0703014664054030b440785010b00011003c1c1d0401c0810b011901d00d001000c40d0320750749408488194800b0b08802c49400480e041f10340c400c4002c607400060300300031003580020801490241c010b40800d8101c1c4560b00c200d40250292807031581c0d221000c1c0c50350441182c00340d000035030800060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 219027392 1250 219026142 219026161
    0x406120f0507050a050a0216060201061505071e0503070f060c0f0c0809010e0d050105090c131a0108270705090f040c060f050408030318070906050306130501090c0902090108060414 79
    0x1b42000003071031040300c5140d013041d03c1498148003030390040c10050751140c6060001c501c071032081518043c1a881c1052a081d640e4460048011f0802100f1450007442092002802000c00c00c3d500b0f0340303400007012900400c0720302e0240018908085201e021a0032104185100c501030006130403d0350701303c000c0614000a02e0011500f43d55003805080e8801c42d5003540c680401c03000d1142c42d01c02c0c0040e400800e2401d40040801c0126102810282c4031542013060b0100c16401080d2000d001800a00f403500b5151118941d98200c5031031165003001901c85c1c030140b074280d900001500d108441043e11051410745442856020800041710003400d400584070b42041550304c03400710441c1810103032414600303194660342080c1c210790050310ba0502618080284190b9080c044c0000402002441300c2000607600d050f000c0b80d1900d0008050400d2200f2070451401407100a4110310702c0c0aa00c01d041001300354840324001c00070340010000710b00180c1c000780002d5550820744900400d070b580303a14107050b184d80c540400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 219028642 1250 219027392 219027397
    0xf060506040e0a03030b090115020d12020c2a010305060604030f030e0d030806120304231513090b0a0e04080306030c090c09011101200a02070b0406120f0507050a05 72
    0x9410a6035060702c089000300a0200c2c03a80c184c0701e036030041002c00e01401080f0581d801070f009840c0752000442c00075800d580001d80c103e010f5900f0b0800303045488107083d4083c024010701d0039044803400380203038406e1003010640c0f20418040f510f101a088142405c1300460031540111505900084100700500208501d0b440280400b4030900c0c045000444400106040b07503402a81280402c515405100d002e14080d4140130400d0941d000171070a0610700b055890b110030f41c403000720440403c140b850708019203c9680c0c1c2e00302e111160f50003640d40c4844480124000700103110b00c6940324a084901c09240c50000700b05011184641c41d0500a40c0382d0b615444180c0c0d10240100782c2c035109031210007030962110782c052445940381a402d10b440d00480000075000c0071030500344801603498040b81d400001265a03c0030710040d0840040c07030702e850803180181d240026076044003075208804600000e0341940000c0b8428007110b0220140030143c03900465009a500540d814004190107021005549104201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 219029892 1250 219028642 219028651
    0xa15060c05100908280203030610090e01060503010501020d0f05040605030a0b0d2d050a030e03120f0406030c05070302070b0d02090a08150916050103050a021c09020112090f0605 78
    0x103903810080d46001c0c0204441e038003c0e04450110740424440c00c8a010101d0b00030000c07001c0000811100201c040080d103070310004081c1403043e05d01540c0c8040c610301c03c0d844540500401d002d0500196181d14014280b40c100340300f0203005103d001240e591841c4180528040c0041c03944841c0c0c00c103410401c09803a03a402c01003481d20b8107540c94051000c00d6460b1944980c007580503401c149450001000d040281e000f1440134081c02064001c07a80c0300003400001e05038105500361078001e4a580020000034240341c040840540402d00114641d010000e0202c01042101c205031400c1006a45001090742c07540143d60010300541c00c036640070443c0c198400020a080c15074814014070300a04000040c2c51407545402c09005075102800381d02600901807100b54004105400620440413900c4141070306000d640146070401d40c4034070110301544160f80507200d480001c80c0c40aa119090104030784010080d41e10140c2c0010031030240548844890700c10600c2035a00b0005020b4041c42c0c0d071300c9107405088040c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 219031142 1250 219029892 219029903
    0x10321080a11090310050709050111060a05180d0e031e2509020c010204030b060f03030a0e0402041203050909010906081b0a050411040e0a021602010309141002120a15060c 75
    0x483c0d000035684c1030215079507410b950705c8000b42d00c0c28000e100030464111034003e01c0c144001c400444e50800750009116070302916904000c03602d541c40c0606030141165081c610f080b03500ca00c400c0046e07165009400340c254000c1c150219801d0f040580900c81113903004034400600c03504210309141c000790009403010362005034003039020210359413008610100c0e070051821030f0199601283c18801c0050b0380c0541c4d5040f5508032000c2150440640000e80c503417007504d14181c280402140c4030820350f00d454050358001c06444806074803241d81810054855405140c105204620030320000c60380320524810319080d914248010301d03c6210764030807001881402e03000f069010911140009244c0c1d80d501590240340f01402c0c007a910340d45400e8241d10b022a001d000314211500602c00f07a15541d052038080030040390246000318202d502400d012100c82d10904440100d801500c0801c10421142d400401c206c490b20b02caa5600d80e0307034481c2d1010844080c039803010041229190f00300041c41c81600310058150160 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 219032392 1250 219031142 219031147
    0x9090302120c030a0305010b040b030f07140a030617070f06050d06031b0513050603030901080421030506011205091905030c06070207050f06130b0c03070501090506010321080a11 78
    0x1081e039203110740000b0040d035001d9000290090358103502d07009150040502140d220300342410501c100e00705000042001d04558a01c20010708513a00c541c071016100c041d104129a682c1040450040142c486400307840440c1e251680200c003501030006000048504403101117420a00380601250a80c0c4400b00c0e01031140e0312014048003140c00c03103010040040b0300c1b8481d0103296207458244040705840401e0240030520306030070440c143d2404000c651114809280c590101c1e41c841c600b4850600e010b2940b0001019007003071001242d5050b43c0074a01032207090320741070b5038a078034030a492007910012903d410054000310003c0300007880c25140901170742e03c108150380c200301c1030010480c0b621008903410001648061810004e81c1031541812240c01000e4030f889103407030350054560402807200e1090009801d80066480100d280610590300001c1d4408001d102c0c07505241041a501e1000b0301056541c00e183c240241511144400c9110400f0f03a1511210040d070b0795036044c00024860000c0011105204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 219033642 1250 219032392 219032413
    0x3020112020d060914070f0219031707030b150c07121e080901030c0f020d271e0906060f0c0317090109030809030405030a021e1c0b0601080606030109090302 69
    0x80c000c40c009050710200000e03103504140d0011040d404043d2a0001f40010b2070ba0301c0346220343c041044000000c0f158070385020613006103000c660424502c0703607500d0341000d00000c0c0b0a10540c103810101c03030903804176a4004161004035020701e41d88603111884026502400c800c0081071551686002750034029020f0f0702c0c40325600c0030035a01148004800311400d00c400580103070a0b41e01445500f180c00e1b050729081540800541c8040d40c3c501d030016401342030103408a4688655040020a0b1031602e408a00c4c41d0f40700d60307031000f80c0080b030080e01d030a0300e11284058002043d2142c862056400b201c00554031030601c1d00300000b0076038805882003020b400b00f00340e045e01001c04186608403980211600d00c0001030b4801c890034003e04c0f08102401480490f001001300f08599a030000e12105010340465510048081c61051007042050100381d041d0403602c0361954400001c04c0c03a40b0400c0c240c3c0580700c40703262075031703400011289080101d5003e5801041400140031030841c603070000000358440c2c01202c5942c4c92 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 219034892 1250 219033642 219033667
    0x30209040f120203030a0e010203010e010303120e01020a0903150c2010110304060b12061f050424080106030b010905060111011a01090806060303070303110d0c02060a060b0c070302011202 82
    0x1070900b10310301580c00007081c0403241006106055030078030f015000318115418028402150001840003404001500c0460010081b4590210340b039481c040001310350300d9244003009416800544070540d40ca0380e0040448a03080101e0042e00d914a400da69910344d40c14005032903203100c0d0560301d02c0742c90911030401c41483c68061071007400c55020b881140c464a07440c040c94188190f805241d6801d010380e9004440d500c1c039960010340705400111405940c5030120340081039504005003540034035442400d020301c10030110f9500c40350242d0000454030020589440390440f60a842e5070340302c0148800c201800412030300d101a48856004041450306510908040210301d00f9926a0070302c9a1115003810700b00c50f010360308011840000c1440c40083e10311450504002500c80c000d00341c014003810384503002d41140d014000101d4043c0300d08d41904004548607080020b64644045a001525500d00000417540b41d1182080d10f00d01c0600c0030042c0541d070300b158011101c800d81000203c0040c2c2e0240050032074500d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 219036142 1250 219034892 219034913
    0x610050c030c1b030a0c05010819140a1d0c0f06040510120b100215040c030203240c0306030c01030b0109050a030605061f021b0307090207050f0f16030209040f 70
    0x4942c0d002404016401c65039018030342c0668080381d100c0e511040d00d69001a014446040403507600b420140c01da03550303080d03103411020000030b801c80825140c4000c143c6044c0002604a01458491000300a861180d0594101070303610f10a40f0109030b0b01802c03485815107010541000b000c01c020309494107141d072742e1020940800d41c51310800301160f10501601c2c004841407107414886c0c14119180c070618a184640030b91038145003000501d00f500e8200010301031100d0260010019503014080b40c40c0700200025030b0380740c80c5442c413203a50824140c202260b41e0a004a05590240c0b00c001c010381310f4804c2c100d00540040500300c0c01241403000500e400250780d500c9252900065010310f0021501c0d24101081111541d0000f001800714060105d188154582c00600c0e8890240350300700301d44141c3c006600180c0f030011194002d500d410300004002c0c0c100721022440210100600c0212080c0b00e9910710141e407104185442d00c00d882607080c10400141c074115558075042801010101041842c035101e040303880 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 219037392 1250 219036142 219036157
    0x1903080f190f0b040c05090d080705030403020312131e05061c0e0f01051006170c0403150c0e0901060807120902030f0a1b05060a03110d05040606050f06120610050c03 73
    0x1556290500c3d04182842d000c1d6039a10a07061900354175010655000440800c2a550302404c5c00102081120070042c0800c1164080e6400030b0444460300aa400400c55544c00071102800596100708c0001310305080708082e40506084001c41010b507802c0409000c89034100500d806003104200c1c8440c684e080443c842c3c0e1100403010405880c2c5030886108143c01e542d8050001c0d43c405945100c2000b0580e8800001d6500d0004150388003400d4540c114590290701580d0000b520b4602c0007405e40c400407403658001600e030013031511142c83e0541560100f00b015002445288041405a00050b2510740b0030030041b020076a1860b00011000810380209142031821201c040340ca034411100340c02070008100c041e0a02d0b8072249001c160550600c80494980e0289004040074180c513821100102417182c0d00b5980c114032a46400c005600c0c00b404c0c500c0142c1101d102d0940542d1180304180d00c20308111080304ea100c514603060085540340c0f5000d012038901c015801204004040c4900e00340c41350184000c1c580d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 219038642 1250 219037392 219037421
    0xf0309010323040b090d1d04020f130605070b0901140619180c031506020d0804020a09050a0501050405070e01050313020d081207182d090e01020304051903080f19 71
    0x4c40c0340c90f81503603140805441c0d603807040c0244140e51075813101e00d20062480407003064801585a0441c1e08843e9168010400580e06010300034101164080d0700c040509000c6005500703110561b1030f844001401c0356040c01d80e200d03000d490a00040e0351402c0c00d840204d000c1003804084540543d8a03074000b8644044504840801501c4502042950340d140c024611400400c00b041c284c45072410a001e940c035003180003100c1c24484188002425959801d58000c01001131240601181c0351140481004050902426100381e140c40c001c145e40034400d184c1c0310040c9a0684990f45107440da90203022548151031405c981c0402180d40103400a074501c7c0180c041c80c10283c850100905140d800540b92400720076a000000020100801c00703800c44101d1035589421310807031400b00d0701c425074450b480400250005505103007403c0c04800c490a0541c02035120358000c0c002c1d50200c0350366228114160400c03071000b40003d014140441c41800c0c540c24801d400007000526442c01c02003c00c07a0206884850008410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 219039892 1250 219038642 219038663
    0x1140904111902010c0f11120c0f0709050c1c02091513050f181b0c0703050c060c0604030f0203090d061a010c0c060e06071e0309080f030901032304 65
    0x1000b80301c9100c0c100608800c3e0000340161040b1140060604400d69406001c0100c2440c804061000a1044840341d0a0030b00840c2e549500181d10f060341c070030316a10704400350700c2010350000d0700ca042c51107994040e40c5002003040c038083c80b0b500c111000070041c240079810294200401049070362489103411250092005980e203540700011101088182580b00c140124058842c1c03c11a41e58100c664210074152104a421034554054006c1810800e0700b508004200c0000d28074540b403000114442128407402c01c1310068050101800b407140201083c4e1181c981c8480c1c0443c00003030040301d14072600702040c81143c1c00c2c01c481c4000120008111001500c116030385101c011243da0619144802c08402820a0b240b4142d070380d0389030700ca0044030348588410001c2c5904425143d6480c10200ca8113039402c80c03070544c486540c203042503c98003003040c1e0840c00b05101410000d03d00c41d0118000c2c4041891802960500c105400103401400301c80802002c0501030000800031041000c000a00a500070b1103000c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 219041142 1250 219039892 219039907
    0xf150906051002010c020316030c05070801020d0b06070c03020108070c0b041a0c03040b042406080d030605030a0308060f2b02041a22061502030d0c0801140114090411 73
    0x41c0902c0380c01e4101d411641000007084845400100300d075855000480b01040601d0a4182210200c0c10600024a680519000091031500540190518400c8c0a0007009426601801c1203010301ca80c403001040006010310410156000e0400310740c1c80386481c1041904004c8590b0343c3c100d0002d0480d0203c0c0d0b600341c1d0b10744a072000c0e00300140c00c95201620034402c928600702900c2d46491104000c10040c0b51142040c0c182d0106045058102e0015050b50800c1c45080c0d10b442d2044e44030030b29000780d50006450104e000074245800a407030402584c15813100c1009440d8003047c003450015200c0565003042c80300d100940789199890018035400c400d0a02846103039500e00c104003d82c8c6000603d48842c004289015942c0e07619840c084405a00200342c4150440140c102c0340c0142440e50300004031910156141e07001640c0200041a44038442031040000800c0e0036416074a813a000c3c00744085c4031a140c10050600c0d40540d141c0e002400d030f800b000d03a04006142000405039406005606035494000c00d102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 219042392 1250 219041142 219041149
    0x213170105060a061b03110307030302030108060c090a030803071b060207030314060a090902121903020708010603120509031606051c09050327091302030607020705060406030f15090605 81
    0x100e810450890381640340f245040c80c02400400c06041c100403003000d005a641c1098003480380c00c00110101020360b5121030180c100035001790001d01c200100d600520000410600007d01114038582004100004040c1941c580001c4c0b07800040c103100902c0008890301c1403032030313840341929240c9114010140c0e48160302d00d0010b0030303107004015506090072000184400303a601c807911001500d01010700052a25058000601007806030704000d80321340151546106042d040c0010440800e029400f21003c0c544d447d0900c07401ca83c141c0c40042c04840e8045e41840740c1601c16402005250002811a090f0b200722005a0142441c654410804035400082003002c50b044d559000c100030390804020040e511241e00c501e51a0f118801c03e0041019490b0510100d5134001542c020f41108007402c603010301d00d4420800d444001440320706900c00d108600024001f184006800000d5920141c902410289800e20680c0a0000010f038a04210b4691b08031103d5501c01c500540c004206282d80814202d1030001803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 219043642 1250 219042392 219042401
    0x7060e0a0206300c0301090b032d0a0605010b03040c14030307020f06070b0702010608100b1c02011101110301092703050d020c030309070303030c020f071e0b07030e03072306070602131701 82
    0x38103002b50007040410810303a01e0640c1440381c031600f8100fa0884c0da50f44281c1039040810b41c11004140a1a000000c01c0e5894501c0c0594400c03489020184441a10356004281c0c00507450b10851f410740c420440350b80182021045c50140200c0500082d05001c00355a45526900c4100c2c1c11400503951100f082002c2d00e0100091408900d06080c100074515281000c9050308035060391100308401062910011a4854002c0001400d1400004c2000404100031004560f1007840f54024950405c001c62b05c1042d0700c0040400d440d01c101000d400300501a50307064620b40c21a240000742030340d09020b00340c456102840194030910411018007001030131071074060708441d41e11711034070115405440450080100011145c003a52034240c0107040c41c04078440146240c25180c0c00c580075861000ca211070415401c40d031100c1e07012800f01d040c3d43c4450340303070f440d90855030345480441403196444001c0d0ba28642070810003011540c1c0100c00141c500300101e905650300500560004000540c21070040791600420700c179 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 219044892 1250 219043642 219043661
    0x504050a0b1005040f03060203060a03080a0809060708090a140f01020d090510020a0807110a080c0d03050a110a050c0f06011205160f0306020901090302031207060e0a0206300c030109 80
    0x3d00c81d082600700b00d824480c1d81e80b00d0200400d942d031300202051059a0341400400250b501000c07155440d040030741c0080ca14401032311403245c507218441c0400c880c2400703403901da40300d09660401415084a20b841e090b980141c10300f03194403940603050b00c0002c0c0e24400e000800d90410100c0c2e0126505480349001840e2101240500035110b20502050450580c403229558025a00f49001d8411002400143d810075040c1c030b0f0300a00d092030008103070029103404291307102c15070080d0301d0801440c0e898010540c00d036044c081000f20b039124100a6071050a004001400d04100c10000702c984554029569515105003a0841d00940302282c2c506001c004c010841d003400c03a0808003450010300d190642a40c004500350000514030358001c07560b510107912030b10040c0001c5800034112a054090b0782019641035008000c203845545c00c140c0325154503080010300e4080194042d082502d407071002002c40c1e11009403141503070700c2c10000c1e0782051004245c0c0d14003580107841c0005869500d501d48500308007103811115 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 219046142 1250 219044892 219044897
    0x10504030801030b2509080c010e101d060c0601050909030a0c03050703120f020a02010b030c060d0203180708060f130c060305090705042307181406040504050a0b10 72
    0x14108000607070320a62503411203910405681c050344420a620401d5264651041c0100100c1040048250743c8107404c40101d0b118103095501d8172090740011141c00011900860700004401e2405802a10981421552035291a03480343c400c814400018401c2c0d00030a020301803a881400188800d140042c821900200408001c40c5000080000542180c103807001c050144a80460b0710b00034075002e410b0216050700d4805040081c2d01038030f02c2c1040290010311070b0318015803901894010701c0c200041c2525003000020b02c61401c1a01d1a00718001030740c401800c1c110301d480c0d401a1090803034001c019030806051080d001e09454940340301d410b2801c1c06e0040000b08001d000c1d1a40c8000720304120603850a81c0c440c0e142c0494a541c3d1000558030f030030055400140c02074034100141142101c02d0048489450112034002004d4039030383c408803415944d03a4400307410303403001702030030840081101e500032021280030303141504003591140010102c4408407061122503889100c01081d500d05006411100700c1c190 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 219047392 1250 219046142 219046151
    0x10903050c060313050a0c0e07030603050606060d0b180403170f070e061b0a051006050603011206091205030f060103020309031c09080a0f1403061309171b07050301 72
    0x580314195125540c04059001d2280000800c5500c144a18035906180d00a4200c512460b640e1034864581810f62017a04850f0310220b0109100520a010320300481c0c7c1c0000c010700c7c2c84d4540e00e08015031580600b091070321341551410020142d442e0008103940307100d000d0380c03c44864542428050080b0401141811a0411a004100310b40083c1480580c0010007882d111030400d802c03102045040c450510030314800c0720011407240f44001c0c000b0f0311388d503200e1044050b10240300b60b590081040c1d0b40b0a0181c1a4450004e100602c44e0341c03082c42040c0b20440c0120408103902000c2d8403041c17520042c00100d0b90005400104000218079025005600304c01c081c80c08600c1c524101000707589a00800c110400d48a100c0d8044c695092801c0d0004a40550050744c2c680d502c40b80810050072250100410b5404a100c44001c000004044c0095a209001c00f070010700c040d00031031004500078600c861088510020040823003412140f64400340c02000020218061180c44000701c1d83c0c83d2069541c440ca109a052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 219048642 1250 219047392 219047399
    0x20f060c070b18010e010f0315360b030a022701150f09030c18140a0504050d0809060f0c0d050108240606070b06011b030c0c05010203030403020a11010309050102041e050109 76
    0x40f49a542100c1f94030b00041d40702001da490241990b001c0e44015060808850340c0d8024846074a40400584c0364201da821021900c42c4520302558001c6a20f5907054001d03214190150914084200c2c2503402e85061048018034515408040202a0010403807410b10240c080e218503002801d00b503000034582840240b003450341e50f80d088070070b0aa00400c00000041420b81e00b40100b541c003c40010b000402c521715140c5403841440c0000d03c821101030728140703c1c6540050760300d401007110758002c11000d409417490f951081c0c3c0d0850100720103071002d1000c2400304800d0019800e6480b07018081d10310f280c080c0c040d4844502801c2005000c440031000094005024020640e94140864001a50100d81510340c3d50714040141c0c1e00203000040717045040c40368092241019409428203440758400c211049045d03842c0e900491f0f40c0e000803140100944c1c010510f80000c601d40038101040c03401d0524000c10040302ca0341c0c7d4182a60810340c0201061010f2118004040c80e003650480080d180a28141c400f1628 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 219049892 1250 219048642 219048647
    0x902090a020c1b0303040302130504020a050607050613111c0b01060e0d1b050303070b010e010e010305061911040806040b0a021905030a15030506092503020f060c070b18010e01 77
    0x5180500d080d008495010f00c00071034038103009440c021b40d0000d041454015040c6c0e440c001405089500b24480e07940c00401080903e8210260382c002c41e00540244101d80e01c80f203601a0740030480d003060307660885109085080340d039541c40001c440342d0300780d02e403c00c0071000b86040101041d041c0c1150090052140e218506911140c03c2001e07581e403c00c800d040a403028181c100c00c52031140e00040d826010004002c0207100b0740b801007604845c01141d4803029a80d0b00c42d00301c01c00c04000c7c007009117070360031480108001d0302c9084202c4498214200c0000360407021661101d5403035025900107191307508001c04100a0240c42030807507600201d1000194a009002442c1c100c14503801041402848030200100703640161580c8801d100b55861f01e8017100c6143c03282440d0795640e008460b00f6501384030302d01c06406148005440088030500346000c3c00800d50a507401c01880410500f059600240c0038001c03494050720401804001341603150303149644441d4684070a81110100300c52034140152255081040c1e40d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 219051142 1250 219049892 219049903
    0x311011202090d0f080712090f0b030115050318030307210501060c08031e0a02070b061e0402070510020a08160206070525150507030f05010f06030504170d0902090a020c 74
    0x1039024141c030090791802d1405d02c041d80510070005e40f41030b0112590481103904030070302c1000d0707440380310420391001d590301040a01e510003401150024140301d0b0032501c1041c0200007450304200c1420f0900074000c21a60340d2407554008442000001c2e02d6800c1100b00342c0800c8122240e0100303000c809210541c103090020b0080c500c0c01500078555000040014242c0780f6050801c2c41100c0b200554a0042c00c0035450840690840c0d01c2c26540014400c0c003040b100d10f1f208107800709841c10170b030403850f0050020003000000d40100c8000e990034011182c11340b0340c2032031a10051103064001d4031a10380b18185561094007080500d42c00005651040b007d1189882d040003c1c0c540c1c48402c020b003040d44021422040303480d008010801410640625082c0504c81e101d5001f05205841a90741004005182000d030025a1420310590307214488808091003202d10075040907602034054449941c000380d500800840c1c2d076000080d00801d06581d8440c0c02c0840c40d0081c1555004038090005604000c1240c10711611917 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 219052392 1250 219051142 219051169
    0xf03060906011a16080d24061103090d06020d0b27100e070c050606040b0f100203090a030b04020f0105070b060108041e06050f0121150b04020301031101120209 70
    0x5100031100503d40c0003540101c8400e0700940d480101c2030000b61505031141e0b0403d0160b41c5040d4100302d5200030002400c1c90700881e43d8150030700400c0031407a000f000c0c1c0c3c425508640c0448240020031a81040740c50b0403401c2607205101c1e14005944404001c240710072a081c541c1c3c8144128183c401c840f02c0c9040140140b88004400840c555440d00e42504020b11421540d005c3c0301892484010400c0c40c90700800d0303d800190103401590401c1ea00e10040000701c1e413480d6400350307019a9840c08841d2504103c0d003603101c00119401241d16041c410380c00510700741655802100c60b050407004000460034544010b0302c1420083c00e00b40d0030701d50150f44522400350b004240604000342034000a080c0270a6009982411109204a00071884541000e402400c1c04440040444007101d0000075188030079180805941006030351000010015950300041401c00c2c0c0c40d81d4419506c0381000b04ca10f564902c0114000e500c80c001010400800030b0014005450642c001d414051050150b40300584036004d489000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 219053642 1250 219052392 219052409
    0xa1b081531110f040f0212011e030609080c031309111305060703090b1b01050c040602070e07120c030c02012a03020a2c031005040c050108060d021302090f0306090601 73
    0x89680d40c0b0100b000e0b4070004203101d60007070402c0344c40195003c041d4002c2c0b600080840004501c1c2e81c03200c0354014089102d1100309002c81c000001040414916881003100600c600074241c0b4100945080e5455078204442400e0340da0f8a5071005c0100000600c50761251000381c0d1103190620422a424841342480b0f441218091400000c2c401c0070036100f10003a00180890b410310944400101c0108004880d00d1404d0009561900340800c41da0007040003950704039a41c650050031a40e00340704015010302d601520190601141a85424840410f4001e031100200359640000b010038040800130700303441c005183c0181200b1b8540c05800916245104811a00f5240c200582d450218600881e40000003c01d8501d01080d070591102e092050007164032101d40d000c40898490049908140f4100c0300161030081241c415000204019402000841d6000034001e01000040d003064010a0010402c0c3d40c031081e0084d400030f440189441c0140407514400c0040d002401140f0300380401c90354840042c0240b140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 219054892 1250 219053642 219053663
    0x80105100c05070306050a0605060301120204200a05130b070302070603051f03050606031203071d12030c01060905010602070315090206091005030f0705070201020a1b081531 76
    0x40250061003000c401c1680b000c200c0e10010707943c3c280100280300c2914025112801d0210014883c946882528103031540c0d50002c40940c103180e801c020080c0074030004004148003484084036000c44500250400350225112150354130500000b00706031a016170480440a00c062000c070011a50008400302076503000d04001905449420040c40510550142102c6140c6100e1001c4104100810440d000304010780444d05e8585040e41c03100c0302804103c41c0070000035144482d112011010034030340c40d801c00000d019140303030780f140720729031401c5600c403079447c0e0340503034441c0c00403c109426132240b140189450b1016008050a5648206522003102e50030091140c030b80c1c0c1c5420070b56030b03600304a59980400521400400d00c2c1d480c00a000e0350000c0f14018201400314001030741450007081200c4803594144e0151050544035074410400f0f003c2184900202d00b41c40c000414103803020000045a0a0100060301c0c01d4502003c03544c224490700c02030b000e030112981d002c80031241e0200071001c4080340e000d651481c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 219056142 1250 219054892 219054919
    0x506060108370e030409060e0105010507150b06070b070f02062503020c10020a0f09060c0b07110a0b0a060e01050a080c011d03030720090603070b070609050703030906110d080105 78
    0x1409007140003085201d1380000200014400702e60b40c000030031540d500b01c20041d03c0c0c2c0c0e545d005560078003e12401030002c54642100c40200381c0d050340200081030f00200760034149621500c0c1c18921000850300324000c9030046d00001842601080443d42c0b102c070001c00c2900e80003a18000c0c0c1d0303100883c0c003407003070601d0380120b08507105140601c00c1707130140d2450b074004544404140c6402082e05101d107202e40701003002c011000c41d00e2442451843d040c035030404800901a1182103088554062425404059020f00e07042400003402072410103001310318502000c40c00700d0400c81003120404043c1c0c4640d201e00344150080110036008200c8514055003400c0c05184075041104e0300e00309000f05030900d07600d404009014420400c070070544810103603000044902000d40e0b0014000c4012041e25165816807041008105c6018508020004140300d010f001c551001156a00b529150032a00304602041d0f402000b1b100c0c1640c04040d49aa00d28040000d0400707a44007000907184110602075075008040c0c03080c82c5c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 219057392 1250 219056142 219056251
    0xf0506220e10090c0902090a0501080702150415060504270f33090b0415020d0612050c01050a1b020a0806090c041107050c0409050a0b040506060108 65
    0x416208004100381c42c0d000c103808140074010a500c000071a0200c865102c0130815807114425a0703042d010180030802d009061030300560b920b40001700101c08510a0042d080141c42e05c41401900661044444000345008900010306540c850381049011b189000040740c880b10181c0008103601241e0f0b1000786050b9510b041c401145505200c0c00381032849800b0680c5d0a000ca0841d081461401240786903180e0500030050720142c4041120140400264002140c0030901c3d00d0800340c00071186000c018a01081c600000058800c1d036444108013a07016040e05003401000d00c90003950940919290785000c00c52503024041c001d0b81411501340c0c2854905410454a44102d05000360245000700c0b052450501142540d03201041e4500d0300850614070030111a40003503080d1401d15038001c01400d2041c91007400e0000411030540161114410f08550b103002c90080052903000e81d0050001d08810701d4004009000c1900181151007692501100150740515030541040d66040c1a1000e1603561004c81c00d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 219058642 1250 219057392 219057401
    0x210609060e061807140303190201180302030d0605010804050a060504033b0102061605160c030b1e011a36090f01051c080d0507030501090f050622 64
    0x414914440c030b1082c042c107894245000003403030280c102101c0003d80ca444412203031090800382281c06600911610301031002003450041400c080e440001180010a0408039001032000f4059016810000b032518500040d800380e24045c000a007410700c100c1c2007903a1011340d5105500380140041e40e0314800b140400d072117003462041c48a01c4202007490710340700c0202120300300c01010f50507a0f154040080c0d1043d65001040c56480740403c402d4004104c030310301005403941d45c4900c56840215000f00d905d040024400d4460038055405144c07a0041c03031030240420b00c001c2004c81540d140180600d0010041440c008240526030079100d60000e0316445404015002d01e20303860000203190450000d107100c5002d1010401d600094100c81c85001c54446001842e070010342070141c01c1d008000e0314800c04c0780c500c2a40031415618030410a0a1911101d04245800c4420688841c00003d13110801080000d0f16030042011141926504001904295000880f5000440001702401d41000b2545510100c560312 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 219059892 1250 219058642 219058661
    0x13050d050a0201050a0e1e090f151002070504020406090e09070e01050f19030305091009120803091002030a05010302011409090a0509011103040f1208010305070506030c0c010903030902040621060906 87
    0x95680e8007d06120800284a07a94060707016010b00000600100c5901c103d8a0250300d1520031040c002c09440e0a1084c60071f5080480d10a52240ca000020350303807900e02c000d00041c507055807410079030340c00e000800c620b125024160544076031081c801400803010001a15044a0049074031614214640d00410303050806c03050207a948915041c0e002061541110060890300c5003145c0f00c80c0c2e0224401c000b82c41c000000d00600800740c40140f000320011384040021034110440400301c80406a00620207801da0f403044401e0032a5984510041045582001d400c0803900c01504d10340703040141082c0881c905890052239a400643c0b10404070781c40200a601880030031030003898095072454242400308030004106821614200c500f00ca00d04624880c280b000c0c180e907800009068114a4501001a0b40d00080c4c101544a407041012140000c804d1158040c117500c40d03103002c1070038015401008203d6010f5031041400500700008805840c40480c20440407035400000000d1450305030418070b004007102003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 219061142 1250 219059892 219059899
    0x3041523011827050c042a0512090a0302060109020f0307080a0e030a0314010801021312050102090901080a05070602061006140d05010b030412021902040e1f0213050d050a0201050a0e 80
    0x24407802514980484043c80314010300c00c41c3c0861030044240000c0fa4000a01d18112618000c001c0410008648a611002e41c06113400f40c180b0401c03004200403403100362000d040680c48003000c8010990107200160061852034411424582c803402002250303c0014440000c0146503000920070b07a569920044001c000c000440e600e1f42c2440a01030010442c0c40c041000b202e03681400042c08030814000c4802250881d258001d000b498110101140da00301c02d03081350555001d01181006490f2903240e02d000f0300500f8028109641d00e8109079042c081d041d0802c03011900458100070140003070b10640303801c4804900e000b40c100180c2c01d40c00403880c001c140c4100e001609000000620314260b034051801a8025180b403a002c41c01c002082e41e070390034a035185064a40c99500c80c1009031415a1140c43d8100607081541c1d0140041000e0107500e40300320041c40580766003ca29800c0102950700c080e0003800b02542e541c0d6031400b1503181d196560541c6040241001000603400d00d01c0d5115000010034444040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 219062392 1250 219061142 219061181
    0x5070801051008100c09030b0a0605030a030f0f0201140105060904060806010603051902070507140609280e06060910020f0706020307021503060d12050f030415230118 73
    0x3a16000142601c6200d040f880780b06011416003400c2d0749101e801c151600c10384409050340d15603540e1501034000103001042e1036580b1640010251018000300d08542d109603544070030400707881405843c4107003024150086a00d0304550921044140c200ea5055078030484a083c0c07950721402c001005811342d600035103020300480000246054140d00418041c0780c60075010072a032903000c0c0e0580200c6c0642e55000e401580001d0707003084064207107418000340d00c0c00545801d00c0c1c00e00d4607002c40d6581522580001070350001d440c4c021440b51003a05200b01520341240400941d003041c000040d403070b005001084e4490b07032080c10f002d800741d4001c00048032000c410200703442c040b6030744040283d100d4100303079004e0b400303465010205101030315194100da11a60b0000d2104054514070748941008403540c000400500030b0401c131100d060404100074620440c440c1c1c2244000b12050304003074040d02e4a005070074403440420744410440b189100c03d00d0741511345601b50900000d8144088401800518014802081c0c08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 219063642 1250 219062392 219062401
    0x5180a030b06010905010c0302061306020714160803180f040b0307030506070311040b180616080304170c030d02070f0b01120c06020706140c0a08030f040308060d1e0507080105 77
    0x50507845100741001d0b01c460700c40c60754440041d95069089500240140c1044001a101d00b103030380a03182615001d1800141071400c1ea03554981110b030310080c00300c0c1c40d81c1705817100201003201c00781d00c0b00a0940c0d0307800b45044c0321806060214000082e0700b03181c0716a507000b6003440c60b610750f603100d044480c000400711100c040e564140180c4504041e20100300003402c020302d88040300c0211080303400301c48103030a590340b07131004000b8100314a06100c4c920726407014040001c920201c9041103040080b80c06920000d030b50342050315040d003040d14003110740100d03218140000c0e60048004810350748030040c2c0040250769500325151285155145490081c0384941c18000030034041b20075005a0320091180c0e4440c07640300c0e00d400060b40d407002180310f9000024040f02c0b2200c140c44422001c1c0015400c1501100e020800c00d5550011540084a85800c8100004100014164001c5079140c02810598140c2c20380400341d03c1e04100d0104000e1009410f44201380c100e4108201000900000c040030360003004103080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 219064748 1106 219063642 219063653
    0x203040c0b210a020c070e130b090a0b180c01090e01090f020d020a0e01090f0605040b18030d020106090c020c06032a0f04150c1205180a03 61
    0x4000045040c5007480c0a0b085014110310b00000d40c5849a0400b1140740810310341c4022101e00024040c401c0b102d00080021502d90f4101c4500c0c4040da5407468082d14020003a0704c002c164a51000401c601804486250070558644505440d07140100000444c1e60704994041e000000701d144c1e004101409265104c4196000003a0000d41850b4000b03003843c0c100c1c1c00031800344011a42641440b4019a80140d0724000b40c80d2160300d800480d414503070b008000c2d0265000300c01c02c4400c001103c508880e0507000324800524020210ba481411002e0700038084c004134417424814a00300344032103d80500214170704454400181c081d600f16510146c0558a001c0c0742a1020010552081c9450001894000611041d020303541c000e40c2c0c8501c0d00c0c8054909224901021040084040e036030000070b41211410302d050a00e41ca4000c0d10b5458103019115401e0702c07074042c241c7c032000c0342000004201 = true := by decide +kernel

theorem cover : BRFrame.Cov 218884892 219064748 := by
  have h0 := BRFrame.cov_init 218884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 218884892 ≤ n) (h2 : n < 219064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
